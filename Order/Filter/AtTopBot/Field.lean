/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Convergence to ±infinity in linear ordered (semi)fields
-/

public section

namespace Filter

variable {α β : Type*}

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  {l : Filter β} {f : β → α} {r c : α} {n : ℕ}

/-!
### Multiplication by constant: iff lemmas
-/

/-- If `r` is a positive constant, `fun x ↦ r * f x` tends to infinity along a filter
if and only if `f` tends to infinity along the same filter. -/
/-
**Filter.tendsto_const_mul_atTop_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atTop_of_pos (hr : 0 < r) : Tendsto (fun x => r * f x) l
 atTop ↔ Tendsto f l atTop
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_const_mul₀`：∀ {α : Type u_1} {β : Type u_2} [ins
t : Semiring α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {c : α}, 0…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
If `r` is a positive constant, `fun x ↦ r * f x` tends to infinity along a filte
r
if and only if `f` tends to infinity along the same filter.
-/
theorem tendsto_const_mul_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop :=
  ⟨fun h => h.atTop_of_const_mul₀ hr, fun h =>
    Tendsto.atTop_of_const_mul₀ (inv_pos.2 hr) <| by simpa only [inv_mul_cancel_left₀ hr.ne'] ⟩

/-- If `r` is a positive constant, `fun x ↦ f x * r` tends to infinity along a filter
if and only if `f` tends to infinity along the same filter. -/
/-
**Filter.tendsto_mul_const_atTop_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atTop_of_pos (hr : 0 < r) : Tendsto (fun x => f x * r) l
 atTop ↔ Tendsto f l atTop
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.tendsto_const_mul_atTop_of_pos`：tendsto_const_mul_atTop_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop

--- 原说明 ---
If `r` is a positive constant, `fun x ↦ f x * r` tends to infinity along a filte
r
if and only if `f` tends to infinity along the same filter.
-/
theorem tendsto_mul_const_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atTop := by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_pos hr

/-- If `r` is a positive constant, `x ↦ f x / r` tends to infinity along a filter
if and only if `f` tends to infinity along the same filter. -/
/-
**Filter.tendsto_div_const_atTop_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atTop_of_pos (hr : 0 < r) : Tendsto (fun x => f x / r) l
 atTop ↔ Tendsto f l atTop
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.tendsto_mul_const_atTop_of_pos`：tendsto_mul_const_atTop_of_pos (h
r : 0 < r) : Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
If `r` is a positive constant, `x ↦ f x / r` tends to infinity along a filter
if and only if `f` tends to infinity along the same filter.
-/
lemma tendsto_div_const_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ Tendsto f l atTop := by
  simpa only [div_eq_mul_inv] using tendsto_mul_const_atTop_of_pos (inv_pos.2 hr)

/-- If `f` tends to infinity along a nontrivial filter `l`, then
`fun x ↦ r * f x` tends to infinity if and only if `0 < r`. -/
/-
**Filter.tendsto_const_mul_atTop_iff_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) : Tendst
o (fun x => r * f x) l atTop ↔ 0 < r
参数：h : Tendsto f l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atTop_of_pos`：tendsto_const_mul_atTop_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop

--- 原说明 ---
If `f` tends to infinity along a nontrivial filter `l`, then
`fun x ↦ r * f x` tends to infinity if and only if `0 < r`.
-/
theorem tendsto_const_mul_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop ↔ 0 < r := by
  refine ⟨fun hrf => not_le.mp fun hr => ?_, fun hr => (tendsto_const_mul_atTop_of_pos hr).mpr h⟩
  rcases ((h.eventually_ge_atTop 0).and (hrf.eventually_gt_atTop 0)).exists with ⟨x, hx, hrx⟩
  exact (mul_nonpos_of_nonpos_of_nonneg hr hx).not_gt hrx

/-- If `f` tends to infinity along a nontrivial filter `l`, then
`fun x ↦ f x * r` tends to infinity if and only if `0 < r`. -/
/-
**Filter.tendsto_mul_const_atTop_iff_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) : Tendst
o (fun x => f x * r) l atTop ↔ 0 < r
参数：h : Tendsto f l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.tendsto_const_mul_atTop_iff_pos`：tendsto_const_mul_atTop_iff_pos 
[NeBot l] (h : Tendsto f l atTop) : Tendsto (fun x => r * f x) l atTop ↔ 0 < r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to infinity along a nontrivial filter `l`, then
`fun x ↦ f x * r` tends to infinity if and only if `0 < r`.
-/
theorem tendsto_mul_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop ↔ 0 < r := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_pos h]

/-- If `f` tends to infinity along a nontrivial filter `l`, then
`x ↦ f x * r` tends to infinity if and only if `0 < r`. -/
/-
**Filter.tendsto_div_const_atTop_iff_pos** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) : Tendst
o (fun x => f x / r) l atTop ↔ 0 < r
参数：h : Tendsto f l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.tendsto_mul_const_atTop_iff_pos`：tendsto_mul_const_atTop_iff_pos 
[NeBot l] (h : Tendsto f l atTop) : Tendsto (fun x => f x * r) l atTop ↔ 0 < r
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to infinity along a nontrivial filter `l`, then
`x ↦ f x * r` tends to infinity if and only if `0 < r`.
-/
lemma tendsto_div_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ 0 < r := by
  simp only [div_eq_mul_inv, tendsto_mul_const_atTop_iff_pos h, inv_pos]

/-- If `f` tends to infinity along a filter, then `f` multiplied by a positive
constant (on the left) also tends to infinity. For a version working in `ℕ` or `ℤ`, use
`Filter.Tendsto.const_mul_atTop'` instead. -/
/-
**Filter.Tendsto.const_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Semifield α] [inst_1 : LinearOrder
 α] [IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, 0 < r → Filter
.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => r * f x) l Filter.atTop
参数：fun x => r * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atTop_of_pos`：tendsto_const_mul_atTop_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop

--- 原说明 ---
If `f` tends to infinity along a filter, then `f` multiplied by a positive
constant (on the left) also tends to infinity. For a version working in `ℕ` or `
ℤ`, use
`Filter.Tendsto.const_mul_atTop'` instead.
-/
theorem Tendsto.const_mul_atTop (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop :=
  (tendsto_const_mul_atTop_of_pos hr).2 hf

/-- If a function `f` tends to infinity along a filter, then `f` multiplied by a positive
constant (on the right) also tends to infinity. For a version working in `ℕ` or `ℤ`, use
`Filter.Tendsto.atTop_mul_const'` instead. -/
/-
**Filter.Tendsto.atTop_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Semifield α] [inst_1 : LinearOrder
 α] [IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, 0 < r → Filter
.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => f x * r) l Filter.atTop
参数：fun x => f x * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_mul_const_atTop_of_pos`：tendsto_mul_const_atTop_of_pos (h
r : 0 < r) : Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atTop

--- 原说明 ---
If a function `f` tends to infinity along a filter, then `f` multiplied by a pos
itive
constant (on the right) also tends to infinity. For a version working in `ℕ` or 
`ℤ`, use
`Filter.Tendsto.atTop_mul_const'` instead.
-/
theorem Tendsto.atTop_mul_const (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop :=
  (tendsto_mul_const_atTop_of_pos hr).2 hf

/-- If a function `f` tends to infinity along a filter, then `f` divided by a positive
constant also tends to infinity. -/
/-
**Filter.Tendsto.atTop_div_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Semifield α] [inst_1 : LinearOrder
 α] [IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, 0 < r → Filter
.Tendsto f l Filter.atTop → Filter.Tendsto (fun x => f x / r) l Filter.atTop
参数：fun x => f x / r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.Tendsto.atTop_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
If a function `f` tends to infinity along a filter, then `f` divided by a positi
ve
constant also tends to infinity.
-/
theorem Tendsto.atTop_div_const (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x / r) l atTop := by
  simpa only [div_eq_mul_inv] using hf.atTop_mul_const (inv_pos.2 hr)
/-
**Filter.tendsto_const_mul_pow_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_pow_atTop (hn : n != 0) (hc : 0 < c) : Tendsto (fun x =>
 c * x ^ n) atTop atTop
参数：hn : n != 0；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem tendsto_const_mul_pow_atTop (hn : n ≠ 0) (hc : 0 < c) :
    Tendsto (fun x => c * x ^ n) atTop atTop :=
  Tendsto.const_mul_atTop hc (tendsto_pow_atTop hn)
/-
**Filter.tendsto_const_mul_pow_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_pow_atTop_iff : Tendsto (fun x => c * x ^ n) atTop atTop
 ↔ n != 0 ∧ 0 < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `pos_of_mul_pos_left`：pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a 
* b) (hb : 0 <= b) : 0 < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.tendsto_const_mul_pow_atTop`：tendsto_const_mul_pow_atTop (hn : n 
!= 0) (hc : 0 < c) : Tendsto (fun x => c * x ^ n) atTop atTop
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_const_mul_pow_atTop_iff :
    Tendsto (fun x => c * x ^ n) atTop atTop ↔ n ≠ 0 ∧ 0 < c := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => tendsto_const_mul_pow_atTop h.1 h.2⟩
  · rintro rfl
    simp only [pow_zero, not_tendsto_const_atTop] at h
  · rcases ((h.eventually_gt_atTop 0).and (eventually_ge_atTop 0)).exists with ⟨k, hck, hk⟩
    exact pos_of_mul_pos_left hck (pow_nonneg hk _)
/-
**Filter.tendsto_zpow_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_zpow_atTop_atTop {n : Int} (hn : 0 < n) : Tendsto (fun x : α => x 
^ n) atTop atTop
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma tendsto_zpow_atTop_atTop {n : ℤ} (hn : 0 < n) : Tendsto (fun x : α ↦ x ^ n) atTop atTop := by
  lift n to ℕ using hn.le; simp [(Int.natCast_pos.mp hn).ne']
/-
**Filter.map_div_atTop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_div_atTop_eq (k : α) (hk : 0 < k) : map (fun a => a / k) atTop = atTop
参数：k : α；hk : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_atTop_eq_of_gc`：map_atTop_eq_of_gc [Preorder α] [IsDirectedOr
der α] [PartialOrder β] [IsDirectedOrder β] {f : α -> β} (g : β -> α) (b : β) (h
f : Monotone f)…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_div_atTop_eq (k : α) (hk : 0 < k) : map (fun a => a / k) atTop = atTop :=
  map_atTop_eq_of_gc (fun b => k * b) 1 (fun _ _ h => div_le_div_of_nonneg_right h (le_of_lt hk))
    (fun a b _ => (by rw [div_le_iff₀' hk]))
    fun b _ => (by rw [mul_div_assoc, mul_div_cancel₀]; exact ne_of_gt hk)

end LinearOrderedSemifield


section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {l : Filter β} {f : β → α} {r : α}

/-- If `r` is a positive constant, `fun x ↦ r * f x` tends to negative infinity along a filter
if and only if `f` tends to negative infinity along the same filter. -/
/-
**Filter.tendsto_const_mul_atBot_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atBot_of_pos (hr : 0 < r) : Tendsto (fun x => r * f x) l
 atBot ↔ Tendsto f l atBot
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.tendsto_const_mul_atTop_of_pos`：tendsto_const_mul_atTop_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop

--- 原说明 ---
If `r` is a positive constant, `fun x ↦ r * f x` tends to negative infinity alon
g a filter
if and only if `f` tends to negative infinity along the same filter.
-/
theorem tendsto_const_mul_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atBot := by
  simpa only [← mul_neg, ← tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos hr

/-- If `r` is a positive constant, `fun x ↦ f x * r` tends to negative infinity along a filter
if and only if `f` tends to negative infinity along the same filter. -/
/-
**Filter.tendsto_mul_const_atBot_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atBot_of_pos (hr : 0 < r) : Tendsto (fun x => f x * r) l
 atBot ↔ Tendsto f l atBot
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.tendsto_const_mul_atBot_of_pos`：tendsto_const_mul_atBot_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atBot

--- 原说明 ---
If `r` is a positive constant, `fun x ↦ f x * r` tends to negative infinity alon
g a filter
if and only if `f` tends to negative infinity along the same filter.
-/
theorem tendsto_mul_const_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atBot := by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_pos hr

/-- If `r` is a positive constant, `fun x ↦ f x / r` tends to negative infinity along a filter
if and only if `f` tends to negative infinity along the same filter. -/
/-
**Filter.tendsto_div_const_atBot_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atBot_of_pos (hr : 0 < r) : Tendsto (fun x => f x / r) l
 atBot ↔ Tendsto f l atBot
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `r` is a positive constant, `fun x ↦ f x / r` tends to negative infinity alon
g a filter
if and only if `f` tends to negative infinity along the same filter.
-/
lemma tendsto_div_const_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_pos, hr]

/-- If `r` is a negative constant, `fun x ↦ r * f x` tends to infinity along a filter `l`
if and only if `f` tends to negative infinity along `l`. -/
/-
**Filter.tendsto_const_mul_atTop_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atTop_of_neg (hr : r < 0) : Tendsto (fun x => r * f x) l
 atTop ↔ Tendsto f l atBot
参数：hr : r < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.tendsto_const_mul_atBot_of_pos`：tendsto_const_mul_atBot_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atBot
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `r` is a negative constant, `fun x ↦ r * f x` tends to infinity along a filte
r `l`
if and only if `f` tends to negative infinity along `l`.
-/
theorem tendsto_const_mul_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atBot := by
  simpa only [neg_mul, tendsto_neg_atBot_iff] using tendsto_const_mul_atBot_of_pos (neg_pos.2 hr)

/-- If `r` is a negative constant, `fun x ↦ f x * r` tends to infinity along a filter `l`
if and only if `f` tends to negative infinity along `l`. -/
/-
**Filter.tendsto_mul_const_atTop_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atTop_of_neg (hr : r < 0) : Tendsto (fun x => f x * r) l
 atTop ↔ Tendsto f l atBot
参数：hr : r < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.tendsto_const_mul_atTop_of_neg`：tendsto_const_mul_atTop_of_neg (h
r : r < 0) : Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atBot

--- 原说明 ---
If `r` is a negative constant, `fun x ↦ f x * r` tends to infinity along a filte
r `l`
if and only if `f` tends to negative infinity along `l`.
-/
theorem tendsto_mul_const_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atBot := by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_neg hr

/-- If `r` is a negative constant, `fun x ↦ f x / r` tends to infinity along a filter `l`
if and only if `f` tends to negative infinity along `l`. -/
/-
**Filter.tendsto_div_const_atTop_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atTop_of_neg (hr : r < 0) : Tendsto (fun x => f x / r) l
 atTop ↔ Tendsto f l atBot
参数：hr : r < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `r` is a negative constant, `fun x ↦ f x / r` tends to infinity along a filte
r `l`
if and only if `f` tends to negative infinity along `l`.
-/
lemma tendsto_div_const_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_of_neg, hr]

/-- If `r` is a negative constant, `fun x ↦ r * f x` tends to negative infinity along a filter `l`
if and only if `f` tends to infinity along `l`. -/
/-
**Filter.tendsto_const_mul_atBot_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atBot_of_neg (hr : r < 0) : Tendsto (fun x => r * f x) l
 atBot ↔ Tendsto f l atTop
参数：hr : r < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.tendsto_const_mul_atTop_of_pos`：tendsto_const_mul_atTop_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `r` is a negative constant, `fun x ↦ r * f x` tends to negative infinity alon
g a filter `l`
if and only if `f` tends to infinity along `l`.
-/
theorem tendsto_const_mul_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atTop := by
  simpa only [neg_mul, tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos (neg_pos.2 hr)

/-- If `r` is a negative constant, `fun x ↦ f x * r` tends to negative infinity along a filter `l`
if and only if `f` tends to infinity along `l`. -/
/-
**Filter.tendsto_mul_const_atBot_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atBot_of_neg (hr : r < 0) : Tendsto (fun x => f x * r) l
 atBot ↔ Tendsto f l atTop
参数：hr : r < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.tendsto_const_mul_atBot_of_neg`：tendsto_const_mul_atBot_of_neg (h
r : r < 0) : Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atTop

--- 原说明 ---
If `r` is a negative constant, `fun x ↦ f x * r` tends to negative infinity alon
g a filter `l`
if and only if `f` tends to infinity along `l`.
-/
theorem tendsto_mul_const_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atTop := by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_neg hr

/-- If `r` is a negative constant, `fun x ↦ f x / r` tends to negative infinity along a filter `l`
if and only if `f` tends to infinity along `l`. -/
/-
**Filter.tendsto_div_const_atBot_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atBot_of_neg (hr : r < 0) : Tendsto (fun x => f x / r) l
 atBot ↔ Tendsto f l atTop
参数：hr : r < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `r` is a negative constant, `fun x ↦ f x / r` tends to negative infinity alon
g a filter `l`
if and only if `f` tends to infinity along `l`.
-/
lemma tendsto_div_const_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ Tendsto f l atTop := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_neg, hr]

/-- The function `fun x ↦ r * f x` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to negative infinity. -/
/-
**Filter.tendsto_const_mul_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atTop_iff [NeBot l] : Tendsto (fun x => r * f x) l atTop
 ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
The function `fun x ↦ r * f x` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to neg
ative infinity.
-/
theorem tendsto_const_mul_atTop_iff [NeBot l] :
    Tendsto (fun x => r * f x) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_neg]
  · simp [not_tendsto_const_atTop]
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_pos]

/-- The function `fun x ↦ f x * r` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to negative infinity. -/
/-
**Filter.tendsto_mul_const_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atTop_iff [NeBot l] : Tendsto (fun x => f x * r) l atTop
 ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The function `fun x ↦ f x * r` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to neg
ative infinity.
-/
theorem tendsto_mul_const_atTop_iff [NeBot l] :
    Tendsto (fun x => f x * r) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff]

/-- The function `fun x ↦ f x / r` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to negative infinity. -/
/-
**Filter.tendsto_div_const_atTop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atTop_iff [NeBot l] : Tendsto (fun x => f x / r) l atTop
 ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The function `fun x ↦ f x / r` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to neg
ative infinity.
-/
lemma tendsto_div_const_atTop_iff [NeBot l] :
    Tendsto (fun x ↦ f x / r) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff]

/-- The function `fun x ↦ r * f x` tends to negative infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` tends to infinity. -/
/-
**Filter.tendsto_const_mul_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atBot_iff [NeBot l] : Tendsto (fun x => r * f x) l atBot
 ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The function `fun x ↦ r * f x` tends to negative infinity along a nontrivial fil
ter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` ten
ds to infinity.
-/
theorem tendsto_const_mul_atBot_iff [NeBot l] :
    Tendsto (fun x => r * f x) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp only [← tendsto_neg_atTop_iff, ← mul_neg, tendsto_const_mul_atTop_iff, neg_neg]

/-- The function `fun x ↦ f x * r` tends to negative infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` tends to infinity. -/
/-
**Filter.tendsto_mul_const_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atBot_iff [NeBot l] : Tendsto (fun x => f x * r) l atBot
 ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The function `fun x ↦ f x * r` tends to negative infinity along a nontrivial fil
ter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` ten
ds to infinity.
-/
theorem tendsto_mul_const_atBot_iff [NeBot l] :
    Tendsto (fun x => f x * r) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff]

/-- The function `fun x ↦ f x / r` tends to negative infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` tends to infinity. -/
/-
**Filter.tendsto_div_const_atBot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atBot_iff [NeBot l] : Tendsto (fun x => f x / r) l atBot
 ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The function `fun x ↦ f x / r` tends to negative infinity along a nontrivial fil
ter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` ten
ds to infinity.
-/
lemma tendsto_div_const_atBot_iff [NeBot l] :
    Tendsto (fun x ↦ f x / r) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff]

/-- If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ r * f x` tends to infinity if and only if `r < 0`. -/
/-
**Filter.tendsto_const_mul_atTop_iff_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) : Tendst
o (fun x => r * f x) l atTop ↔ r < 0
参数：h : Tendsto f l atBot。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `Filter.disjoint_atBot_atTop`：disjoint_atBot_atTop [PartialOrder α] [Nont
rivial α] : Disjoint (atBot : Filter α) atTop
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ r * f x` tends to infinity if and only if `r < 0`.
-/
theorem tendsto_const_mul_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atTop ↔ r < 0 := by
  simp [tendsto_const_mul_atTop_iff, h, h.not_tendsto disjoint_atBot_atTop]

/-- If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ f x * r` tends to infinity if and only if `r < 0`. -/
/-
**Filter.tendsto_mul_const_atTop_iff_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) : Tendst
o (fun x => f x * r) l atTop ↔ r < 0
参数：h : Tendsto f l atBot。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.tendsto_const_mul_atTop_iff_neg`：tendsto_const_mul_atTop_iff_neg 
[NeBot l] (h : Tendsto f l atBot) : Tendsto (fun x => r * f x) l atTop ↔ r < 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ f x * r` tends to infinity if and only if `r < 0`.
-/
theorem tendsto_mul_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop ↔ r < 0 := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_neg h]

/-- If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ f x / r` tends to infinity if and only if `r < 0`. -/
/-
**Filter.tendsto_div_const_atTop_iff_neg** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) : Tendst
o (fun x => f x / r) l atTop ↔ r < 0
参数：h : Tendsto f l atBot。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.tendsto_mul_const_atTop_iff_neg`：tendsto_mul_const_atTop_iff_neg 
[NeBot l] (h : Tendsto f l atBot) : Tendsto (fun x => f x * r) l atTop ↔ r < 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ f x / r` tends to infinity if and only if `r < 0`.
-/
lemma tendsto_div_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ r < 0 := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff_neg h]

/-- If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ r * f x` tends to negative infinity if and only if `0 < r`. -/
/-
**Filter.tendsto_const_mul_atBot_iff_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) : Tendst
o (fun x => r * f x) l atBot ↔ 0 < r
参数：h : Tendsto f l atBot。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `Filter.disjoint_atBot_atTop`：disjoint_atBot_atTop [PartialOrder α] [Nont
rivial α] : Disjoint (atBot : Filter α) atTop
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ r * f x` tends to negative infinity if and only if `0 < r`.
-/
theorem tendsto_const_mul_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atBot ↔ 0 < r := by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atBot_atTop]

/-- If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ f x * r` tends to negative infinity if and only if `0 < r`. -/
/-
**Filter.tendsto_mul_const_atBot_iff_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) : Tendst
o (fun x => f x * r) l atBot ↔ 0 < r
参数：h : Tendsto f l atBot。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.tendsto_const_mul_atBot_iff_pos`：tendsto_const_mul_atBot_iff_pos 
[NeBot l] (h : Tendsto f l atBot) : Tendsto (fun x => r * f x) l atBot ↔ 0 < r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ f x * r` tends to negative infinity if and only if `0 < r`.
-/
theorem tendsto_mul_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot ↔ 0 < r := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_pos h]

/-- If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ f x / r` tends to negative infinity if and only if `0 < r`. -/
/-
**Filter.tendsto_div_const_atBot_iff_pos** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) : Tendst
o (fun x => f x / r) l atBot ↔ 0 < r
参数：h : Tendsto f l atBot。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.tendsto_mul_const_atBot_iff_pos`：tendsto_mul_const_atBot_iff_pos 
[NeBot l] (h : Tendsto f l atBot) : Tendsto (fun x => f x * r) l atBot ↔ 0 < r
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ f x / r` tends to negative infinity if and only if `0 < r`.
-/
lemma tendsto_div_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ 0 < r := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_pos h]

/-- If `f` tends to infinity along a nontrivial filter,
`fun x ↦ r * f x` tends to negative infinity if and only if `r < 0`. -/
/-
**Filter.tendsto_const_mul_atBot_iff_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) : Tendst
o (fun x => r * f x) l atBot ↔ r < 0
参数：h : Tendsto f l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `Filter.disjoint_atTop_atBot`：∀ {α : Type u_3} [inst : PartialOrder α] [N
ontrivial α], Disjoint Filter.atTop Filter.atBot
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to infinity along a nontrivial filter,
`fun x ↦ r * f x` tends to negative infinity if and only if `r < 0`.
-/
theorem tendsto_const_mul_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atBot ↔ r < 0 := by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atTop_atBot]

/-- If `f` tends to infinity along a nontrivial filter,
`fun x ↦ f x * r` tends to negative infinity if and only if `r < 0`. -/
/-
**Filter.tendsto_mul_const_atBot_iff_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) : Tendst
o (fun x => f x * r) l atBot ↔ r < 0
参数：h : Tendsto f l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.tendsto_const_mul_atBot_iff_neg`：tendsto_const_mul_atBot_iff_neg 
[NeBot l] (h : Tendsto f l atTop) : Tendsto (fun x => r * f x) l atBot ↔ r < 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to infinity along a nontrivial filter,
`fun x ↦ f x * r` tends to negative infinity if and only if `r < 0`.
-/
theorem tendsto_mul_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot ↔ r < 0 := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_neg h]

/-- If `f` tends to infinity along a nontrivial filter,
`fun x ↦ f x / r` tends to negative infinity if and only if `r < 0`. -/
/-
**Filter.tendsto_div_const_atBot_iff_neg** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_div_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) : Tendst
o (fun x => f x / r) l atBot ↔ r < 0
参数：h : Tendsto f l atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.tendsto_mul_const_atBot_iff_neg`：tendsto_mul_const_atBot_iff_neg 
[NeBot l] (h : Tendsto f l atTop) : Tendsto (fun x => f x * r) l atBot ↔ r < 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` tends to infinity along a nontrivial filter,
`fun x ↦ f x / r` tends to negative infinity if and only if `r < 0`.
-/
lemma tendsto_div_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ r < 0 := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_neg h]

/-- If a function `f` tends to infinity along a filter,
then `f` multiplied by a negative constant (on the left) tends to negative infinity. -/
/-
**Filter.Tendsto.const_mul_atTop_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendst
o`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, r < 0 → Filter.Ten
dsto f l Filter.atTop → Filter.Tendsto (fun x => r * f x) l Filter.atBot
参数：fun x => r * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atBot_of_neg`：tendsto_const_mul_atBot_of_neg (h
r : r < 0) : Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atTop

--- 原说明 ---
If a function `f` tends to infinity along a filter,
then `f` multiplied by a negative constant (on the left) tends to negative infin
ity.
-/
theorem Tendsto.const_mul_atTop_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atBot :=
  (tendsto_const_mul_atBot_of_neg hr).2 hf

/-- If a function `f` tends to infinity along a filter,
then `f` multiplied by a negative constant (on the right) tends to negative infinity. -/
/-
**Filter.Tendsto.atTop_mul_const_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendst
o`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, r < 0 → Filter.Ten
dsto f l Filter.atTop → Filter.Tendsto (fun x => f x * r) l Filter.atBot
参数：fun x => f x * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_mul_const_atBot_of_neg`：tendsto_mul_const_atBot_of_neg (h
r : r < 0) : Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atTop

--- 原说明 ---
If a function `f` tends to infinity along a filter,
then `f` multiplied by a negative constant (on the right) tends to negative infi
nity.
-/
theorem Tendsto.atTop_mul_const_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot :=
  (tendsto_mul_const_atBot_of_neg hr).2 hf

/-- If a function `f` tends to infinity along a filter,
then `f` divided by a negative constant tends to negative infinity. -/
/-
**Filter.Tendsto.atTop_div_const_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendst
o`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, r < 0 → Filter.Ten
dsto f l Filter.atTop → Filter.Tendsto (fun x => f x / r) l Filter.atBot
参数：fun x => f x / r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.tendsto_div_const_atBot_of_neg`：tendsto_div_const_atBot_of_neg (h
r : r < 0) : Tendsto (fun x => f x / r) l atBot ↔ Tendsto f l atTop

--- 原说明 ---
If a function `f` tends to infinity along a filter,
then `f` divided by a negative constant tends to negative infinity.
-/
lemma Tendsto.atTop_div_const_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atBot := (tendsto_div_const_atBot_of_neg hr).2 hf

/-- If a function `f` tends to negative infinity along a filter, then `f` multiplied by
a positive constant (on the left) also tends to negative infinity. -/
/-
**Filter.Tendsto.const_mul_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, 0 < r → Filter.Ten
dsto f l Filter.atBot → Filter.Tendsto (fun x => r * f x) l Filter.atBot
参数：fun x => r * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atBot_of_pos`：tendsto_const_mul_atBot_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atBot

--- 原说明 ---
If a function `f` tends to negative infinity along a filter, then `f` multiplied
 by
a positive constant (on the left) also tends to negative infinity.
-/
theorem Tendsto.const_mul_atBot (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atBot :=
  (tendsto_const_mul_atBot_of_pos hr).2 hf

/-- If a function `f` tends to negative infinity along a filter, then `f` multiplied by
a positive constant (on the right) also tends to negative infinity. -/
/-
**Filter.Tendsto.atBot_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, 0 < r → Filter.Ten
dsto f l Filter.atBot → Filter.Tendsto (fun x => f x * r) l Filter.atBot
参数：fun x => f x * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_mul_const_atBot_of_pos`：tendsto_mul_const_atBot_of_pos (h
r : 0 < r) : Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atBot

--- 原说明 ---
If a function `f` tends to negative infinity along a filter, then `f` multiplied
 by
a positive constant (on the right) also tends to negative infinity.
-/
theorem Tendsto.atBot_mul_const (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot :=
  (tendsto_mul_const_atBot_of_pos hr).2 hf

/-- If a function `f` tends to negative infinity along a filter, then `f` divided by
a positive constant also tends to negative infinity. -/
/-
**Filter.Tendsto.atBot_div_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, 0 < r → Filter.Ten
dsto f l Filter.atBot → Filter.Tendsto (fun x => f x / r) l Filter.atBot
参数：fun x => f x / r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.tendsto_div_const_atBot_of_pos`：tendsto_div_const_atBot_of_pos (h
r : 0 < r) : Tendsto (fun x => f x / r) l atBot ↔ Tendsto f l atBot

--- 原说明 ---
If a function `f` tends to negative infinity along a filter, then `f` divided by
a positive constant also tends to negative infinity.
-/
theorem Tendsto.atBot_div_const (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x / r) l atBot := (tendsto_div_const_atBot_of_pos hr).2 hf

/-- If a function `f` tends to negative infinity along a filter,
then `f` multiplied by a negative constant (on the left) tends to positive infinity. -/
/-
**Filter.Tendsto.const_mul_atBot_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendst
o`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, r < 0 → Filter.Ten
dsto f l Filter.atBot → Filter.Tendsto (fun x => r * f x) l Filter.atTop
参数：fun x => r * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atTop_of_neg`：tendsto_const_mul_atTop_of_neg (h
r : r < 0) : Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atBot

--- 原说明 ---
If a function `f` tends to negative infinity along a filter,
then `f` multiplied by a negative constant (on the left) tends to positive infin
ity.
-/
theorem Tendsto.const_mul_atBot_of_neg (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atTop :=
  (tendsto_const_mul_atTop_of_neg hr).2 hf

/-- If a function tends to negative infinity along a filter,
then `f` multiplied by a negative constant (on the right) tends to positive infinity. -/
/-
**Filter.Tendsto.atBot_mul_const_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendst
o`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α] {l : Filter β}   {f : β → α} {r : α}, r < 0 → Filter.Ten
dsto f l Filter.atBot → Filter.Tendsto (fun x => f x * r) l Filter.atTop
参数：fun x => f x * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_mul_const_atTop_of_neg`：tendsto_mul_const_atTop_of_neg (h
r : r < 0) : Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atBot

--- 原说明 ---
If a function tends to negative infinity along a filter,
then `f` multiplied by a negative constant (on the right) tends to positive infi
nity.
-/
theorem Tendsto.atBot_mul_const_of_neg (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop :=
  (tendsto_mul_const_atTop_of_neg hr).2 hf
/-
**Filter.tendsto_neg_const_mul_pow_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_neg_const_mul_pow_atTop {c : α} {n : Nat} (hn : n != 0) (hc : c < 
0) : Tendsto (fun x => c * x ^ n) atTop atBot
参数：hn : n != 0；hc : c < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_mul_atTop_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem tendsto_neg_const_mul_pow_atTop {c : α} {n : ℕ} (hn : n ≠ 0) (hc : c < 0) :
    Tendsto (fun x => c * x ^ n) atTop atBot :=
  (tendsto_pow_atTop hn).const_mul_atTop_of_neg hc
/-
**Filter.tendsto_const_mul_pow_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_mul_pow_atBot_iff {c : α} {n : Nat} : Tendsto (fun x => c * 
x ^ n) atTop atBot ↔ n != 0 ∧ c < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_const_mul_pow_atBot_iff {c : α} {n : ℕ} :
    Tendsto (fun x => c * x ^ n) atTop atBot ↔ n ≠ 0 ∧ c < 0 := by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul, tendsto_const_mul_pow_atTop_iff, neg_pos]

end LinearOrderedField
end Filter

