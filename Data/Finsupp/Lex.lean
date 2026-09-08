/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.DFinsupp.Lex
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `Finsupp`.
-/

@[expose] public section


variable {α N : Type*}

namespace Finsupp

section NHasZero

variable [Zero N]

/-- `Finsupp.Lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
and `N` is ordered by `s`.

The type synonym `Lex (α →₀ N)` has an order given by `Finsupp.Lex (· < ·) (· < ·)`.
-/
/-
**Finsupp.Lex** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{α : Type u_1} → {N : Type u_2} → [inst : Zero N] → (α → α → Prop) → (N → 
N → Prop) → (α →₀ N) → (α →₀ N) → Prop
参数：α → α → Prop；N → N → Prop；α →₀ N；α →₀ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.Lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordere
d by `r`,
and `N` is ordered by `s`.

The type synonym `Lex (α →₀ N)` has an order given by `Finsupp.Lex (· < ·) (· < 
·)`.
-/
protected def Lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
  Pi.Lex r s x y
/-
**Finsupp._root_.Pi.lex_eq_finsupp_lex** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.lex_eq_finsupp_lex {r : α → α → Prop} {s : N → N → Prop} (a b : α →₀ N) :
    Pi.Lex r s a b = Finsupp.Lex r s a b :=
  rfl
/-
**Finsupp.lex_def** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lex_def {r : α -> α -> Prop} {s : N -> N -> Prop} {a b : α ->₀ N} : Finsup
p.Lex r s a b ↔ exists j, (forall d, r d j -> a d = b d) ∧ s (a j) (b j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
    Finsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) :=
  .rfl
/-
**Finsupp.lex_eq_invImage_dfinsupp_lex** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lex_eq_invImage_dfinsupp_lex (r : α -> α -> Prop) (s : N -> N -> Prop) : F
insupp.Lex r s = InvImage (DFinsupp.Lex r fun _ => s) toDFinsupp
参数：r : α -> α -> Prop；s : N -> N -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lex_eq_invImage_dfinsupp_lex (r : α → α → Prop) (s : N → N → Prop) :
    Finsupp.Lex r s = InvImage (DFinsupp.Lex r fun _ ↦ s) toDFinsupp :=
  rfl
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] [LT N] : LT (Lex (α →₀ N)) :=
  ⟨fun f g ↦ Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] [LT N] : LT (Colex (α →₀ N)) :=
  ⟨fun f g ↦ Finsupp.Lex (· > ·) (· < ·) (ofColex f) (ofColex g)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.Lex.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : LT α] [inst_2 : 
LT N] {a b : Lex (α →₀ N)},   a < b ↔ ∃ i, (∀ j < i, (ofLex a) j = (ofLex b) j) 
∧ (ofLex a) i < (ofLex b) i
参数：α →₀ N；∀ j < i, (ofLex a) j = (ofLex b) j；ofLex a；ofLex b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Lex.lt_iff [LT α] [LT N] {a b : Lex (α →₀ N)} :
    a < b ↔ ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i :=
  .rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.Colex.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : LT α] [inst_2 : 
LT N] {a b : Colex (α →₀ N)},   a < b ↔ ∃ i, (∀ (j : α), i < j → (ofColex a) j =
 (ofColex b) j) ∧ (ofColex a) i < (ofColex b) i
参数：α →₀ N；∀ (j : α), i < j → (ofColex a) j = (ofColex b) j；ofColex a；ofColex b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Colex.lt_iff [LT α] [LT N] {a b : Colex (α →₀ N)} :
    a < b ↔ ∃ i, (∀ j, i < j → a j = b j) ∧ a i < b i :=
  .rfl
/-
**Finsupp.lex_lt_of_lt_of_preorder** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lex_lt_of_lt_of_preorder [Preorder N] (r) [IsStrictOrder α r] {x y : α ->₀
 N} (hlt : x < y) : exists i, (forall j, r j i -> x j <= y j ∧ y j <= x j) ∧ x i
 < y i
参数：r；hlt : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lex_lt_of_lt_of_preorder`：lex_lt_of_lt_of_preorder [forall i, P
reorder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i} (hlt : x < y) : exists 
i, (forall j, r j i -> …
-/
theorem lex_lt_of_lt_of_preorder [Preorder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  DFinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDFinsupp < y.toDFinsupp)
/-
**Finsupp.lex_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lex_lt_of_lt [PartialOrder N] (r) [IsStrictOrder α r] {x y : α ->₀ N} (hlt
 : x < y) : Pi.Lex r (· < ·) x y
参数：r；hlt : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lex_lt_of_lt`：lex_lt_of_lt [forall i, PartialOrder (α i)] (r) [
IsStrictOrder ι r] {x y : Π₀ i, α i} (hlt : x < y) : Pi.Lex r (· < ·) x y
-/
theorem lex_lt_of_lt [PartialOrder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    Pi.Lex r (· < ·) x y :=
  DFinsupp.lex_lt_of_lt r (id hlt : x.toDFinsupp < y.toDFinsupp)
/-
**Finsupp.lex_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lex_iff_of_unique [Unique α] [LT N] {r} [Std.Irrefl r] {x y : α ->₀ N} : F
insupp.Lex r (· < ·) x y ↔ x default < y default
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lex_iff_of_unique`：lex_iff_of_unique [Unique ι] [forall i, LT (β i)] 
{r} [Std.Irrefl r] {x y : forall i, β i} : Pi.Lex r (· < ·) x y ↔ x default < y 
default
-/
theorem lex_iff_of_unique [Unique α] [LT N] {r} [Std.Irrefl r] {x y : α →₀ N} :
    Finsupp.Lex r (· < ·) x y ↔ x default < y default :=
  Pi.lex_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.Lex.lt_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : Unique α] [inst_
2 : LT N] [inst_3 : Preorder α]   {x y : Lex (α →₀ N)}, x < y ↔ (ofLex x) defaul
t < (ofLex y) default
参数：α →₀ N；ofLex x；ofLex y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lex_iff_of_unique`：lex_iff_of_unique [Unique α] [LT N] {r} [Std.
Irrefl r] {x y : α ->₀ N} : Finsupp.Lex r (· < ·) x y ↔ x default < y default
-/
theorem Lex.lt_iff_of_unique [Unique α] [LT N] [Preorder α] {x y : Lex (α →₀ N)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.Colex.lt_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : Unique α] [inst_
2 : LT N] [inst_3 : Preorder α]   {x y : Colex (α →₀ N)}, x < y ↔ (ofColex x) de
fault < (ofColex y) default
参数：α →₀ N；ofColex x；ofColex y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.lt_iff_of_unique`：∀ {α : Type u_1} {N : Type u_2} [inst : Ze
ro N] [inst_1 : Unique α] [inst_2 : LT N] [inst_3 : Preorder α]   {x y : Lex (α 
→₀ N)}, x < y ↔ (o…
-/
theorem Colex.lt_iff_of_unique [Unique α] [LT N] [Preorder α] {x y : Colex (α →₀ N)} :
    x < y ↔ x default < y default :=
  Lex.lt_iff_of_unique (α := αᵒᵈ)

variable [LinearOrder α]
/-
**Finsupp.Lex.isStrictOrder** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : LinearOrder α] [
inst_2 : PartialOrder N],   IsStrictOrder (Lex (α →₀ N)) fun x1 x2 => x1 < x2
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
instance Lex.isStrictOrder [PartialOrder N] : IsStrictOrder (Lex (α →₀ N)) (· < ·) where
  irrefl _ := lt_irrefl (α := Lex (α → N)) _
  trans _ _ _ := lt_trans (α := Lex (α → N))
/-
**Finsupp.Colex.isStrictOrder** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : LinearOrder α] [
inst_2 : PartialOrder N],   IsStrictOrder (Colex (α →₀ N)) fun x1 x2 => x1 < x2
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.isStrictOrder`：∀ {α : Type u_1} {N : Type u_2} [inst : Zero 
N] [inst_1 : LinearOrder α] [inst_2 : PartialOrder N],   IsStrictOrder (Lex (α →
₀ N)) fun x1 x2…
-/
instance Colex.isStrictOrder [PartialOrder N] : IsStrictOrder (Colex (α →₀ N)) (· < ·) :=
  Lex.isStrictOrder (α := αᵒᵈ)

/-- The partial order on `Finsupp`s obtained by the lexicographic ordering.
See `Finsupp.Lex.linearOrder` for a proof that this partial order is in fact linear. -/
/-
**Finsupp.Lex.partialOrder** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.Lex`。
形式化陈述：{α : Type u_1} → {N : Type u_2} → [inst : Zero N] → [LinearOrder α] → [Par
tialOrder N] → PartialOrder (Lex (α →₀ N))
参数：Lex (α →₀ N)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial order on `Finsupp`s obtained by the lexicographic ordering.
See `Finsupp.Lex.linearOrder` for a proof that this partial order is in fact lin
ear.
-/
instance Lex.partialOrder [PartialOrder N] : PartialOrder (Lex (α →₀ N)) where
  lt := (· < ·)
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Lex (α →₀ N) ↦ toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := Finsupp α N))

/-- The partial order on `Finsupp`s obtained by the colexicographic ordering.
See `Finsupp.Colex.linearOrder` for a proof that this partial order is in fact linear. -/
/-
**Finsupp.Colex.partialOrder** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.Colex`。
形式化陈述：{α : Type u_1} → {N : Type u_2} → [inst : Zero N] → [LinearOrder α] → [Par
tialOrder N] → PartialOrder (Colex (α →₀ N))
参数：Colex (α →₀ N)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial order on `Finsupp`s obtained by the colexicographic ordering.
See `Finsupp.Colex.linearOrder` for a proof that this partial order is in fact l
inear.
-/
instance Colex.partialOrder [PartialOrder N] : PartialOrder (Colex (α →₀ N)) where
  lt := (· < ·)
  le x y := ⇑(ofColex x) = ⇑(ofColex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Colex (α →₀ N) ↦ toColex (⇑(ofColex x)))
    (DFunLike.coe_injective (F := Finsupp α N))

/-- The linear order on `Finsupp`s obtained by the lexicographic ordering. -/
/-
**Finsupp.Lex.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.Lex`。
形式化陈述：{α : Type u_1} → {N : Type u_2} → [inst : Zero N] → [LinearOrder α] → [Lin
earOrder N] → LinearOrder (Lex (α →₀ N))
参数：Lex (α →₀ N)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear order on `Finsupp`s obtained by the lexicographic ordering.
-/
instance Lex.linearOrder [LinearOrder N] : LinearOrder (Lex (α →₀ N)) where
  __ := Lex.partialOrder
  __ := LinearOrder.lift' (toLex ∘ toDFinsupp ∘ ofLex) finsuppEquivDFinsupp.injective

/-- The linear order on `Finsupp`s obtained by the colexicographic ordering. -/
/-
**Finsupp.Colex.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.Colex`。
形式化陈述：{α : Type u_1} → {N : Type u_2} → [inst : Zero N] → [LinearOrder α] → [Lin
earOrder N] → LinearOrder (Colex (α →₀ N))
参数：Colex (α →₀ N)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear order on `Finsupp`s obtained by the colexicographic ordering.
-/
instance Colex.linearOrder [LinearOrder N] : LinearOrder (Colex (α →₀ N)) where
  lt := (· < ·)
  le := (· ≤ ·)
  __ := LinearOrder.lift' (toColex ∘ toDFinsupp ∘ ofColex) finsuppEquivDFinsupp.injective

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.Lex.le_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : LinearOrder α] [
inst_2 : Unique α] [inst_3 : PartialOrder N]   {x y : Lex (α →₀ N)}, x ≤ y ↔ (of
Lex x) default ≤ (ofLex y) default
参数：α →₀ N；ofLex x；ofLex y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lex_le_iff_of_unique`：lex_le_iff_of_unique [Unique ι] [LinearOrder ι]
 [forall i, PartialOrder (β i)] {x y : Lex (forall i, β i)} : x <= y ↔ x default
 <= y default
-/
theorem Lex.le_iff_of_unique [Unique α] [PartialOrder N] {x y : Lex (α →₀ N)} :
    x ≤ y ↔ x default ≤ y default :=
  Pi.lex_le_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.Colex.le_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : LinearOrder α] [
inst_2 : Unique α] [inst_3 : PartialOrder N]   {x y : Colex (α →₀ N)}, x ≤ y ↔ (
ofColex x) default ≤ (ofColex y) default
参数：α →₀ N；ofColex x；ofColex y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.le_iff_of_unique`：∀ {α : Type u_1} {N : Type u_2} [inst : Ze
ro N] [inst_1 : LinearOrder α] [inst_2 : Unique α] [inst_3 : PartialOrder N]   {
x y : Lex (α →₀ N)…
-/
theorem Colex.le_iff_of_unique [Unique α] [PartialOrder N] {x y : Colex (α →₀ N)} :
    x ≤ y ↔ x default ≤ y default :=
  Lex.le_iff_of_unique (α := αᵒᵈ)
/-
**Finsupp.Lex.single_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α], StrictAnti fun a => toLex fun₀ | 
a => 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem Lex.single_strictAnti : StrictAnti fun (a : α) ↦ toLex (single a 1) := by
  intro a b h
  simp only [LT.lt, Finsupp.lex_def]
  simp only [ofLex_toLex, Nat.lt_eq]
  use a
  constructor
  · intro d hd
    simp only [Finsupp.single_eq_of_ne hd.ne, Finsupp.single_eq_of_ne (hd.trans h).ne]
  · simp [h.ne']
/-
**Finsupp.Colex.single_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α], StrictMono fun a => toColex fun₀ 
| a => 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.single_strictAnti`：∀ {α : Type u_1} [inst : LinearOrder α], 
StrictAnti fun a => toLex fun₀ | a => 1
-/
theorem Colex.single_strictMono : StrictMono fun (a : α) ↦ toColex (single a 1) :=
  fun _ _ h ↦ Lex.single_strictAnti (α := αᵒᵈ) h
/-
**Finsupp.Lex.single_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ((toLex fun₀ | b => 1) 
< toLex fun₀ | a => 1) ↔ a < b
参数：(toLex fun₀ | b => 1) < toLex fun₀ | a => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.lt_iff_gt`：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α}
 : f a < f b ↔ b < a
· 使用定理 `Finsupp.Lex.single_strictAnti`：∀ {α : Type u_1} [inst : LinearOrder α], 
StrictAnti fun a => toLex fun₀ | a => 1
-/
theorem Lex.single_lt_iff {a b : α} : toLex (single b 1) < toLex (single a 1) ↔ a < b :=
  Lex.single_strictAnti.lt_iff_gt
/-
**Finsupp.Colex.single_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ((toColex fun₀ | a => 1
) < toColex fun₀ | b => 1) ↔ a < b
参数：(toColex fun₀ | a => 1) < toColex fun₀ | b => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Finsupp.Colex.single_strictMono`：∀ {α : Type u_1} [inst : LinearOrder α]
, StrictMono fun a => toColex fun₀ | a => 1
-/
theorem Colex.single_lt_iff {a b : α} : toColex (single a 1) < toColex (single b 1) ↔ a < b :=
  Colex.single_strictMono.lt_iff_lt
/-
**Finsupp.Lex.single_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ((toLex fun₀ | b => 1) 
≤ toLex fun₀ | a => 1) ↔ a ≤ b
参数：(toLex fun₀ | b => 1) ≤ toLex fun₀ | a => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `Finsupp.Lex.single_strictAnti`：∀ {α : Type u_1} [inst : LinearOrder α], 
StrictAnti fun a => toLex fun₀ | a => 1
-/
theorem Lex.single_le_iff {a b : α} : toLex (single b 1) ≤ toLex (single a 1) ↔ a ≤ b :=
  Lex.single_strictAnti.le_iff_ge
/-
**Finsupp.Colex.single_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ((toColex fun₀ | a => 1
) ≤ toColex fun₀ | b => 1) ↔ a ≤ b
参数：(toColex fun₀ | a => 1) ≤ toColex fun₀ | b => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Finsupp.Colex.single_strictMono`：∀ {α : Type u_1} [inst : LinearOrder α]
, StrictMono fun a => toColex fun₀ | a => 1
-/
theorem Colex.single_le_iff {a b : α} : toColex (single a 1) ≤ toColex (single b 1) ↔ a ≤ b :=
  Colex.single_strictMono.le_iff_le

variable [PartialOrder N]
/-
**Finsupp.toLex_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toLex_monotone : Monotone (@toLex (α ->₀ N))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.toLex_monotone`：toLex_monotone : Monotone (@toLex (Π₀ i, α i))
-/
theorem toLex_monotone : Monotone (@toLex (α →₀ N)) :=
  fun a b h ↦ DFinsupp.toLex_monotone (id h : ∀ i, (toDFinsupp a) i ≤ (toDFinsupp b) i)
/-
**Finsupp.toColex_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toColex_monotone : Monotone (@toColex (α ->₀ N))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toLex_monotone`：toLex_monotone : Monotone (@toLex (α ->₀ N))
-/
theorem toColex_monotone : Monotone (@toColex (α →₀ N)) :=
  toLex_monotone (α := αᵒᵈ)

end NHasZero

section Covariants

variable [LinearOrder α] [AddMonoid N] [LinearOrder N]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `AddLeftStrictMono` (covariant with *strict* inequality `<`) also when proving the one
with the *weak* inequality `≤`.  This is actually necessary: addition on `Lex (α →₀ N)` may fail to
be monotone, when it is "just" monotone on `N`.

See `Counterexamples/ZeroDivisorsInAddMonoidAlgebras.lean` for a counterexample. -/


section Left

variable [AddLeftStrictMono N]

/-
**Finsupp.Lex.addLeftStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddMonoid
 N] [inst_2 : LinearOrder N]   [AddLeftStrictMono N], AddLeftStrictMono (Lex (α 
→₀ N))
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
-/
instance Lex.addLeftStrictMono : AddLeftStrictMono (Lex (α →₀ N)) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ ↦ ⟨a, fun j ja ↦ congr_arg _ (lta j ja), add_lt_add_right ha _⟩⟩
/-
**Finsupp.Colex.addLeftStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddMonoid
 N] [inst_2 : LinearOrder N]   [AddLeftStrictMono N], AddLeftStrictMono (Colex (
α →₀ N))
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.addLeftStrictMono`：∀ {α : Type u_1} {N : Type u_2} [inst : L
inearOrder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddLeftStrictMo
no N], AddLeftStric…
-/
instance Colex.addLeftStrictMono : AddLeftStrictMono (Colex (α →₀ N)) :=
  Lex.addLeftStrictMono (α := αᵒᵈ)
/-
**Finsupp.Lex.addLeftMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddMonoid
 N] [inst_2 : LinearOrder N]   [AddLeftStrictMono N], AddLeftMono (Lex (α →₀ N))
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `addLeftMono_of_addLeftStrictMono`：∀ (M : Type u_3) [inst : Add M] [inst_
1 : PartialOrder M] [AddLeftStrictMono M], AddLeftMono M
· 使用定理 `Finsupp.Lex.addLeftStrictMono`：∀ {α : Type u_1} {N : Type u_2} [inst : L
inearOrder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddLeftStrictMo
no N], AddLeftStric…
-/
instance Lex.addLeftMono : AddLeftMono (Lex (α →₀ N)) :=
  addLeftMono_of_addLeftStrictMono _
/-
**Finsupp.Colex.addLeftMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddMonoid
 N] [inst_2 : LinearOrder N]   [AddLeftStrictMono N], AddLeftMono (Colex (α →₀ N
))
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `addLeftMono_of_addLeftStrictMono`：∀ (M : Type u_3) [inst : Add M] [inst_
1 : PartialOrder M] [AddLeftStrictMono M], AddLeftMono M
· 使用定理 `Finsupp.Colex.addLeftStrictMono`：∀ {α : Type u_1} {N : Type u_2} [inst :
 LinearOrder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddLeftStrict
Mono N], AddLeftStric…
-/
instance Colex.addLeftMono : AddLeftMono (Colex (α →₀ N)) :=
  addLeftMono_of_addLeftStrictMono _

end Left

section Right

variable [AddRightStrictMono N]

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.Lex.addRightStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddMonoid
 N] [inst_2 : LinearOrder N]   [AddRightStrictMono N], AddRightStrictMono (Lex (
α →₀ N))
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
-/
instance Lex.addRightStrictMono : AddRightStrictMono (Lex (α →₀ N)) :=
  ⟨fun f _ _ ⟨a, lta, ha⟩ ↦ ⟨a, fun j ja ↦ congr($(lta j ja) + f j), add_lt_add_left ha _⟩⟩
/-
**Finsupp.Colex.addRightStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddMonoid
 N] [inst_2 : LinearOrder N]   [AddRightStrictMono N], AddRightStrictMono (Colex
 (α →₀ N))
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.addRightStrictMono`：∀ {α : Type u_1} {N : Type u_2} [inst : 
LinearOrder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddRightStrict
Mono N], AddRightStr…
-/
instance Colex.addRightStrictMono : AddRightStrictMono (Colex (α →₀ N)) :=
  Lex.addRightStrictMono (α := αᵒᵈ)
/-
**Finsupp.Lex.addRightMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddMonoid
 N] [inst_2 : LinearOrder N]   [AddRightStrictMono N], AddRightMono (Lex (α →₀ N
))
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `addRightMono_of_addRightStrictMono`：∀ (M : Type u_3) [inst : Add M] [ins
t_1 : PartialOrder M] [AddRightStrictMono M], AddRightMono M
· 使用定理 `Finsupp.Lex.addRightStrictMono`：∀ {α : Type u_1} {N : Type u_2} [inst : 
LinearOrder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddRightStrict
Mono N], AddRightStr…
-/
instance Lex.addRightMono : AddRightMono (Lex (α →₀ N)) :=
  addRightMono_of_addRightStrictMono _
/-
**Finsupp.Colex.addRightMono** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddMonoid
 N] [inst_2 : LinearOrder N]   [AddRightStrictMono N], AddRightMono (Colex (α →₀
 N))
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `addRightMono_of_addRightStrictMono`：∀ (M : Type u_3) [inst : Add M] [ins
t_1 : PartialOrder M] [AddRightStrictMono M], AddRightMono M
· 使用定理 `Finsupp.Colex.addRightStrictMono`：∀ {α : Type u_1} {N : Type u_2} [inst 
: LinearOrder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddRightStri
ctMono N], AddRightStr…
-/
instance Colex.addRightMono : AddRightMono (Colex (α →₀ N)) :=
  addRightMono_of_addRightStrictMono _

end Right

end Covariants

section OrderedAddMonoid

variable [LinearOrder α]

/-
**Finsupp.Lex.orderBot** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.Lex`。
形式化陈述：{α : Type u_1} →   {N : Type u_2} →     [inst : LinearOrder α] →       [in
st_1 : AddCommMonoid N] → [inst_2 : PartialOrder N] → [IsBotZeroClass N] → Order
Bot (Lex (α →₀ N))
参数：Lex (α →₀ N)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Lex.orderBot [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N] :
    OrderBot (Lex (α →₀ N)) where
  bot := 0
  bot_le _ := Finsupp.toLex_monotone bot_le
/-
**Finsupp.Lex.isBotZeroClass** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddCommMo
noid N] [inst_2 : PartialOrder N]   [IsBotZeroClass N], IsBotZeroClass (Lex (α →
₀ N))
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isBot_bot`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α], IsBot ⊥
-/
instance Lex.isBotZeroClass [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N] :
    IsBotZeroClass (Lex (α →₀ N)) where
  isBot_zero := isBot_bot
/-
**Finsupp.Colex.orderBot** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.Colex`。
形式化陈述：{α : Type u_1} →   {N : Type u_2} →     [inst : LinearOrder α] →       [in
st_1 : AddCommMonoid N] → [inst_2 : PartialOrder N] → [IsBotZeroClass N] → Order
Bot (Colex (α →₀ N))
参数：Colex (α →₀ N)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Colex.orderBot [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N] :
    OrderBot (Colex (α →₀ N)) where
  bot := 0
  bot_le _ := Finsupp.toColex_monotone bot_le
/-
**Finsupp.Colex.isBotZeroClass** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddCommMo
noid N] [inst_2 : PartialOrder N]   [IsBotZeroClass N], IsBotZeroClass (Colex (α
 →₀ N))
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isBot_bot`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α], IsBot ⊥
-/
instance Colex.isBotZeroClass [AddCommMonoid N] [PartialOrder N] [IsBotZeroClass N] :
    IsBotZeroClass (Colex (α →₀ N)) where
  isBot_zero := isBot_bot
/-
**Finsupp.Lex.isOrderedCancelAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddCommMo
noid N] [inst_2 : PartialOrder N]   [IsOrderedCancelAddMonoid N], IsOrderedCance
lAddMonoid (Lex (α →₀ N))
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `Pi.Lex.isOrderedAddCancelMonoid`：∀ {ι : Type u_1} {α : ι → Type u_2} [in
st : LinearOrder ι] [inst_1 : (i : ι) → AddCommMonoid (α i)]   [inst_2 : (i : ι)
 → PartialOrder (α i)…
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `Lex.instIsLeftCancelAdd`：∀ {α : Type u_1} [inst : Add α] [IsLeftCancelAd
d α], IsLeftCancelAdd (Lex α)
· 使用定理 `Pi.instIsLeftCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I)
 → Add (f i)] [∀ (i : I), IsLeftCancelAdd (f i)],   IsLeftCancelAdd ((i : I) → f
 i)
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
-/
instance Lex.isOrderedCancelAddMonoid
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Lex (α →₀ N)) where
  add_le_add_left _ _ h _ := add_le_add_left (α := Lex (α → N)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (α → N))
/-
**Finsupp.Colex.isOrderedCancelAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Cole
x`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : LinearOrder α] [inst_1 : AddCommMo
noid N] [inst_2 : PartialOrder N]   [IsOrderedCancelAddMonoid N], IsOrderedCance
lAddMonoid (Colex (α →₀ N))
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.isOrderedCancelAddMonoid`：∀ {α : Type u_1} {N : Type u_2} [i
nst : LinearOrder α] [inst_1 : AddCommMonoid N] [inst_2 : PartialOrder N]   [IsO
rderedCancelAddMonoid N], …
-/
instance Colex.isOrderedCancelAddMonoid
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] :
    IsOrderedCancelAddMonoid (Colex (α →₀ N)) :=
  Lex.isOrderedCancelAddMonoid (α := αᵒᵈ)

end OrderedAddMonoid

end Finsupp

