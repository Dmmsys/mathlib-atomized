/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
module

public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Data.DFinsupp.Order
public import Mathlib.Data.DFinsupp.NeLocus
public import Mathlib.Order.WellFoundedSet

/-!
# Lexicographic order on finitely supported dependent functions

This file defines the lexicographic order on `DFinsupp`.
-/

@[expose] public section


variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

section Zero

variable [∀ i, Zero (α i)]

/-- `DFinsupp.Lex r s` is the lexicographic relation on `Π₀ i, α i`, where `ι` is ordered by `r`,
and `α i` is ordered by `s i`.

The type synonym `Lex (Π₀ i, α i)` has an order given by `DFinsupp.Lex (· < ·) (· < ·)`, whereas
`Colex (Π₀ i, α i)` has an order given by `DFinsupp.Lex (· > ·) (· < ·)`.
-/
/-
**DFinsupp.Lex** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       (ι → ι → Prop) → ((i : ι) → α i → α i → Prop) → (Π₀ (i : ι), α i) → (Π₀ 
(i : ι), α i) → Prop
参数：i : ι；α i；ι → ι → Prop；(i : ι) → α i → α i → Prop；Π₀ (i : ι), α i；Π₀ (i : ι),
 α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.Lex r s` is the lexicographic relation on `Π₀ i, α i`, where `ι` is or
dered by `r`,
and `α i` is ordered by `s i`.

The type synonym `Lex (Π₀ i, α i)` has an order given by `DFinsupp.Lex (· < ·) (
· < ·)`, whereas
`Colex (Π₀ i, α i)` has an order given by `DFinsupp.Lex (· > ·) (· < ·)`.
-/
protected def Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) (x y : Π₀ i, α i) : Prop :=
  Pi.Lex r (s _) x y
/-
**DFinsupp._root_.Pi.lex_eq_dfinsupp_lex** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.lex_eq_dfinsupp_lex {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop}
    (a b : Π₀ i, α i) : Pi.Lex r (s _) (a : ∀ i, α i) b = DFinsupp.Lex r s a b :=
  rfl
/-
**DFinsupp.lex_def** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lex_def {r : ι -> ι -> Prop} {s : forall i, α i -> α i -> Prop} {a b : Π₀ 
i, α i} : DFinsupp.Lex r s a b ↔ exists j, (forall d, r d j -> a d = b d) ∧ s j 
(a j) (b j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lex_def {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop} {a b : Π₀ i, α i} :
    DFinsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s j (a j) (b j) :=
  .rfl
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT ι] [∀ i, LT (α i)] : LT (Lex (Π₀ i, α i)) :=
  ⟨fun f g ↦ DFinsupp.Lex (· < ·) (fun _ ↦ (· < ·)) (ofLex f) (ofLex g)⟩
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT ι] [∀ i, LT (α i)] : LT (Colex (Π₀ i, α i)) :=
  ⟨fun f g ↦ DFinsupp.Lex (· > ·) (fun _ ↦ (· < ·)) (ofColex f) (ofColex g)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Lex.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: LT ι] [inst_2 : (i : ι) → LT (α i)]   {a b : Lex (Π₀ (i : ι), α i)}, a < b ↔ ∃
 i, (∀ j < i, (ofLex a) j = (ofLex b) j) ∧ (ofLex a) i < (ofLex b) i
参数：i : ι；α i；i : ι；α i；Π₀ (i : ι), α i；∀ j < i, (ofLex a) j = (ofLex b) j；ofLex 
a；ofLex b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Lex.lt_iff [LT ι] [∀ i, LT (α i)] {a b : Lex (Π₀ i, α i)} :
    a < b ↔ ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i :=
  .rfl

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: LT ι] [inst_2 : (i : ι) → LT (α i)]   {a b : Colex (Π₀ (i : ι), α i)},   a < b
 ↔ ∃ i, (∀ (j : ι), i < j → (ofColex a) j = (ofColex b) j) ∧ (ofColex a) i < (of
Colex b) i
参数：i : ι；α i；i : ι；α i；Π₀ (i : ι), α i；∀ (j : ι), i < j → (ofColex a) j = (ofCol
ex b) j；ofColex a；ofColex b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Colex.lt_iff [LT ι] [∀ i, LT (α i)] {a b : Colex (Π₀ i, α i)} :
    a < b ↔ ∃ i, (∀ j, i < j → a j = b j) ∧ a i < b i :=
  .rfl
/-
**DFinsupp.lex_lt_of_lt_of_preorder** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lex_lt_of_lt_of_preorder [forall i, Preorder (α i)] (r) [IsStrictOrder ι r
] {x y : Π₀ i, α i} (hlt : x < y) : exists i, (forall j, r j i -> x j <= y j ∧ y
 j <= x j) ∧ x i < y i
参数：α i；r；hlt : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `Set.Finite.wellFoundedOn`：∀ {α : Type u_2} {r : α → α → Prop} [IsStrictO
rder α r] {s : Set α}, s.Finite → s.WellFoundedOn r
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFinsupp.mem_neLocus`：mem_neLocus {f g : Π₀ a, N a} {a : α} : a in f.neL
ocus g ↔ f a != g a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_not_le`：ne_of_not_le (h : ¬a <= b) : a != b
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
-/
theorem lex_lt_of_lt_of_preorder [∀ i, Preorder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
    (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i := by
  obtain ⟨hle, j, hlt⟩ := Pi.lt_def.1 hlt
  classical
  have : (x.neLocus y : Set ι).WellFoundedOn r := (x.neLocus y).finite_toSet.wellFoundedOn
  obtain ⟨i, hi, hl⟩ := this.has_min { i | x i < y i } ⟨⟨j, mem_neLocus.2 hlt.ne⟩, hlt⟩
  refine ⟨i, fun k hk ↦ ⟨hle k, ?_⟩, hi⟩
  exact of_not_not fun h ↦ hl ⟨k, mem_neLocus.2 (ne_of_not_le h).symm⟩ ((hle k).lt_of_not_ge h) hk
/-
**DFinsupp.lex_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lex_lt_of_lt [forall i, PartialOrder (α i)] (r) [IsStrictOrder ι r] {x y :
 Π₀ i, α i} (hlt : x < y) : Pi.Lex r (· < ·) x y
参数：α i；r；hlt : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `DFinsupp.lex_lt_of_lt_of_preorder`：lex_lt_of_lt_of_preorder [forall i, P
reorder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i} (hlt : x < y) : exists 
i, (forall j, r j i -> …
-/
theorem lex_lt_of_lt [∀ i, PartialOrder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
    (hlt : x < y) : Pi.Lex r (· < ·) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder r hlt
/-
**DFinsupp.lex_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lex_iff_of_unique [Unique ι] [forall i, LT (α i)] {r} [Std.Irrefl r] {x y 
: Π₀ i, α i} : DFinsupp.Lex r (fun _ => (· < ·)) x y ↔ x default < y default
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lex_iff_of_unique`：lex_iff_of_unique [Unique ι] [forall i, LT (β i)] 
{r} [Std.Irrefl r] {x y : forall i, β i} : Pi.Lex r (· < ·) x y ↔ x default < y 
default
-/
theorem lex_iff_of_unique [Unique ι] [∀ i, LT (α i)] {r} [Std.Irrefl r] {x y : Π₀ i, α i} :
    DFinsupp.Lex r (fun _ ↦ (· < ·)) x y ↔ x default < y default :=
  Pi.lex_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Lex.lt_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: Unique ι] [inst_2 : (i : ι) → LT (α i)]   [inst_3 : Preorder ι] {x y : Lex (Π₀
 (i : ι), α i)}, x < y ↔ (ofLex x) default < (ofLex y) default
参数：i : ι；α i；i : ι；α i；Π₀ (i : ι), α i；ofLex x；ofLex y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lex_iff_of_unique`：lex_iff_of_unique [Unique ι] [forall i, LT (
α i)] {r} [Std.Irrefl r] {x y : Π₀ i, α i} : DFinsupp.Lex r (fun _ => (· < ·)) x
 y ↔ x default <…
-/
theorem Lex.lt_iff_of_unique [Unique ι] [∀ i, LT (α i)] [Preorder ι] {x y : Lex (Π₀ i, α i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.colex_lt_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：colex_lt_iff_of_unique [Unique ι] [forall i, LT (α i)] [Preorder ι] {x y :
 Colex (Π₀ i, α i)} : x < y ↔ x default < y default
参数：α i；Π₀ i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lex_iff_of_unique`：lex_iff_of_unique [Unique ι] [forall i, LT (
α i)] {r} [Std.Irrefl r] {x y : Π₀ i, α i} : DFinsupp.Lex r (fun _ => (· < ·)) x
 y ↔ x default <…
· 使用定理 `instIrreflGt`：∀ {α : Type u} [inst : Preorder α], Std.Irrefl fun x1 x2 =
> x2 < x1
-/
theorem colex_lt_iff_of_unique [Unique ι] [∀ i, LT (α i)] [Preorder ι] {x y : Colex (Π₀ i, α i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique

variable [LinearOrder ι]
/-
**DFinsupp.Lex.isStrictOrder** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: LinearOrder ι]   [inst_2 : (i : ι) → PartialOrder (α i)], IsStrictOrder (Lex (
Π₀ (i : ι), α i)) fun x1 x2 => x1 < x2
参数：i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
instance Lex.isStrictOrder [∀ i, PartialOrder (α i)] :
    IsStrictOrder (Lex (Π₀ i, α i)) (· < ·) where
  irrefl _ := lt_irrefl (α := Lex (∀ i, α i)) _
  trans _ _ _ := lt_trans (α := Lex (∀ i, α i))

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.isStrictOrder** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: LinearOrder ι]   [inst_2 : (i : ι) → PartialOrder (α i)], IsStrictOrder (Colex
 (Π₀ (i : ι), α i)) fun x1 x2 => x1 < x2
参数：i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.isStrictOrder`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : 
(i : ι) → Zero (α i)] [inst_1 : LinearOrder ι]   [inst_2 : (i : ι) → PartialOrde
r (α i)], IsStri…
-/
instance Colex.isStrictOrder [∀ i, PartialOrder (α i)] :
    IsStrictOrder (Colex (Π₀ i, α i)) (· < ·) :=
  Lex.isStrictOrder (ι := ιᵒᵈ)

/-- The partial order on `DFinsupp`s obtained by the lexicographic ordering.
See `DFinsupp.Lex.linearOrder` for a proof that this partial order is in fact linear. -/
/-
**DFinsupp.Lex.partialOrder** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Lex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       [LinearOrder ι] → [(i : ι) → PartialOrder (α i)] → PartialOrder (Lex (Π₀
 (i : ι), α i))
参数：i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial order on `DFinsupp`s obtained by the lexicographic ordering.
See `DFinsupp.Lex.linearOrder` for a proof that this partial order is in fact li
near.
-/
instance Lex.partialOrder [∀ i, PartialOrder (α i)] : PartialOrder (Lex (Π₀ i, α i)) where
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  toLT := instLTLex
  __ := PartialOrder.lift (fun x : Lex (Π₀ i, α i) ↦ toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := DFinsupp α))

/-- The partial order on `DFinsupp`s obtained by the colexicographic ordering.
See `DFinsupp.Colex.linearOrder` for a proof that this partial order is in fact linear. -/
/-
**DFinsupp.Colex.partialOrder** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Colex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       [LinearOrder ι] → [(i : ι) → PartialOrder (α i)] → PartialOrder (Colex (
Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial order on `DFinsupp`s obtained by the colexicographic ordering.
See `DFinsupp.Colex.linearOrder` for a proof that this partial order is in fact 
linear.
-/
instance Colex.partialOrder [∀ i, PartialOrder (α i)] : PartialOrder (Colex (Π₀ i, α i)) where
  le x y := ⇑(ofColex x) = ⇑(ofColex y) ∨ x < y
  toLT := instLTColex
  __ := PartialOrder.lift (fun x : Colex (Π₀ i, α i) ↦ toColex (⇑(ofColex x)))
    (DFunLike.coe_injective (F := DFinsupp α))

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Lex.le_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: LinearOrder ι] [inst_2 : Unique ι]   [inst_3 : (i : ι) → PartialOrder (α i)] {
x y : Lex (Π₀ (i : ι), α i)}, x ≤ y ↔ (ofLex x) default ≤ (ofLex y) default
参数：i : ι；α i；i : ι；α i；Π₀ (i : ι), α i；ofLex x；ofLex y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lex_le_iff_of_unique`：lex_le_iff_of_unique [Unique ι] [LinearOrder ι]
 [forall i, PartialOrder (β i)] {x y : Lex (forall i, β i)} : x <= y ↔ x default
 <= y default
-/
theorem Lex.le_iff_of_unique [Unique ι] [∀ i, PartialOrder (α i)] {x y : Lex (Π₀ i, α i)} :
    x ≤ y ↔ x default ≤ y default :=
  Pi.lex_le_iff_of_unique

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.le_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: LinearOrder ι] [inst_2 : Unique ι]   [inst_3 : (i : ι) → PartialOrder (α i)] {
x y : Colex (Π₀ (i : ι), α i)},   x ≤ y ↔ (ofColex x) default ≤ (ofColex y) defa
ult
参数：i : ι；α i；i : ι；α i；Π₀ (i : ι), α i；ofColex x；ofColex y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.le_iff_of_unique`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst
 : (i : ι) → Zero (α i)] [inst_1 : LinearOrder ι] [inst_2 : Unique ι]   [inst_3 
: (i : ι) → Partial…
-/
theorem Colex.le_iff_of_unique [Unique ι] [∀ i, PartialOrder (α i)] {x y : Colex (Π₀ i, α i)} :
    x ≤ y ↔ x default ≤ y default :=
  Lex.le_iff_of_unique (ι := ιᵒᵈ)

section LinearOrder

variable [∀ i, LinearOrder (α i)]

set_option backward.privateInPublic true in
/-- Auxiliary helper to case split computably. There is no need for this to be public, as it
can be written with `Or.by_cases` on `lt_trichotomy` once the instances below are constructed. -/
/-
**DFinsupp.lt_trichotomy_rec** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary helper to case split computably. There is no need for this to be publi
c, as it
can be written with `Or.by_cases` on `lt_trichotomy` once the instances below ar
e constructed.
-/
private def lt_trichotomy_rec {P : Lex (Π₀ i, α i) → Lex (Π₀ i, α i) → Sort*}
    (h_lt : ∀ {f g}, toLex f < toLex g → P (toLex f) (toLex g))
    (h_eq : ∀ {f g}, toLex f = toLex g → P (toLex f) (toLex g))
    (h_gt : ∀ {f g}, toLex g < toLex f → P (toLex f) (toLex g)) : ∀ f g, P f g :=
  Lex.rec fun f ↦ Lex.rec fun g ↦ match (motive := ∀ y, (f.neLocus g).min = y → _) _, rfl with
  | ⊤, h => h_eq (neLocus_eq_empty.mp <| Finset.min_eq_top.mp h)
  | (wit : ι), h => by
    apply (mem_neLocus.mp <| Finset.mem_of_min h).lt_or_gt.by_cases <;> intro hwit
    · exact h_lt ⟨wit, fun j hj ↦ notMem_neLocus.mp (Finset.notMem_of_lt_min hj h), hwit⟩
    · exact h_gt ⟨wit, fun j hj ↦
        notMem_neLocus.mp (Finset.notMem_of_lt_min hj <| by rwa [neLocus_comm]), hwit⟩
/-
**DFinsupp.Lex.total_le** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: LinearOrder ι]   [inst_2 : (i : ι) → LinearOrder (α i)], Std.Total fun x1 x2 =
> x1 ≤ x2
参数：i : ι；α i；i : ι；α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
instance Lex.total_le : @Std.Total (Lex (Π₀ i, α i)) (· ≤ ·) where
  total := lt_trichotomy_rec (fun h ↦ Or.inl h.le) (fun h ↦ Or.inl h.le) fun h ↦ Or.inr h.le

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.total_le** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: LinearOrder ι]   [inst_2 : (i : ι) → LinearOrder (α i)], Std.Total fun x1 x2 =
> x1 ≤ x2
参数：i : ι；α i；i : ι；α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.total_le`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : 
ι) → Zero (α i)] [inst_1 : LinearOrder ι]   [inst_2 : (i : ι) → LinearOrder (α i
)], Std.Tot…
-/
instance Colex.total_le : @Std.Total (Colex (Π₀ i, α i)) (· ≤ ·) :=
  Lex.total_le (ι := ιᵒᵈ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The less-or-equal relation for the lexicographic ordering is decidable. -/
/-
**DFinsupp.Lex.decidableLE** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Lex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       [inst_1 : LinearOrder ι] → [inst_2 : (i : ι) → LinearOrder (α i)] → Deci
dableLE (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The less-or-equal relation for the lexicographic ordering is decidable.
-/
instance Lex.decidableLE : DecidableLE (Lex (Π₀ i, α i)) :=
  lt_trichotomy_rec (fun h ↦ isTrue <| Or.inr h)
    (fun h ↦ isTrue <| Or.inl <| congr_arg _ h)
    fun h ↦ isFalse fun h' ↦ lt_irrefl _ (h.trans_le h')

set_option backward.isDefEq.respectTransparency false in
/-- The less-or-equal relation for the colexicographic ordering is decidable. -/
/-
**DFinsupp.Colex.decidableLE** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Colex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       [inst_1 : LinearOrder ι] → [inst_2 : (i : ι) → LinearOrder (α i)] → Deci
dableLE (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The less-or-equal relation for the colexicographic ordering is decidable.
-/
instance Colex.decidableLE : DecidableLE (Colex (Π₀ i, α i)) :=
  Lex.decidableLE (ι := ιᵒᵈ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The less-than relation for the lexicographic ordering is decidable. -/
/-
**DFinsupp.Lex.decidableLT** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Lex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       [inst_1 : LinearOrder ι] → [inst_2 : (i : ι) → LinearOrder (α i)] → Deci
dableLT (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The less-than relation for the lexicographic ordering is decidable.
-/
instance Lex.decidableLT : DecidableLT (Lex (Π₀ i, α i)) :=
  lt_trichotomy_rec (fun h ↦ isTrue h) (fun h ↦ isFalse h.not_lt) fun h ↦ isFalse h.asymm

set_option backward.isDefEq.respectTransparency false in
/-- The less-than relation for the colexicographic ordering is decidable. -/
/-
**DFinsupp.Colex.decidableLT** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Colex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       [inst_1 : LinearOrder ι] → [inst_2 : (i : ι) → LinearOrder (α i)] → Deci
dableLT (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The less-than relation for the colexicographic ordering is decidable.
-/
instance Colex.decidableLT : DecidableLT (Colex (Π₀ i, α i)) :=
  Lex.decidableLT (ι := ιᵒᵈ)

/-- The linear order on `DFinsupp`s obtained by the lexicographic ordering. -/
/-
**DFinsupp.Lex.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Lex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       [LinearOrder ι] → [(i : ι) → LinearOrder (α i)] → LinearOrder (Lex (Π₀ (
i : ι), α i))
参数：i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear order on `DFinsupp`s obtained by the lexicographic ordering.
-/
instance Lex.linearOrder : LinearOrder (Lex (Π₀ i, α i)) where
  le_total := total_of _
  toDecidableLT := decidableLT
  toDecidableLE := decidableLE

/-- The linear order on `DFinsupp`s obtained by the colexicographic ordering. -/
/-
**DFinsupp.Colex.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Colex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : (i : ι) → Zero (α i)] 
→       [LinearOrder ι] → [(i : ι) → LinearOrder (α i)] → LinearOrder (Colex (Π₀
 (i : ι), α i))
参数：i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear order on `DFinsupp`s obtained by the colexicographic ordering.
-/
instance Colex.linearOrder : LinearOrder (Colex (Π₀ i, α i)) where
  le_total := total_of _
  toDecidableLT := decidableLT
  toDecidableLE := decidableLE

end LinearOrder

variable [∀ i, PartialOrder (α i)]

/-
**DFinsupp.toLex_monotone** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toLex_monotone : Monotone (@toLex (Π₀ i, α i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_lt_or_eq`：le_of_lt_or_eq (h : a < b ∨ a = b) : a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `DFinsupp.nonempty_neLocus_iff`：nonempty_neLocus_iff {f g : Π₀ a, N a} : 
(f.neLocus g).Nonempty ↔ f != g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.notMem_neLocus`：notMem_neLocus {f g : Π₀ a, N a} {a : α} : a ∉ 
f.neLocus g ↔ f a = g a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `DFinsupp.mem_neLocus`：mem_neLocus {f g : Π₀ a, N a} {a : α} : a in f.neL
ocus g ↔ f a != g a
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
-/
theorem toLex_monotone : Monotone (@toLex (Π₀ i, α i)) := by
  intro a b h
  refine le_of_lt_or_eq (or_iff_not_imp_right.2 fun hne ↦ ?_)
  classical
  exact ⟨Finset.min' _ (nonempty_neLocus_iff.2 hne),
    fun j hj ↦ notMem_neLocus.1 fun h ↦ (Finset.min'_le _ _ h).not_gt hj,
    (h _).lt_of_ne (mem_neLocus.1 <| Finset.min'_mem _ _)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.toColex_monotone** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toColex_monotone : Monotone (@toColex (Π₀ i, α i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.toLex_monotone`：toLex_monotone : Monotone (@toLex (Π₀ i, α i))
-/
theorem toColex_monotone : Monotone (@toColex (Π₀ i, α i)) :=
  toLex_monotone (ι := ιᵒᵈ)

end Zero

section Covariants

variable [LinearOrder ι] [∀ i, AddMonoid (α i)] [∀ i, LinearOrder (α i)]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `AddLeftStrictMono` (covariant with *strict* inequality `<`) also when proving the one
with the *weak* inequality `≤`. This is actually necessary: addition on `Lex (Π₀ i, α i)` may fail
to be monotone, when it is "just" monotone on `α i`. -/

section Left

variable [∀ i, AddLeftStrictMono (α i)]

set_option backward.defeqAttrib.useBackward true in
/-
**DFinsupp.Lex.addLeftStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOrder (α i)] [∀ (i : ι), AddLe
ftStrictMono (α i)], AddLeftStrictMono (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
-/
instance Lex.addLeftStrictMono : AddLeftStrictMono (Lex (Π₀ i, α i)) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ ↦ ⟨a, fun j ja ↦ congr_arg _ (lta j ja), by dsimp; gcongr⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.addLeftStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOrder (α i)] [∀ (i : ι), AddLe
ftStrictMono (α i)],   AddLeftStrictMono (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.addLeftStrictMono`：∀ {ι : Type u_1} {α : ι → Type u_2} [ins
t : LinearOrder ι] [inst_1 : (i : ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → Li
nearOrder (α i)] [∀ …
-/
instance Colex.addLeftStrictMono : AddLeftStrictMono (Colex (Π₀ i, α i)) :=
  Lex.addLeftStrictMono (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Lex.addLeftMono** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOrder (α i)] [∀ (i : ι), AddLe
ftStrictMono (α i)], AddLeftMono (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `addLeftMono_of_addLeftStrictMono`：∀ (M : Type u_3) [inst : Add M] [inst_
1 : PartialOrder M] [AddLeftStrictMono M], AddLeftMono M
· 使用定理 `DFinsupp.Lex.addLeftStrictMono`：∀ {ι : Type u_1} {α : ι → Type u_2} [ins
t : LinearOrder ι] [inst_1 : (i : ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → Li
nearOrder (α i)] [∀ …
-/
instance Lex.addLeftMono : AddLeftMono (Lex (Π₀ i, α i)) :=
  addLeftMono_of_addLeftStrictMono _

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.addLeftMono** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOrder (α i)] [∀ (i : ι), AddLe
ftStrictMono (α i)], AddLeftMono (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.addLeftMono`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : Li
nearOrder ι] [inst_1 : (i : ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOr
der (α i)] [∀ …
-/
instance Colex.addLeftMono : AddLeftMono (Colex (Π₀ i, α i)) :=
  Lex.addLeftMono (ι := ιᵒᵈ)

end Left

section Right

variable [∀ i, AddRightStrictMono (α i)]

set_option backward.defeqAttrib.useBackward true in
/-
**DFinsupp.Lex.addRightStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOrder (α i)] [∀ (i : ι), AddRi
ghtStrictMono (α i)],   AddRightStrictMono (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
-/
instance Lex.addRightStrictMono : AddRightStrictMono (Lex (Π₀ i, α i)) :=
  ⟨fun f _ _ ⟨a, lta, ha⟩ ↦
    ⟨a, fun j ja ↦ congr_arg (· + ofLex f j) (lta j ja), by dsimp; gcongr⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.addRightStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOrder (α i)] [∀ (i : ι), AddRi
ghtStrictMono (α i)],   AddRightStrictMono (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.addRightStrictMono`：∀ {ι : Type u_1} {α : ι → Type u_2} [in
st : LinearOrder ι] [inst_1 : (i : ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → L
inearOrder (α i)] [∀ …
-/
instance Colex.addRightStrictMono : AddRightStrictMono (Colex (Π₀ i, α i)) :=
  Lex.addRightStrictMono (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Lex.addRightMono** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOrder (α i)] [∀ (i : ι), AddRi
ghtStrictMono (α i)], AddRightMono (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `addRightMono_of_addRightStrictMono`：∀ (M : Type u_3) [inst : Add M] [ins
t_1 : PartialOrder M] [AddRightStrictMono M], AddRightMono M
· 使用定理 `DFinsupp.Lex.addRightStrictMono`：∀ {ι : Type u_1} {α : ι → Type u_2} [in
st : LinearOrder ι] [inst_1 : (i : ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → L
inearOrder (α i)] [∀ …
-/
instance Lex.addRightMono : AddRightMono (Lex (Π₀ i, α i)) :=
  addRightMono_of_addRightStrictMono _

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.addRightMono** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearOrder (α i)] [∀ (i : ι), AddRi
ghtStrictMono (α i)], AddRightMono (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.addRightMono`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : L
inearOrder ι] [inst_1 : (i : ι) → AddMonoid (α i)]   [inst_2 : (i : ι) → LinearO
rder (α i)] [∀ …
-/
instance Colex.addRightMono : AddRightMono (Colex (Π₀ i, α i)) :=
  Lex.addRightMono (ι := ιᵒᵈ)

end Right

end Covariants

section OrderedAddMonoid

variable [LinearOrder ι]

/-
**DFinsupp.Lex.orderBot** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Lex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : LinearOrder ι] →      
 [inst_1 : (i : ι) → AddCommMonoid (α i)] →         [inst_2 : (i : ι) → PartialO
rder (α i)] → [∀ (i : ι), IsBotZeroClass (α i)] → OrderBot (Lex (Π₀ (i : ι), α i
))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Lex.orderBot [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsBotZeroClass (α i)] :
    OrderBot (Lex (Π₀ i, α i)) where
  bot := 0
  bot_le _ := DFinsupp.toLex_monotone bot_le
/-
**DFinsupp.Lex.isBotZeroClass** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddCommMonoid (α i)]   [inst_2 : (i : ι) → PartialOrder (α i)] [∀ (i : ι), 
IsBotZeroClass (α i)], IsBotZeroClass (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isBot_bot`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α], IsBot ⊥
-/
instance Lex.isBotZeroClass [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsBotZeroClass (α i)] :
    IsBotZeroClass (Lex (Π₀ i, α i)) where
  isBot_zero := isBot_bot
/-
**DFinsupp.Colex.orderBot** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.Colex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     [inst : LinearOrder ι] →      
 [inst_1 : (i : ι) → AddCommMonoid (α i)] →         [inst_2 : (i : ι) → PartialO
rder (α i)] → [∀ (i : ι), IsBotZeroClass (α i)] → OrderBot (Colex (Π₀ (i : ι), α
 i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Colex.orderBot [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsBotZeroClass (α i)] :
    OrderBot (Colex (Π₀ i, α i)) where
  bot := 0
  bot_le _ := DFinsupp.toColex_monotone bot_le
/-
**DFinsupp.Colex.isBotZeroClass** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddCommMonoid (α i)]   [inst_2 : (i : ι) → PartialOrder (α i)] [∀ (i : ι), 
IsBotZeroClass (α i)], IsBotZeroClass (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isBot_bot`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α], IsBot ⊥
-/
instance Colex.isBotZeroClass [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsBotZeroClass (α i)] :
    IsBotZeroClass (Colex (Π₀ i, α i)) where
  isBot_zero := isBot_bot
/-
**DFinsupp.Lex.isOrderedCancelAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`
。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddCommMonoid (α i)]   [inst_2 : (i : ι) → PartialOrder (α i)] [∀ (i : ι), 
IsOrderedCancelAddMonoid (α i)],   IsOrderedCancelAddMonoid (Lex (Π₀ (i : ι), α 
i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
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
instance Lex.isOrderedCancelAddMonoid [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedCancelAddMonoid (α i)] :
    IsOrderedCancelAddMonoid (Lex (Π₀ i, α i)) where
  add_le_add_left _ _ h _ := add_le_add_left (α := Lex (∀ i, α i)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (∀ i, α i))

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.isOrderedCancelAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Co
lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddCommMonoid (α i)]   [inst_2 : (i : ι) → PartialOrder (α i)] [∀ (i : ι), 
IsOrderedCancelAddMonoid (α i)],   IsOrderedCancelAddMonoid (Colex (Π₀ (i : ι), 
α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.isOrderedCancelAddMonoid`：∀ {ι : Type u_1} {α : ι → Type u_
2} [inst : LinearOrder ι] [inst_1 : (i : ι) → AddCommMonoid (α i)]   [inst_2 : (
i : ι) → PartialOrder (α i)…
-/
instance Colex.isOrderedCancelAddMonoid [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedCancelAddMonoid (α i)] :
    IsOrderedCancelAddMonoid (Colex (Π₀ i, α i)) :=
  Lex.isOrderedCancelAddMonoid (ι := ιᵒᵈ)
/-
**DFinsupp.Lex.isOrderedAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddCommGroup (α i)]   [inst_2 : (i : ι) → PartialOrder (α i)] [∀ (i : ι), I
sOrderedAddMonoid (α i)],   IsOrderedAddMonoid (Lex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Lex (Π₀ (i : ι), α i)。
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
· 使用定理 `DFinsupp.Lex.isOrderedCancelAddMonoid`：∀ {ι : Type u_1} {α : ι → Type u_
2} [inst : LinearOrder ι] [inst_1 : (i : ι) → AddCommMonoid (α i)]   [inst_2 : (
i : ι) → PartialOrder (α i)…
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
-/
instance Lex.isOrderedAddMonoid [∀ i, AddCommGroup (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedAddMonoid (α i)] :
    IsOrderedAddMonoid (Lex (Π₀ i, α i)) where
  add_le_add_left _ _ := add_le_add_left

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.Colex.isOrderedAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.Colex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : 
ι) → AddCommGroup (α i)]   [inst_2 : (i : ι) → PartialOrder (α i)] [∀ (i : ι), I
sOrderedAddMonoid (α i)],   IsOrderedAddMonoid (Colex (Π₀ (i : ι), α i))
参数：i : ι；α i；i : ι；α i；i : ι；α i；Colex (Π₀ (i : ι), α i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.Lex.isOrderedAddMonoid`：∀ {ι : Type u_1} {α : ι → Type u_2} [in
st : LinearOrder ι] [inst_1 : (i : ι) → AddCommGroup (α i)]   [inst_2 : (i : ι) 
→ PartialOrder (α i)]…
-/
instance Colex.isOrderedAddMonoid [∀ i, AddCommGroup (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedAddMonoid (α i)] :
    IsOrderedAddMonoid (Colex (Π₀ i, α i)) :=
  Lex.isOrderedAddMonoid (ι := ιᵒᵈ)

end OrderedAddMonoid

end DFinsupp

