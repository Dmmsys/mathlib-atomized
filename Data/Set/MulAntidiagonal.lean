/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
module

public import Mathlib.Order.WellFoundedSet

/-! # Multiplication antidiagonal -/

@[expose] public section


namespace Set

variable {α : Type*}

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Set α} {a : α} {x : α × α}

/-- `Set.mulAntidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that multiply to `a`. -/
@[to_additive
      /-- `Set.addAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that add to `a`. -/]
/-
**Set.mulAntidiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：mulAntidiagonal (s t : Set α) (a : α) : Set (α × α)
参数：s t : Set α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulAntidiagonal (s t : Set α) (a : α) : Set (α × α) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a }

@[to_additive (attr := simp)]
/-
**Set.mem_mulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_mulAntidiagonal : x in mulAntidiagonal s t a ↔ x.1 in s ∧ x.2 in t ∧ x
.1 * x.2 = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mulAntidiagonal : x ∈ mulAntidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a :=
  Iff.rfl

@[to_additive]
/-
**Set.mulAntidiagonal_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulAntidiagonal_mono_left (h : s₁ subseteq s₂) : mulAntidiagonal s₁ t a su
bseteq mulAntidiagonal s₂ t a
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mulAntidiagonal_mono_left (h : s₁ ⊆ s₂) : mulAntidiagonal s₁ t a ⊆ mulAntidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
/-
**Set.mulAntidiagonal_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulAntidiagonal_mono_right (h : t₁ subseteq t₂) : mulAntidiagonal s t₁ a s
ubseteq mulAntidiagonal s t₂ a
参数：h : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mulAntidiagonal_mono_right (h : t₁ ⊆ t₂) :
    mulAntidiagonal s t₁ a ⊆ mulAntidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

end Mul

-- The left-hand side is not in simp normal form, see variant below.
@[to_additive]
/-
**Set.swap_mem_mulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：swap_mem_mulAntidiagonal [CommMagma α] {s t : Set α} {a : α} {x : α × α} :
 x.swap in Set.mulAntidiagonal s t a ↔ x in Set.mulAntidiagonal t s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem swap_mem_mulAntidiagonal [CommMagma α] {s t : Set α} {a : α} {x : α × α} :
    x.swap ∈ Set.mulAntidiagonal s t a ↔ x ∈ Set.mulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]

@[to_additive (attr := simp)]
/-
**Set.swap_mem_mulAntidiagonal_aux** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：swap_mem_mulAntidiagonal_aux [CommMagma α] {s t : Set α} {a : α} {x : α × 
α} : x.snd in s ∧ x.fst in t ∧ x.snd * x.fst = a ↔ x in Set.mulAntidiagonal t s 
a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem swap_mem_mulAntidiagonal_aux [CommMagma α] {s t : Set α} {a : α} {x : α × α} :
    x.snd ∈ s ∧ x.fst ∈ t ∧ x.snd * x.fst = a
      ↔ x ∈ Set.mulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]


namespace MulAntidiagonal

section CancelCommMonoid

variable [CommMonoid α] [IsCancelMul α] {s t : Set α} {a : α} {x y : mulAntidiagonal s t a}

-- We have to translate the names manually because the namespace name `MulAntidiagonal`
-- does not match the declaration `mulAntidiagonal` that has the `to_additive` attribute.
@[to_additive Set.AddAntidiagonal.fst_eq_fst_iff_snd_eq_snd]
/-
**Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `Set.M
ulAntidiagonal`。
形式化陈述：fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 
= (y : α × α).2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
-/
theorem fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2 :=
  ⟨fun h =>
    mul_left_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    mul_right_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive Set.AddAntidiagonal.eq_of_fst_eq_fst]
/-
**Set.MulAntidiagonal.eq_of_fst_eq_fst** 是 Mathlib 中的一个定理，位于命名空间 `Set.MulAntidia
gonal`。
形式化陈述：eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y
参数：h : (x : α × α).fst = (y : α × α).fst。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd`：fst_eq_fst_iff_snd_eq_snd
 : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2
-/
theorem eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive Set.AddAntidiagonal.eq_of_snd_eq_snd]
/-
**Set.MulAntidiagonal.eq_of_snd_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `Set.MulAntidia
gonal`。
形式化陈述：eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y
参数：h : (x : α × α).snd = (y : α × α).snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd`：fst_eq_fst_iff_snd_eq_snd
 : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2
-/
theorem eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsCancelMul α] [MulLeftMono α] [MulRightStrictMono α]
  (s t : Set α) (a : α) {x y : mulAntidiagonal s t a}

@[to_additive Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd]
/-
**Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd** 是 Mathlib 中的一个定理，位于命名空间 `
Set.MulAntidiagonal`。
形式化陈述：eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 <= (y : α × α).1) (h₂ :
 (x : α × α).2 <= (y : α × α).2) : x = y
参数：h₁ : (x : α × α).1 <= (y : α × α).1；h₂ : (x : α × α).2 <= (y : α × α).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MulAntidiagonal.eq_of_fst_eq_fst`：eq_of_fst_eq_fst (h : (x : α × α).
fst = (y : α × α).fst) : x = y
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_mulAntidiagonal`：mem_mulAntidiagonal : x in mulAntidiagonal s t 
a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 ≤ (y : α × α).1)
    (h₂ : (x : α × α).2 ≤ (y : α × α).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (mul_lt_mul_of_lt_of_le hlt h₂).ne <|
        (mem_mulAntidiagonal.1 x.2).2.2.trans (mem_mulAntidiagonal.1 y.2).2.2.symm

variable {s t}

@[to_additive Set.AddAntidiagonal.finite_of_isPWO]
/-
**Set.MulAntidiagonal.finite_of_isPWO** 是 Mathlib 中的一个定理，位于命名空间 `Set.MulAntidiag
onal`。
形式化陈述：finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (mulAntidiagonal s t a
).Finite
参数：hs : s.IsPWO；ht : t.IsPWO；a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_mulAntidiagonal`：mem_mulAntidiagonal : x in mulAntidiagonal s t 
a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.PartiallyWellOrderedOn.exists_monotone_subseq`：∀ {α : Type u_2} {r :
 α → α → Prop} {s : Set α} [IsPreorder α r],   s.PartiallyWellOrderedOn r → ∀ {f
 : ℕ → α}, (∀ (n : ℕ), f n ∈ s) → ∃ g, …
· 使用定理 `Order.Preimage.instIsPreorder`：∀ {α : Type u} {β : Type v} {r : α → α → 
Prop} [IsPreorder α r] {f : β → α}, IsPreorder β (f ⁻¹'o r)
· 使用定理 `instIsPreorderLe`：∀ {α : Type u} [inst : Preorder α], IsPreorder α fun x
1 x2 => x1 ≤ x2
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd`：eq_of_fst_le_fst_of_
snd_le_snd (h₁ : (x : α × α).1 <= (y : α × α).1) (h₂ : (x : α × α).2 <= (y : α ×
 α).2) : x = y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (mulAntidiagonal s t a).Finite := by
  by_contra! h
  have h1 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) :=
    fun f ↦ hs fun n ↦ ⟨_, (mem_mulAntidiagonal.1 (f n).2).1⟩
  have h2 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) :=
    fun f ↦ ht fun n ↦ ⟨_, (mem_mulAntidiagonal.1 (f n).2).2.1⟩
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq fun n ↦ (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 fun n ↦ h.natEmbedding _ _
  refine mn.ne (g.injective <| (h.natEmbedding _).injective ?_)
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'

end OrderedCancelCommMonoid

variable [CancelCommMonoid α] [LinearOrder α] [MulLeftMono α] [MulRightStrictMono α]

@[to_additive Set.AddAntidiagonal.finite_of_isWF]
/-
**Set.MulAntidiagonal.finite_of_isWF** 是 Mathlib 中的一个定理，位于命名空间 `Set.MulAntidiago
nal`。
形式化陈述：finite_of_isWF {s t : Set α} (hs : s.IsWF) (ht : t.IsWF) (a) : (mulAntidia
gonal s t a).Finite
参数：hs : s.IsWF；ht : t.IsWF；a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MulAntidiagonal.finite_of_isPWO`：finite_of_isPWO (hs : s.IsPWO) (ht 
: t.IsPWO) (a) : (mulAntidiagonal s t a).Finite
· 使用定理 `CancelMonoid.toIsCancelMul`：∀ (M : Type u) [inst : CancelMonoid M], IsCa
ncelMul M
· 使用定理 `Set.IsWF.isPWO`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}, s.I
sWF → s.IsPWO
-/
theorem finite_of_isWF {s t : Set α} (hs : s.IsWF) (ht : t.IsWF)
    (a) : (mulAntidiagonal s t a).Finite :=
  finite_of_isPWO hs.isPWO ht.isPWO a

end MulAntidiagonal

end Set

