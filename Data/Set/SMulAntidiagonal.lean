/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Order.AddTorsor
public import Mathlib.Order.WellFoundedSet

/-!
# Antidiagonal for scalar multiplication

Given partially ordered sets `G` and `P`, with an action of `G` on `P`, we construct, for any
element `a` in `P` and subsets `s` in `G` and `t` in `P`, the set of all pairs of an element in `s`
and an element in `t` that scalar-multiply to `a`.

## Definitions
* SMul.antidiagonal : Set-valued antidiagonal for SMul.
* VAdd.antidiagonal : Set-valued antidiagonal for VAdd.
-/

@[expose] public section

variable {G P : Type*}

namespace Set

section SMul

variable [SMul G P] {s s₁ s₂ : Set G} {t t₁ t₂ : Set P} {a : P} {x : G × P}

/-- `smulAntidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that scalar multiply to `a`. -/
@[to_additive /-- `vaddAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that vector-add to `a`. -/]
/-
**Set.smulAntidiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：smulAntidiagonal (s : Set G) (t : Set P) (a : P) : Set (G × P)
参数：s : Set G；t : Set P；a : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def smulAntidiagonal (s : Set G) (t : Set P) (a : P) : Set (G × P) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a }

@[to_additive (attr := simp)]
/-
**Set.mem_smulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_smulAntidiagonal : x in smulAntidiagonal s t a ↔ x.1 in s ∧ x.2 in t ∧
 x.1 • x.2 = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_smulAntidiagonal : x ∈ smulAntidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a :=
  Iff.rfl

@[to_additive]
/-
**Set.smulAntidiagonal_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smulAntidiagonal_mono_left (h : s₁ subseteq s₂) : smulAntidiagonal s₁ t a 
subseteq smulAntidiagonal s₂ t a
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem smulAntidiagonal_mono_left (h : s₁ ⊆ s₂) :
    smulAntidiagonal s₁ t a ⊆ smulAntidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
/-
**Set.smulAntidiagonal_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smulAntidiagonal_mono_right (h : t₁ subseteq t₂) : smulAntidiagonal s t₁ a
 subseteq smulAntidiagonal s t₂ a
参数：h : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem smulAntidiagonal_mono_right (h : t₁ ⊆ t₂) :
    smulAntidiagonal s t₁ a ⊆ smulAntidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

end SMul

open SMul

namespace SMulAntidiagonal

variable {s : Set G} {t : Set P} {a : P}

section CancelSMul

variable [SMul G P] {x y : smulAntidiagonal s t a}

@[to_additive VAddAntidiagonal.fst_eq_fst_iff_snd_eq_snd]
/-
**Set.SMulAntidiagonal.fst_eq_fst_iff_snd_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `Set.
SMulAntidiagonal`。
形式化陈述：fst_eq_fst_iff_snd_eq_snd [IsCancelSMul G P] : (x : G × P).1 = (y : G × P)
.1 ↔ (x : G × P).2 = (y : G × P).2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCancelSMul.left_cancel`：IsCancelSMul.left_cancel {G P} [SMul G P] [IsC
ancelSMul G P] (a : G) (b c : P) : a • b = a • c -> b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCancelSMul.right_cancel`：IsCancelSMul.right_cancel {G P} [SMul G P] [I
sCancelSMul G P] (a b : G) (c : P) : a • c = b • c -> a = b
-/
theorem fst_eq_fst_iff_snd_eq_snd [IsCancelSMul G P] :
    (x : G × P).1 = (y : G × P).1 ↔ (x : G × P).2 = (y : G × P).2 :=
  ⟨fun h =>
    IsCancelSMul.left_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    IsCancelSMul.right_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive VAddAntidiagonal.eq_of_fst_eq_fst]
/-
**Set.SMulAntidiagonal.eq_of_fst_eq_fst** 是 Mathlib 中的一个定理，位于命名空间 `Set.SMulAntid
iagonal`。
形式化陈述：eq_of_fst_eq_fst [IsLeftCancelSMul G P] (h : (x : G × P).fst = (y : G × P)
.fst) : x = y
参数：h : (x : G × P).fst = (y : G × P).fst。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用引理 `IsLeftCancelSMul.left_cancel`：IsLeftCancelSMul.left_cancel {G P} [SMul G
 P] [IsLeftCancelSMul G P] (a : G) (b c : P) : a • b = a • c -> b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem eq_of_fst_eq_fst [IsLeftCancelSMul G P] (h : (x : G × P).fst = (y : G × P).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| IsLeftCancelSMul.left_cancel _ _ _
    (y.2.2.2.trans <| by rw [← h]; exact x.2.2.2.symm).symm

@[to_additive VAddAntidiagonal.finite_of_finite]
/-
**Set.SMulAntidiagonal.finite_of_finite_fst** 是 Mathlib 中的一个定理，位于命名空间 `Set.SMulA
ntidiagonal`。
形式化陈述：finite_of_finite_fst [IsLeftCancelSMul G P] (hs : s.Finite) (t) (p : P) : 
(s.smulAntidiagonal t p).Finite
参数：hs : s.Finite；t；p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_injOn`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set α}
 {t : Set β}, Set.MapsTo f s t → Set.InjOn f s → t.Finite → s.Finite
-/
theorem finite_of_finite_fst [IsLeftCancelSMul G P] (hs : s.Finite) (t) (p : P) :
    (s.smulAntidiagonal t p).Finite :=
  hs.of_injOn (fun _ ⟨h, _⟩ ↦ h) fun _ _ _ _ _ ↦ by
    grind only [mem_smulAntidiagonal, IsLeftCancelSMul.left_cancel]

@[to_additive VAddAntidiagonal.eq_of_snd_eq_snd]
/-
**Set.SMulAntidiagonal.eq_of_snd_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `Set.SMulAntid
iagonal`。
形式化陈述：eq_of_snd_eq_snd [IsCancelSMul G P] (h : (x : G × P).snd = (y : G × P).snd
) : x = y
参数：h : (x : G × P).snd = (y : G × P).snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.SMulAntidiagonal.fst_eq_fst_iff_snd_eq_snd`：fst_eq_fst_iff_snd_eq_sn
d [IsCancelSMul G P] : (x : G × P).1 = (y : G × P).1 ↔ (x : G × P).2 = (y : G × 
P).2
-/
theorem eq_of_snd_eq_snd [IsCancelSMul G P] (h : (x : G × P).snd = (y : G × P).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

end CancelSMul

variable [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P]
  {x y : smulAntidiagonal s t a}

@[to_additive VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd]
/-
**Set.SMulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd** 是 Mathlib 中的一个定理，位于命名空间 
`Set.SMulAntidiagonal`。
形式化陈述：eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : G × P).1 <= (y : G × P).1) (h₂ :
 (x : G × P).2 <= (y : G × P).2) : x = y
参数：h₁ : (x : G × P).1 <= (y : G × P).1；h₂ : (x : G × P).2 <= (y : G × P).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SMulAntidiagonal.eq_of_fst_eq_fst`：eq_of_fst_eq_fst [IsLeftCancelSMu
l G P] (h : (x : G × P).fst = (y : G × P).fst) : x = y
· 使用定理 `IsCancelSMul.toIsLeftCancelSMul`：∀ {G : Type u_9} {P : Type u_10} {inst 
: SMul G P} [self : IsCancelSMul G P], IsLeftCancelSMul G P
· 使用定理 `instIsCancelSMulOfIsOrderedCancelSMul`：∀ {G : Type u_1} {P : Type u_2} [
inst : PartialOrder G] [inst_1 : PartialOrder P] [inst_2 : SMul G P]   [IsOrdere
dCancelSMul G P], IsCancelS…
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `SMul.smul_lt_smul_of_lt_of_le`：smul_lt_smul_of_lt_of_le [Preorder G] [Pr
eorder P] [SMul G P] [IsOrderedCancelSMul G P] {a b : G} {c d : P} (h₁ : a < b) 
(h₂ : c <= d) : a •…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_smulAntidiagonal`：mem_smulAntidiagonal : x in smulAntidiagonal s
 t a ↔ x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : G × P).1 ≤ (y : G × P).1)
    (h₂ : (x : G × P).2 ≤ (y : G × P).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (smul_lt_smul_of_lt_of_le hlt h₂).ne <|
        (mem_smulAntidiagonal.1 x.2).2.2.trans (mem_smulAntidiagonal.1 y.2).2.2.symm

@[to_additive VAddAntidiagonal.finite_of_isPWO]
/-
**Set.SMulAntidiagonal.finite_of_isPWO** 是 Mathlib 中的一个定理，位于命名空间 `Set.SMulAntidi
agonal`。
形式化陈述：finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (smulAntidiagonal s t 
a).Finite
参数：hs : s.IsPWO；ht : t.IsPWO；a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_smulAntidiagonal`：mem_smulAntidiagonal : x in smulAntidiagonal s
 t a ↔ x.1 in s ∧ x.2 in t ∧ x.1 • x.2 = a
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
· 使用定理 `Set.SMulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd`：eq_of_fst_le_fst_of
_snd_le_snd (h₁ : (x : G × P).1 <= (y : G × P).1) (h₂ : (x : G × P).2 <= (y : G 
× P).2) : x = y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (smulAntidiagonal s t a).Finite := by
  by_contra! h
  have h1 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) :=
    fun f ↦ hs fun n ↦ ⟨_, (mem_smulAntidiagonal.1 (f n).2).1⟩
  have h2 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) :=
    fun f ↦ ht fun n ↦ ⟨_, (mem_smulAntidiagonal.1 (f n).2).2.1⟩
  obtain ⟨g, hg⟩ := h1.exists_monotone_subseq fun n ↦ (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 fun n ↦ h.natEmbedding _ _
  refine mn.ne (g.injective <| (h.natEmbedding _).injective ?_)
  exact eq_of_fst_le_fst_of_snd_le_snd (hg _ _ mn.le) h2'

end Set.SMulAntidiagonal

