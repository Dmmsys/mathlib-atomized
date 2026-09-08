/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.Interval.Set.OrdConnected

/-! # Subtypes of conditionally complete linear orders

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `OrdConnected` set satisfies these conditions.

## TODO

Add appropriate instances for all `Set.Ixx`. This requires a refactor that will allow different
default values for `sSup` and `sInf`.
-/

@[expose] public section

assert_not_exists Multiset

open Set

variable {ι : Sort*} {α : Type*} (s : Set α)

section SupSet

variable [Preorder α] [SupSet α]

open scoped Classical in
/-- `SupSet` structure on a nonempty subset `s` of a preorder with `SupSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
@[instance_reducible]
/-
**subsetSupSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subsetSupSet [Inhabited s] : SupSet s where sSup t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SupSet` structure on a nonempty subset `s` of a preorder with `SupSet`. This de
finition is
non-canonical (it uses `default s`); it should be used only as here, as an auxil
iary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure.
-/
noncomputable def subsetSupSet [Inhabited s] : SupSet s where
  sSup t :=
    if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
    then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
    else default

attribute [local instance] subsetSupSet

open scoped Classical in
@[simp]
/-
**subset_sSup_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_sSup_def [Inhabited s] : @sSup s _ = fun t => if ht : t.Nonempty ∧ 
BddAbove t ∧ sSup ((↑) '' t : Set α) in s then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
 else default
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_sSup_def [Inhabited s] :
    @sSup s _ = fun t =>
      if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) ∈ s
      then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
      else default :=
  rfl
/-
**subset_sSup_of_within** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_sSup_of_within [Inhabited s] {t : Set s} (h' : t.Nonempty) (h'' : B
ddAbove t) (h : sSup ((↑) '' t : Set α) in s) : sSup ((↑) '' t : Set α) = (@sSup
 s _ t : α)
参数：h' : t.Nonempty；h'' : BddAbove t；h : sSup ((↑) '' t : Set α) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subset_sSup_of_within [Inhabited s] {t : Set s}
    (h' : t.Nonempty) (h'' : BddAbove t) (h : sSup ((↑) '' t : Set α) ∈ s) :
    sSup ((↑) '' t : Set α) = (@sSup s _ t : α) := by simp [h, h', h'']
/-
**subset_sSup_emptyset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_sSup_emptyset [Inhabited s] : sSup (∅ : Set s) = default
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subset_sSup_emptyset [Inhabited s] :
    sSup (∅ : Set s) = default := by
  simp [sSup]
/-
**subset_sSup_of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_sSup_of_not_bddAbove [Inhabited s] {t : Set s} (ht : ¬BddAbove t) :
 sSup t = default
参数：ht : ¬BddAbove t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subset_sSup_of_not_bddAbove [Inhabited s] {t : Set s} (ht : ¬BddAbove t) :
    sSup t = default := by
  simp [sSup, ht]

end SupSet

section InfSet

variable [Preorder α] [InfSet α]

open scoped Classical in
/-- `InfSet` structure on a nonempty subset `s` of a preorder with `InfSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
@[instance_reducible]
/-
**subsetInfSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subsetInfSet [Inhabited s] : InfSet s where sInf t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InfSet` structure on a nonempty subset `s` of a preorder with `InfSet`. This de
finition is
non-canonical (it uses `default s`); it should be used only as here, as an auxil
iary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure.
-/
noncomputable def subsetInfSet [Inhabited s] : InfSet s where
  sInf t :=
    if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
    then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
    else default

attribute [local instance] subsetInfSet

open scoped Classical in
@[simp]
/-
**subset_sInf_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_sInf_def [Inhabited s] : @sInf s _ = fun t => if ht : t.Nonempty ∧ 
BddBelow t ∧ sInf ((↑) '' t : Set α) in s then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
 else default
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_sInf_def [Inhabited s] :
    @sInf s _ = fun t =>
      if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) ∈ s
      then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩ else
      default :=
  rfl
/-
**subset_sInf_of_within** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_sInf_of_within [Inhabited s] {t : Set s} (h' : t.Nonempty) (h'' : B
ddBelow t) (h : sInf ((↑) '' t : Set α) in s) : sInf ((↑) '' t : Set α) = (@sInf
 s _ t : α)
参数：h' : t.Nonempty；h'' : BddBelow t；h : sInf ((↑) '' t : Set α) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subset_sInf_of_within [Inhabited s] {t : Set s}
    (h' : t.Nonempty) (h'' : BddBelow t) (h : sInf ((↑) '' t : Set α) ∈ s) :
    sInf ((↑) '' t : Set α) = (@sInf s _ t : α) := by simp [h, h', h'']
/-
**subset_sInf_emptyset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_sInf_emptyset [Inhabited s] : sInf (∅ : Set s) = default
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subset_sInf_emptyset [Inhabited s] :
    sInf (∅ : Set s) = default := by
  simp [sInf]
/-
**subset_sInf_of_not_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_sInf_of_not_bddBelow [Inhabited s] {t : Set s} (ht : ¬BddBelow t) :
 sInf t = default
参数：ht : ¬BddBelow t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subset_sInf_of_not_bddBelow [Inhabited s] {t : Set s} (ht : ¬BddBelow t) :
    sInf t = default := by
  simp [sInf, ht]

end InfSet

section OrdConnected

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetSupSet

attribute [local instance] subsetInfSet

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `sSup` of all its nonempty bounded-above subsets, and
the `sInf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
/-
**subsetConditionallyCompleteLinearOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：subsetConditionallyCompleteLinearOrder [Inhabited s] (h_Sup : forall {t : 
Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) '' t : Set α) in s) (h_
Inf : forall {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), sInf ((↑) '' t 
: Set α) in s) : ConditionallyCompleteLinearOrder s
参数：h_Sup : forall {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) 
'' t : Set α) in s；h_Inf : forall {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelo
w t), sInf ((↑) '' t : Set α) in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a nonempty subset of a conditionally complete linear order to be a condition
ally complete
linear order, it suffices that it contain the `sSup` of all its nonempty bounded
-above subsets, and
the `sInf` of all its nonempty bounded-below subsets.
See note [reducible non-instances].
-/
noncomputable abbrev subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), sInf ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
    isLUB_csSup t ht h_bdd := .of_image Subtype.coe_le_coe <| by
      rw [← subset_sSup_of_within s ht h_bdd (h_Sup ht h_bdd)]
      exact isLUB_csSup (ht.image _) ((Subtype.mono_coe _).map_bddAbove h_bdd)
    isGLB_csInf t ht h_bdd := .of_image Subtype.coe_le_coe <| by
      rw [← subset_sInf_of_within s ht h_bdd (h_Inf ht h_bdd)]
      exact isGLB_csInf (ht.image _) ((Subtype.mono_coe _).map_bddBelow h_bdd)
    csSup_of_not_bddAbove := fun t ht ↦ by simp [ht]
    csInf_of_not_bddBelow := fun t ht ↦ by simp [ht] }

/-- The `sSup` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
/-
**sSup_within_of_ordConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ 
(ht : t.Nonempty) (h_bdd : BddAbove t) : sSup ((↑) '' t : Set α) in s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Monotone.le_csSup_image`：le_csSup_image {s : Set α} {c : α} (hcs : c in 
s) (h_bdd : BddAbove s) : f c <= sSup (f '' s)
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Monotone.csSup_image_le`：csSup_image_le {s : Set α} (hs : s.Nonempty) {B
 : α} (hB : B in upperBounds s) : sSup (f '' s) <= f B

--- 原说明 ---
The `sSup` function on a nonempty `OrdConnected` set `s` in a conditionally comp
lete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`.
-/
theorem sSup_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : sSup ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine hs.out c.2 B.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· ∈ s)).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe (· ∈ s)).csSup_image_le ⟨c, hct⟩ hB

/-- The `sInf` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
/-
**sInf_within_of_ordConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ 
(ht : t.Nonempty) (h_bdd : BddBelow t) : sInf ((↑) '' t : Set α) in s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Monotone.le_csInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditi
onallyCompleteLattice β] [inst_1 : Preorder α] {f : α → β},   Monotone f → ∀ {s 
: Set α}, s.N…
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Monotone.csInf_image_le`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditi
onallyCompleteLattice β] [inst_1 : Preorder α] {f : α → β},   Monotone f → ∀ {s 
: Set α} {c :…

--- 原说明 ---
The `sInf` function on a nonempty `OrdConnected` set `s` in a conditionally comp
lete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`.
-/
theorem sInf_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : sInf ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine hs.out B.2 c.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· ∈ s)).le_csInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe (· ∈ s)).csInf_image_le hct ⟨B, hB⟩

/-- A nonempty `OrdConnected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
/-
**ordConnectedSubsetConditionallyCompleteLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `
`。
形式化陈述：ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s] [OrdConne
cted s] : ConditionallyCompleteLinearOrder s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_within_of_ordConnected`：sSup_within_of_ordConnected {s : Set α} [hs
 : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty) (h_bdd : BddAbove t) : sSup ((↑
) '' t : Set α) i…
· 使用定理 `sInf_within_of_ordConnected`：sInf_within_of_ordConnected {s : Set α} [hs
 : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty) (h_bdd : BddBelow t) : sInf ((↑
) '' t : Set α) i…

--- 原说明 ---
A nonempty `OrdConnected` set in a conditionally complete linear order is natura
lly a
conditionally complete linear order.
-/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s]
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)

end OrdConnected

section Icc

/-- Complete lattice structure on `Set.Icc` -/
/-
**Set.Icc.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.Icc.completeLattice [ConditionallyCompleteLattice α] {a b : α} [Fact (
a <= b)] : CompleteLattice (Set.Icc a b) where __
参数：a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Complete lattice structure on `Set.Icc`
-/
noncomputable instance Set.Icc.completeLattice [ConditionallyCompleteLattice α]
    {a b : α} [Fact (a ≤ b)] : CompleteLattice (Set.Icc a b) where
  __ := (inferInstance : BoundedOrder ↑(Icc a b))
  sSup S := if hS : S = ∅ then ⟨a, le_rfl, Fact.out⟩ else ⟨sSup ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hS
    refine ⟨?_, csSup_le (hS.image Subtype.val) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.2)⟩
    obtain ⟨c, hc⟩ := hS
    exact c.2.1.trans (le_csSup ⟨b, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.2⟩ ⟨c, hc, rfl⟩)⟩
  isLUB_sSup S := by
    split_ifs with hS
    · subst hS; simp only [isLUB_empty_iff, isBot_iff_eq_bot]; rfl
    · exact .of_image Subtype.coe_le_coe <| isLUB_csSup ((Set.nonempty_iff_ne_empty.mpr hS).image _)
        ((Subtype.mono_coe _).map_bddAbove (OrderTop.bddAbove S))
  sInf S := if hS : S = ∅ then ⟨b, Fact.out, le_rfl⟩ else ⟨sInf ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hS
    refine ⟨le_csInf (hS.image Subtype.val) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.1), ?_⟩
    obtain ⟨c, hc⟩ := hS
    exact le_trans (csInf_le ⟨a, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.1⟩ ⟨c, hc, rfl⟩) c.2.2⟩
  isGLB_sInf S := by
    split_ifs with hS
    · subst hS; simp only [isGLB_empty_iff, isTop_iff_eq_top]; rfl
    · exact .of_image Subtype.coe_le_coe <| isGLB_csInf ((Set.nonempty_iff_ne_empty.mpr hS).image _)
        ((Subtype.mono_coe _).map_bddBelow (OrderBot.bddBelow S))

/-- Complete linear order structure on `Set.Icc` -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Complete linear order structure on `Set.Icc`
-/
noncomputable instance [ConditionallyCompleteLinearOrder α] {a b : α} [Fact (a ≤ b)] :
    CompleteLinearOrder (Set.Icc a b) :=
  { Set.Icc.completeLattice, Subtype.instLinearOrder _, LinearOrder.toBiheytingAlgebra _ with }
/-
**Set.Icc.coe_sSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Icc.coe_sSup [ConditionallyCompleteLattice α] {a b : α} (h : a <= b) {
S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a <= b)
参数：h : a <= b；Set.Icc a b；hS : S.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma Set.Icc.coe_sSup [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a ≤ b) := ⟨h⟩
    ↑(sSup S) = sSup ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)
/-
**Set.Icc.coe_sInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Icc.coe_sInf [ConditionallyCompleteLattice α] {a b : α} (h : a <= b) {
S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a <= b)
参数：h : a <= b；Set.Icc a b；hS : S.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma Set.Icc.coe_sInf [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a ≤ b) := ⟨h⟩
    ↑(sInf S) = sInf ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)
/-
**Set.Icc.coe_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Icc.coe_iSup [ConditionallyCompleteLattice α] {a b : α} (h : a <= b) [
Nonempty ι] {S : ι -> Set.Icc a b} : have : Fact (a <= b)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.Icc.coe_sSup`：Set.Icc.coe_sSup [ConditionallyCompleteLattice α] {a b
 : α} (h : a <= b) {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a <=
 b)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
lemma Set.Icc.coe_iSup [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    [Nonempty ι] {S : ι → Set.Icc a b} : have : Fact (a ≤ b) := ⟨h⟩
    ↑(iSup S) = (⨆ i, S i : α) :=
  (Set.Icc.coe_sSup h (range_nonempty S)).trans (congrArg sSup (range_comp Subtype.val S).symm)
/-
**Set.Icc.coe_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Icc.coe_iInf [ConditionallyCompleteLattice α] {a b : α} (h : a <= b) [
Nonempty ι] {S : ι -> Set.Icc a b} : have : Fact (a <= b)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.Icc.coe_sInf`：Set.Icc.coe_sInf [ConditionallyCompleteLattice α] {a b
 : α} (h : a <= b) {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a <=
 b)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
lemma Set.Icc.coe_iInf [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    [Nonempty ι] {S : ι → Set.Icc a b} : have : Fact (a ≤ b) := ⟨h⟩
    ↑(iInf S) = (⨅ i, S i : α) :=
  (Set.Icc.coe_sInf h (range_nonempty S)).trans (congrArg sInf (range_comp Subtype.val S).symm)

end Icc

namespace Set.Iic

variable [CompleteLattice α] {a : α}

/-
**Set.Iic.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `Set.Iic`。
形式化陈述：instCompleteLattice : CompleteLattice (Iic a) where sSup S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteLattice : CompleteLattice (Iic a) where
  sSup S := ⟨sSup ((↑) '' S), by simpa using fun b hb _ ↦ hb⟩
  sInf S := ⟨a ⊓ sInf ((↑) '' S), by simp⟩
  isLUB_sSup _ := .of_image Subtype.coe_le_coe (isLUB_sSup _)
  isGLB_sInf _ :=
    ⟨fun _ hb ↦ inf_le_of_right_le <| sInf_le <| mem_image_of_mem Subtype.val hb,
      fun b hb ↦ le_inf_iff.mpr ⟨b.property, le_sInf fun _ ⟨_, hd, hd'⟩ ↦ hd' ▸ hb hd⟩⟩
  le_top := by simp
  bot_le := by simp

variable (S : Set <| Iic a) (f : ι → Iic a) (p : ι → Prop)
/-
**Set.Iic.coe_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_2} [inst : CompleteLattice α] {a : α} (S : Set ↑(Set.Iic a))
, ↑(sSup S) = sSup (Subtype.val '' S)
参数：S : Set ↑(Set.Iic a)；sSup S；Subtype.val '' S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_sSup : (↑(sSup S) : α) = sSup ((↑) '' S) := rfl
/-
**Set.Iic.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattice α] {a : α} (f : ι 
→ ↑(Set.Iic a)), ↑(⨆ i, f i) = ⨆ i, ↑(f i)
参数：f : ι → ↑(Set.Iic a)；⨆ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.Iic.coe_sSup`：∀ {α : Type u_2} [inst : CompleteLattice α] {a : α} (S
 : Set ↑(Set.Iic a)), ↑(sSup S) = sSup (Subtype.val '' S)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem coe_iSup : (↑(⨆ i, f i) : α) = ⨆ i, (f i : α) := by
  rw [iSup, coe_sSup]; congr; ext; simp
/-
**Set.Iic.coe_biSup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：coe_biSup : (↑(⨆ i, ⨆ (_ : p i), f i) : α) = ⨆ i, ⨆ (_ : p i), (f i : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic.coe_iSup`：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattic
e α] {a : α} (f : ι → ↑(Set.Iic a)), ↑(⨆ i, f i) = ⨆ i, ↑(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_biSup : (↑(⨆ i, ⨆ (_ : p i), f i) : α) = ⨆ i, ⨆ (_ : p i), (f i : α) := by simp
/-
**Set.Iic.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_2} [inst : CompleteLattice α] {a : α} (S : Set ↑(Set.Iic a))
, ↑(sInf S) = a ⊓ sInf (Subtype.val '' S)
参数：S : Set ↑(Set.Iic a)；sInf S；Subtype.val '' S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_sInf : (↑(sInf S) : α) = a ⊓ sInf ((↑) '' S) := rfl
/-
**Set.Iic.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattice α] {a : α} (f : ι 
→ ↑(Set.Iic a)), ↑(⨅ i, f i) = a ⊓ ⨅ i, ↑(f i)
参数：f : ι → ↑(Set.Iic a)；⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Set.Iic.coe_sInf`：∀ {α : Type u_2} [inst : CompleteLattice α] {a : α} (S
 : Set ↑(Set.Iic a)), ↑(sInf S) = a ⊓ sInf (Subtype.val '' S)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem coe_iInf : (↑(⨅ i, f i) : α) = a ⊓ ⨅ i, (f i : α) := by
  rw [iInf, coe_sInf]; congr; ext; simp
/-
**Set.Iic.coe_biInf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：coe_biInf : (↑(⨅ i, ⨅ (_ : p i), f i) : α) = a ⊓ ⨅ i, ⨅ (_ : p i), (f i : 
α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic.coe_iInf`：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattic
e α] {a : α} (f : ι → ↑(Set.Iic a)), ↑(⨅ i, f i) = a ⊓ ⨅ i, ↑(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
theorem coe_biInf : (↑(⨅ i, ⨅ (_ : p i), f i) : α) = a ⊓ ⨅ i, ⨅ (_ : p i), (f i : α) := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [coe_iInf, ← inf_iInf, ← inf_assoc, inf_idem]


end Set.Iic

