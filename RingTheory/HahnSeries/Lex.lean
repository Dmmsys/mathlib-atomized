/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Algebra.Order.Ring.Synonym
public import Mathlib.Order.Hom.Lex
public import Mathlib.Order.PiLex
public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!

# Lexicographical order on Hahn series

In this file, we define lexicographical ordered `Lex R⟦Γ⟧`, and show this is a `LinearOrder` when
`Γ` and `R` themselves are linearly ordered. Additionally, it is an ordered group or ring whenever
`R` is.

## Main definitions

* `HahnSeries.finiteArchimedeanClassOrderIsoLex`: `FiniteArchimedeanClass` of `Lex R⟦Γ⟧`
  can be decomposed by `Γ`.

-/

@[expose] public section

namespace HahnSeries

variable {Γ R : Type*} [LinearOrder Γ]

section PartialOrder
variable [Zero R] [PartialOrder R]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Lex R⟦Γ⟧) :=
  PartialOrder.lift (toLex <| ofLex · |>.coeff) fun x y ↦ by simp
/-
**HahnSeries.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：lt_iff (a b : Lex R⟦Γ⟧) : a < b ↔ exists (i : Γ), (forall (j : Γ), j < i -
> (ofLex a).coeff j = (ofLex b).coeff j) ∧ (ofLex a).coeff i < (ofLex b).coeff i
参数：a b : Lex R⟦Γ⟧。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff (a b : Lex R⟦Γ⟧) :
    a < b ↔ ∃ (i : Γ), (∀ (j : Γ), j < i → (ofLex a).coeff j = (ofLex b).coeff j)
    ∧ (ofLex a).coeff i < (ofLex b).coeff i := by rfl

end PartialOrder

section LinearOrder
variable [Zero R] [LinearOrder R]

noncomputable
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder (Lex R⟦Γ⟧) where
  le_total a b := by
    rcases eq_or_ne a b with hab | hab
    · exact Or.inl hab.le
    · have hab := Function.ne_iff.mp <| HahnSeries.ext_iff.ne.mp hab
      let u := {i : Γ | (ofLex a).coeff i ≠ 0} ∪ {i : Γ | (ofLex b).coeff i ≠ 0}
      let v := {i : Γ | (ofLex a).coeff i ≠ (ofLex b).coeff i}
      have hvu : v ⊆ u := by
        intro i h
        rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
        contrapose! h
        rw [Set.notMem_ofPred_iff, not_not, h.1, h.2]
      have hv : v.IsWF :=
        ((ofLex a).isPWO_support'.isWF.union (ofLex b).isPWO_support'.isWF).subset hvu
      let i := hv.min hab
      have hji (j) : j < i → (ofLex a).coeff j = (ofLex b).coeff j :=
        not_imp_not.mp <| fun h' ↦ hv.not_lt_min hab h'
      have hne : (ofLex a).coeff i ≠ (ofLex b).coeff i := hv.min_mem hab
      obtain hi | hi := lt_or_gt_of_ne hne
      · exact Or.inl (le_of_lt ⟨i, hji, hi⟩)
      · exact Or.inr (le_of_lt ⟨i, fun j hj ↦ (hji j hj).symm, hi⟩)
  toDecidableLE := Classical.decRel _

@[simp]
/-
**HahnSeries.leadingCoeff_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_pos_iff {x : Lex R⟦Γ⟧} : 0 < (ofLex x).leadingCoeff ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.lt_iff`：lt_iff (a b : Lex R⟦Γ⟧) : a < b ↔ exists (i : Γ), (fo
rall (j : Γ), j < i -> (ofLex a).coeff j = (ofLex b).coeff j) ∧ (ofLex a).coeff 
i < (of…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HahnSeries.leadingCoeff_ne_zero`：leadingCoeff_ne_zero {x : R⟦Γ⟧} : x.lea
dingCoeff != 0 ↔ x != 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_orderTop`：coeff_eq_zero_of_lt_orderTop {x
 : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.coeff i = 0
· 使用定理 `WithTop.lt_untop_iff`：∀ {α : Type u_1} {b : α} [inst : LT α] {x : WithTo
p α} (hx : x ≠ ⊤), b < x.untop hx ↔ ↑b < x
· 使用定理 `HahnSeries.coeff_untop_eq_leadingCoeff`：coeff_untop_eq_leadingCoeff {x :
 R⟦Γ⟧} (hx) : x.coeff (x.orderTop.untop hx) = x.leadingCoeff
· 使用定理 `HahnSeries.orderTop_eq_of_le`：orderTop_eq_of_le {x : R⟦Γ⟧} {g : Γ} (hg :
 g in x.support) (hx : forall g' in x.support, g <= g') : orderTop x = g
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WithTop.ne_top_iff_exists`：∀ {α : Type u_1} {x : WithTop α}, x ≠ ⊤ ↔ ∃ a
, ↑a = x
· 使用定理 `WithTop.untop_eq_iff`：∀ {α : Type u_1} {a : WithTop α} {b : α} (h : a ≠ 
⊤), a.untop h = b ↔ a = ↑b
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
-/
theorem leadingCoeff_pos_iff {x : Lex R⟦Γ⟧} : 0 < (ofLex x).leadingCoeff ↔ 0 < x := by
  rw [lt_iff]
  constructor
  · intro hpos
    have hne : (ofLex x) ≠ 0 := leadingCoeff_ne_zero.mp hpos.ne.symm
    have htop : (ofLex x).orderTop ≠ ⊤ := orderTop_ne_top.2 hne
    refine ⟨(ofLex x).orderTop.untop htop, ?_, by simpa [coeff_untop_eq_leadingCoeff] using hpos⟩
    intro j hj
    simpa using (coeff_eq_zero_of_lt_orderTop ((WithTop.lt_untop_iff htop).mp hj)).symm
  · intro ⟨i, hj, hi⟩
    have horder : (ofLex x).orderTop = WithTop.some i := by
      apply orderTop_eq_of_le
      · simpa using hi.ne.symm
      · intro g hg
        contrapose! hg
        simpa using (hj g hg).symm
    have htop : (ofLex x).orderTop ≠ ⊤ := WithTop.ne_top_iff_exists.mpr ⟨i, horder.symm⟩
    have hne : ofLex x ≠ 0 := orderTop_ne_top.1 htop
    have horder' : (ofLex x).orderTop.untop htop = i := (WithTop.untop_eq_iff _).mpr horder
    rw [leadingCoeff_of_ne_zero hne, horder']
    simpa using hi

@[simp]
/-
**HahnSeries.leadingCoeff_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_nonneg_iff {x : Lex R⟦Γ⟧} : 0 <= (ofLex x).leadingCoeff ↔ 0 <
= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HahnSeries.leadingCoeff_eq_zero`：leadingCoeff_eq_zero {x : R⟦Γ⟧} : x.lea
dingCoeff = 0 ↔ x = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `HahnSeries.leadingCoeff_pos_iff`：leadingCoeff_pos_iff {x : Lex R⟦Γ⟧} : 0
 < (ofLex x).leadingCoeff ↔ 0 < x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem leadingCoeff_nonneg_iff {x : Lex R⟦Γ⟧} : 0 ≤ (ofLex x).leadingCoeff ↔ 0 ≤ x := by
  constructor <;> intro h
  · obtain heq | hlt := h.eq_or_lt
    · exact le_of_eq (leadingCoeff_eq_zero.mp heq.symm).symm
    · exact (leadingCoeff_pos_iff.mp hlt).le
  · obtain rfl | hlt := h.eq_or_lt
    · simp
    · exact (leadingCoeff_pos_iff.mpr hlt).le

@[simp]
/-
**HahnSeries.leadingCoeff_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_neg_iff {x : Lex R⟦Γ⟧} : (ofLex x).leadingCoeff < 0 ↔ x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem leadingCoeff_neg_iff {x : Lex R⟦Γ⟧} : (ofLex x).leadingCoeff < 0 ↔ x < 0 := by
  simp [← not_le]

@[simp]
/-
**HahnSeries.leadingCoeff_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_nonpos_iff {x : Lex R⟦Γ⟧} : (ofLex x).leadingCoeff <= 0 ↔ x <
= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem leadingCoeff_nonpos_iff {x : Lex R⟦Γ⟧} : (ofLex x).leadingCoeff ≤ 0 ↔ x ≤ 0 := by
  simp [← not_lt]

end LinearOrder

section OrderedMonoid
variable [PartialOrder R] [AddCommMonoid R] [AddLeftStrictMono R] [IsOrderedAddMonoid R]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedAddMonoid (Lex R⟦Γ⟧) where
  add_le_add_left a b hab c := by
    obtain rfl | hlt := hab.eq_or_lt
    · simp
    · apply le_of_lt
      rw [lt_iff] at hlt ⊢
      obtain ⟨i, hj, hi⟩ := hlt
      refine ⟨i, fun j hji ↦ ?_, add_left_strictMono hi⟩
      simp [hj j hji]

end OrderedMonoid

section OrderedGroup
variable [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]

@[simp]
/-
**HahnSeries.support_abs** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：support_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).support = (ofLex x).support
参数：x : Lex R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_neg_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Line
arOrder G] [IsOrderedAddMonoid G] {a : G}, |a| = -a ↔ a ≤ 0
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.support_neg`：support_neg {x : R⟦Γ⟧} : (-x).support = x.suppor
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
-/
theorem support_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).support = (ofLex x).support := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    simp
  · rw [abs_eq_self.mpr hge]

@[simp]
/-
**HahnSeries.orderTop_abs** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：orderTop_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).orderTop = (ofLex x).orderTop
参数：x : Lex R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_neg_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Line
arOrder G] [IsOrderedAddMonoid G] {a : G}, |a| = -a ↔ a ≤ 0
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ofLex_neg`：∀ {α : Type u_1} [inst : Neg α] (a : Lex α), ofLex (-a) = -of
Lex a
· 使用定理 `HahnSeries.orderTop_neg`：orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.ord
erTop
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
-/
theorem orderTop_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).orderTop = (ofLex x).orderTop := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle, ofLex_neg, orderTop_neg]
  · rw [abs_eq_self.mpr hge]
/-
**HahnSeries.order_abs** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：order_abs [Zero Γ] (x : Lex R⟦Γ⟧) : (ofLex |x|).order = (ofLex x).order
参数：x : Lex R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `WithTop.coe_injective`：∀ {α : Type u_1}, Function.Injective WithTop.some
· 使用定理 `HahnSeries.order_eq_orderTop_of_ne_zero`：order_eq_orderTop_of_ne_zero (h
x : x != 0) : order x = orderTop x
· 使用定理 `HahnSeries.orderTop_abs`：orderTop_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).order
Top = (ofLex x).orderTop
-/
theorem order_abs [Zero Γ] (x : Lex R⟦Γ⟧) : (ofLex |x|).order = (ofLex x).order := by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  · have hne' : ofLex x ≠ 0 := hne
    have habs : ofLex |x| ≠ 0 := by simpa using hne
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne_zero habs, order_eq_orderTop_of_ne_zero hne']
    apply orderTop_abs
/-
**HahnSeries.leadingCoeff_abs** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：leadingCoeff_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).leadingCoeff = |(ofLex x).le
adingCoeff|
参数：x : Lex R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_neg_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Line
arOrder G] [IsOrderedAddMonoid G] {a : G}, |a| = -a ↔ a ≤ 0
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `HahnSeries.leadingCoeff_neg_iff`：leadingCoeff_neg_iff {x : Lex R⟦Γ⟧} : (
ofLex x).leadingCoeff < 0 ↔ x < 0
· 使用定理 `ofLex_neg`：∀ {α : Type u_1} [inst : Neg α] (a : Lex α), ofLex (-a) = -of
Lex a
· 使用定理 `HahnSeries.leadingCoeff_neg`：leadingCoeff_neg {x : R⟦Γ⟧} : (-x).leadingC
oeff = -x.leadingCoeff
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `HahnSeries.leadingCoeff_pos_iff`：leadingCoeff_pos_iff {x : Lex R⟦Γ⟧} : 0
 < (ofLex x).leadingCoeff ↔ 0 < x
-/
theorem leadingCoeff_abs (x : Lex R⟦Γ⟧) :
    (ofLex |x|).leadingCoeff = |(ofLex x).leadingCoeff| := by
  obtain hlt | rfl | hgt := lt_trichotomy x 0
  · obtain hlt' := leadingCoeff_neg_iff.mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le, abs_eq_neg_self.mpr hlt'.le, ofLex_neg, leadingCoeff_neg]
  · simp
  · obtain hgt' := leadingCoeff_pos_iff.mpr hgt
    rw [abs_eq_self.mpr hgt.le, abs_eq_self.mpr hgt'.le]
/-
**HahnSeries.abs_lt_abs_of_orderTop_ofLex** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`
。
形式化陈述：abs_lt_abs_of_orderTop_ofLex {x y : Lex R⟦Γ⟧} (h : (ofLex y).orderTop < (o
fLex x).orderTop) : |x| < |y|
参数：h : (ofLex y).orderTop < (ofLex x).orderTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.lt_iff`：lt_iff (a b : Lex R⟦Γ⟧) : a < b ↔ exists (i : Γ), (fo
rall (j : Γ), j < i -> (ofLex a).coeff j = (ofLex b).coeff j) ∧ (ofLex a).coeff 
i < (of…
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.orderTop_abs`：orderTop_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).order
Top = (ofLex x).orderTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_orderTop`：coeff_eq_zero_of_lt_orderTop {x
 : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.coeff i = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `HahnSeries.coeff_untop_eq_leadingCoeff`：coeff_untop_eq_leadingCoeff {x :
 R⟦Γ⟧} (hx) : x.coeff (x.orderTop.untop hx) = x.leadingCoeff
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem abs_lt_abs_of_orderTop_ofLex {x y : Lex R⟦Γ⟧}
    (h : (ofLex y).orderTop < (ofLex x).orderTop) : |x| < |y| := by
  rw [← orderTop_abs x, ← orderTop_abs y] at h
  refine (lt_iff _ _).mpr ⟨(ofLex |y|).orderTop.untop h.ne_top, ?_, ?_⟩
  · simp +contextual [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, h.trans']
  · simpa [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, coeff_untop_eq_leadingCoeff, h]
      using h.ne_top

set_option backward.isDefEq.respectTransparency false in
/-
**HahnSeries.archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex** 是 
Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex {x y : Lex 
R⟦Γ⟧} (h : (ofLex x).orderTop = (ofLex y).orderTop) : ArchimedeanClass.mk x <= .
mk y ↔ ArchimedeanClass.mk (ofLex x).leadingCoeff <= .mk (ofLex y).leadingCoeff
参数：h : (ofLex x).orderTop = (ofLex y).orderTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.orderTop_abs`：orderTop_abs (x : Lex R⟦Γ⟧) : (ofLex |x|).order
Top = (ofLex x).orderTop
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `nsmul_lt_nsmul_left`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pre
order M] [AddLeftStrictMono M] {a : M} {n m : ℕ},   0 < a → n < m → n • a < m • 
a
· 使用定理 `Lex.instIsLeftCancelAdd`：∀ {α : Type u_1} [inst : Add α] [IsLeftCancelAd
d α], IsLeftCancelAdd (Lex α)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HahnSeries.lt_iff`：lt_iff (a b : Lex R⟦Γ⟧) : a < b ↔ exists (i : Γ), (fo
rall (j : Γ), j < i -> (ofLex a).coeff j = (ofLex b).coeff j) ∧ (ofLex a).coeff 
i < (of…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 45 条，此处仅展示前 30 条）
-/
theorem archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex {x y : Lex R⟦Γ⟧}
    (h : (ofLex x).orderTop = (ofLex y).orderTop) :
    ArchimedeanClass.mk x ≤ .mk y ↔
      ArchimedeanClass.mk (ofLex x).leadingCoeff ≤ .mk (ofLex y).leadingCoeff := by
  simp_rw [ArchimedeanClass.mk_le_mk]
  obtain rfl | hy := eq_or_ne y 0
  · -- special case: both `x` and `y` are zero
    simp_all
  -- general case: `x` and `y` are not zero
  have hx : x ≠ 0 := by simpa using orderTop_ne_top.1 <| h ▸ orderTop_ne_top.2 (by simpa using hy)
  have h' : (ofLex |x|).orderTop = (ofLex |y|).orderTop := by simpa using h
  constructor
  · -- `mk x ≤ mk y → mk x.leadingCoeff ≤ mk y.leadingCoeff`
    intro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    have hn' : |y| < (n + 1) • |x| :=
      lt_of_le_of_lt hn <| nsmul_lt_nsmul_left (by simpa using hx) (by simp)
    obtain ⟨j, hj, hi⟩ := (lt_iff _ _).mp hn'
    simp_rw [ofLex_smul, coeff_smul] at hj hi
    simp_rw [← leadingCoeff_abs]
    rw [leadingCoeff_of_ne_zero (by simpa using hy), leadingCoeff_of_ne_zero (by simpa using hx)]
    simp_rw [← h']
    obtain hjlt | hjeq | hjgt := lt_trichotomy (WithTop.some j) (ofLex |x|).orderTop
    · -- impossible case: `x` and `y` differ before their leading coefficients
      have hjlt' : j < (ofLex |y|).orderTop := h'.symm ▸ hjlt
      simp [coeff_eq_zero_of_lt_orderTop hjlt, coeff_eq_zero_of_lt_orderTop hjlt'] at hi
    · convert! hi.le <;> exact (WithTop.untop_eq_iff _).mpr hjeq.symm
    · exact (hj _ ((WithTop.untop_lt_iff _).mpr hjgt)).le
  · -- `mk x.leadingCoeff ≤ mk y.leadingCoeff → mk x ≤ mk y`
    intro ⟨n, hn⟩
    refine ⟨n + 1, ((lt_iff _ _).mpr ?_).le⟩
    refine ⟨(ofLex x).orderTop.untop (by simpa using hx), ?_, ?_⟩
    · -- all coefficients before the leading coefficient are zero
      intro j hj
      trans 0
      · apply coeff_eq_zero_of_lt_orderTop
        simpa [← h] using hj
      · suffices (ofLex |x|).coeff j = 0 by simp [this]
        apply coeff_eq_zero_of_lt_orderTop
        simpa using hj
    -- the leading coefficient determines the relation
    rw [ofLex_smul, coeff_smul]
    suffices |(ofLex y).leadingCoeff| < (n + 1) • |(ofLex x).leadingCoeff| by
      simp_rw [← leadingCoeff_abs] at this
      rw [leadingCoeff_of_ne_zero (by simpa using hy), leadingCoeff_of_ne_zero (by simpa using hx)]
        at this
      convert! this using 3 <;> simp [h]
    refine lt_of_le_of_lt hn <| nsmul_lt_nsmul_left ?_ (by simp)
    rwa [abs_pos, leadingCoeff_ne_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**HahnSeries.archimedeanClassMk_le_archimedeanClassMk_iff** 是 Mathlib 中的一个定理，位于命
名空间 `HahnSeries`。
形式化陈述：archimedeanClassMk_le_archimedeanClassMk_iff {x y : Lex R⟦Γ⟧} : Archimedea
nClass.mk x <= .mk y ↔ (ofLex x).orderTop < (ofLex y).orderTop ∨ (ofLex x).order
Top = (ofLex y).orderTop ∧ ArchimedeanClass.mk (ofLex x).leadingCoeff <= .mk (of
Lex y).leadingCoeff
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `HahnSeries.abs_lt_abs_of_orderTop_ofLex`：abs_lt_abs_of_orderTop_ofLex {x
 y : Lex R⟦Γ⟧} (h : (ofLex y).orderTop < (ofLex x).orderTop) : |x| < |y|
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `HahnSeries.archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLe
x`：archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex {x y : Lex R⟦Γ
⟧} (h : (ofLex x).orderTop = (ofLex y).orderTop) : ArchimedeanC…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_nsmul`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrde
r G] [IsOrderedAddMonoid G] (n : ℕ) (a : G),   |n • a| = n • |a|
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `HahnSeries.orderTop_smul_not_lt`：orderTop_smul_not_lt (r : R) (x : V⟦Γ⟧)
 : ¬ (r • x).orderTop < x.orderTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 35 条，此处仅展示前 30 条）
-/
theorem archimedeanClassMk_le_archimedeanClassMk_iff {x y : Lex R⟦Γ⟧} :
    ArchimedeanClass.mk x ≤ .mk y ↔
      (ofLex x).orderTop < (ofLex y).orderTop ∨
        (ofLex x).orderTop = (ofLex y).orderTop ∧
          ArchimedeanClass.mk (ofLex x).leadingCoeff ≤ .mk (ofLex y).leadingCoeff := by
  obtain hlt | heq | hgt := lt_trichotomy (ofLex x).orderTop (ofLex y).orderTop
  · -- when `x`'s order is less than `y`'s, this reduces to abs_lt_abs_of_orderTop_ofLex
    simpa [ArchimedeanClass.mk_le_mk, hlt] using
      ⟨1, by simpa using (abs_lt_abs_of_orderTop_ofLex hlt).le⟩
  · -- when `x` and `y` have the same order, this reduces to
    -- `archimedeanClass_le_iff_of_orderTop_eq`
    simpa [heq] using archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex heq
  -- when `x`'s order is greater than `y`'s, neither side is true
  simp_rw [ArchimedeanClass.mk_le_mk]
  refine ⟨?_, by simp [hgt.not_gt, hgt.ne']⟩
  intro ⟨n, hn⟩
  contrapose! hn
  rw [← abs_nsmul]
  have hgt' : (ofLex y).orderTop < (ofLex (n • x)).orderTop := by
    apply lt_of_lt_of_le hgt
    simpa using orderTop_smul_not_lt n (ofLex x)
  exact abs_lt_abs_of_orderTop_ofLex hgt'
/-
**HahnSeries.archimedeanClassMk_eq_archimedeanClassMk_iff** 是 Mathlib 中的一个定理，位于命
名空间 `HahnSeries`。
形式化陈述：archimedeanClassMk_eq_archimedeanClassMk_iff {x y : Lex R⟦Γ⟧} : Archimedea
nClass.mk x = ArchimedeanClass.mk y ↔ (ofLex x).orderTop = (ofLex y).orderTop ∧ 
ArchimedeanClass.mk (ofLex x).leadingCoeff = ArchimedeanClass.mk (ofLex y).leadi
ngCoeff
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `HahnSeries.archimedeanClassMk_le_archimedeanClassMk_iff`：archimedeanClas
sMk_le_archimedeanClassMk_iff {x y : Lex R⟦Γ⟧} : ArchimedeanClass.mk x <= .mk y 
↔ (ofLex x).orderTop < (ofLex y).orderTop ∨ (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem archimedeanClassMk_eq_archimedeanClassMk_iff {x y : Lex R⟦Γ⟧} :
    ArchimedeanClass.mk x = ArchimedeanClass.mk y ↔
    (ofLex x).orderTop = (ofLex y).orderTop ∧
    ArchimedeanClass.mk (ofLex x).leadingCoeff = ArchimedeanClass.mk (ofLex y).leadingCoeff := by
  rw [le_antisymm_iff, archimedeanClassMk_le_archimedeanClassMk_iff,
    archimedeanClassMk_le_archimedeanClassMk_iff]
  constructor
  · simpa +contextual [or_imp, ne_of_gt, le_of_lt] using fun _ ↦ le_antisymm
  · intro ⟨horder, hcoeff⟩
    exact ⟨.inr ⟨horder, hcoeff.le⟩, .inr ⟨horder.symm, hcoeff.ge⟩⟩

variable (Γ R) in
/-- Finite archimedean classes of `Lex R⟦Γ⟧` decompose into lexicographical pairs
of `order` and the finite archimedean class of `leadingCoeff`. -/
/-
**HahnSeries.finiteArchimedeanClassOrderHomLex** 是 Mathlib 中的一个定义，位于命名空间 `HahnSe
ries`。
形式化陈述：finiteArchimedeanClassOrderHomLex : FiniteArchimedeanClass (Lex R⟦Γ⟧) ->o 
Γ ×ₗ FiniteArchimedeanClass R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite archimedean classes of `Lex R⟦Γ⟧` decompose into lexicographical pairs
of `order` and the finite archimedean class of `leadingCoeff`.
-/
noncomputable def finiteArchimedeanClassOrderHomLex :
    FiniteArchimedeanClass (Lex R⟦Γ⟧) →o Γ ×ₗ FiniteArchimedeanClass R :=
  FiniteArchimedeanClass.liftOrderHom
    (fun ⟨x, hx⟩ ↦ toLex
      ⟨(ofLex x).orderTop.untop (by simp [orderTop_of_ne_zero (show ofLex x ≠ 0 by exact hx)]),
      FiniteArchimedeanClass.mk (ofLex x).leadingCoeff (leadingCoeff_ne_zero.mpr hx)⟩)
    fun ⟨a, ha⟩ ⟨b, hb⟩ h ↦ by
      rw [Prod.Lex.le_iff]
      simp only [ofLex_toLex]
      rw [FiniteArchimedeanClass.mk_le_mk] at ⊢ h
      rw [WithTop.untop_eq_iff]
      simpa using archimedeanClassMk_le_archimedeanClassMk_iff.mp h

variable (Γ R) in
/-- The inverse of `finiteArchimedeanClassOrderHomLex`. -/
/-
**HahnSeries.finiteArchimedeanClassOrderHomInvLex** 是 Mathlib 中的一个定义，位于命名空间 `Hah
nSeries`。
形式化陈述：finiteArchimedeanClassOrderHomInvLex : Γ ×ₗ FiniteArchimedeanClass R ->o F
initeArchimedeanClass (Lex R⟦Γ⟧) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of `finiteArchimedeanClassOrderHomLex`.
-/
noncomputable def finiteArchimedeanClassOrderHomInvLex :
    Γ ×ₗ FiniteArchimedeanClass R →o FiniteArchimedeanClass (Lex R⟦Γ⟧) where
  toFun x := (ofLex x).2.liftOrderHom
    (fun a ↦ FiniteArchimedeanClass.mk (toLex (single (ofLex x).1 a.val)) (by
      simpa using! a.prop))
    fun ⟨a, ha⟩ ⟨b, hb⟩ h ↦ by
      rw [FiniteArchimedeanClass.mk_le_mk, archimedeanClassMk_le_archimedeanClassMk_iff]
      simpa [ha, hb] using! h
  monotone' a b := a.rec fun (ao, ac) ↦ b.rec fun (bo, bc) h ↦ by
    obtain h | ⟨rfl, hle⟩ := Prod.Lex.le_iff.mp h
    · induction ac using FiniteArchimedeanClass.ind with | mk a ha
      induction bc using FiniteArchimedeanClass.ind with | mk b hb
      simp only [ne_eq, ofLex_toLex, FiniteArchimedeanClass.liftOrderHom_mk]
      rw [FiniteArchimedeanClass.mk_le_mk, archimedeanClassMk_le_archimedeanClassMk_iff]
      exact .inl (by simpa [ha, hb] using! h)
    · exact OrderHom.monotone _ hle

set_option backward.isDefEq.respectTransparency.types false in
variable (Γ R) in
/-- The correspondence between finite archimedean classes of `Lex R⟦Γ⟧`
and lexicographical pairs of `HahnSeries.orderTop` and the finite archimedean class of
`HahnSeries.leadingCoeff`. -/
/-
**HahnSeries.finiteArchimedeanClassOrderIsoLex** 是 Mathlib 中的一个定义，位于命名空间 `HahnSe
ries`。
形式化陈述：finiteArchimedeanClassOrderIsoLex : FiniteArchimedeanClass (Lex R⟦Γ⟧) ≃o Γ
 ×ₗ FiniteArchimedeanClass R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The correspondence between finite archimedean classes of `Lex R⟦Γ⟧`
and lexicographical pairs of `HahnSeries.orderTop` and the finite archimedean cl
ass of
`HahnSeries.leadingCoeff`.
-/
noncomputable def finiteArchimedeanClassOrderIsoLex :
    FiniteArchimedeanClass (Lex R⟦Γ⟧) ≃o Γ ×ₗ FiniteArchimedeanClass R := by
  apply OrderIso.ofHomInv (finiteArchimedeanClassOrderHomLex Γ R)
    (finiteArchimedeanClassOrderHomInvLex Γ R)
  · ext x
    cases x with | h x
    obtain ⟨order, coeff⟩ := x
    induction coeff using FiniteArchimedeanClass.ind with | mk a ha
    simp [finiteArchimedeanClassOrderHomLex, finiteArchimedeanClassOrderHomInvLex, ha]
  · ext x
    induction x using FiniteArchimedeanClass.ind with | mk a ha
    simp [finiteArchimedeanClassOrderHomLex, finiteArchimedeanClassOrderHomInvLex,
      archimedeanClassMk_eq_archimedeanClassMk_iff, ha]

@[simp]
/-
**HahnSeries.finiteArchimedeanClassOrderIsoLex_apply_fst** 是 Mathlib 中的一个定理，位于命名
空间 `HahnSeries`。
形式化陈述：finiteArchimedeanClassOrderIsoLex_apply_fst {x : Lex R⟦Γ⟧} (h : x != 0) : 
(ofLex (finiteArchimedeanClassOrderIsoLex Γ R (FiniteArchimedeanClass.mk x h))).
1 = (ofLex x).orderTop
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `OrderIso.ofHomInv_apply`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α →o β) (g : β →o α)   (h₁ : f.comp g = OrderHom
.id) (h₂ : g.…
· 使用定理 `FiniteArchimedeanClass.liftOrderHom_mk`：∀ {M : Type u_1} [inst : AddComm
Group M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {α : Type u_2}
   [inst_3 : PartialOrder α]…
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finiteArchimedeanClassOrderIsoLex_apply_fst {x : Lex R⟦Γ⟧} (h : x ≠ 0) :
    (ofLex (finiteArchimedeanClassOrderIsoLex Γ R (FiniteArchimedeanClass.mk x h))).1 =
    (ofLex x).orderTop := by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

@[simp]
/-
**HahnSeries.finiteArchimedeanClassOrderIsoLex_apply_snd** 是 Mathlib 中的一个定理，位于命名
空间 `HahnSeries`。
形式化陈述：finiteArchimedeanClassOrderIsoLex_apply_snd {x : Lex R⟦Γ⟧} (h : x != 0) : 
(ofLex (finiteArchimedeanClassOrderIsoLex Γ R (FiniteArchimedeanClass.mk x h))).
2.val = ArchimedeanClass.mk (ofLex x).leadingCoeff
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `OrderIso.ofHomInv_apply`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α →o β) (g : β →o α)   (h₁ : f.comp g = OrderHom
.id) (h₂ : g.…
· 使用定理 `FiniteArchimedeanClass.liftOrderHom_mk`：∀ {M : Type u_1} [inst : AddComm
Group M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {α : Type u_2}
   [inst_3 : PartialOrder α]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finiteArchimedeanClassOrderIsoLex_apply_snd {x : Lex R⟦Γ⟧} (h : x ≠ 0) :
    (ofLex (finiteArchimedeanClassOrderIsoLex Γ R (FiniteArchimedeanClass.mk x h))).2.val =
    ArchimedeanClass.mk (ofLex x).leadingCoeff := by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

section Archimedean
variable [Archimedean R] [Nontrivial R]

variable (Γ R) in
/-- For `Archimedean` coefficients, there is a correspondence between finite
archimedean classes and `HahnSeries.orderTop` without the top element. -/
/-
**HahnSeries.finiteArchimedeanClassOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `HahnSerie
s`。
形式化陈述：finiteArchimedeanClassOrderIso : FiniteArchimedeanClass (Lex R⟦Γ⟧) ≃o Γ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `Archimedean` coefficients, there is a correspondence between finite
archimedean classes and `HahnSeries.orderTop` without the top element.
-/
noncomputable def finiteArchimedeanClassOrderIso :
    FiniteArchimedeanClass (Lex R⟦Γ⟧) ≃o Γ :=
  have : Unique (FiniteArchimedeanClass R) := (nonempty_unique _).some
  (finiteArchimedeanClassOrderIsoLex Γ R).trans (Prod.Lex.prodUnique _ _)

@[simp]
/-
**HahnSeries.finiteArchimedeanClassOrderIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `Hah
nSeries`。
形式化陈述：finiteArchimedeanClassOrderIso_apply {x : Lex R⟦Γ⟧} (h : x != 0) : finiteA
rchimedeanClassOrderIso Γ R (FiniteArchimedeanClass.mk x h) = (ofLex x).orderTop
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.finiteArchimedeanClassOrderIsoLex_apply_fst`：finiteArchimedea
nClassOrderIsoLex_apply_fst {x : Lex R⟦Γ⟧} (h : x != 0) : (ofLex (finiteArchimed
eanClassOrderIsoLex Γ R (FiniteArchimedeanCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finiteArchimedeanClassOrderIso_apply {x : Lex R⟦Γ⟧} (h : x ≠ 0) :
    finiteArchimedeanClassOrderIso Γ R (FiniteArchimedeanClass.mk x h) = (ofLex x).orderTop := by
  simp [finiteArchimedeanClassOrderIso]

variable (Γ R) in
/-- For `Archimedean` coefficients, there is a correspondence between
archimedean classes (with top) and `HahnSeries.orderTop`. -/
/-
**HahnSeries.archimedeanClassOrderIsoWithTop** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeri
es`。
形式化陈述：archimedeanClassOrderIsoWithTop : ArchimedeanClass (Lex R⟦Γ⟧) ≃o WithTop Γ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `Archimedean` coefficients, there is a correspondence between
archimedean classes (with top) and `HahnSeries.orderTop`.
-/
noncomputable def archimedeanClassOrderIsoWithTop :
    ArchimedeanClass (Lex R⟦Γ⟧) ≃o WithTop Γ :=
  (FiniteArchimedeanClass.withTopOrderIso _).symm.trans
  (finiteArchimedeanClassOrderIso _ _).withTopCongr

@[simp]
/-
**HahnSeries.archimedeanClassOrderIsoWithTop_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ha
hnSeries`。
形式化陈述：archimedeanClassOrderIsoWithTop_apply (x : Lex R⟦Γ⟧) : archimedeanClassOrd
erIsoWithTop Γ R (ArchimedeanClass.mk x) = (ofLex x).orderTop
参数：x : Lex R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
· 使用定理 `InfTopHomClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Min α] [inst_2 : Min β] [inst_3 : Top α]  
 [inst_4 : Top β] …
· 使用定理 `OrderIsoClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : OrderTop
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FiniteArchimedeanClass.withTopOrderIso_symm_apply`：∀ {M : Type u_1} [ins
t : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a 
: M} (h : a ≠ 0),   (FiniteArchimedeanC…
· 使用定理 `HahnSeries.finiteArchimedeanClassOrderIso_apply`：finiteArchimedeanClassO
rderIso_apply {x : Lex R⟦Γ⟧} (h : x != 0) : finiteArchimedeanClassOrderIso Γ R (
FiniteArchimedeanClass.mk x h) = (ofL…
-/
theorem archimedeanClassOrderIsoWithTop_apply (x : Lex R⟦Γ⟧) :
    archimedeanClassOrderIsoWithTop Γ R (ArchimedeanClass.mk x) = (ofLex x).orderTop := by
  unfold archimedeanClassOrderIsoWithTop
  obtain rfl | h := eq_or_ne x 0 <;>
    simp [FiniteArchimedeanClass.withTopOrderIso_symm_apply, *]

end Archimedean

end OrderedGroup

section OrderedRing
variable [LinearOrder R] [Ring R] [AddCommMonoid Γ]
  [IsOrderedCancelAddMonoid Γ]

/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsOrderedRing R] [NoZeroDivisors R] : IsOrderedRing (Lex R⟦Γ⟧) where
  zero_le_one := by simp [← leadingCoeff_nonneg_iff]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← sub_nonneg] at hbc ⊢
    rw [← mul_sub, ← leadingCoeff_nonneg_iff, ofLex_mul, leadingCoeff_mul]
    apply mul_nonneg
    · simpa
    · rwa [leadingCoeff_nonneg_iff]
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← sub_nonneg] at hbc ⊢
    rw [← sub_mul, ← leadingCoeff_nonneg_iff, ofLex_mul, leadingCoeff_mul]
    apply mul_nonneg
    · rwa [leadingCoeff_nonneg_iff]
    · simpa
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStrictOrderedRing R] : IsStrictOrderedRing (Lex R⟦Γ⟧) where

end OrderedRing

section EmbDomain
variable [PartialOrder R] {Γ' : Type*} [LinearOrder Γ'] (f : Γ ↪o Γ')

/-- `HahnSeries.embDomain` as an `OrderEmbedding`. -/
@[simps]
noncomputable
/-
**HahnSeries.embDomainOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：embDomainOrderEmbedding [Zero R] : Lex R⟦Γ⟧ ↪o Lex R⟦Γ'⟧ where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def embDomainOrderEmbedding [Zero R] : Lex R⟦Γ⟧ ↪o Lex R⟦Γ'⟧ where
  toFun a := toLex (embDomain f (ofLex a))
  inj' := toLex.injective.comp (embDomain_injective.comp (ofLex.injective))
  map_rel_iff' {a b} := by
    simp_rw [le_iff_lt_or_eq, lt_iff]
    simp only [Function.Embedding.coeFn_mk, ofLex_toLex, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro (⟨i, hj, hi⟩ | heq)
      · have himem : i ∈ Set.range f := by
          contrapose hi
          simp [embDomain_of_notMem_range hi]
        obtain ⟨k, rfl⟩ := himem
        refine Or.inl ⟨k, fun j hjk ↦ ?_, by simpa using hi⟩
        simpa using hj (f j) (f.lt_iff_lt.mpr hjk)
      · exact Or.inr <| embDomain_injective.comp (ofLex.injective) heq
    · rintro (⟨i, hj, hi⟩ | rfl)
      · refine Or.inl ⟨f i, fun k hki ↦ ?_, by simpa using hi⟩
        by_cases hkmem : k ∈ Set.range f
        · obtain ⟨j', rfl⟩ := hkmem
          simpa using hj _ <| f.lt_iff_lt.mp hki
        · simp_rw [embDomain_of_notMem_range hkmem]
      · simp

/-- `HahnSeries.embDomain` as an `OrderAddMonoidHom`. -/
@[simps]
noncomputable
/-
**HahnSeries.embDomainOrderAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：embDomainOrderAddMonoidHom [AddMonoid R] : Lex R⟦Γ⟧ ->+o Lex R⟦Γ'⟧ where _
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def embDomainOrderAddMonoidHom [AddMonoid R] : Lex R⟦Γ⟧ →+o Lex R⟦Γ'⟧ where
  __ := (embDomainOrderEmbedding f).toOrderHom
  map_zero' := by simp
  map_add' := by simp [embDomainOrderEmbedding, embDomain_add]
/-
**HahnSeries.embDomainOrderAddMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Hah
nSeries`。
形式化陈述：embDomainOrderAddMonoidHom_injective [AddMonoid R] : Function.Injective (e
mbDomainOrderAddMonoidHom f (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem embDomainOrderAddMonoidHom_injective [AddMonoid R] :
    Function.Injective (embDomainOrderAddMonoidHom f (R := R)) :=
  (embDomainOrderEmbedding f).injective

end EmbDomain

end HahnSeries

