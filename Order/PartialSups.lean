/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.Basic
import Mathlib.Data.Finset.Max

import Mathlib.Data.Fintype.Order

/-!
# The monotone sequence of partial supremums of a sequence

For `ι` a preorder in which all bounded-above intervals are finite (such as `ℕ`), and `α` a
`⊔`-semilattice, we define `partialSups : (ι → α) → ι →o α` by the formula
`partialSups f i = (Finset.Iic i).sup' ⋯ f`, where the `⋯` denotes a proof that `Finset.Iic i` is
nonempty. This is a way of spelling `⊔ k ≤ i, f k` which does not require a `α` to have a bottom
element, and makes sense in conditionally-complete lattices (where indexed suprema over sets are
badly-behaved).

Under stronger hypotheses on `α` and `ι`, we show that this coincides with other candidate
definitions, see e.g. `partialSups_eq_biSup`, `partialSups_eq_sup_range`,
and `partialSups_eq_sup'_range`.

We show this construction gives a Galois insertion between functions `ι → α` and monotone functions
`ι →o α`, see `partialSups.gi`.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because:
* Starting at `⊥` requires... having a bottom element.
* `fun f i ↦ (Finset.Iio i).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partialSups.gi`.

-/

@[expose] public section

open Finset

variable {α β ι : Type*}

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β]

section Preorder

variable [Preorder ι] [LocallyFiniteOrderBot ι]

/-- The monotone sequence whose value at `i` is the supremum of the `f j` where `j ≤ i`. -/
/-
**partialSups** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：partialSups (f : ι -> α) : ι ->o α where toFun i
参数：f : ι -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty

--- 原说明 ---
The monotone sequence whose value at `i` is the supremum of the `f j` where `j ≤
 i`.
-/
def partialSups (f : ι → α) : ι →o α where
  toFun i := (Iic i).sup' nonempty_Iic f
  monotone' _ _ hmn := sup'_mono f (Iic_subset_Iic.mpr hmn) nonempty_Iic
/-
**partialSups_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_apply (f : ι -> α) (i : ι) : partialSups f i = (Iic i).sup' no
nempty_Iic f
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma partialSups_apply (f : ι → α) (i : ι) :
    partialSups f i = (Iic i).sup' nonempty_Iic f :=
  rfl
/-
**partialSups_iff_forall** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_iff_forall {f : ι -> α} (p : α -> Prop) (hp : forall {a b}, p 
(a ⊔ b) ↔ p a ∧ p b) {i : ι} : p (partialSups f i) ↔ forall j <= i, p (f j)
参数：p : α -> Prop；hp : forall {a b}, p (a ⊔ b) ↔ p a ∧ p b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `partialSups_apply`：partialSups_apply (f : ι -> α) (i : ι) : partialSups 
f i = (Iic i).sup' nonempty_Iic f
· 使用定理 `Finset.apply_sup'_eq_sup'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma partialSups_iff_forall {f : ι → α} (p : α → Prop)
    (hp : ∀ {a b}, p (a ⊔ b) ↔ p a ∧ p b) {i : ι} :
    p (partialSups f i) ↔ ∀ j ≤ i, p (f j) := by
  rw [partialSups_apply, apply_sup'_eq_sup'_comp (γ := Propᵒᵈ) _ p, sup'_eq_sup]
  · change (Iic i).inf (p ∘ f) ↔ _
    simp [Finset.inf_eq_iInf]
  · intro x y
    rw [hp]
    rfl

@[simp]
/-
**partialSups_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_le_iff {f : ι -> α} {i : ι} {a : α} : partialSups f i <= a ↔ f
orall j <= i, f j <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `partialSups_iff_forall`：partialSups_iff_forall {f : ι -> α} (p : α -> Pr
op) (hp : forall {a b}, p (a ⊔ b) ↔ p a ∧ p b) {i : ι} : p (partialSups f i) ↔ f
orall j <= i…
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
-/
lemma partialSups_le_iff {f : ι → α} {i : ι} {a : α} :
    partialSups f i ≤ a ↔ ∀ j ≤ i, f j ≤ a :=
  partialSups_iff_forall (· ≤ a) sup_le_iff
/-
**le_partialSups_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_partialSups_of_le (f : ι -> α) {i j : ι} (h : i <= j) : f i <= partialS
ups f j
参数：f : ι -> α；h : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `partialSups_le_iff`：partialSups_le_iff {f : ι -> α} {i : ι} {a : α} : pa
rtialSups f i <= a ↔ forall j <= i, f j <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_partialSups_of_le (f : ι → α) {i j : ι} (h : i ≤ j) :
    f i ≤ partialSups f j :=
  partialSups_le_iff.1 le_rfl i h
/-
**le_partialSups** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_partialSups (f : ι -> α) : f <= partialSups f
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_partialSups_of_le`：le_partialSups_of_le (f : ι -> α) {i j : ι} (h : i
 <= j) : f i <= partialSups f j
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_partialSups (f : ι → α) :
    f ≤ partialSups f :=
  fun _ => le_partialSups_of_le f le_rfl
/-
**partialSups_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_le (f : ι -> α) (i : ι) (a : α) (w : forall j <= i, f j <= a) 
: partialSups f i <= a
参数：f : ι -> α；i : ι；a : α；w : forall j <= i, f j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `partialSups_le_iff`：partialSups_le_iff {f : ι -> α} {i : ι} {a : α} : pa
rtialSups f i <= a ↔ forall j <= i, f j <= a
-/
theorem partialSups_le (f : ι → α) (i : ι) (a : α) (w : ∀ j ≤ i, f j ≤ a) :
    partialSups f i ≤ a :=
  partialSups_le_iff.2 w

@[simp]
/-
**upperBounds_range_partialSups** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperBounds_range_partialSups (f : ι -> α) : upperBounds (Set.range (parti
alSups f)) = upperBounds (Set.range f)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma upperBounds_range_partialSups (f : ι → α) :
    upperBounds (Set.range (partialSups f)) = upperBounds (Set.range f) := by
  ext a
  simp only [mem_upperBounds, Set.forall_mem_range, partialSups_le_iff]
  exact ⟨fun h _ ↦ h _ _ le_rfl, fun h _ _ _ ↦ h _⟩

@[simp]
/-
**bddAbove_range_partialSups** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_range_partialSups {f : ι -> α} : BddAbove (Set.range (partialSups
 f)) ↔ BddAbove (Set.range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `upperBounds_range_partialSups`：upperBounds_range_partialSups (f : ι -> α
) : upperBounds (Set.range (partialSups f)) = upperBounds (Set.range f)
-/
theorem bddAbove_range_partialSups {f : ι → α} :
    BddAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f) :=
  .of_eq <| congr_arg Set.Nonempty <| upperBounds_range_partialSups f
/-
**Monotone.partialSups_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.partialSups_eq {f : ι -> α} (hf : Monotone f) : partialSups f = f
参数：hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `partialSups_le`：partialSups_le (f : ι -> α) (i : ι) (a : α) (w : forall 
j <= i, f j <= a) : partialSups f i <= a
· 使用定理 `le_partialSups`：le_partialSups (f : ι -> α) : f <= partialSups f
-/
theorem Monotone.partialSups_eq {f : ι → α} (hf : Monotone f) :
    partialSups f = f :=
  funext fun i ↦ le_antisymm (partialSups_le _ _ _ (@hf · i)) (le_partialSups _ _)
/-
**partialSups_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_mono : Monotone (partialSups : (ι -> α) -> ι ->o α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `partialSups_le_iff`：partialSups_le_iff {f : ι -> α} {i : ι} {a : α} : pa
rtialSups f i <= a ↔ forall j <= i, f j <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_partialSups_of_le`：le_partialSups_of_le (f : ι -> α) {i j : ι} (h : i
 <= j) : f i <= partialSups f j
-/
theorem partialSups_mono :
    Monotone (partialSups : (ι → α) → ι →o α) :=
  fun _ _ h _ ↦ partialSups_le_iff.2 fun j hj ↦ (h j).trans (le_partialSups_of_le _ hj)
/-
**partialSups_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_monotone (f : ι -> α) : Monotone (partialSups f)
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `partialSups_le`：partialSups_le (f : ι -> α) (i : ι) (a : α) (w : forall 
j <= i, f j <= a) : partialSups f i <= a
· 使用定理 `le_partialSups_of_le`：le_partialSups_of_le (f : ι -> α) {i j : ι} (h : i
 <= j) : f i <= partialSups f j
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma partialSups_monotone (f : ι → α) :
    Monotone (partialSups f) :=
  fun i _ hnm ↦ partialSups_le f i _ (fun _ hm'n ↦ le_partialSups_of_le _ (hm'n.trans hnm))

/-- `partialSups` forms a Galois insertion with the coercion from monotone functions to functions.
-/
/-
**partialSups.gi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：partialSups.gi : GaloisInsertion (partialSups : (ι -> α) -> ι ->o α) (↑) w
here choice f h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`partialSups` forms a Galois insertion with the coercion from monotone functions
 to functions.
-/
def partialSups.gi :
    GaloisInsertion (partialSups : (ι → α) → ι →o α) (↑) where
  choice f h :=
    ⟨f, by convert! (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine ⟨(le_partialSups f).trans, fun h ↦ ?_⟩
    convert! partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHom.ext _ _ ((le_partialSups f).antisymm h)
/-
**Pi.partialSups_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_3} [inst : Preorder ι] [inst_1 : LocallyFiniteOrderBot ι] {τ
 : Type u_4} {π : τ → Type u_5}   [inst_2 : (t : τ) → SemilatticeSup (π t)] (f :
 ι → (t : τ) → π t) (i : ι) (t : τ),   (partialSups f) i t = (partialSups fun x 
=> f x t) i
参数：t : τ；π t；f : ι → (t : τ) → π t；i : ι；t : τ；partialSups f；partialSups fun x =
> f x t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_apply`：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [i
nst : (b : β) → SemilatticeSup (C b)] {s : Finset α}   (H : s.Nonempty) (f : α →
 (b : β…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma Pi.partialSups_apply {τ : Type*} {π : τ → Type*} [∀ t, SemilatticeSup (π t)]
    (f : ι → (t : τ) → π t) (i : ι) (t : τ) :
    partialSups f i t = partialSups (f · t) i := by
  simp only [partialSups_apply, Finset.sup'_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**comp_partialSups** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：comp_partialSups {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : ι ->
 α) (g : F) : partialSups (g ∘ f) = g ∘ partialSups f
参数：f : ι -> α；g : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `OrderHom.mk.congr_simp`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder
 α] [inst_1 : Preorder β] (toFun toFun_1 : α → β)   (e_toFun : toFun = toFun_1) 
(monotone' :…
· 使用定理 `map_finset_sup'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   [inst_2 : FunLike
 F α …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_partialSups {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : ι → α) (g : F) :
    partialSups (g ∘ f) = g ∘ partialSups f := by
  funext _; simp [partialSups]
/-
**map_partialSups** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_partialSups {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : F) (g
 : ι -> α) (i : ι) : partialSups (fun j => f (g j)) i = f (partialSups g i)
参数：f : F；g : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `comp_partialSups`：comp_partialSups {F : Type*} [FunLike F α β] [SupHomCl
ass F α β] (f : ι -> α) (g : F) : partialSups (g ∘ f) = g ∘ partialSups f
-/
lemma map_partialSups {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : F) (g : ι → α) (i : ι) :
    partialSups (fun j ↦ f (g j)) i = f (partialSups g i) := congr($(comp_partialSups ..) i)

end Preorder

@[simp]
/-
**partialSups_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_succ [LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccOrder ι] (
f : ι -> α) (i : ι) : partialSups f (Order.succ i) = partialSups f i ⊔ f (Order.
succ i)
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_succ_iff_eq_or_le`：le_succ_iff_eq_or_le : a <= succ b ↔ a = suc
c b ∨ a <= b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_union`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty)   (h₂ : s₂.N
onempty…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem partialSups_succ [LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccOrder ι]
    (f : ι → α) (i : ι) :
    partialSups f (Order.succ i) = partialSups f i ⊔ f (Order.succ i) := by
  suffices Iic (Order.succ i) = Iic i ∪ {Order.succ i} by simp only [partialSups_apply, this,
    sup'_union nonempty_Iic ⟨_, mem_singleton_self _⟩ f, sup'_singleton]
  ext
  simp only [mem_Iic, mem_union, mem_singleton]
  constructor
  · exact fun h ↦ (Order.le_succ_iff_eq_or_le.mp h).symm
  · exact fun h ↦ h.elim (le_trans · <| Order.le_succ _) le_of_eq

@[simp]
/-
**partialSups_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_bot [PartialOrder ι] [LocallyFiniteOrder ι] [OrderBot ι] (f : 
ι -> α) : partialSups f ⊥ = f ⊥
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Set.Iic_bot`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : OrderBot
 α], Set.Iic ⊥ = {⊥}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
-/
theorem partialSups_bot [PartialOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    (f : ι → α) : partialSups f ⊥ = f ⊥ := by
  simp only [partialSups_apply]
  -- should we add a lemma `Finset.Iic_bot`?
  suffices Iic (⊥ : ι) = {⊥} by simp only [this, sup'_singleton]
  simp only [← coe_eq_singleton, coe_Iic, Set.Iic_bot]

/-!
### Functions out of `ℕ`
-/

@[simp]
/-
**partialSups_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_zero (f : Nat -> α) : partialSups f 0 = f 0
参数：f : Nat -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `partialSups_bot`：partialSups_bot [PartialOrder ι] [LocallyFiniteOrder ι]
 [OrderBot ι] (f : ι -> α) : partialSups f ⊥ = f ⊥

--- 原说明 ---
### Functions out of `ℕ`
-/
theorem partialSups_zero (f : ℕ → α) : partialSups f 0 = f 0 :=
  partialSups_bot f
/-
**partialSups_eq_sup'_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] (f : ℕ → α) (n : ℕ), (partialSu
ps f) n = (Finset.range (n + 1)).sup' ⋯ f
参数：f : ℕ → α；n : ℕ；partialSups f；Finset.range (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.nonempty_range_add_one`：nonempty_range_add_one : (range <| n + 1)
.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem partialSups_eq_sup'_range (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup' nonempty_range_add_one f :=
  eq_of_forall_ge_iff fun _ ↦ by simp [Nat.lt_succ_iff]
/-
**partialSups_eq_sup_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_eq_sup_range [OrderBot α] (f : Nat -> α) (n : Nat) : partialSu
ps f n = (Finset.range (n + 1)).sup f
参数：f : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem partialSups_eq_sup_range [OrderBot α] (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup f :=
  eq_of_forall_ge_iff fun _ ↦ by simp [Nat.lt_succ_iff]

end SemilatticeSup

section DistribLattice

/-!
### Functions valued in a distributive lattice

These lemmas require the target to be a distributive lattice, so they are not useful (or true) in
situations such as submodules.
-/

variable [Preorder ι] [LocallyFiniteOrderBot ι] [DistribLattice α] [OrderBot α]

@[simp]
/-
**disjoint_partialSups_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_partialSups_left {f : ι -> α} {i : ι} {x : α} : Disjoint (partial
Sups f i) x ↔ forall j <= i, Disjoint (f j) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `partialSups_iff_forall`：partialSups_iff_forall {f : ι -> α} (p : α -> Pr
op) (hp : forall {a b}, p (a ⊔ b) ↔ p a ∧ p b) {i : ι} : p (partialSups f i) ↔ f
orall j <= i…
· 使用定理 `disjoint_sup_left`：disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c
 ∧ Disjoint b c
-/
lemma disjoint_partialSups_left {f : ι → α} {i : ι} {x : α} :
    Disjoint (partialSups f i) x ↔ ∀ j ≤ i, Disjoint (f j) x :=
  partialSups_iff_forall (Disjoint · x) disjoint_sup_left

@[simp]
/-
**disjoint_partialSups_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_partialSups_right {f : ι -> α} {i : ι} {x : α} : Disjoint x (part
ialSups f i) ↔ forall j <= i, Disjoint x (f j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `partialSups_iff_forall`：partialSups_iff_forall {f : ι -> α} (p : α -> Pr
op) (hp : forall {a b}, p (a ⊔ b) ↔ p a ∧ p b) {i : ι} : p (partialSups f i) ↔ f
orall j <= i…
· 使用定理 `disjoint_sup_right`：disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a
 b ∧ Disjoint a c
-/
lemma disjoint_partialSups_right {f : ι → α} {i : ι} {x : α} :
    Disjoint x (partialSups f i) ↔ ∀ j ≤ i, Disjoint x (f j) :=
  partialSups_iff_forall (Disjoint x) disjoint_sup_right

open scoped Function in -- required for scoped `on` notation
/- Note this lemma requires a distributive lattice, so is not useful (or true) in situations such as
submodules. -/
/-
**partialSups_disjoint_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_disjoint_of_disjoint (f : ι -> α) (h : Pairwise (Disjoint on f
)) {i j : ι} (hij : i < j) : Disjoint (partialSups f i) (f j)
参数：f : ι -> α；h : Pairwise (Disjoint on f)；hij : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `disjoint_partialSups_left`：disjoint_partialSups_left {f : ι -> α} {i : ι
} {x : α} : Disjoint (partialSups f i) x ↔ forall j <= i, Disjoint (f j) x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
Note this lemma requires a distributive lattice, so is not useful (or true) in s
ituations such as
submodules.
-/
theorem partialSups_disjoint_of_disjoint (f : ι → α) (h : Pairwise (Disjoint on f))
    {i j : ι} (hij : i < j) :
    Disjoint (partialSups f i) (f j) :=
  disjoint_partialSups_left.2 fun _ hk ↦ h (hk.trans_lt hij).ne

end DistribLattice

section ConditionallyCompleteLattice

/-!
### Lemmas about the supremum over the whole domain

These lemmas require some completeness assumptions on the target space.
-/
variable [Preorder ι] [LocallyFiniteOrderBot ι]

/-
**partialSups_eq_ciSup_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_eq_ciSup_Iic [ConditionallyCompleteLattice α] (f : ι -> α) (i 
: ι) : partialSups f i = ⨆ i : Set.Iic i, f i
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
-/
theorem partialSups_eq_ciSup_Iic [ConditionallyCompleteLattice α] (f : ι → α) (i : ι) :
    partialSups f i = ⨆ i : Set.Iic i, f i := by
  simp only [partialSups_apply]
  apply le_antisymm
  · exact sup'_le _ _ fun j hj ↦ Finite.le_ciSup_of_le
      ⟨j, by simpa only [Set.mem_Iic, mem_Iic] using hj⟩ le_rfl
  · exact ciSup_le fun ⟨j, hj⟩ ↦ le_sup' f (by simpa only [mem_Iic, Set.mem_Iic] using hj)

@[simp]
/-
**ciSup_partialSups_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_partialSups_eq [ConditionallyCompleteLattice α] {f : ι -> α} (h : Bd
dAbove (Set.range f)) : ⨆ i, partialSups f i = ⨆ i, f i
参数：h : BddAbove (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `partialSups_eq_ciSup_Iic`：partialSups_eq_ciSup_Iic [ConditionallyComplet
eLattice α] (f : ι -> α) (i : ι) : partialSups f i = ⨆ i : Set.Iic i, f i
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `ciSup_mono`：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : fora
ll x, f x <= g x) : iSup f <= iSup g
· 使用定理 `bddAbove_range_partialSups`：bddAbove_range_partialSups {f : ι -> α} : Bd
dAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f)
· 使用定理 `le_partialSups`：le_partialSups (f : ι -> α) : f <= partialSups f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
-/
theorem ciSup_partialSups_eq [ConditionallyCompleteLattice α]
    {f : ι → α} (h : BddAbove (Set.range f)) :
    ⨆ i, partialSups f i = ⨆ i, f i := by
  by_cases hι : Nonempty ι
  · refine (ciSup_le fun i ↦ ?_).antisymm (ciSup_mono ?_ <| le_partialSups f)
    · simpa only [partialSups_eq_ciSup_Iic] using ciSup_le fun i ↦ le_ciSup h _
    · rwa [bddAbove_range_partialSups]
  · exact congr_arg _ (funext (not_nonempty_iff.mp hι).elim)

/-- Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring a
`ConditionallyCompleteLinearOrder` rather than just a `ConditionallyCompleteLattice`. -/
@[simp]
/-
**ciSup_partialSups_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_partialSups_eq' [ConditionallyCompleteLinearOrder α] (f : ι -> α) : 
⨆ i, partialSups f i = ⨆ i, f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_partialSups_eq`：ciSup_partialSups_eq [ConditionallyCompleteLattice
 α] {f : ι -> α} (h : BddAbove (Set.range f)) : ⨆ i, partialSups f i = ⨆ i, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove`：∀ {α : Type u_5}
 [self : ConditionallyCompleteLinearOrder α] (s : Set α), ¬BddAbove s → sSup s =
 sSup ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `bddAbove_range_partialSups`：bddAbove_range_partialSups {f : ι -> α} : Bd
dAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f)

--- 原说明 ---
Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring
 a
`ConditionallyCompleteLinearOrder` rather than just a `ConditionallyCompleteLatt
ice`.
-/
theorem ciSup_partialSups_eq' [ConditionallyCompleteLinearOrder α] (f : ι → α) :
    ⨆ i, partialSups f i = ⨆ i, f i := by
  by_cases h : BddAbove (Set.range f)
  · exact ciSup_partialSups_eq h
  · rw [iSup, iSup, ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _ h,
      ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _
        (bddAbove_range_partialSups.not.mpr h)]

end ConditionallyCompleteLattice

section CompleteLattice

variable [Preorder ι] [LocallyFiniteOrderBot ι] [CompleteLattice α]

/-- Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring a
`CompleteLattice` rather than just a `ConditionallyCompleteLattice`. -/
/-
**iSup_partialSups_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_partialSups_eq (f : ι -> α) : ⨆ i, partialSups f i = ⨆ i, f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_partialSups_eq`：ciSup_partialSups_eq [ConditionallyCompleteLattice
 α] {f : ι -> α} (h : BddAbove (Set.range f)) : ⨆ i, partialSups f i = ⨆ i, f i
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s

--- 原说明 ---
Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring
 a
`CompleteLattice` rather than just a `ConditionallyCompleteLattice`.
-/
theorem iSup_partialSups_eq (f : ι → α) :
    ⨆ i, partialSups f i = ⨆ i, f i :=
  ciSup_partialSups_eq <| OrderTop.bddAbove _
/-
**partialSups_eq_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partialSups_eq_biSup (f : ι -> α) (i : ι) : partialSups f i = ⨆ j <= i, f 
j
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `partialSups_eq_ciSup_Iic`：partialSups_eq_ciSup_Iic [ConditionallyComplet
eLattice α] (f : ι -> α) (i : ι) : partialSups f i = ⨆ i : Set.Iic i, f i
-/
theorem partialSups_eq_biSup (f : ι → α) (i : ι) :
    partialSups f i = ⨆ j ≤ i, f j := by
  simpa only [iSup_subtype] using! partialSups_eq_ciSup_Iic f i
/-
**iSup_le_iSup_of_partialSups_le_partialSups** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_le_iSup_of_partialSups_le_partialSups {f g : ι -> α} (h : partialSups
 f <= partialSups g) : ⨆ i, f i <= ⨆ i, g i
参数：h : partialSups f <= partialSups g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_partialSups_eq`：iSup_partialSups_eq (f : ι -> α) : ⨆ i, partialSups
 f i = ⨆ i, f i
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
-/
theorem iSup_le_iSup_of_partialSups_le_partialSups {f g : ι → α}
    (h : partialSups f ≤ partialSups g) : ⨆ i, f i ≤ ⨆ i, g i := by
  rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g]
  exact iSup_mono h
/-
**iSup_eq_iSup_of_partialSups_eq_partialSups** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_iSup_of_partialSups_eq_partialSups {f g : ι -> α} (h : partialSups
 f = partialSups g) : ⨆ i, f i = ⨆ i, g i
参数：h : partialSups f = partialSups g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_partialSups_eq`：iSup_partialSups_eq (f : ι -> α) : ⨆ i, partialSups
 f i = ⨆ i, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_eq_iSup_of_partialSups_eq_partialSups {f g : ι → α}
    (h : partialSups f = partialSups g) : ⨆ i, f i = ⨆ i, g i := by
  simp_rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g, h]

end CompleteLattice

section Set
/-!
### Functions into `Set α`
-/

/-
**partialSups_eq_sUnion_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_eq_sUnion_image (s : Nat -> Set α) (n : Nat) : partialSups s n
 = ⋃₀ ↑((Finset.range (n + 1)).image s)
参数：s : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `partialSups_eq_biSup`：partialSups_eq_biSup (f : ι -> α) (i : ι) : partia
lSups f i = ⨆ j <= i, f j
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Functions into `Set α`
-/
lemma partialSups_eq_sUnion_image (s : ℕ → Set α) (n : ℕ) :
    partialSups s n = ⋃₀ ↑((Finset.range (n + 1)).image s) := by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]
/-
**partialSups_eq_biUnion_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_eq_biUnion_range (s : Nat -> Set α) (n : Nat) : partialSups s 
n = ⋃ i in Finset.range (n + 1), s i
参数：s : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `partialSups_eq_biSup`：partialSups_eq_biSup (f : ι -> α) (i : ι) : partia
lSups f i = ⨆ j <= i, f j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma partialSups_eq_biUnion_range (s : ℕ → Set α) (n : ℕ) :
    partialSups s n = ⋃ i ∈ Finset.range (n + 1), s i := by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]

end Set

section LinearOrder
/-!
### Functions taking values on some `LinearOrder`.
-/

variable [Preorder ι] [LocallyFiniteOrderBot ι] [LinearOrder α]

/-
**exists_partialSups_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_partialSups_eq (f : ι -> α) (i : ι) : exists j <= i, partialSups f 
i = f j
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_max_image`：exists_max_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x' <= f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `partialSups_le`：partialSups_le (f : ι -> α) (i : ι) (a : α) (w : forall 
j <= i, f j <= a) : partialSups f i <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_partialSups_of_le`：le_partialSups_of_le (f : ι -> α) {i j : ι} (h : i
 <= j) : f i <= partialSups f j
-/
theorem exists_partialSups_eq (f : ι → α) (i : ι) :
    ∃ j ≤ i, partialSups f i = f j := by
  obtain ⟨j, hj_mem, hj_le⟩ : ∃ j ∈ Finset.Iic i, ∀ k ∈ Finset.Iic i, f k ≤ f j :=
    Finset.exists_max_image _ _ ⟨i, Finset.mem_Iic.mpr le_rfl⟩
  simp only [Finset.mem_Iic] at hj_mem hj_le
  use j, hj_mem
  apply le_antisymm
  · exact partialSups_le _ _ _ fun k hk => hj_le k hk
  · exact le_partialSups_of_le f hj_mem

end LinearOrder

