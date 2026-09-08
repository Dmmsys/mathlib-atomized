/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Finset.Fin

/-!
# Kruskal-Katona theorem

This file proves the Kruskal-Katona theorem. This is a sharp statement about how many sets of size
`k - 1` are covered by a family of sets of size `k`, given only its size.

## Main declarations

The key results proved here are:
* `Finset.kruskal_katona`: The basic Kruskal-Katona theorem. Given a set family `𝒜` consisting of
  `r`-sets, and `𝒞` an initial segment of the colex order of the same size, the shadow of `𝒞` is
  smaller than the shadow of `𝒜`. In particular, this shows that the minimum shadow size is
  achieved by initial segments of colex.
* `Finset.iterated_kruskal_katona`: An iterated form of the Kruskal-Katona theorem, stating that the
  minimum iterated shadow size is given by initial segments of colex.

## TODO

* Define the `k`-cascade representation of a natural and prove the corresponding version of
  Kruskal-Katona.
* Abstract away from `Fin n` so that it also applies to `ℕ`. Probably `LocallyFiniteOrderBot`
  will help here.
* Characterise the equality case.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

kruskal-katona, kruskal, katona, shadow, initial segments, intersecting
-/

public section

open Nat
open scoped FinsetFamily

namespace Finset
namespace Colex
variable {α : Type*} [LinearOrder α] {𝒜 : Finset (Finset α)} {s : Finset α} {r : ℕ}

/-- This is important for iterating Kruskal-Katona: the shadow of an initial segment is also an
initial segment. -/
/-
**Finset.Colex.shadow_initSeg** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：shadow_initSeg [Fintype α] (hs : s.Nonempty) : ∂ (initSeg s) = initSeg (er
ase s <| min' s hs)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.erase_insert_eq_erase`：erase_insert_eq_erase (s : Finset α) (a : 
α) : (insert a s).erase a = s.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Finset.Colex.erase_le_erase_min'`：erase_le_erase_min' (hst : toColex s <
= toColex t) (hcard : #s <= #t) (ha : a in s) : toColex (s.erase a) <= toColex (
t.erase <| min' t <| c…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
This is important for iterating Kruskal-Katona: the shadow of an initial segment
 is also an
initial segment.
-/
lemma shadow_initSeg [Fintype α] (hs : s.Nonempty) :
    ∂ (initSeg s) = initSeg (erase s <| min' s hs) := by
  -- This is a pretty painful proof, with lots of cases.
  ext t
  simp only [mem_shadow_iff_insert_mem, mem_initSeg]
  constructor
  -- First show that if t ∪ a ≤ s, then t ≤ s - min s
  · rintro ⟨a, ha, hst, hts⟩
    constructor
    · rw [card_erase_of_mem (min'_mem _ _), hst, card_insert_of_notMem ha, add_tsub_cancel_right]
    · simpa [ha] using erase_le_erase_min' hts hst.ge (mem_insert_self _ _)
  -- Now show that if t ≤ s - min s, there is j such that t ∪ j ≤ s
  -- We choose j as the smallest thing not in t
  simp_rw [le_iff_eq_or_lt, lt_iff_exists_filter_lt, mem_sdiff, filter_inj, and_assoc]
  simp only [toColex_inj, and_imp]
  rintro cards' (rfl | ⟨k, hks, hkt, z⟩)
  -- If t = s - min s, then use j = min s so t ∪ j = s
  · refine ⟨min' s hs, notMem_erase _ _, ?_⟩
    rw [insert_erase (min'_mem _ _)]
    exact ⟨rfl, Or.inl rfl⟩
  set j := min' tᶜ ⟨k, mem_compl.2 hkt⟩
  -- Assume first t < s - min s, and take k as the colex witness for this
  have hjk : j ≤ k := min'_le _ _ (mem_compl.2 ‹k ∉ t›)
  have : j ∉ t := mem_compl.1 (min'_mem _ _)
  have hcard : #s = #(insert j t) := by
    rw [card_insert_of_notMem ‹j ∉ t›, ← ‹_ = #t›, card_erase_add_one (min'_mem _ _)]
  refine ⟨j, ‹_›, hcard, ?_⟩
  -- Cases on j < k or j = k
  obtain hjk | r₁ := hjk.lt_or_eq
  -- if j < k, k is our colex witness for t ∪ {j} < s
  · refine Or.inr ⟨k, mem_of_mem_erase ‹_›, fun hk ↦ hkt <| mem_of_mem_insert_of_ne hk hjk.ne',
      fun x hx ↦ ?_⟩
    simpa only [mem_insert, z hx, (hjk.trans hx).ne', mem_erase, Ne, false_or,
      and_iff_right_iff_imp] using fun _ ↦ ((min'_le _ _ <| mem_of_mem_erase hks).trans_lt hx).ne'
  -- if j = k, all of range k is in t so by sizes t ∪ {j} = s
  refine Or.inl (eq_of_subset_of_card_le (fun a ha ↦ ?_) hcard.ge).symm
  rcases lt_trichotomy k a with (lt | rfl | gt)
  · apply mem_insert_of_mem
    rw [z lt]
    refine mem_erase_of_ne_of_mem (lt_of_le_of_lt ?_ lt).ne' ha
    apply min'_le _ _ (mem_of_mem_erase ‹_›)
  · rw [r₁]; apply mem_insert_self
  · apply mem_insert_of_mem
    rw [← r₁] at gt
    by_contra
    apply (min'_le tᶜ _ _).not_gt gt
    rwa [mem_compl]

/-- The shadow of an initial segment is also an initial segment. -/
/-
**Finset.Colex.IsInitSeg.shadow** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex.IsInitSe
g`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {𝒜 : Finset (Finset α)} {r : ℕ} [F
inite α],   Finset.Colex.IsInitSeg 𝒜 r → Finset.Colex.IsInitSeg 𝒜.shadow (r - 1)
参数：Finset α；r - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.shadow_monotone`：shadow_monotone : Monotone (shadow : Finset (Fin
set α) -> Finset (Finset α))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.Colex.IsInitSeg.exists_initSeg`：∀ {α : Type u_1} [inst : LinearOr
der α] {𝒜 : Finset (Finset α)} {r : ℕ} [inst_1 : Fintype α],   Finset.Colex.IsIn
itSeg 𝒜 r → 𝒜.Nonempty → ∃ …
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用引理 `Finset.Colex.shadow_initSeg`：shadow_initSeg [Fintype α] (hs : s.Nonempty
) : ∂ (initSeg s) = initSeg (erase s <| min' s hs)
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用引理 `Finset.Colex.isInitSeg_initSeg`：isInitSeg_initSeg : IsInitSeg (initSeg s
) #s

--- 原说明 ---
The shadow of an initial segment is also an initial segment.
-/
protected lemma IsInitSeg.shadow [Finite α] (h₁ : IsInitSeg 𝒜 r) : IsInitSeg (∂ 𝒜) (r - 1) := by
  cases nonempty_fintype α
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · have : 𝒜 ⊆ {∅} := fun s hs ↦ by rw [mem_singleton, ← Finset.card_eq_zero]; exact h₁.1 hs
    have := shadow_monotone this
    simp only [subset_empty, shadow_singleton_empty] at this
    simp [this]
  obtain rfl | h𝒜 := 𝒜.eq_empty_or_nonempty
  · simp
  obtain ⟨s, rfl, rfl⟩ := h₁.exists_initSeg h𝒜
  rw [shadow_initSeg (card_pos.1 hr), ← card_erase_of_mem (min'_mem _ _)]
  exact isInitSeg_initSeg

end Colex

open Finset.Colex UV
open scoped FinsetFamily

variable {α : Type*} [LinearOrder α] {s U V : Finset α} {n : ℕ}

namespace UV

/-- Applying the compression makes the set smaller in colex. This is intuitive since a portion of
the set is being "shifted down" as `max U < max V`. -/
/-
**Finset.UV.toColex_compress_lt_toColex** 是 Mathlib 中的一个引理，位于命名空间 `Finset.UV`。
形式化陈述：toColex_compress_lt_toColex {hU : U.Nonempty} {hV : V.Nonempty} (h : max' 
U hU < max' V hV) (hA : compress U V s != s) : toColex (compress U V s) < toCole
x s
参数：h : max' U hU < max' V hV；hA : compress U V s != s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.compress.eq_1`：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] 
[inst_1 : DecidableRel Disjoint] [inst_2 : DecidableLE α]   (u v a : α), UV.comp
ress u…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ite_ne_right_iff`：ite_ne_right_iff : ite P a b != b ↔ P ∧ a != b
· 使用引理 `Finset.Colex.lt_iff_exists_filter_lt`：lt_iff_exists_filter_lt : toColex 
s < toColex t ↔ exists w in t \ s, {a in s | w < a} = {a in t | w < a}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `Finset.notMem_sdiff_of_mem_right`：notMem_sdiff_of_mem_right (h : a in t)
 : a ∉ s \ t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Applying the compression makes the set smaller in colex. This is intuitive since
 a portion of
the set is being "shifted down" as `max U < max V`.
-/
lemma toColex_compress_lt_toColex {hU : U.Nonempty} {hV : V.Nonempty} (h : max' U hU < max' V hV)
    (hA : compress U V s ≠ s) : toColex (compress U V s) < toColex s := by
  rw [compress, ite_ne_right_iff] at hA
  rw [compress, if_pos hA.1, lt_iff_exists_filter_lt]
  simp_rw [mem_sdiff (s := s), filter_inj, and_assoc]
  refine ⟨_, hA.1.2 <| max'_mem _ hV, notMem_sdiff_of_mem_right <| max'_mem _ _, fun a ha ↦ ?_⟩
  have : a ∉ V := fun H ↦ ha.not_ge (le_max' _ _ H)
  have : a ∉ U := fun H ↦ ha.not_gt ((le_max' _ _ H).trans_lt h)
  simp [‹a ∉ U›, ‹a ∉ V›]

set_option backward.privateInPublic true in
/-- These are the compressions which we will apply to decrease the "measure" of a family of sets. -/
/-
**Finset.UV.UsefulCompression** 是 Mathlib 中的一个定义，位于命名空间 `Finset.UV`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These are the compressions which we will apply to decrease the "measure" of a fa
mily of sets.
-/
private def UsefulCompression (U V : Finset α) : Prop :=
  Disjoint U V ∧ #U = #V ∧ ∃ (HU : U.Nonempty) (HV : V.Nonempty), max' U HU < max' V HV
/-
**Finset.UV.UsefulCompression.instDecidableRel** 是 Mathlib 中的一个实例，位于命名空间 `Finset
.UV`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance UsefulCompression.instDecidableRel :
    DecidableRel (α := Finset α) UsefulCompression :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Applying a good compression will decrease measure, keep cardinality, keep sizes and decrease
shadow. In particular, 'good' means it's useful, and every smaller compression won't make a
difference. -/
/-
**Finset.UV.compression_improved** 是 Mathlib 中的一个引理，位于命名空间 `Finset.UV`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying a good compression will decrease measure, keep cardinality, keep sizes 
and decrease
shadow. In particular, 'good' means it's useful, and every smaller compression w
on't make a
difference.
-/
private lemma compression_improved (𝒜 : Finset (Finset α)) (h₁ : UsefulCompression U V)
    (h₂ : ∀ ⦃U₁ V₁⦄, UsefulCompression U₁ V₁ → #U₁ < #U → IsCompressed U₁ V₁ 𝒜) :
    #(∂ (𝓒 U V 𝒜)) ≤ #(∂ 𝒜) := by
  obtain ⟨UVd, same_size, hU, hV, max_lt⟩ := h₁
  refine card_shadow_compression_le _ _ fun x Hx ↦ ⟨min' V hV, min'_mem _ _, ?_⟩
  obtain hU' | hU' := eq_or_lt_of_le (succ_le_iff.2 hU.card_pos)
  · rw [← hU'] at same_size
    have : erase U x = ∅ := by rw [← Finset.card_eq_zero, card_erase_of_mem Hx, ← hU']
    have : erase V (min' V hV) = ∅ := by
      rw [← Finset.card_eq_zero, card_erase_of_mem (min'_mem _ _), ← same_size]
    rw [‹erase U x = ∅›, ‹erase V (min' V hV) = ∅›]
    exact isCompressed_self _ _
  refine h₂ ⟨UVd.mono (erase_subset ..) (erase_subset ..), ?_, ?_, ?_, ?_⟩ (card_erase_lt_of_mem Hx)
  · rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size]
  · rwa [← card_pos, card_erase_of_mem Hx, tsub_pos_iff_lt]
  · rwa [← Finset.card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, tsub_pos_iff_lt]
  · exact (Finset.max'_subset _ <| erase_subset _ _).trans_lt (max_lt.trans_le <| le_max' _ _ <|
      mem_erase.2 ⟨(min'_lt_max'_of_card _ (by rwa [← same_size])).ne', max'_mem _ _⟩)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If we're compressed by all useful compressions, then we're an initial segment. This is the other
key Kruskal-Katona part. -/
/-
**Finset.UV.isInitSeg_of_compressed** 是 Mathlib 中的一个引理，位于命名空间 `Finset.UV`。
形式化陈述：isInitSeg_of_compressed {ℬ : Finset (Finset α)} {r : Nat} (h₁ : (ℬ : Set (
Finset α)).Sized r) (h₂ : forall U V, UsefulCompression U V -> IsCompressed U V 
ℬ) : IsInitSeg ℬ r
参数：Finset α；h₁ : (ℬ : Set (Finset α)).Sized r；h₂ : forall U V, UsefulCompression
 U V -> IsCompressed U V ℬ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sdiff_nonempty`：sdiff_nonempty : (s \ t).Nonempty ↔ ¬s subseteq t
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
· 使用定理 `Finset.disjoint_sdiff`：disjoint_sdiff : Disjoint s (t \ s)
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.compress_sdiff_sdiff`：compress_sdiff_sdiff (a b : α) : compress (a \ 
b) (b \ a) b = a
· 使用引理 `Finset.UV.toColex_compress_lt_toColex`：toColex_compress_lt_toColex {hU :
 U.Nonempty} {hV : V.Nonempty} (h : max' U hU < max' V hV) (hA : compress U V s 
!= s) : toColex (compress U…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in 
t -> a ∉ s
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `UV.IsCompressed.eq`：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α
] [inst_1 : DecidableRel Disjoint] [inst_2 : DecidableLE α]   {s : Finset α} {u 
v : α} […
· 使用定理 `Finset.card_sdiff_comm`：∀ {α : Type u_1} {s t : Finset α} [inst : Decida
bleEq α], s.card = t.card → (s \ t).card = (t \ s).card
· 使用定理 `UV.mem_compression`：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u
 v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a

--- 原说明 ---
If we're compressed by all useful compressions, then we're an initial segment. T
his is the other
key Kruskal-Katona part.
-/
lemma isInitSeg_of_compressed {ℬ : Finset (Finset α)} {r : ℕ} (h₁ : (ℬ : Set (Finset α)).Sized r)
    (h₂ : ∀ U V, UsefulCompression U V → IsCompressed U V ℬ) : IsInitSeg ℬ r := by
  refine ⟨h₁, ?_⟩
  rintro A B hA ⟨hBA, sizeA⟩
  by_contra hB
  have hAB : A ≠ B := ne_of_mem_of_not_mem hA hB
  have hAB' : #A = #B := (h₁ hA).trans sizeA.symm
  have hU : (A \ B).Nonempty := sdiff_nonempty.2 fun h ↦ hAB <| eq_of_subset_of_card_le h hAB'.ge
  have hV : (B \ A).Nonempty :=
    sdiff_nonempty.2 fun h ↦ hAB.symm <| eq_of_subset_of_card_le h hAB'.le
  have disj : Disjoint (B \ A) (A \ B) := disjoint_sdiff.mono_left sdiff_subset
  have smaller : max' _ hV < max' _ hU := by
    obtain hlt | heq | hgt := lt_trichotomy (max' _ hU) (max' _ hV)
    · rw [← compress_sdiff_sdiff A B] at hAB hBA
      cases hBA.not_gt <| toColex_compress_lt_toColex hlt hAB
    · exact (disjoint_right.1 disj (max'_mem _ hU) <| heq.symm ▸ max'_mem _ _).elim
    · assumption
  refine hB ?_
  rw [← (h₂ _ _ ⟨disj, card_sdiff_comm hAB'.symm, hV, hU, smaller⟩).eq]
  exact mem_compression.2 (Or.inr ⟨hB, A, hA, compress_sdiff_sdiff _ _⟩)

attribute [-instance] Fintype.decidableForallFintype

/-- This measures roughly how compressed the family is.

Note that this does depend on the order of the ground set, unlike the Kruskal-Katona theorem itself
(although `kruskal_katona` currently is stated in an order-dependent manner). -/
/-
**Finset.UV.familyMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Finset.UV`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This measures roughly how compressed the family is.

Note that this does depend on the order of the ground set, unlike the Kruskal-Ka
tona theorem itself
(although `kruskal_katona` currently is stated in an order-dependent manner).
-/
private def familyMeasure (𝒜 : Finset (Finset (Fin n))) : ℕ := ∑ A ∈ 𝒜, ∑ a ∈ A, 2 ^ (a : ℕ)

/-- Applying a compression strictly decreases the measure. This helps show that "compress until we
can't any more" is a terminating process. -/
private lemma familyMeasure_compression_lt_familyMeasure {U V : Finset (Fin n)} {hU : U.Nonempty}
    {hV : V.Nonempty} (h : max' U hU < max' V hV) {𝒜 : Finset (Finset (Fin n))} (a : 𝓒 U V 𝒜 ≠ 𝒜) :
    familyMeasure (𝓒 U V 𝒜) < familyMeasure 𝒜 := by
  rw [compression] at a ⊢
  have q : ∀ Q ∈ {A ∈ 𝒜 | compress U V A ∉ 𝒜}, compress U V Q ≠ Q := by grind
  have uA : {A ∈ 𝒜 | compress U V A ∈ 𝒜} ∪ {A ∈ 𝒜 | compress U V A ∉ 𝒜} = 𝒜 :=
    filter_union_filter_not_eq _ _
  have ne₂ : {A ∈ 𝒜 | compress U V A ∉ 𝒜}.Nonempty := by
    contrapose! a
    rw [filter_image, a, image_empty, union_empty]
    rwa [a, union_empty] at uA
  rw [familyMeasure, familyMeasure, sum_union compress_disjoint]
  conv_rhs => rw [← uA]
  rw [sum_union (disjoint_filter_filter_not _ _ _), add_lt_add_iff_left, filter_image,
    sum_image compress_injOn]
  refine sum_lt_sum_of_nonempty ne₂ fun A hA ↦ ?_
  simp_rw [← sum_image Fin.val_injective.injOn]
  rw [geomSum_lt_geomSum_iff_toColex_lt_toColex le_rfl,
    toColex_image_lt_toColex_image Fin.val_strictMono]
  exact toColex_compress_lt_toColex h <| q _ hA

/-- The main Kruskal-Katona helper: use induction with our measure to keep compressing until
we can't any more, which gives a set family which is fully compressed and has the nice properties we
want. -/
private lemma kruskal_katona_helper {r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h : (𝒜 : Set (Finset (Fin n))).Sized r) :
    ∃ ℬ : Finset (Finset (Fin n)), #(∂ ℬ) ≤ #(∂ 𝒜) ∧ #𝒜 = #ℬ ∧
      (ℬ : Set (Finset (Fin n))).Sized r ∧ ∀ U V, UsefulCompression U V → IsCompressed U V ℬ := by
  classical
  -- Are there any compressions we can make now?
  set usable : Finset (Finset (Fin n) × Finset (Fin n)) :=
    {t | UsefulCompression t.1 t.2 ∧ ¬ IsCompressed t.1 t.2 𝒜}
  obtain husable | husable := usable.eq_empty_or_nonempty
  -- No. Then where we are is the required set family.
  · refine ⟨𝒜, le_rfl, rfl, h, fun U V hUV ↦ ?_⟩
    rw [eq_empty_iff_forall_notMem] at husable
    by_contra h
    exact husable ⟨U, V⟩ <| mem_filter.2 ⟨mem_univ _, hUV, h⟩
  -- Yes. Then apply the smallest compression, then keep going
  obtain ⟨⟨U, V⟩, hUV, t⟩ := exists_min_image usable (fun t ↦ #t.1) husable
  rw [mem_filter] at hUV
  have h₂ : ∀ U₁ V₁, UsefulCompression U₁ V₁ → #U₁ < #U → IsCompressed U₁ V₁ 𝒜 := by
    rintro U₁ V₁ huseful hUcard
    by_contra h
    exact hUcard.not_ge <| t ⟨U₁, V₁⟩ <| mem_filter.2 ⟨mem_univ _, huseful, h⟩
  have p1 : #(∂ (𝓒 U V 𝒜)) ≤ #(∂ 𝒜) := compression_improved _ hUV.2.1 h₂
  obtain ⟨-, hUV', hu, hv, hmax⟩ := hUV.2.1
  have := familyMeasure_compression_lt_familyMeasure hmax hUV.2.2
  obtain ⟨t, q1, q2, q3, q4⟩ := UV.kruskal_katona_helper (𝓒 U V 𝒜) (h.uvCompression hUV')
  exact ⟨t, q1.trans p1, (card_compression _ _ _).symm.trans q2, q3, q4⟩
termination_by familyMeasure 𝒜

end UV

-- Finally we can prove Kruskal-Katona.
section KK
variable {r k i : ℕ} {𝒜 𝒞 : Finset <| Finset <| Fin n}

/-- The **Kruskal-Katona theorem**.

Given a set family `𝒜` consisting of `r`-sets, and `𝒞` an initial segment of the colex order of the
same size, the shadow of `𝒞` is smaller than the shadow of `𝒜`. In particular, this gives that the
minimum shadow size is achieved by initial segments of colex. -/
theorem kruskal_katona (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r) (h𝒞𝒜 : #𝒞 ≤ #𝒜)
    (h𝒞 : IsInitSeg 𝒞 r) : #(∂ 𝒞) ≤ #(∂ 𝒜) := by
  -- WLOG `|𝒜| = |𝒞|`
  obtain ⟨𝒜', h𝒜, h𝒜𝒞⟩ := exists_subset_card_eq h𝒞𝒜
  -- By `kruskal_katona_helper`, we find a fully compressed family `ℬ` of the same size as `𝒜`
  -- whose shadow is no bigger.
  obtain ⟨ℬ, hℬ𝒜, h𝒜ℬ, hℬr, hℬ⟩ := UV.kruskal_katona_helper 𝒜' (h𝒜r.mono (by gcongr))
  -- This means that `ℬ` is an initial segment of the same size as `𝒞`. Hence they are equal and
  -- we are done.
  suffices ℬ = 𝒞 by subst 𝒞; exact hℬ𝒜.trans (by gcongr)
  have hcard : #ℬ = #𝒞 := h𝒜ℬ.symm.trans h𝒜𝒞
  obtain h𝒞ℬ | hℬ𝒞 := h𝒞.total (UV.isInitSeg_of_compressed hℬr hℬ)
  · exact (eq_of_subset_of_card_le h𝒞ℬ hcard.le).symm
  · exact eq_of_subset_of_card_le hℬ𝒞 hcard.ge

/-- An iterated form of the Kruskal-Katona theorem. In particular, the minimum possible iterated
shadow size is attained by initial segments. -/
theorem iterated_kk (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : #𝒞 ≤ #𝒜) (h₃ : IsInitSeg 𝒞 r) :
    #(∂^[k] 𝒞) ≤ #(∂^[k] 𝒜) := by
  induction k generalizing r 𝒜 𝒞 with
  | zero => simpa
  | succ _ ih =>
    refine ih h₁.shadow (kruskal_katona h₁ h₂ h₃) ?_
    convert! h₃.shadow

/-- The **Lovasz formulation of the Kruskal-Katona theorem**.

If `|𝒜| ≥ k choose r`, (and everything in `𝒜` has size `r`) then the initial segment we compare to
is just all the subsets of `{0, ..., k - 1}` of size `r`. The `i`-th iterated shadow of this is all
the subsets of `{0, ..., k - 1}` of size `r - i`, so the `i`-th iterated shadow of `𝒜` has at least
`k.choose (r - i)` elements. -/
theorem kruskal_katona_lovasz_form (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  set range'k : Finset (Fin n) :=
    attachFin (range k) fun m ↦ by rw [mem_range]; apply forall_lt_iff_le.2 hkn
  set 𝒞 : Finset (Finset (Fin n)) := powersetCard r range'k
  have : (𝒞 : Set (Finset (Fin n))).Sized r := Set.sized_powersetCard _ _
  calc
    k.choose (r - i)
    _ = #(powersetCard (r - i) range'k) := by rw [card_powersetCard, card_attachFin, card_range]
    _ = #(∂^[i] 𝒞) := by
      congr!
      ext B
      rw [mem_powersetCard, mem_shadow_iterate_iff_exists_sdiff]
      constructor
      · rintro ⟨hBk, hB⟩
        have := exists_subsuperset_card_eq hBk (Nat.le_add_left _ i) <| by
          rwa [hB, card_attachFin, card_range, ← Nat.add_sub_assoc hir, Nat.add_sub_cancel_left]
        obtain ⟨C, BsubC, hCrange, hcard⟩ := this
        rw [hB, ← Nat.add_sub_assoc hir, Nat.add_sub_cancel_left] at hcard
        refine ⟨C, mem_powersetCard.2 ⟨hCrange, hcard⟩, BsubC, ?_⟩
        rw [card_sdiff_of_subset BsubC, hcard, hB, Nat.sub_sub_self hir]
      · rintro ⟨A, Ah, hBA, card_sdiff_i⟩
        rw [mem_powersetCard] at Ah
        refine ⟨hBA.trans Ah.1, eq_tsub_of_add_eq ?_⟩
        rw [← Ah.2, ← card_sdiff_i, add_comm, card_sdiff_add_card_eq_card hBA]
    _ ≤ #(∂^[i] 𝒜) := by
      refine iterated_kk h₁ ?_ ⟨‹_›, ?_⟩
      · rwa [card_powersetCard, card_attachFin, card_range]
      simp_rw [𝒞, mem_powersetCard]
      rintro A B hA ⟨HB₁, HB₂⟩
      refine ⟨fun t ht ↦ ?_, ‹_›⟩
      rw [mem_attachFin, mem_range]
      have : toColex (image Fin.val B) < toColex (image Fin.val A) := by
        rwa [toColex_image_lt_toColex_image Fin.val_strictMono]
      apply Colex.forall_lt_mono this.le _ t (mem_image.2 ⟨t, ht, rfl⟩)
      simp_rw [mem_image]
      rintro _ ⟨a, ha, hab⟩
      simpa [range'k, hab] using hA.1 ha

end KK

/-- The **Erdős–Ko–Rado theorem**.

The maximum size of an intersecting family in `α` where all sets have size `r` is bounded by
`(card α - 1).choose (r - 1)`. This bound is sharp. -/
theorem erdos_ko_rado {𝒜 : Finset (Finset (Fin n))} {r : ℕ}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) (h₂ : (𝒜 : Set (Finset (Fin n))).Sized r)
    (h₃ : r ≤ n / 2) :
    #𝒜 ≤ (n - 1).choose (r - 1) := by
  -- Take care of the r=0 case first: it's not very interesting.
  rcases Nat.eq_zero_or_pos r with b | h1r
  · convert! Nat.zero_le _
    rw [Finset.card_eq_zero, eq_empty_iff_forall_notMem]
    refine fun A HA ↦ h𝒜 HA HA ?_
    rw [disjoint_self_iff_empty, ← Finset.card_eq_zero, ← b]
    exact h₂ HA
  refine le_of_not_gt fun size ↦ ?_
  -- Consider 𝒜ᶜˢ = {sᶜ | s ∈ 𝒜}
  -- Its iterated shadow (∂^[n-2k] 𝒜ᶜˢ) is disjoint from 𝒜 by intersecting-ness
  have : Disjoint 𝒜 (∂^[n - 2 * r] 𝒜ᶜˢ) := disjoint_right.2 fun A hAbar hA ↦ by
    simp only [mem_shadow_iterate_iff_exists_sdiff, mem_compls] at hAbar
    obtain ⟨C, hC, hAC, _⟩ := hAbar
    exact h𝒜 hA hC (disjoint_of_subset_left hAC disjoint_compl_right)
  have : r ≤ n := h₃.trans (Nat.div_le_self n 2)
  have : 1 ≤ n := ‹1 ≤ r›.trans ‹r ≤ n›
  -- We know the size of 𝒜ᶜˢ since it's the same size as 𝒜
  have z : (n - 1).choose (n - r) < #𝒜ᶜˢ := by
    rwa [card_compls, choose_symm_of_eq_add (tsub_add_tsub_cancel ‹r ≤ n› ‹1 ≤ r›).symm]
  -- and everything in 𝒜ᶜˢ has size n-r.
  have h𝒜bar : (𝒜ᶜˢ : Set (Finset (Fin n))).Sized (n - r) := by simpa using h₂.compls
  -- We can use the Lovasz form of Kruskal-Katona to get |∂^[n-2k] 𝒜ᶜˢ| ≥ (n-1) choose r
  have kk := kruskal_katona_lovasz_form (i := n - 2 * r) (by lia)
    ((tsub_le_tsub_iff_left ‹1 ≤ n›).2 h1r) tsub_le_self h𝒜bar z.le
  have : n - r - (n - 2 * r) = r := by lia
  rw [this] at kk
  -- But this gives a contradiction: `n choose r < |𝒜| + |∂^[n-2k] 𝒜ᶜˢ|`
  have := calc
    n.choose r = (n - 1).choose (r - 1) + (n - 1).choose r := by
      convert! Nat.choose_succ_succ _ _ using 3 <;> rwa [Nat.sub_one, Nat.succ_pred_eq_of_pos]
    _ < #𝒜 + #(∂^[n - 2 * r] 𝒜ᶜˢ) := add_lt_add_of_lt_of_le size kk
    _ = #(𝒜 ∪ ∂^[n - 2 * r] 𝒜ᶜˢ) := by rw [card_union_of_disjoint ‹_›]
  apply this.not_ge
  convert! Set.Sized.card_le _
  · rw [Fintype.card_fin]
  rw [coe_union, Set.sized_union]
  refine ⟨‹_›, ?_⟩
  convert! h𝒜bar.shadow_iterate
  lia

end Finset

