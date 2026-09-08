/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.UpperLower.Basic

/-!
# Harris-Kleitman inequality

This file proves the Harris-Kleitman inequality. This relates `#𝒜 * #ℬ` and
`2 ^ card α * #(𝒜 ∩ ℬ)` where `𝒜` and `ℬ` are upward- or downcard-closed finite families of
finsets. This can be interpreted as saying that any two lower sets (resp. any two upper sets)
correlate in the uniform measure.

## Main declarations

* `IsLowerSet.le_card_inter_finset`: One form of the Harris-Kleitman inequality.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

public section


open Finset

variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s : Finset α} {a : α}

/-
**IsLowerSet.nonMemberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.nonMemberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) : IsLo
werSet (𝒜.nonMemberSubfamily a : Set (Finset α))
参数：h : IsLowerSet (𝒜 : Set (Finset α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem IsLowerSet.nonMemberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet (𝒜.nonMemberSubfamily a : Set (Finset α)) := fun s t hts => by
  simp_rw [mem_coe, mem_nonMemberSubfamily]
  exact And.imp (h hts) (mt <| @hts _)
/-
**IsLowerSet.memberSubfamily** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.memberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) : IsLower
Set (𝒜.memberSubfamily a : Set (Finset α))
参数：h : IsLowerSet (𝒜 : Set (Finset α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Finset.insert_subset_insert`：insert_subset_insert (a : α) {s t : Finset 
α} (h : s subseteq t) : insert a s subseteq insert a t
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem IsLowerSet.memberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet (𝒜.memberSubfamily a : Set (Finset α)) := by
  rintro s t hts
  simp_rw [mem_coe, mem_memberSubfamily]
  exact And.imp (h <| insert_subset_insert _ hts) (mt <| @hts _)
/-
**IsLowerSet.memberSubfamily_subset_nonMemberSubfamily** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsLowerSet.memberSubfamily_subset_nonMemberSubfamily (h : IsLowerSet (𝒜 : 
Set (Finset α))) : 𝒜.memberSubfamily a subseteq 𝒜.nonMemberSubfamily a
参数：h : IsLowerSet (𝒜 : Set (Finset α))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_memberSubfamily`：mem_memberSubfamily : s in 𝒜.memberSubfamily
 a ↔ insert a s in 𝒜 ∧ a ∉ s
· 使用定理 `Finset.mem_nonMemberSubfamily`：mem_nonMemberSubfamily : s in 𝒜.nonMember
Subfamily a ↔ s in 𝒜 ∧ a ∉ s
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
-/
theorem IsLowerSet.memberSubfamily_subset_nonMemberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    𝒜.memberSubfamily a ⊆ 𝒜.nonMemberSubfamily a := fun s => by
  rw [mem_memberSubfamily, mem_nonMemberSubfamily]
  exact And.imp_left (h <| subset_insert _ _)

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
/-
**IsLowerSet.le_card_inter_finset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.le_card_inter_finset' (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (h
ℬ : IsLowerSet (ℬ : Set (Finset α))) (h𝒜s : forall t in 𝒜, t subseteq s) (hℬs : 
forall t in ℬ, t subseteq s) : #𝒜 * #ℬ <= 2 ^ #s * #(𝒜 inter ℬ)
参数：h𝒜 : IsLowerSet (𝒜 : Set (Finset α))；hℬ : IsLowerSet (ℬ : Set (Finset α))；h𝒜s
 : forall t in 𝒜, t subseteq s；hℬs : forall t in ℬ, t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.empty_inter`：empty_inter (s : Finset α) : ∅ inter s = ∅
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.inter_empty`：inter_empty (s : Finset α) : s inter ∅ = ∅
· 使用定理 `Finset.inter_singleton_of_mem`：inter_singleton_of_mem {a : α} {s : Finse
t α} (h : a in s) : s inter {a} = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Finset.card_memberSubfamily_add_card_nonMemberSubfamily`：card_memberSubf
amily_add_card_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : #(𝒜.memberSu
bfamily a) + #(𝒜.nonMemberSubfamily a) = #𝒜
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `mul_add_mul_le_mul_add_mul`：mul_add_mul_le_mul_add_mul [ExistsAddOfLE R]
 [MulPosMono R] [AddLeftMono R] [AddLeftReflectLE R] (hab : a <= b) (hcd : c <= 
d) : a * d + b *…
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
**Harris-Kleitman inequality**: Any two lower sets of finsets correlate.
-/
theorem IsLowerSet.le_card_inter_finset' (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) (h𝒜s : ∀ t ∈ 𝒜, t ⊆ s) (hℬs : ∀ t ∈ ℬ, t ⊆ s) :
    #𝒜 * #ℬ ≤ 2 ^ #s * #(𝒜 ∩ ℬ) := by
  induction s using Finset.induction generalizing 𝒜 ℬ with
  | empty =>
    simp_rw [subset_empty, ← subset_singleton_iff', subset_singleton_iff] at h𝒜s hℬs
    obtain rfl | rfl := h𝒜s
    · simp only [card_empty, zero_mul, empty_inter, mul_zero, le_refl]
    obtain rfl | rfl := hℬs
    · simp
    · simp only [card_empty, pow_zero, inter_singleton_of_mem, mem_singleton, card_singleton,
        le_refl]
  | insert a s hs ih =>
  rw [card_insert_of_notMem hs, ← card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜, ←
    card_memberSubfamily_add_card_nonMemberSubfamily a ℬ, add_mul, mul_add, mul_add,
    add_comm (_ * _), add_add_add_comm]
  grw [mul_add_mul_le_mul_add_mul
    (card_le_card h𝒜.memberSubfamily_subset_nonMemberSubfamily) <|
      card_le_card hℬ.memberSubfamily_subset_nonMemberSubfamily, ← two_mul, pow_succ', mul_assoc]
  have h₀ : ∀ 𝒞 : Finset (Finset α), (∀ t ∈ 𝒞, t ⊆ insert a s) →
      ∀ t ∈ 𝒞.nonMemberSubfamily a, t ⊆ s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_nonMemberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 (h𝒞 _ ht.1)
  have h₁ : ∀ 𝒞 : Finset (Finset α), (∀ t ∈ 𝒞, t ⊆ insert a s) →
      ∀ t ∈ 𝒞.memberSubfamily a, t ⊆ s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_memberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 ((subset_insert _ _).trans <| h𝒞 _ ht.1)
  gcongr
  refine (add_le_add (ih h𝒜.memberSubfamily hℬ.memberSubfamily (h₁ _ h𝒜s) <| h₁ _ hℬs) <|
    ih h𝒜.nonMemberSubfamily hℬ.nonMemberSubfamily (h₀ _ h𝒜s) <| h₀ _ hℬs).trans_eq ?_
  rw [← mul_add, ← memberSubfamily_inter, ← nonMemberSubfamily_inter,
    card_memberSubfamily_add_card_nonMemberSubfamily]

variable [Fintype α]

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
/-
**IsLowerSet.le_card_inter_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.le_card_inter_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ
 : IsLowerSet (ℬ : Set (Finset α))) : #𝒜 * #ℬ <= 2 ^ Fintype.card α * #(𝒜 inter 
ℬ)
参数：h𝒜 : IsLowerSet (𝒜 : Set (Finset α))；hℬ : IsLowerSet (ℬ : Set (Finset α))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLowerSet.le_card_inter_finset'`：IsLowerSet.le_card_inter_finset' (h𝒜 :
 IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) (h𝒜s : 
forall t in 𝒜, t subse…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ

--- 原说明 ---
**Harris-Kleitman inequality**: Any two lower sets of finsets correlate.
-/
theorem IsLowerSet.le_card_inter_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) : #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) :=
h𝒜.le_card_inter_finset' hℬ (fun _ _ => subset_univ _) fun _ _ => subset_univ _

/-- **Harris-Kleitman inequality**: Upper sets and lower sets of finsets anticorrelate. -/
/-
**IsUpperSet.card_inter_le_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.card_inter_le_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ
 : IsLowerSet (ℬ : Set (Finset α))) : 2 ^ Fintype.card α * #(𝒜 inter ℬ) <= #𝒜 * 
#ℬ
参数：h𝒜 : IsUpperSet (𝒜 : Set (Finset α))；hℬ : IsLowerSet (ℬ : Set (Finset α))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLowerSet.le_card_inter_finset`：IsLowerSet.le_card_inter_finset (h𝒜 : I
sLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) : #𝒜 * #ℬ
 <= 2 ^ Fintype.card …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `isLowerSet_compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 sᶜ ↔ IsUpperSet s
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `sdiff_compl`：sdiff_compl : x \ yᶜ = x ⊓ y
· 使用定理 `Finset.sdiff_inter_self_right`：sdiff_inter_self_right (s t : Finset α) :
 s \ (t inter s) = s \ t
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
· 使用定理 `mul_tsub`：mul_tsub (a b c : R) : a * (b - c) = a * b - a * c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tsub_le_iff_tsub_le`：tsub_le_iff_tsub_le : a - b <= c ↔ a - c <= b
· 使用定理 `tsub_mul`：tsub_mul [MulRightMono R] (a b c : R) : (a - b) * c = a * c - 
b * c
· 使用定理 `Fintype.card_finset`：Fintype.card_finset [Fintype α] : Fintype.card (Fin
set α) = 2 ^ Fintype.card α
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s

--- 原说明 ---
**Harris-Kleitman inequality**: Upper sets and lower sets of finsets anticorrela
te.
-/
theorem IsUpperSet.card_inter_le_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    2 ^ Fintype.card α * #(𝒜 ∩ ℬ) ≤ #𝒜 * #ℬ := by
  rw [← isLowerSet_compl, ← coe_compl] at h𝒜
  have := h𝒜.le_card_inter_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, tsub_le_iff_tsub_le, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this

/-- **Harris-Kleitman inequality**: Lower sets and upper sets of finsets anticorrelate. -/
/-
**IsLowerSet.card_inter_le_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.card_inter_le_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ
 : IsUpperSet (ℬ : Set (Finset α))) : 2 ^ Fintype.card α * #(𝒜 inter ℬ) <= #𝒜 * 
#ℬ
参数：h𝒜 : IsLowerSet (𝒜 : Set (Finset α))；hℬ : IsUpperSet (ℬ : Set (Finset α))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUpperSet.card_inter_le_finset`：IsUpperSet.card_inter_le_finset (h𝒜 : I
sUpperSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) : 2 ^ Fin
type.card α * #(𝒜 int…

--- 原说明 ---
**Harris-Kleitman inequality**: Lower sets and upper sets of finsets anticorrela
te.
-/
theorem IsLowerSet.card_inter_le_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    2 ^ Fintype.card α * #(𝒜 ∩ ℬ) ≤ #𝒜 * #ℬ := by
  rw [inter_comm, mul_comm #𝒜]
  exact hℬ.card_inter_le_finset h𝒜

/-- **Harris-Kleitman inequality**: Any two upper sets of finsets correlate. -/
/-
**IsUpperSet.le_card_inter_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.le_card_inter_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ
 : IsUpperSet (ℬ : Set (Finset α))) : #𝒜 * #ℬ <= 2 ^ Fintype.card α * #(𝒜 inter 
ℬ)
参数：h𝒜 : IsUpperSet (𝒜 : Set (Finset α))；hℬ : IsUpperSet (ℬ : Set (Finset α))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLowerSet.card_inter_le_finset`：IsLowerSet.card_inter_le_finset (h𝒜 : I
sLowerSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α))) : 2 ^ Fin
type.card α * #(𝒜 int…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `isLowerSet_compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 sᶜ ↔ IsUpperSet s
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `sdiff_compl`：sdiff_compl : x \ yᶜ = x ⊓ y
· 使用定理 `Finset.sdiff_inter_self_right`：sdiff_inter_self_right (s t : Finset α) :
 s \ (t inter s) = s \ t
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
· 使用定理 `mul_tsub`：mul_tsub (a b c : R) : a * (b - c) = a * b - a * c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_tsub_iff_le_tsub`：le_tsub_iff_le_tsub (h₁ : a <= b) (h₂ : c <= b) : a
 <= b - c ↔ c <= b - a
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Fintype.card_finset`：Fintype.card_finset [Fintype α] : Fintype.card (Fin
set α) = 2 ^ Fintype.card α
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `tsub_mul`：tsub_mul [MulRightMono R] (a b c : R) : (a - b) * c = a * c - 
b * c
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s

--- 原说明 ---
**Harris-Kleitman inequality**: Any two upper sets of finsets correlate.
-/
theorem IsUpperSet.le_card_inter_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) := by
  rw [← isLowerSet_compl, ← coe_compl] at h𝒜
  have := h𝒜.card_inter_le_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, le_tsub_iff_le_tsub, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this
  · grw [inter_subset_right]
  · grw [← Fintype.card_finset, card_le_univ]
