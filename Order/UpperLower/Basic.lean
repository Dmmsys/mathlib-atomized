/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.OrderEmbedding
public import Mathlib.Order.SetNotation
public import Mathlib.Order.WellFounded

/-!
# Properties of unbundled upper/lower sets

This file proves results on `IsUpperSet` and `IsLowerSet`, including their interactions with
set operations, images, preimages and order duals, and properties that reflect stronger assumptions
on the underlying order (such as `PartialOrder` and `LinearOrder`).

## TODO

* Lattice structure on antichains.
* Order equivalence between upper/lower sets and antichains.
-/

public section

open OrderDual Set

variable {α β : Type*} {ι : Sort*} {κ : ι → Sort*}

attribute [aesop norm unfold] IsUpperSet IsLowerSet

section LE

variable [LE α] {s t : Set α} {a : α}

@[to_dual]
/-
**isUpperSet_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_empty : IsUpperSet (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUpperSet_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id

@[to_dual]
/-
**isUpperSet_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_univ : IsUpperSet (univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUpperSet_univ : IsUpperSet (univ : Set α) := fun _ _ _ => id

@[to_dual]
/-
**IsUpperSet.compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ := fun _a _b h hb ha => hb <| hs h ha

@[to_dual (attr := simp)]
/-
**isUpperSet_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `IsUpperSet.compl`：IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ
· 使用定理 `IsLowerSet.compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 s → IsUpperSet sᶜ
-/
theorem isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s :=
  ⟨fun h => by
    convert! h.compl
    rw [compl_compl], IsLowerSet.compl⟩

@[to_dual]
/-
**IsUpperSet.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s u
nion t)
参数：hs : IsUpperSet s；ht : IsUpperSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
-/
theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∪ t) :=
  fun _ _ h => Or.imp (hs h) (ht h)

@[to_dual]
/-
**IsUpperSet.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s i
nter t)
参数：hs : IsUpperSet s；ht : IsUpperSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
-/
theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∩ t) :=
  fun _ _ h => And.imp (hs h) (ht h)

@[to_dual]
/-
**isUpperSet_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_sUnion {S : Set (Set α)} (hf : forall s in S, IsUpperSet s) : I
sUpperSet (⋃₀ S)
参数：Set α；hf : forall s in S, IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isUpperSet_sUnion {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋃₀ S) :=
  fun _ _ h => Exists.imp fun _ hs => ⟨hs.1, hf _ hs.1 h hs.2⟩

@[to_dual]
/-
**isUpperSet_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_iUnion {f : ι -> Set α} (hf : forall i, IsUpperSet (f i)) : IsU
pperSet (⋃ i, f i)
参数：hf : forall i, IsUpperSet (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_sUnion`：isUpperSet_sUnion {S : Set (Set α)} (hf : forall s in
 S, IsUpperSet s) : IsUpperSet (⋃₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isUpperSet_iUnion {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) :=
  isUpperSet_sUnion <| forall_mem_range.2 hf

@[to_dual]
/-
**isUpperSet_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_iUnion {f : ι -> Set α} (hf : forall i, IsUpperSet (f i)) : IsU
pperSet (⋃ i, f i)
参数：hf : forall i, IsUpperSet (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_sUnion`：isUpperSet_sUnion {S : Set (Set α)} (hf : forall s in
 S, IsUpperSet s) : IsUpperSet (⋃₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isUpperSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋃ (i) (j), f i j) :=
  isUpperSet_iUnion fun i => isUpperSet_iUnion <| hf i

@[to_dual]
/-
**isUpperSet_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_sInter {S : Set (Set α)} (hf : forall s in S, IsUpperSet s) : I
sUpperSet (⋂₀ S)
参数：Set α；hf : forall s in S, IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
-/
theorem isUpperSet_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋂₀ S) :=
  fun _ _ h => forall₂_imp fun s hs => hf s hs h

@[to_dual]
/-
**isUpperSet_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_iInter {f : ι -> Set α} (hf : forall i, IsUpperSet (f i)) : IsU
pperSet (⋂ i, f i)
参数：hf : forall i, IsUpperSet (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_sInter`：isUpperSet_sInter {S : Set (Set α)} (hf : forall s in
 S, IsUpperSet s) : IsUpperSet (⋂₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isUpperSet_iInter {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) :=
  isUpperSet_sInter <| forall_mem_range.2 hf

@[to_dual]
/-
**isUpperSet_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_iInter {f : ι -> Set α} (hf : forall i, IsUpperSet (f i)) : IsU
pperSet (⋂ i, f i)
参数：hf : forall i, IsUpperSet (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUpperSet_sInter`：isUpperSet_sInter {S : Set (Set α)} (hf : forall s in
 S, IsUpperSet s) : IsUpperSet (⋂₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isUpperSet_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋂ (i) (j), f i j) :=
  isUpperSet_iInter fun i => isUpperSet_iInter <| hf i

@[to_dual (attr := simp)]
/-
**isUpperSet_preimage_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_preimage_ofDual_iff : IsUpperSet (ofDual ⁻¹' s) ↔ IsLowerSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUpperSet_preimage_ofDual_iff : IsUpperSet (ofDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[to_dual (attr := simp)]
/-
**isUpperSet_preimage_toDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsUpperSet (toDual ⁻¹' s) ↔
 IsLowerSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUpperSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsUpperSet (toDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[to_dual] alias ⟨_, IsUpperSet.toDual⟩ := isLowerSet_preimage_ofDual_iff
@[to_dual] alias ⟨_, IsUpperSet.ofDual⟩ := isLowerSet_preimage_toDual_iff

@[to_dual]
/-
**IsUpperSet.isLowerSet_preimage_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.isLowerSet_preimage_coe (hs : IsUpperSet s) : IsLowerSet ((↑) ⁻
¹' t : Set s) ↔ forall b in s, forall c in t, b <= c -> b in t
参数：hs : IsUpperSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma IsUpperSet.isLowerSet_preimage_coe (hs : IsUpperSet s) :
    IsLowerSet ((↑) ⁻¹' t : Set s) ↔ ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t := by aesop

@[to_dual]
/-
**IsUpperSet.sdiff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.sdiff (hs : IsUpperSet s) (ht : forall b in s, forall c in t, b
 <= c -> b in t) : IsUpperSet (s \ t)
参数：hs : IsUpperSet s；ht : forall b in s, forall c in t, b <= c -> b in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsUpperSet.sdiff (hs : IsUpperSet s) (ht : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    IsUpperSet (s \ t) :=
  fun _b _c hbc hb ↦ ⟨hs hbc hb.1, fun hc ↦ hb.2 <| ht _ hb.1 _ hc hbc⟩

@[to_dual]
/-
**IsUpperSet.sdiff_of_isLowerSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.sdiff_of_isLowerSet (hs : IsUpperSet s) (ht : IsLowerSet t) : I
sUpperSet (s \ t)
参数：hs : IsUpperSet s；ht : IsLowerSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUpperSet.sdiff`：IsUpperSet.sdiff (hs : IsUpperSet s) (ht : forall b in
 s, forall c in t, b <= c -> b in t) : IsUpperSet (s \ t)
-/
lemma IsUpperSet.sdiff_of_isLowerSet (hs : IsUpperSet s) (ht : IsLowerSet t) : IsUpperSet (s \ t) :=
  hs.sdiff <| by aesop

@[to_dual]
/-
**IsUpperSet.erase** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.erase (hs : IsUpperSet s) (has : forall b in s, b <= a -> b = a
) : IsUpperSet (s \ {a})
参数：hs : IsUpperSet s；has : forall b in s, b <= a -> b = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUpperSet.sdiff`：IsUpperSet.sdiff (hs : IsUpperSet s) (ht : forall b in
 s, forall c in t, b <= c -> b in t) : IsUpperSet (s \ t)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma IsUpperSet.erase (hs : IsUpperSet s) (has : ∀ b ∈ s, b ≤ a → b = a) : IsUpperSet (s \ {a}) :=
  hs.sdiff <| by simpa using has

end LE

section Preorder

variable [Preorder α] [Preorder β] {s : Set α} {p : α → Prop} (a : α)

/-
**isUpperSet_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsUpperSet (Set.Ici a)
参数：a : α；Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ge_trans`：ge_trans : b <= a -> c <= b -> c <= a
-/
@[to_dual] theorem isUpperSet_Ici : IsUpperSet (Ici a) := fun _ _ => ge_trans
/-
**isUpperSet_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsUpperSet (Set.Ioi a)
参数：a : α；Set.Ioi a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
@[to_dual] theorem isUpperSet_Ioi : IsUpperSet (Ioi a) := fun _ _ => flip lt_of_lt_of_le

@[to_dual]
/-
**isUpperSet_iff_Ici_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_iff_Ici_subset : IsUpperSet s ↔ forall ⦃a⦄, a in s -> Ici a sub
seteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUpperSet_iff_Ici_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ici a ⊆ s := by
  simp [IsUpperSet, subset_def, @forall_comm (_ ∈ s)]

@[to_dual] alias ⟨IsUpperSet.Ici_subset, _⟩ := isUpperSet_iff_Ici_subset

@[to_dual]
/-
**IsUpperSet.Ioi_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.Ioi_subset (h : IsUpperSet s) ⦃a⦄ (ha : a in s) : Ioi a subsete
q s
参数：h : IsUpperSet s；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `IsUpperSet.Ici_subset`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 IsUpperSet s → ∀ ⦃a : α⦄, a ∈ s → Set.Ici a ⊆ s
-/
theorem IsUpperSet.Ioi_subset (h : IsUpperSet s) ⦃a⦄ (ha : a ∈ s) : Ioi a ⊆ s :=
  Ioi_subset_Ici_self.trans <| h.Ici_subset ha
/-
**IsUpperSet.ordConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.ordConnected (h : IsUpperSet s) : s.OrdConnected
参数：h : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `IsUpperSet.Ici_subset`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 IsUpperSet s → ∀ ⦃a : α⦄, a ∈ s → Set.Ici a ⊆ s
-/
theorem IsUpperSet.ordConnected (h : IsUpperSet s) : s.OrdConnected :=
  ⟨fun _ ha _ _ => Icc_subset_Ici_self.trans <| h.Ici_subset ha⟩

-- `to_dual` cannot yet reorder arguments of arguments
@[to_dual existing]
/-
**IsLowerSet.ordConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.ordConnected (h : IsLowerSet s) : s.OrdConnected
参数：h : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `IsLowerSet.Iic_subset`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 IsLowerSet s → ∀ ⦃a : α⦄, a ∈ s → Set.Iic a ⊆ s
-/
theorem IsLowerSet.ordConnected (h : IsLowerSet s) : s.OrdConnected :=
  ⟨fun _ _ _ hb => Icc_subset_Iic_self.trans <| h.Iic_subset hb⟩

@[to_dual]
/-
**IsUpperSet.preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.preimage (hs : IsUpperSet s) {f : β -> α} (hf : Monotone f) : I
sUpperSet (f ⁻¹' s : Set β)
参数：hs : IsUpperSet s；hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsUpperSet.preimage (hs : IsUpperSet s) {f : β → α} (hf : Monotone f) :
    IsUpperSet (f ⁻¹' s : Set β) := fun _ _ h => hs <| hf h

@[to_dual]
/-
**IsUpperSet.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : IsUpperSet (f '' s : S
et β)
参数：hs : IsUpperSet s；f : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `IsUpperSet.preimage`：IsUpperSet.preimage (hs : IsUpperSet s) {f : β -> α
} (hf : Monotone f) : IsUpperSet (f ⁻¹' s : Set β)
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
-/
theorem IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : IsUpperSet (f '' s : Set β) := by
  change IsUpperSet ((f : α ≃ β) '' s)
  rw [Equiv.image_eq_preimage_symm]
  exact hs.preimage f.symm.monotone

@[to_dual]
/-
**OrderEmbedding.image_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderEmbedding.image_Ici (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) 
: e '' Ici a = Ici (e a)
参数：e : α ↪o β；he : IsUpperSet (range e)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.preimage_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Ici (e x) = Se
t.Ici x
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `IsUpperSet.Ici_subset`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 IsUpperSet s → ∀ ⦃a : α⦄, a ∈ s → Set.Ici a ⊆ s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem OrderEmbedding.image_Ici (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) :
    e '' Ici a = Ici (e a) := by
  rw [← e.preimage_Ici, image_preimage_eq_inter_range,
    inter_eq_left.2 <| he.Ici_subset (mem_range_self _)]

@[to_dual]
/-
**OrderEmbedding.image_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderEmbedding.image_Ioi (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) 
: e '' Ioi a = Ioi (e a)
参数：e : α ↪o β；he : IsUpperSet (range e)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.preimage_Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Ioi (e x) = Se
t.Ioi x
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `IsUpperSet.Ioi_subset`：IsUpperSet.Ioi_subset (h : IsUpperSet s) ⦃a⦄ (ha 
: a in s) : Ioi a subseteq s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem OrderEmbedding.image_Ioi (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) :
    e '' Ioi a = Ioi (e a) := by
  rw [← e.preimage_Ioi, image_preimage_eq_inter_range,
    inter_eq_left.2 <| he.Ioi_subset (mem_range_self _)]

@[simp]
/-
**Set.monotone_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.monotone_mem : Monotone (· in s) ↔ IsUpperSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Set.monotone_mem : Monotone (· ∈ s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
/-
**Set.antitone_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.antitone_mem : Antitone (· in s) ↔ IsLowerSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem Set.antitone_mem : Antitone (· ∈ s) ↔ IsLowerSet s :=
  forall_comm

@[simp]
/-
**isUpperSet_setOfPred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_setOfPred : IsUpperSet { a | p a } ↔ Monotone p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUpperSet_setOfPred : IsUpperSet { a | p a } ↔ Monotone p :=
  Iff.rfl

@[deprecated (since := "2026-07-09")] alias isUpperSet_setOf := isUpperSet_setOfPred

@[simp]
/-
**isLowerSet_setOfPred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLowerSet_setOfPred : IsLowerSet { a | p a } ↔ Antitone p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem isLowerSet_setOfPred : IsLowerSet { a | p a } ↔ Antitone p :=
  forall_comm

@[deprecated (since := "2026-07-09")] alias isLowerSet_setOf := isLowerSet_setOfPred

@[to_dual]
/-
**IsUpperSet.upperBounds_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.upperBounds_subset (hs : IsUpperSet s) : s.Nonempty -> upperBou
nds s subseteq s
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsUpperSet.upperBounds_subset (hs : IsUpperSet s) : s.Nonempty → upperBounds s ⊆ s :=
  fun ⟨_a, ha⟩ _b hb ↦ hs (hb ha) ha

section OrderTop

variable [OrderTop α]

@[to_dual]
/-
**IsLowerSet.top_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ in s ↔ s = univ
参数：hs : IsLowerSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun _ => hs le_top h, fun h => h.symm ▸ mem_univ _⟩

@[to_dual]
/-
**IsUpperSet.top_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ in s ↔ s.Nonempty
参数：hs : IsUpperSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_a, ha⟩ => hs le_top ha⟩

@[to_dual]
/-
**IsUpperSet.top_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.top_notMem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅
参数：hs : IsUpperSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `IsUpperSet.top_mem`：IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ in s ↔ s.
Nonempty
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
-/
theorem IsUpperSet.top_notMem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.not.trans not_nonempty_iff_eq_empty

end OrderTop

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
/-
**IsUpperSet.not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s.Nonempty -> ¬BddAbove s
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s.Nonempty → ¬BddAbove s := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_ge (hb <| hs ((hb ha).trans hc.le) ha)

@[to_dual]
/-
**not_bddAbove_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_bddAbove_Ici : ¬BddAbove (Ici a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.not_bddAbove`：IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s
.Nonempty -> ¬BddAbove s
· 使用定理 `isUpperSet_Ici`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsUpperSet
 (Set.Ici a)
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty
-/
theorem not_bddAbove_Ici : ¬BddAbove (Ici a) :=
  (isUpperSet_Ici _).not_bddAbove nonempty_Ici

@[to_dual]
/-
**not_bddAbove_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_bddAbove_Ioi : ¬BddAbove (Ioi a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.not_bddAbove`：IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s
.Nonempty -> ¬BddAbove s
· 使用定理 `isUpperSet_Ioi`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsUpperSet
 (Set.Ioi a)
· 使用定理 `Set.nonempty_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [NoMaxOrd
er α], (Set.Ioi a).Nonempty
-/
theorem not_bddAbove_Ioi : ¬BddAbove (Ioi a) :=
  (isUpperSet_Ioi _).not_bddAbove nonempty_Ioi

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α}

@[to_dual]
/-
**isUpperSet_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_iff_forall_lt : IsUpperSet s ↔ forall ⦃a b : α⦄, a < b -> a in 
s -> b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUpperSet_iff_forall_lt : IsUpperSet s ↔ ∀ ⦃a b : α⦄, a < b → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]

@[to_dual]
/-
**isUpperSet_iff_Ioi_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUpperSet_iff_Ioi_subset : IsUpperSet s ↔ forall ⦃a⦄, a in s -> Ioi a sub
seteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUpperSet_iff_Ioi_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ioi a ⊆ s := by
  simp [isUpperSet_iff_forall_lt, subset_def, @forall_comm (_ ∈ s)]

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s t : Set α}

@[to_dual]
/-
**IsUpperSet.total** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.total (hs : IsUpperSet s) (ht : IsUpperSet t) : s subseteq t ∨ 
t subseteq s
参数：hs : IsUpperSet s；ht : IsUpperSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsUpperSet.total (hs : IsUpperSet s) (ht : IsUpperSet t) : s ⊆ t ∨ t ⊆ s := by
  grind [isUpperSet_iff_forall_lt]

@[to_dual]
/-
**IsUpperSet.eq_empty_or_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.eq_empty_or_Ici [WellFoundedLT α] (h : IsUpperSet s) : s = ∅ ∨ 
exists a, s = Ici a
参数：h : IsUpperSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `WellFounded.min_le`：WellFounded.min_le (h : WellFounded ((· < ·) : β -> 
β -> Prop)) {x : β} {s : Set β} (hx : x in s) : h.min s ⟨x, hx⟩ <= x
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
-/
theorem IsUpperSet.eq_empty_or_Ici [WellFoundedLT α] (h : IsUpperSet s) :
    s = ∅ ∨ ∃ a, s = Ici a := by
  refine or_iff_not_imp_left.2 fun ha ↦ ?_
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 ha
  exact ⟨_, ext fun b ↦ ⟨wellFounded_lt.min_le, (h · <| wellFounded_lt.min_mem _ ⟨a, ha⟩)⟩⟩

@[to_dual]
/-
**IsLowerSet.eq_univ_or_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.eq_univ_or_Iio [WellFoundedLT α] (h : IsLowerSet s) : s = univ 
∨ exists a, s = Iio a
参数：h : IsLowerSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Set.compl_Iio`：compl_Iio : (Iio a)ᶜ = Ici a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUpperSet.eq_empty_or_Ici`：IsUpperSet.eq_empty_or_Ici [WellFoundedLT α]
 (h : IsUpperSet s) : s = ∅ ∨ exists a, s = Ici a
· 使用定理 `IsLowerSet.compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 s → IsUpperSet sᶜ
-/
theorem IsLowerSet.eq_univ_or_Iio [WellFoundedLT α] (h : IsLowerSet s) :
    s = univ ∨ ∃ a, s = Iio a := by
  simp_rw [← @compl_inj_iff _ s]
  simpa using h.compl.eq_empty_or_Ici

end LinearOrder

