/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Union
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Data.Set.Pairwise.Lattice

/-!
# The powerset of a finset
-/

@[expose] public section


namespace Finset

open Function Multiset

variable {α : Type*} {s t : Finset α}

/-! ### powerset -/


section Powerset

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
/-
**Finset.powerset** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：powerset (s : Finset α) : Finset (Finset α)
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as 
finsets).
-/
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

@[simp, grind =]
/-
**Finset.mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_powerset {s t : Finset α} : s in powerset t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.mk.injEq`：∀ {α : Type u_4} (val : Multiset α) (nodup : val.Nodup)
 (val_1 : Multiset α) (nodup_1 : val_1.Nodup),   ({ val := val, nodup := nodup }
 = { …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_powerset {s t : Finset α} : s ∈ powerset t ↔ s ⊆ t := by
  cases s
  simp [powerset, mem_mk, mem_pmap, mk.injEq, exists_prop, exists_eq_right,
    ← val_le_iff]

@[simp, norm_cast]
/-
**Finset.coe_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_powerset (s : Finset α) : (s.powerset : Set (Finset α)) = ((↑) : Finse
t α -> Set α) ⁻¹' (s : Set α).powerset
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_powerset (s : Finset α) :
    (s.powerset : Set (Finset α)) = ((↑) : Finset α → Set α) ⁻¹' (s : Set α).powerset := by
  ext
  simp
/-
**Finset.empty_mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_mem_powerset (s : Finset α) : ∅ in powerset s
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem empty_mem_powerset (s : Finset α) : ∅ ∈ powerset s := by simp
/-
**Finset.mem_powerset_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_powerset_self (s : Finset α) : s in powerset s
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem mem_powerset_self (s : Finset α) : s ∈ powerset s := by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.powerset_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_nonempty (s : Finset α) : s.powerset.Nonempty
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.empty_mem_powerset`：empty_mem_powerset (s : Finset α) : ∅ in powe
rset s
-/
theorem powerset_nonempty (s : Finset α) : s.powerset.Nonempty :=
  ⟨∅, empty_mem_powerset _⟩

@[simp]
/-
**Finset.powerset_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_mono {s t : Finset α} : powerset s subseteq powerset t ↔ s subset
eq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.mem_powerset_self`：mem_powerset_self (s : Finset α) : s in powers
et s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
-/
theorem powerset_mono {s t : Finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
  ⟨fun h => mem_powerset.1 <| h <| mem_powerset_self _, fun st _u h =>
    mem_powerset.2 <| Subset.trans (mem_powerset.1 h) st⟩
/-
**Finset.powerset_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_injective : Injective (powerset : Finset α -> Finset (Finset α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_eq_imp_le`：Function.Injective.of_eq_imp_le [Partia
lOrder α] {f : α -> β} (h : forall {x y}, f x = f y -> x <= y) : f.Injective
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.powerset_mono`：powerset_mono {s t : Finset α} : powerset s subset
eq powerset t ↔ s subseteq t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem powerset_injective : Injective (powerset : Finset α → Finset (Finset α)) :=
  .of_eq_imp_le (powerset_mono.1 ·.le)

@[simp]
/-
**Finset.powerset_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_inj : powerset s = powerset t ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finset.powerset_injective`：powerset_injective : Injective (powerset : Fi
nset α -> Finset (Finset α))
-/
theorem powerset_inj : powerset s = powerset t ↔ s = t :=
  powerset_injective.eq_iff

@[simp]
/-
**Finset.powerset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_empty : (∅ : Finset α).powerset = {∅}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powerset_empty : (∅ : Finset α).powerset = {∅} :=
  rfl

@[simp]
/-
**Finset.powerset_eq_singleton_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_eq_singleton_empty : s.powerset = {∅} ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.powerset_empty`：powerset_empty : (∅ : Finset α).powerset = {∅}
· 使用定理 `Finset.powerset_inj`：powerset_inj : powerset s = powerset t ↔ s = t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem powerset_eq_singleton_empty : s.powerset = {∅} ↔ s = ∅ := by
  rw [← powerset_empty, powerset_inj]
/-
**Finset.image_injOn_powerset_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_injOn_powerset_of_injOn {β : Type*} [DecidableEq β] {f : α -> β} (H 
: Set.InjOn f s) : Set.InjOn (α
参数：H : Set.InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_injOn_powerset_of_injOn {β : Type*} [DecidableEq β] {f : α → β} (H : Set.InjOn f s) :
    Set.InjOn (α := Finset α) (·.image f) s.powerset := by
  have {z a} (_ : z ⊆ s) (_ : a ∈ s) : a ∈ z ↔ f a ∈ z.image f := by grind [H.eq_iff]
  exact fun _ _ _ _ _ => by grind

/-- Variant of `Finset.image_injOn_powerset_of_injOn` for a family `S` of finsets whose
union supports an `InjOn` hypothesis, rather than the full powerset of a set. -/
/-
**Finset.injOn_image_of_biUnion_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：injOn_image_of_biUnion_injOn {β : Type*} [DecidableEq α] [DecidableEq β] {
S : Finset (Finset α)} {f : α -> β} (hf : (S.biUnion id : Set α).InjOn f) : (S :
 Set (Finset α)).InjOn (·.image f)
参数：Finset α；hf : (S.biUnion id : Set α).InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_powerset`：coe_powerset (s : Finset α) : (s.powerset : Set (Fi
nset α)) = ((↑) : Finset α -> Set α) ⁻¹' (s : Set α).powerset
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Finset.image_injOn_powerset_of_injOn`：image_injOn_powerset_of_injOn {β :
 Type*} [DecidableEq β] {f : α -> β} (H : Set.InjOn f s) : Set.InjOn (α

--- 原说明 ---
Variant of `Finset.image_injOn_powerset_of_injOn` for a family `S` of finsets wh
ose
union supports an `InjOn` hypothesis, rather than the full powerset of a set.
-/
theorem injOn_image_of_biUnion_injOn {β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset (Finset α)} {f : α → β} (hf : (S.biUnion id : Set α).InjOn f) :
    (S : Set (Finset α)).InjOn (·.image f) :=
  (image_injOn_powerset_of_injOn hf).mono (by aesop (add simp Set.subset_def))

/-- `s.biUnion id ⊆ t` iff every member of `s` is a subset of `t`, i.e. `s ⊆ t.powerset`. -/
/-
**Finset.biUnion_id_subset_iff_subset_powerset** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
形式化陈述：biUnion_id_subset_iff_subset_powerset [DecidableEq α] {s : Finset (Finset 
α)} : s.biUnion id subseteq t ↔ s subseteq t.powerset
参数：Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
`s.biUnion id ⊆ t` iff every member of `s` is a subset of `t`, i.e. `s ⊆ t.power
set`.
-/
lemma biUnion_id_subset_iff_subset_powerset [DecidableEq α] {s : Finset (Finset α)} :
    s.biUnion id ⊆ t ↔ s ⊆ t.powerset := by
  aesop (add simp subset_iff)
/-
**Finset.image_surjOn_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_surjOn_powerset {β : Type*} [DecidableEq β] {f : α -> β} : Set.SurjO
n (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_surjOn_powerset {β : Type*} [DecidableEq β] {f : α → β} :
    Set.SurjOn (α := Finset α) (·.image f) s.powerset (s.image f).powerset :=
  fun t ht => ⟨{ x ∈ s | f x ∈ t}, by grind⟩
/-
**Finset.powerset_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_image {β : Type*} [DecidableEq β] {f : α -> β} : (s.image f).powe
rset = s.powerset.image (·.image f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
-/
theorem powerset_image {β : Type*} [DecidableEq β] {f : α → β} :
    (s.image f).powerset = s.powerset.image (·.image f) :=
  ext fun a => ⟨fun _ => mem_image.mpr ⟨{ x ∈ s | f x ∈ a}, by grind⟩, by grind⟩

/-- **Number of Subsets of a Set** -/
@[simp]
/-
**Finset.card_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_powerset (s : Finset α) : card (powerset s) = 2 ^ card s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.card_pmap`：card_pmap {p : α -> Prop} (f : forall a, p a -> β) (
s H) : card (pmap f s H) = card s
· 使用定理 `Multiset.card_powerset`：card_powerset (s : Multiset α) : card (powerset 
s) = 2 ^ card s

--- 原说明 ---
**Number of Subsets of a Set**
-/
theorem card_powerset (s : Finset α) : card (powerset s) = 2 ^ card s :=
  (card_pmap _ _ _).trans (Multiset.card_powerset s.1)
/-
**Finset.notMem_of_mem_powerset_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_of_mem_powerset_of_notMem {s t : Finset α} {a : α} (ht : t in s.pow
erset) (h : a ∉ s) : a ∉ t
参数：ht : t in s.powerset；h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
-/
theorem notMem_of_mem_powerset_of_notMem {s t : Finset α} {a : α} (ht : t ∈ s.powerset)
    (h : a ∉ s) : a ∉ t := by
  apply mt _ h
  apply mem_powerset.1 ht
/-
**Finset.powerset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_insert [DecidableEq α] (s : Finset α) (a : α) : powerset (insert 
a s) = s.powerset union s.powerset.image (insert a)
参数：s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem powerset_insert [DecidableEq α] (s : Finset α) (a : α) :
    powerset (insert a s) = s.powerset ∪ s.powerset.image (insert a) := by
  ext t
  simp only [mem_powerset, mem_image, mem_union, subset_insert_iff]
  grind
/-
**Finset.pairwiseDisjoint_pair_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_pair_insert [DecidableEq α] {a : α} (ha : a ∉ s) : (s.pow
erset : Set (Finset α)).PairwiseDisjoint fun t => ({t, insert a t} : Set (Finset
 α))
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.insert_erase_invOn`：insert_erase_invOn : Set.InvOn (insert a) (fu
n s => s.erase a) {s : Finset α | a in s} {s : Finset α | a ∉ s}
-/
lemma pairwiseDisjoint_pair_insert [DecidableEq α] {a : α} (ha : a ∉ s) :
    (s.powerset : Set (Finset α)).PairwiseDisjoint fun t ↦ ({t, insert a t} : Set (Finset α)) := by
  simp_rw [Set.pairwiseDisjoint_iff, mem_coe, mem_powerset]
  rintro i hi j hj
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, or_imp, imp_self, true_and]
  refine ⟨?_, ?_, insert_erase_invOn.2.injOn (notMem_mono hi ha) (notMem_mono hj ha)⟩ <;>
    rintro rfl <;>
    cases Finset.notMem_mono ‹_› ha (Finset.mem_insert_self _ _)

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
/-
**Finset.decidableExistsOfDecidableSubsets** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableExistsOfDecidableSubsets {s : Finset α} {p : forall t subseteq s,
 Prop} [forall (t) (h : t subseteq s), Decidable (p t h)] : Decidable (exists (t
 : _) (h : t subseteq s), p t h)
参数：t；h : t subseteq s；p t h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For predicate `p` decidable on subsets, it is decidable whether `p` holds for an
y subset.
-/
instance decidableExistsOfDecidableSubsets {s : Finset α} {p : ∀ t ⊆ s, Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∃ (t : _) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∃ (t : _) (hs : t ∈ s.powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
/-
**Finset.decidableForallOfDecidableSubsets** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableForallOfDecidableSubsets {s : Finset α} {p : forall t subseteq s,
 Prop} [forall (t) (h : t subseteq s), Decidable (p t h)] : Decidable (forall (t
) (h : t subseteq s), p t h)
参数：t；h : t subseteq s；p t h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For predicate `p` decidable on subsets, it is decidable whether `p` holds for ev
ery subset.
-/
instance decidableForallOfDecidableSubsets {s : Finset α} {p : ∀ t ⊆ s, Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∀ (t) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
/-
**Finset.decidableExistsOfDecidableSubsets'** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableExistsOfDecidableSubsets' {s : Finset α} {p : Finset α -> Prop} [
forall t, Decidable (p t)] : Decidable (exists t subseteq s, p t)
参数：p t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For predicate `p` decidable on subsets, it is decidable whether `p` holds for an
y subset.
-/
instance decidableExistsOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    [∀ t, Decidable (p t)] : Decidable (∃ t ⊆ s, p t) :=
  decidable_of_iff (∃ (t : _) (_h : t ⊆ s), p t) <| by simp

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
/-
**Finset.decidableForallOfDecidableSubsets'** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableForallOfDecidableSubsets' {s : Finset α} {p : Finset α -> Prop} [
forall t, Decidable (p t)] : Decidable (forall t subseteq s, p t)
参数：p t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For predicate `p` decidable on subsets, it is decidable whether `p` holds for ev
ery subset.
-/
instance decidableForallOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    [∀ t, Decidable (p t)] : Decidable (∀ t ⊆ s, p t) :=
  decidable_of_iff (∀ (t : _) (_h : t ⊆ s), p t) <| by simp

end Powerset

section SSubsets

variable [DecidableEq α]

/-- For `s` a finset, `s.ssubsets` is the finset comprising strict subsets of `s`. -/
/-
**Finset.ssubsets** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：ssubsets (s : Finset α) : Finset (Finset α)
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `s` a finset, `s.ssubsets` is the finset comprising strict subsets of `s`.
-/
def ssubsets (s : Finset α) : Finset (Finset α) :=
  erase (powerset s) s

@[simp, grind =]
/-
**Finset.mem_ssubsets** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_ssubsets {s t : Finset α} : t in s.ssubsets ↔ t ⊂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.ssubsets.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Finse
t α), s.ssubsets = s.powerset.erase s
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.ssubset_iff_subset_ne`：ssubset_iff_subset_ne {s t : Finset α} : s
 ⊂ t ↔ s subseteq t ∧ s != t
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ssubsets {s t : Finset α} : t ∈ s.ssubsets ↔ t ⊂ s := by
  rw [ssubsets, mem_erase, mem_powerset, ssubset_iff_subset_ne, and_comm]
/-
**Finset.empty_mem_ssubsets** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_mem_ssubsets {s : Finset α} (h : s.Nonempty) : ∅ in s.ssubsets
参数：h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_ssubsets`：mem_ssubsets {s t : Finset α} : t in s.ssubsets ↔ t
 ⊂ s
· 使用定理 `Finset.ssubset_iff_subset_ne`：ssubset_iff_subset_ne {s t : Finset α} : s
 ⊂ t ↔ s subseteq t ∧ s != t
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
-/
theorem empty_mem_ssubsets {s : Finset α} (h : s.Nonempty) : ∅ ∈ s.ssubsets := by
  rw [mem_ssubsets, ssubset_iff_subset_ne]
  exact ⟨empty_subset s, h.ne_empty.symm⟩

/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for any ssubset. -/
/-
**Finset.decidableExistsOfDecidableSSubsets** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：decidableExistsOfDecidableSSubsets {s : Finset α} {p : forall t ⊂ s, Prop}
 [forall t h, Decidable (p t h)] : Decidable (exists t h, p t h)
参数：p t h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for a
ny ssubset.
-/
def decidableExistsOfDecidableSSubsets {s : Finset α} {p : ∀ t ⊂ s, Prop}
    [∀ t h, Decidable (p t h)] : Decidable (∃ t h, p t h) :=
  decidable_of_iff (∃ (t : _) (hs : t ∈ s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩

/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for every ssubset. -/
/-
**Finset.decidableForallOfDecidableSSubsets** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：decidableForallOfDecidableSSubsets {s : Finset α} {p : forall t ⊂ s, Prop}
 [forall t h, Decidable (p t h)] : Decidable (forall t h, p t h)
参数：p t h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for e
very ssubset.
-/
def decidableForallOfDecidableSSubsets {s : Finset α} {p : ∀ t ⊂ s, Prop}
    [∀ t h, Decidable (p t h)] : Decidable (∀ t h, p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩

/-- A version of `Finset.decidableExistsOfDecidableSSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
/-
**Finset.decidableExistsOfDecidableSSubsets'** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：decidableExistsOfDecidableSSubsets' {s : Finset α} {p : Finset α -> Prop} 
(hu : forall t ⊂ s, Decidable (p t)) : Decidable (exists (t : _) (_h : t ⊂ s), p
 t)
参数：hu : forall t ⊂ s, Decidable (p t)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Finset.decidableExistsOfDecidableSSubsets` with a non-dependent `p
`.
Typeclass inference cannot find `hu` here, so this is not an instance.
-/
def decidableExistsOfDecidableSSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ t ⊂ s, Decidable (p t)) : Decidable (∃ (t : _) (_h : t ⊂ s), p t) :=
  @Finset.decidableExistsOfDecidableSSubsets _ _ _ _ hu

/-- A version of `Finset.decidableForallOfDecidableSSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
/-
**Finset.decidableForallOfDecidableSSubsets'** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：decidableForallOfDecidableSSubsets' {s : Finset α} {p : Finset α -> Prop} 
(hu : forall t ⊂ s, Decidable (p t)) : Decidable (forall t ⊂ s, p t)
参数：hu : forall t ⊂ s, Decidable (p t)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Finset.decidableForallOfDecidableSSubsets` with a non-dependent `p
`.
Typeclass inference cannot find `hu` here, so this is not an instance.
-/
def decidableForallOfDecidableSSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ t ⊂ s, Decidable (p t)) : Decidable (∀ t ⊂ s, p t) :=
  @Finset.decidableForallOfDecidableSSubsets _ _ _ _ hu

end SSubsets

section powersetCard
variable {n} {s t : Finset α}

/-- Given an integer `n` and a finset `s`, then `powersetCard n s` is the finset of subsets of `s`
of cardinality `n`. -/
/-
**Finset.powersetCard** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：powersetCard (n : Nat) (s : Finset α) : Finset (Finset α)
参数：n : Nat；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an integer `n` and a finset `s`, then `powersetCard n s` is the finset of 
subsets of `s`
of cardinality `n`.
-/
def powersetCard (n : ℕ) (s : Finset α) : Finset (Finset α) :=
  ⟨((s.1.powersetCard n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetCard.1 h).1 s.2,
    s.2.powersetCard.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
/-
**Finset.mem_powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ Finset.powersetCard n t ↔ s
 ⊆ t ∧ s.card = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.mk.injEq`：∀ {α : Type u_4} (val : Multiset α) (nodup : val.Nodup)
 (val_1 : Multiset α) (nodup_1 : val_1.Nodup),   ({ val := val, nodup := nodup }
 = { …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp, grind =] lemma mem_powersetCard : s ∈ powersetCard n t ↔ s ⊆ t ∧ card s = n := by
  cases s; simp [powersetCard, val_le_iff.symm]

@[simp]
/-
**Finset.powersetCard_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powersetCard_mono {n} {s t : Finset α} (h : s subseteq t) : powersetCard n
 s subseteq powersetCard n t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem powersetCard_mono {n} {s t : Finset α} (h : s ⊆ t) : powersetCard n s ⊆ powersetCard n t :=
  fun _u h' => mem_powersetCard.2 <|
    And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powersetCard.1 h')

/-- **Formula for the Number of Combinations** -/
@[simp]
/-
**Finset.card_powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_powersetCard (n : Nat) (s : Finset α) : card (powersetCard n s) = Nat
.choose (card s) n
参数：n : Nat；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.card_pmap`：card_pmap {p : α -> Prop} (f : forall a, p a -> β) (
s H) : card (pmap f s H) = card s
· 使用定理 `Multiset.card_powersetCard`：card_powersetCard (n : Nat) (s : Multiset α)
 : card (powersetCard n s) = Nat.choose (card s) n

--- 原说明 ---
**Formula for the Number of Combinations**
-/
theorem card_powersetCard (n : ℕ) (s : Finset α) :
    card (powersetCard n s) = Nat.choose (card s) n :=
  (card_pmap _ _ _).trans (Multiset.card_powersetCard n s.1)

/-- The `n`-element subsets of `t` containing `s` are exactly the `(n - s.card)`-element
subsets of `t \ s`, unioned with `s`. -/
/-
**Finset.filter_powersetCard_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_powersetCard_subset [DecidableEq α] (s t : Finset α) (n : Nat) (hst
 : s subseteq t) (hsn : #s <= n) : (t.powersetCard n).filter (s subseteq ·) = ((
t \ s).powersetCard (n - #s)).image (· union s)
参数：s t : Finset α；n : Nat；hst : s subseteq t；hsn : #s <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq 
u) (d : Disjoint u t) : Disjoint s t
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂

--- 原说明 ---
The `n`-element subsets of `t` containing `s` are exactly the `(n - s.card)`-ele
ment
subsets of `t \ s`, unioned with `s`.
-/
theorem filter_powersetCard_subset [DecidableEq α] (s t : Finset α) (n : ℕ)
    (hst : s ⊆ t) (hsn : #s ≤ n) :
    (t.powersetCard n).filter (s ⊆ ·) = ((t \ s).powersetCard (n - #s)).image (· ∪ s) := by
  ext x
  simp only [mem_filter, mem_powersetCard, mem_image]
  constructor
  · intro ⟨⟨hxt, hxn⟩, hsx⟩
    exact ⟨x \ s, ⟨fun y hy => mem_sdiff.mpr ⟨hxt (mem_sdiff.mp hy).1, (mem_sdiff.mp hy).2⟩,
           by rw [card_sdiff_of_subset hsx, hxn]⟩, sdiff_union_of_subset hsx⟩
  · rintro ⟨y, ⟨hyt, hyn⟩, rfl⟩
    refine ⟨⟨union_subset (hyt.trans sdiff_subset) hst, ?_⟩, subset_union_right⟩
    rw [card_union_of_disjoint (disjoint_of_subset_left hyt disjoint_sdiff_self_left), hyn]
    lia

/-- The number of `n`-element subsets of `t` containing `s` equals
`Nat.choose (#t - #s) (n - #s)`. -/
/-
**Finset.card_filter_powersetCard_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_filter_powersetCard_subset [DecidableEq α] (s t : Finset α) (n : Nat)
 (hst : s subseteq t) (hsn : #s <= n) : #((t.powersetCard n).filter (s subseteq 
·)) = Nat.choose (#t - #s) (n - #s)
参数：s t : Finset α；n : Nat；hst : s subseteq t；hsn : #s <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.union_sdiff_cancel_right`：union_sdiff_cancel_right (h : Disjoint 
s t) : (s union t) \ t = s
· 使用定理 `Finset.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq 
u) (d : Disjoint u t) : Disjoint s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_powersetCard_subset`：filter_powersetCard_subset [Decidable
Eq α] (s t : Finset α) (n : Nat) (hst : s subseteq t) (hsn : #s <= n) : (t.power
setCard n).filter (s su…
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Finset.card_powersetCard`：card_powersetCard (n : Nat) (s : Finset α) : c
ard (powersetCard n s) = Nat.choose (card s) n
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The number of `n`-element subsets of `t` containing `s` equals
`Nat.choose (#t - #s) (n - #s)`.
-/
lemma card_filter_powersetCard_subset [DecidableEq α] (s t : Finset α) (n : ℕ)
    (hst : s ⊆ t) (hsn : #s ≤ n) :
    #((t.powersetCard n).filter (s ⊆ ·)) = Nat.choose (#t - #s) (n - #s) := by
  have hinj : Set.InjOn (· ∪ s) ↑((t \ s).powersetCard (n - #s)) := fun a ha b hb hab =>
    (union_sdiff_cancel_right
      (disjoint_of_subset_left (mem_powersetCard.mp ha).1 disjoint_sdiff_self_left)).symm.trans
    ((congrArg (· \ s) hab).trans
      (union_sdiff_cancel_right
        (disjoint_of_subset_left (mem_powersetCard.mp hb).1 disjoint_sdiff_self_left)))
  simp only [filter_powersetCard_subset s t n hst hsn, card_image_of_injOn hinj,
             card_powersetCard, card_sdiff_of_subset hst]

@[simp]
/-
**Finset.powersetCard_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powersetCard_zero (s : Finset α) : s.powersetCard 0 = {∅}
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powersetCard_zero (s : Finset α) : s.powersetCard 0 = {∅} := by
  grind
/-
**Finset.powersetCard_empty_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：powersetCard_empty_subsingleton (n : Nat) : (powersetCard n (∅ : Finset α)
 : Set <| Finset α).Subsingleton
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma powersetCard_empty_subsingleton (n : ℕ) :
    (powersetCard n (∅ : Finset α) : Set <| Finset α).Subsingleton := by
  simp [Set.Subsingleton, subset_empty]

@[simp]
/-
**Finset.map_val_val_powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_val_val_powersetCard (s : Finset α) (i : Nat) : (s.powersetCard i).val
.map Finset.val = s.1.powersetCard i
参数：s : Finset α；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_pmap`：map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, 
p a -> β) (s) : forall H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H
· 使用定理 `Multiset.pmap_eq_map`：pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Mult
iset α) : forall H, @pmap _ _ p (fun a _ => f a) s H = map f s
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_val_val_powersetCard (s : Finset α) (i : ℕ) :
    (s.powersetCard i).val.map Finset.val = s.1.powersetCard i := by
  simp [Finset.powersetCard, map_pmap, pmap_eq_map, map_id']
/-
**Finset.powersetCard_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powersetCard_one (s : Finset α) : s.powersetCard 1 = s.map ⟨_, Finset.sing
leton_injective⟩
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
· 使用定理 `Multiset.map_injective`：map_injective {f : α -> β} (hf : Function.Inject
ive f) : Function.Injective (Multiset.map f)
· 使用定理 `Finset.val_injective`：val_injective : Injective (val : Finset α -> Multi
set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_val_val_powersetCard`：map_val_val_powersetCard (s : Finset α)
 (i : Nat) : (s.powersetCard i).val.map Finset.val = s.1.powersetCard i
· 使用定理 `Multiset.powersetCard_one`：powersetCard_one (s : Multiset α) : powersetC
ard 1 s = s.map singleton
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powersetCard_one (s : Finset α) :
    s.powersetCard 1 = s.map ⟨_, Finset.singleton_injective⟩ :=
  eq_of_veq <| Multiset.map_injective val_injective <| by simp [Multiset.powersetCard_one]

@[simp]
/-
**Finset.powersetCard_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：powersetCard_eq_empty : powersetCard n s = ∅ ↔ s.card < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_powersetCard`：card_powersetCard (n : Nat) (s : Finset α) : c
ard (powersetCard n s) = Nat.choose (card s) n
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
-/
lemma powersetCard_eq_empty : powersetCard n s = ∅ ↔ s.card < n := by
  refine ⟨?_, fun h ↦ card_eq_zero.1 <| by rw [card_powersetCard, Nat.choose_eq_zero_of_lt h]⟩
  contrapose!
  exact fun h ↦ (exists_subset_card_eq h).imp <| by simp
/-
**Finset.powersetCard_card_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (s : Finset α), 0 < n → Finset.powersetCard (s.ca
rd + n) s = ∅
参数：s : Finset α；s.card + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma powersetCard_card_add (s : Finset α) (hn : 0 < n) :
    s.powersetCard (s.card + n) = ∅ := by simpa
/-
**Finset.powersetCard_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powersetCard_eq_filter {n} {s : Finset α} : powersetCard n s = (powerset s
).filter fun x => x.card = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem powersetCard_eq_filter {n} {s : Finset α} :
    powersetCard n s = (powerset s).filter fun x => x.card = n := by
  ext
  simp [mem_powersetCard]
/-
**Finset.powersetCard_succ_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powersetCard_succ_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s
) (n : Nat) : powersetCard n.succ (insert x s) = powersetCard n.succ s union (po
wersetCard n s).image (insert x)
参数：h : x ∉ s；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.powersetCard_eq_filter`：powersetCard_eq_filter {n} {s : Finset α}
 : powersetCard n s = (powerset s).filter fun x => x.card = n
· 使用定理 `Finset.powerset_insert`：powerset_insert [DecidableEq α] (s : Finset α) (
a : α) : powerset (insert a s) = s.powerset union s.powerset.image (insert a)
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem powersetCard_succ_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (n : ℕ) :
    powersetCard n.succ (insert x s) =
    powersetCard n.succ s ∪ (powersetCard n s).image (insert x) := by
  rw [powersetCard_eq_filter, powerset_insert, filter_union, ← powersetCard_eq_filter]
  grind

@[simp]
/-
**Finset.powersetCard_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：powersetCard_nonempty : (powersetCard n s).Nonempty ↔ n <= s.card
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma powersetCard_nonempty : (powersetCard n s).Nonempty ↔ n ≤ s.card := by
  aesop (add simp [Finset.Nonempty, exists_subset_card_eq, card_le_card])

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, powersetCard_nonempty_of_le⟩ := powersetCard_nonempty

@[simp]
/-
**Finset.powersetCard_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powersetCard_self (s : Finset α) : powersetCard s.card s = {s}
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem powersetCard_self (s : Finset α) : powersetCard s.card s = {s} := by
  ext
  rw [mem_powersetCard, mem_singleton]
  constructor
  · exact fun ⟨hs, hc⟩ => eq_of_subset_of_card_le hs hc.ge
  · rintro rfl
    simp
/-
**Finset.pairwise_disjoint_powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwise_disjoint_powersetCard (s : Finset α) : Pairwise fun i j => Disjoi
nt (s.powersetCard i) (s.powersetCard j)
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
-/
theorem pairwise_disjoint_powersetCard (s : Finset α) :
    Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j) := fun _i _j hij =>
  Finset.disjoint_left.mpr fun _x hi hj =>
    hij <| (mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.powerset_card_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_card_disjiUnion (s : Finset α) : Finset.powerset s = (range (s.ca
rd + 1)).disjiUnion (fun i => powersetCard i s) (s.pairwise_disjoint_powersetCar
d.set_pairwise _)
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
· 使用定理 `Finset.pairwise_disjoint_powersetCard`：pairwise_disjoint_powersetCard (s
 : Finset α) : Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_disjiUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t
 : α → Finset β} {b : β} {h : (↑s).PairwiseDisjoint t},   b ∈ s.disjiUnion t h ↔
 ∃ a ∈ s, b…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem powerset_card_disjiUnion (s : Finset α) :
    Finset.powerset s =
      (range (s.card + 1)).disjiUnion (fun i => powersetCard i s)
        (s.pairwise_disjoint_powersetCard.set_pairwise _) := by
  refine ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [mem_disjiUnion]
    exact
      ⟨a.card, mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp ha))),
        mem_powersetCard.mpr ⟨mem_powerset.mp ha, rfl⟩⟩
  · rcases mem_disjiUnion.mp ha with ⟨i, _hi, ha⟩
    exact mem_powerset.mpr (mem_powersetCard.mp ha).1

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.powerset_card_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powerset_card_biUnion [DecidableEq (Finset α)] (s : Finset α) : Finset.pow
erset s = (range (s.card + 1)).biUnion fun i => powersetCard i s
参数：Finset α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
· 使用定理 `Finset.pairwise_disjoint_powersetCard`：pairwise_disjoint_powersetCard (s
 : Finset α) : Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f
· 使用定理 `Finset.powerset_card_disjiUnion`：powerset_card_disjiUnion (s : Finset α)
 : Finset.powerset s = (range (s.card + 1)).disjiUnion (fun i => powersetCard i 
s) (s.pairwise_disjoi…
-/
theorem powerset_card_biUnion [DecidableEq (Finset α)] (s : Finset α) :
    Finset.powerset s = (range (s.card + 1)).biUnion fun i => powersetCard i s := by
  simpa only [disjiUnion_eq_biUnion] using powerset_card_disjiUnion s
/-
**Finset.powersetCard_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powersetCard_sup [DecidableEq α] (u : Finset α) (n : Nat) (hn : n < u.card
) : (powersetCard n.succ u).sup id = u
参数：u : Finset α；n : Nat；hn : n < u.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_biUnion`：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset 
α) (t : α -> Finset β) : s.sup t = s.biUnion t
· 使用定理 `Finset.subset_iff`：subset_iff {s₁ s₂ : Finset α} : s₁ subseteq s₂ ↔ fora
ll ⦃x⦄, x in s₁ -> x in s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.powersetCard_nonempty`：powersetCard_nonempty : (powersetCard n s)
.Nonempty ↔ n <= s.card
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Finset.pred_card_le_card_erase`：pred_card_le_card_erase : #s - 1 <= #(s.
erase a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.powersetCard_succ_insert`：powersetCard_succ_insert [DecidableEq α
] {x : α} {s : Finset α} (h : x ∉ s) (n : Nat) : powersetCard n.succ (insert x s
) = powersetCard n.su…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem powersetCard_sup [DecidableEq α] (u : Finset α) (n : ℕ) (hn : n < u.card) :
    (powersetCard n.succ u).sup id = u := by
  apply le_antisymm
  · simp_rw [Finset.sup_le_iff, mem_powersetCard]
    rintro x ⟨h, -⟩
    exact h
  · rw [sup_eq_biUnion, subset_iff]
    intro x hx
    simp only [mem_biUnion, id]
    obtain ⟨t, ht⟩ : ∃ t, t ∈ powersetCard n (u.erase x) := powersetCard_nonempty.2
      (le_trans (Nat.le_sub_one_of_lt hn) pred_card_le_card_erase)
    refine ⟨insert x t, ?_, mem_insert_self _ _⟩
    rw [← insert_erase hx, powersetCard_succ_insert (notMem_erase _ _)]
    exact mem_union_right _ (mem_image_of_mem _ ht)

/-- The union of all `r`-element subsets of `s` is `s`, provided `1 ≤ r ≤ #s`. -/
/-
**Finset.powersetCard_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：powersetCard_biUnion [DecidableEq α] {r : Nat} (hr : r != 0) (hrs : r <= #
s) : (s.powersetCard r).biUnion id = s
参数：hr : r != 0；hrs : r <= #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_eq_biUnion`：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset 
α) (t : α -> Finset β) : s.sup t = s.biUnion t
· 使用定理 `Finset.powersetCard_sup`：powersetCard_sup [DecidableEq α] (u : Finset α)
 (n : Nat) (hn : n < u.card) : (powersetCard n.succ u).sup id = u

--- 原说明 ---
The union of all `r`-element subsets of `s` is `s`, provided `1 ≤ r ≤ #s`.
-/
lemma powersetCard_biUnion [DecidableEq α] {r : ℕ} (hr : r ≠ 0) (hrs : r ≤ #s) :
    (s.powersetCard r).biUnion id = s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [← sup_eq_biUnion]
  exact powersetCard_sup _ _ hrs

/-- If two finsets of equal cardinality have the same `r`-element subsets for some `1 ≤ r ≤ #a`,
they are equal. -/
/-
**Finset.eq_of_powersetCard_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：eq_of_powersetCard_eq {a b : Finset α} {r : Nat} (hab : #a = #b) (hr₀ : r 
!= 0) (hra : r <= #a) (h : a.powersetCard r = b.powersetCard r) : a = b
参数：hab : #a = #b；hr₀ : r != 0；hra : r <= #a；h : a.powersetCard r = b.powersetCar
d r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.powersetCard_biUnion`：powersetCard_biUnion [DecidableEq α] {r : N
at} (hr : r != 0) (hrs : r <= #s) : (s.powersetCard r).biUnion id = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If two finsets of equal cardinality have the same `r`-element subsets for some `
1 ≤ r ≤ #a`,
they are equal.
-/
lemma eq_of_powersetCard_eq {a b : Finset α} {r : ℕ}
    (hab : #a = #b) (hr₀ : r ≠ 0) (hra : r ≤ #a)
    (h : a.powersetCard r = b.powersetCard r) : a = b := by
  classical
  simpa [powersetCard_biUnion hr₀, ← hab, hra] using congr(($h).biUnion id)

/-- For `1 ≤ r ≤ q`, the map `powersetCard r` is injective on the finsets of cardinality `q`. -/
/-
**Finset.powersetCard_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {q r : ℕ}, r ≠ 0 → r ≤ q → Set.InjOn (fun a => Finset.pow
ersetCard r a) {a | a.card = q}
参数：fun a => Finset.powersetCard r a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.eq_of_powersetCard_eq`：eq_of_powersetCard_eq {a b : Finset α} {r 
: Nat} (hab : #a = #b) (hr₀ : r != 0) (hra : r <= #a) (h : a.powersetCard r = b.
powersetCard r) : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
For `1 ≤ r ≤ q`, the map `powersetCard r` is injective on the finsets of cardina
lity `q`.
-/
lemma powersetCard_injOn {q r : ℕ} (hr₀ : r ≠ 0) (hrq : r ≤ q) :
    Set.InjOn (fun a ↦ a.powersetCard r) {a : Finset α | #a = q}
  | _, rfl, _, hbq, h => eq_of_powersetCard_eq hbq.symm hr₀ hrq h
/-
**Finset.powersetCard_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：powersetCard_map {β : Type*} (f : α ↪ β) (n : Nat) (s : Finset α) : powers
etCard n (s.map f) = (powersetCard n s).map (mapEmbedding f).toEmbedding
参数：f : α ↪ β；n : Nat；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem powersetCard_map {β : Type*} (f : α ↪ β) (n : ℕ) (s : Finset α) :
    powersetCard n (s.map f) = (powersetCard n s).map (mapEmbedding f).toEmbedding :=
  ext fun t => by
    simp only [mem_powersetCard, mem_map]
    constructor
    · classical
      intro h
      have : map f (filter (fun x => (f x ∈ t)) s) = t := by grind
      refine ⟨_, ?_, this⟩
      rw [← card_map f, this, h.2]; simp
    · rintro ⟨a, ⟨has, rfl⟩, rfl⟩
      simp [has]

end powersetCard

end Finset

