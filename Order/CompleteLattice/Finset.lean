/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Set.Lattice.Image

/-!
# Lattice operations on finsets

This file is concerned with how big lattice or set operations behave when indexed by a finset.

See also `Mathlib/Data/Finset/Lattice/Fold.lean`, which is concerned with folding binary lattice
operations over a finset.
-/

public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

section Lattice

variable {ι' : Sort*} [CompleteLattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `iSup_eq_iSup_finset'` for a version
that works for `ι : Sort*`. -/
@[to_dual
/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `iInf_eq_iInf_finset'` for a version
that works for `ι : Sort*`. -/]
/-
**iSup_eq_iSup_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_iSup_finset (s : ι -> α) : ⨆ i, s i = ⨆ t : Finset ι, ⨆ i in t, s 
i
参数：s : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_eq_iSup_finset (s : ι → α) : ⨆ i, s i = ⨆ t : Finset ι, ⨆ i ∈ t, s i := by
  refine le_antisymm ?_ ?_
  · exact iSup_le fun b => le_iSup_of_le {b} <| le_iSup_of_le b <| le_iSup_of_le (by simp) <| le_rfl
  · exact iSup_le fun t => iSup_le fun b => iSup_le fun _ => le_iSup _ _

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `iSup_eq_iSup_finset` for a version
that assumes `ι : Type*` but has no `PLift`s. -/
@[to_dual
/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `iInf_eq_iInf_finset` for a version
that assumes `ι : Type*` but has no `PLift`s. -/]
/-
**iSup_eq_iSup_finset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_iSup_finset' (s : ι' -> α) : ⨆ i, s i = ⨆ t : Finset (PLift ι'), ⨆
 i in t, s (PLift.down i)
参数：s : ι' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_eq_iSup_finset`：iSup_eq_iSup_finset (s : ι -> α) : ⨆ i, s i = ⨆ t :
 Finset ι, ⨆ i in t, s i
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem iSup_eq_iSup_finset' (s : ι' → α) :
    ⨆ i, s i = ⨆ t : Finset (PLift ι'), ⨆ i ∈ t, s (PLift.down i) := by
  rw [← iSup_eq_iSup_finset, ← Equiv.plift.surjective.iSup_comp]; rfl

end Lattice

namespace Set

variable {ι' : Sort*}

/-- Union of an indexed family of sets `s : ι → Set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `iUnion_eq_iUnion_finset'` for
a version that works for `ι : Sort*`. -/
/-
**Set.iUnion_eq_iUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_iUnion_finset (s : ι -> Set α) : ⋃ i, s i = ⋃ t : Finset ι, ⋃ i 
in t, s i
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_iSup_finset`：iSup_eq_iSup_finset (s : ι -> α) : ⨆ i, s i = ⨆ t :
 Finset ι, ⨆ i in t, s i

--- 原说明 ---
Union of an indexed family of sets `s : ι → Set α` is equal to the union of the 
unions
of finite subfamilies. This version assumes `ι : Type*`. See also `iUnion_eq_iUn
ion_finset'` for
a version that works for `ι : Sort*`.
-/
theorem iUnion_eq_iUnion_finset (s : ι → Set α) : ⋃ i, s i = ⋃ t : Finset ι, ⋃ i ∈ t, s i :=
  iSup_eq_iSup_finset s

/-- Union of an indexed family of sets `s : ι → Set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `iUnion_eq_iUnion_finset` for
a version that assumes `ι : Type*` but avoids `PLift`s in the right-hand side. -/
/-
**Set.iUnion_eq_iUnion_finset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_eq_iUnion_finset' (s : ι' -> Set α) : ⋃ i, s i = ⋃ t : Finset (PLif
t ι'), ⋃ i in t, s (PLift.down i)
参数：s : ι' -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_iSup_finset'`：iSup_eq_iSup_finset' (s : ι' -> α) : ⨆ i, s i = ⨆ 
t : Finset (PLift ι'), ⨆ i in t, s (PLift.down i)

--- 原说明 ---
Union of an indexed family of sets `s : ι → Set α` is equal to the union of the 
unions
of finite subfamilies. This version works for `ι : Sort*`. See also `iUnion_eq_i
Union_finset` for
a version that assumes `ι : Type*` but avoids `PLift`s in the right-hand side.
-/
theorem iUnion_eq_iUnion_finset' (s : ι' → Set α) :
    ⋃ i, s i = ⋃ t : Finset (PLift ι'), ⋃ i ∈ t, s (PLift.down i) :=
  iSup_eq_iSup_finset' s

/-- Intersection of an indexed family of sets `s : ι → Set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`iInter_eq_iInter_finset'` for a version that works for `ι : Sort*`. -/
/-
**Set.iInter_eq_iInter_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_eq_iInter_finset (s : ι -> Set α) : ⋂ i, s i = ⋂ t : Finset ι, ⋂ i 
in t, s i
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_eq_iInf_finset`：∀ {α : Type u_2} {ι : Type u_5} [inst : CompleteLat
tice α] (s : ι → α), ⨅ i, s i = ⨅ t, ⨅ i ∈ t, s i

--- 原说明 ---
Intersection of an indexed family of sets `s : ι → Set α` is equal to the inters
ection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`iInter_eq_iInter_finset'` for a version that works for `ι : Sort*`.
-/
theorem iInter_eq_iInter_finset (s : ι → Set α) : ⋂ i, s i = ⋂ t : Finset ι, ⋂ i ∈ t, s i :=
  iInf_eq_iInf_finset s

/-- Intersection of an indexed family of sets `s : ι → Set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`iInter_eq_iInter_finset` for a version that assumes `ι : Type*` but avoids `PLift`s in the
right-hand side. -/
/-
**Set.iInter_eq_iInter_finset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_eq_iInter_finset' (s : ι' -> Set α) : ⋂ i, s i = ⋂ t : Finset (PLif
t ι'), ⋂ i in t, s (PLift.down i)
参数：s : ι' -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_eq_iInf_finset'`：∀ {α : Type u_2} {ι' : Sort u_7} [inst : CompleteL
attice α] (s : ι' → α), ⨅ i, s i = ⨅ t, ⨅ i ∈ t, s i.down

--- 原说明 ---
Intersection of an indexed family of sets `s : ι → Set α` is equal to the inters
ection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See als
o
`iInter_eq_iInter_finset` for a version that assumes `ι : Type*` but avoids `PLi
ft`s in the
right-hand side.
-/
theorem iInter_eq_iInter_finset' (s : ι' → Set α) :
    ⋂ i, s i = ⋂ t : Finset (PLift ι'), ⋂ i ∈ t, s (PLift.down i) :=
  iInf_eq_iInf_finset' s
/-
**Set.iUnion_finset_eq_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_finset_eq_set (s : Set ι) : ⋃ s' : Finset s, Subtype.val '' (s' : S
et s) = s
参数：s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_finset_eq_set (s : Set ι) :
    ⋃ s' : Finset s, Subtype.val '' (s' : Set s) = s := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, Subtype.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun ⟨_, hx, _⟩ ↦ hx, fun hx ↦ ⟨{⟨x, hx⟩}, hx, by simp⟩⟩

end Set

namespace Finset

section minimal

variable [DecidableEq α] {P : Finset α → Prop} {s : Finset α}

/-
**Finset.maximal_iff_forall_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：maximal_iff_forall_insert (hP : forall ⦃s t⦄, P t -> s subseteq t -> P s) 
: Maximal P s ↔ P s ∧ forall x ∉ s, ¬ P (insert x s)
参数：hP : forall ⦃s t⦄, P t -> s subseteq t -> P s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Finset.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : 
insert a s subseteq t
-/
theorem maximal_iff_forall_insert (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) :
    Maximal P s ↔ P s ∧ ∀ x ∉ s, ¬ P (insert x s) := by
  simp only [Maximal, and_congr_right_iff]
  exact fun _ ↦ ⟨fun h x hxs hx ↦ hxs <| h hx (subset_insert _ _) (mem_insert_self x s),
    fun h t ht hst x hxt ↦ by_contra fun hxs ↦ h x hxs (hP ht (insert_subset hxt hst))⟩
/-
**Finset.minimal_iff_forall_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：minimal_iff_forall_erase (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s) :
 Minimal P s ↔ P s ∧ forall x in s, ¬ P (s.erase x) where mp h
参数：hP : forall ⦃s t⦄, P t -> t subseteq s -> P s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用引理 `Minimal.le_of_le`：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y
 <= x) : x <= y
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.subset_erase`：subset_erase {a : α} {s t : Finset α} : s subseteq 
t.erase a ↔ s subseteq t ∧ a ∉ s
-/
theorem minimal_iff_forall_erase (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) :
    Minimal P s ↔ P s ∧ ∀ x ∈ s, ¬ P (s.erase x) where
  mp h := ⟨h.prop, fun x hxs hx ↦ by simpa using h.le_of_le hx (erase_subset _ _) hxs⟩
  mpr h := ⟨h.1, fun t ht hts x hxs ↦ by_contra fun hxt ↦
    h.2 x hxs <| hP ht (subset_erase.2 ⟨hts, hxt⟩)⟩

@[deprecated (since := "2026-06-03")]
alias minimal_iff_forall_diff_singleton := minimal_iff_forall_erase

end minimal

/-! ### Interaction with big lattice/set operations -/

section Lattice

@[to_dual]
/-
**Finset.iSup_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iSup_coe [SupSet β] (f : α -> β) (s : Finset α) : ⨆ x in (↑s : Set α), f x
 = ⨆ x in s, f x
参数：f : α -> β；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup_coe [SupSet β] (f : α → β) (s : Finset α) : ⨆ x ∈ (↑s : Set α), f x = ⨆ x ∈ s, f x :=
  rfl

variable [CompleteLattice β]

@[to_dual]
/-
**Finset.iSup_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iSup_singleton (a : α) (s : α -> β) : ⨆ x in ({a} : Finset α), s x = s a
参数：a : α；s : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_singleton (a : α) (s : α → β) : ⨆ x ∈ ({a} : Finset α), s x = s a := by simp

@[to_dual]
/-
**Finset.iSup_option_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iSup_option_toFinset (o : Option α) (f : α -> β) : ⨆ x in o.toFinset, f x 
= ⨆ x in o, f x
参数：o : Option α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_option_toFinset (o : Option α) (f : α → β) : ⨆ x ∈ o.toFinset, f x = ⨆ x ∈ o, f x := by
  simp

variable [DecidableEq α]

@[to_dual]
/-
**Finset.iSup_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iSup_union {f : α -> β} {s t : Finset α} : ⨆ x in s union t, f x = (⨆ x in
 s, f x) ⊔ ⨆ x in t, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_union`：iSup_union {f : β -> α} {s t : Set β} : ⨆ x in s union t, f 
x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x
-/
theorem iSup_union {f : α → β} {s t : Finset α} :
    ⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by
  simpa using! _root_.iSup_union

@[to_dual]
/-
**Finset.iSup_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iSup_insert (a : α) (s : Finset α) (t : α -> β) : ⨆ x in insert a s, t x =
 t a ⊔ ⨆ x in s, t x
参数：a : α；s : Finset α；t : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
-/
theorem iSup_insert (a : α) (s : Finset α) (t : α → β) :
    ⨆ x ∈ insert a s, t x = t a ⊔ ⨆ x ∈ s, t x := by
  simpa using! _root_.iSup_insert

@[to_dual]
/-
**Finset.iSup_finset_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iSup_finset_image {f : γ -> α} {g : α -> β} {s : Finset γ} : ⨆ x in s.imag
e f, g x = ⨆ y in s, g (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
-/
theorem iSup_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    ⨆ x ∈ s.image f, g x = ⨆ y ∈ s, g (f y) := by
  simpa using! iSup_image

@[to_dual]
/-
**Finset.iSup_insert_update** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iSup_insert_update {x : α} {t : Finset α} (f : α -> β) {s : β} (hx : x ∉ t
) : ⨆ i in insert x t, Function.update f x s i = s ⊔ ⨆ i in t, f i
参数：f : α -> β；hx : x ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.iSup_insert`：iSup_insert (a : α) (s : Finset α) (t : α -> β) : ⨆ 
x in insert a s, t x = t a ⊔ ⨆ x in s, t x
-/
theorem iSup_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    ⨆ i ∈ insert x t, Function.update f x s i = s ⊔ ⨆ i ∈ t, f i := by
  rw [Finset.iSup_insert]
  grind

@[to_dual]
/-
**Finset.iSup_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iSup_biUnion (s : Finset γ) (t : γ -> Finset α) (f : α -> β) : ⨆ y in s.bi
Union t, f y = ⨆ (x in s) (y in t x), f y
参数：s : Finset γ；t : γ -> Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    ⨆ y ∈ s.biUnion t, f y = ⨆ (x ∈ s) (y ∈ t x), f y := by simp [@iSup_comm _ α, iSup_and]

end Lattice

/-
**Finset.set_biUnion_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_coe (s : Finset α) (t : α -> Set β) : ⋃ x in (↑s : Set α), t x
 = ⋃ x in s, t x
参数：s : Finset α；t : α -> Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem set_biUnion_coe (s : Finset α) (t : α → Set β) : ⋃ x ∈ (↑s : Set α), t x = ⋃ x ∈ s, t x :=
  rfl
/-
**Finset.set_biInter_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biInter_coe (s : Finset α) (t : α -> Set β) : ⋂ x in (↑s : Set α), t x
 = ⋂ x in s, t x
参数：s : Finset α；t : α -> Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem set_biInter_coe (s : Finset α) (t : α → Set β) : ⋂ x ∈ (↑s : Set α), t x = ⋂ x ∈ s, t x :=
  rfl
/-
**Finset.set_biUnion_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_singleton (a : α) (s : α -> Set β) : ⋃ x in ({a} : Finset α), 
s x = s a
参数：a : α；s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iSup_singleton`：iSup_singleton (a : α) (s : α -> β) : ⨆ x in ({a}
 : Finset α), s x = s a
-/
theorem set_biUnion_singleton (a : α) (s : α → Set β) : ⋃ x ∈ ({a} : Finset α), s x = s a :=
  iSup_singleton a s
/-
**Finset.set_biInter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biInter_singleton (a : α) (s : α -> Set β) : ⋂ x in ({a} : Finset α), 
s x = s a
参数：a : α；s : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iInf_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteL
attice β] (a : α) (s : α → β), ⨅ x ∈ {a}, s x = s a
-/
theorem set_biInter_singleton (a : α) (s : α → Set β) : ⋂ x ∈ ({a} : Finset α), s x = s a :=
  iInf_singleton a s

@[simp]
/-
**Finset.set_biUnion_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_preimage_singleton (f : α -> β) (s : Finset β) : ⋃ y in s, f ⁻
¹' {y} = f ⁻¹' s
参数：f : α -> β；s : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
-/
theorem set_biUnion_preimage_singleton (f : α → β) (s : Finset β) :
    ⋃ y ∈ s, f ⁻¹' {y} = f ⁻¹' s :=
  Set.biUnion_preimage_singleton f s
/-
**Finset.set_biUnion_option_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_option_toFinset (o : Option α) (f : α -> Set β) : ⋃ x in o.toF
inset, f x = ⋃ x in o, f x
参数：o : Option α；f : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iSup_option_toFinset`：iSup_option_toFinset (o : Option α) (f : α 
-> β) : ⨆ x in o.toFinset, f x = ⨆ x in o, f x
-/
theorem set_biUnion_option_toFinset (o : Option α) (f : α → Set β) :
    ⋃ x ∈ o.toFinset, f x = ⋃ x ∈ o, f x :=
  iSup_option_toFinset o f
/-
**Finset.set_biInter_option_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biInter_option_toFinset (o : Option α) (f : α -> Set β) : ⋂ x in o.toF
inset, f x = ⋂ x in o, f x
参数：o : Option α；f : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iInf_option_toFinset`：∀ {α : Type u_2} {β : Type u_3} [inst : Com
pleteLattice β] (o : Option α) (f : α → β),   ⨅ x ∈ o.toFinset, f x = ⨅ x ∈ o, f
 x
-/
theorem set_biInter_option_toFinset (o : Option α) (f : α → Set β) :
    ⋂ x ∈ o.toFinset, f x = ⋂ x ∈ o, f x :=
  iInf_option_toFinset o f
/-
**Finset.subset_set_biUnion_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_set_biUnion_of_mem {s : Finset α} {f : α -> Set β} {x : α} (h : x i
n s) : f x subseteq ⋃ y in s, f y
参数：h : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
-/
theorem subset_set_biUnion_of_mem {s : Finset α} {f : α → Set β} {x : α} (h : x ∈ s) :
    f x ⊆ ⋃ y ∈ s, f y :=
  le_iSup_of_le x <| by simp [h]

variable [DecidableEq α]
/-
**Finset.set_biUnion_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_union (s t : Finset α) (u : α -> Set β) : ⋃ x in s union t, u 
x = (⋃ x in s, u x) union ⋃ x in t, u x
参数：s t : Finset α；u : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iSup_union`：iSup_union {f : α -> β} {s t : Finset α} : ⨆ x in s u
nion t, f x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x
-/
theorem set_biUnion_union (s t : Finset α) (u : α → Set β) :
    ⋃ x ∈ s ∪ t, u x = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  iSup_union
/-
**Finset.set_biInter_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biInter_inter (s t : Finset α) (u : α -> Set β) : ⋂ x in s union t, u 
x = (⋂ x in s, u x) inter ⋂ x in t, u x
参数：s t : Finset α；u : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iInf_union`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatti
ce β] [inst_1 : DecidableEq α] {f : α → β} {s t : Finset α},   ⨅ x ∈ s ∪ t, f x 
= (⨅ x …
-/
theorem set_biInter_inter (s t : Finset α) (u : α → Set β) :
    ⋂ x ∈ s ∪ t, u x = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  iInf_union
/-
**Finset.set_biUnion_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_insert (a : α) (s : Finset α) (t : α -> Set β) : ⋃ x in insert
 a s, t x = t a union ⋃ x in s, t x
参数：a : α；s : Finset α；t : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iSup_insert`：iSup_insert (a : α) (s : Finset α) (t : α -> β) : ⨆ 
x in insert a s, t x = t a ⊔ ⨆ x in s, t x
-/
theorem set_biUnion_insert (a : α) (s : Finset α) (t : α → Set β) :
    ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x :=
  iSup_insert a s t
/-
**Finset.set_biInter_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biInter_insert (a : α) (s : Finset α) (t : α -> Set β) : ⋂ x in insert
 a s, t x = t a inter ⋂ x in s, t x
参数：a : α；s : Finset α；t : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iInf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] [inst_1 : DecidableEq α] (a : α) (s : Finset α) (t : α → β),   ⨅ x ∈ inse
rt a s, …
-/
theorem set_biInter_insert (a : α) (s : Finset α) (t : α → Set β) :
    ⋂ x ∈ insert a s, t x = t a ∩ ⋂ x ∈ s, t x :=
  iInf_insert a s t
/-
**Finset.set_biUnion_finset_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_finset_image {f : γ -> α} {g : α -> Set β} {s : Finset γ} : ⋃ 
x in s.image f, g x = ⋃ y in s, g (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iSup_finset_image`：iSup_finset_image {f : γ -> α} {g : α -> β} {s
 : Finset γ} : ⨆ x in s.image f, g x = ⨆ y in s, g (f y)
-/
theorem set_biUnion_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    ⋃ x ∈ s.image f, g x = ⋃ y ∈ s, g (f y) :=
  iSup_finset_image
/-
**Finset.set_biInter_finset_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biInter_finset_image {f : γ -> α} {g : α -> Set β} {s : Finset γ} : ⋂ 
x in s.image f, g x = ⋂ y in s, g (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iInf_finset_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4}
 [inst : CompleteLattice β] [inst_1 : DecidableEq α] {f : γ → α}   {g : α → β} {
s : Finset γ},…
-/
theorem set_biInter_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    ⋂ x ∈ s.image f, g x = ⋂ y ∈ s, g (f y) :=
  iInf_finset_image
/-
**Finset.set_biUnion_insert_update** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_insert_update {x : α} {t : Finset α} (f : α -> Set β) {s : Set
 β} (hx : x ∉ t) : ⋃ i in insert x t, @update _ _ _ f x s i = s union ⋃ i in t, 
f i
参数：f : α -> Set β；hx : x ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iSup_insert_update`：iSup_insert_update {x : α} {t : Finset α} (f 
: α -> β) {s : β} (hx : x ∉ t) : ⨆ i in insert x t, Function.update f x s i = s 
⊔ ⨆ i in t, f i
-/
theorem set_biUnion_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    ⋃ i ∈ insert x t, @update _ _ _ f x s i = s ∪ ⋃ i ∈ t, f i :=
  iSup_insert_update f hx
/-
**Finset.set_biInter_insert_update** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biInter_insert_update {x : α} {t : Finset α} (f : α -> Set β) {s : Set
 β} (hx : x ∉ t) : ⋂ i in insert x t, @update _ _ _ f x s i = s inter ⋂ i in t, 
f i
参数：f : α -> Set β；hx : x ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iInf_insert_update`：∀ {α : Type u_2} {β : Type u_3} [inst : Compl
eteLattice β] [inst_1 : DecidableEq α] {x : α} {t : Finset α} (f : α → β)   {s :
 β}, x ∉ t → ⨅ …
-/
theorem set_biInter_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    ⋂ i ∈ insert x t, @update _ _ _ f x s i = s ∩ ⋂ i ∈ t, f i :=
  iInf_insert_update f hx
/-
**Finset.set_biUnion_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biUnion_biUnion (s : Finset γ) (t : γ -> Finset α) (f : α -> Set β) : 
⋃ y in s.biUnion t, f y = ⋃ (x in s) (y in t x), f y
参数：s : Finset γ；t : γ -> Finset α；f : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iSup_biUnion`：iSup_biUnion (s : Finset γ) (t : γ -> Finset α) (f 
: α -> β) : ⨆ y in s.biUnion t, f y = ⨆ (x in s) (y in t x), f y
-/
theorem set_biUnion_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    ⋃ y ∈ s.biUnion t, f y = ⋃ (x ∈ s) (y ∈ t x), f y :=
  iSup_biUnion s t f
/-
**Finset.set_biInter_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：set_biInter_biUnion (s : Finset γ) (t : γ -> Finset α) (f : α -> Set β) : 
⋂ y in s.biUnion t, f y = ⋂ (x in s) (y in t x), f y
参数：s : Finset γ；t : γ -> Finset α；f : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.iInf_biUnion`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [ins
t : CompleteLattice β] [inst_1 : DecidableEq α] (s : Finset γ)   (t : γ → Finset
 α) (f : …
-/
theorem set_biInter_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    ⋂ y ∈ s.biUnion t, f y = ⋂ (x ∈ s) (y ∈ t x), f y :=
  iInf_biUnion s t f

end Finset

