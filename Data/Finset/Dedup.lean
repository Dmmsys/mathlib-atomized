/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.Dedup
public import Mathlib.Data.Multiset.Basic

/-!
# Deduplicating Multisets to make Finsets

This file concerns `Multiset.dedup` and `List.dedup` as a way to create `Finset`s.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

@[simp]
/-
**Finset.dedup_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：dedup_eq_self [DecidableEq α] (s : Finset α) : dedup s.1 = s.1
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem dedup_eq_self [DecidableEq α] (s : Finset α) : dedup s.1 = s.1 :=
  s.2.dedup

end Finset

/-! ### dedup on list and multiset -/

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

/-- `toFinset s` removes duplicates from the multiset `s` to produce a finset. -/
/-
**Multiset.toFinset** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：toFinset (s : Multiset α) : Finset α
参数：s : Multiset α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_dedup`：nodup_dedup (s : Multiset α) : Nodup (dedup s)

--- 原说明 ---
`toFinset s` removes duplicates from the multiset `s` to produce a finset.
-/
def toFinset (s : Multiset α) : Finset α :=
  ⟨_, nodup_dedup s⟩

@[simp]
/-
**Multiset.toFinset_val** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_val (s : Multiset α) : s.toFinset.1 = s.dedup
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_val (s : Multiset α) : s.toFinset.1 = s.dedup :=
  rfl
/-
**Multiset.toFinset_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_eq {s : Multiset α} (n : Nodup s) : Finset.mk s n = s.toFinset
参数：n : Nodup s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
-/
theorem toFinset_eq {s : Multiset α} (n : Nodup s) : Finset.mk s n = s.toFinset :=
  Finset.val_inj.1 n.dedup.symm
/-
**Multiset.Nodup.toFinset_inj** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l l' : Multiset α}, l.Nodup → l'.
Nodup → l.toFinset = l'.toFinset → l = l'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.toFinset_eq`：toFinset_eq {s : Multiset α} (n : Nodup s) : Finse
t.mk s n = s.toFinset
· 使用定理 `Finset.mk.injEq`：∀ {α : Type u_4} (val : Multiset α) (nodup : val.Nodup)
 (val_1 : Multiset α) (nodup_1 : val_1.Nodup),   ({ val := val, nodup := nodup }
 = { …
-/
theorem Nodup.toFinset_inj {l l' : Multiset α} (hl : Nodup l) (hl' : Nodup l')
    (h : l.toFinset = l'.toFinset) : l = l' := by
  simpa [← toFinset_eq hl, ← toFinset_eq hl'] using h

@[simp, grind =]
/-
**Multiset.mem_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_toFinset {a : α} {s : Multiset α} : a in s.toFinset ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_dedup`：mem_dedup {a : α} {s : Multiset α} : a in dedup s ↔ 
a in s
-/
theorem mem_toFinset {a : α} {s : Multiset α} : a ∈ s.toFinset ↔ a ∈ s :=
  mem_dedup

@[simp]
/-
**Multiset.toFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_subset : s.toFinset subseteq t.toFinset ↔ s subseteq t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_subset : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp only [Finset.subset_iff, Multiset.subset_iff, Multiset.mem_toFinset]

@[simp]
/-
**Multiset.toFinset_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_ssubset : s.toFinset ⊂ t.toFinset ↔ s ⊂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_ssubset : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp_rw [Finset.ssubset_def, toFinset_subset]
  rfl

@[simp]
/-
**Multiset.toFinset_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_dedup (m : Multiset α) : m.dedup.toFinset = m.toFinset
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.nodup_dedup`：nodup_dedup (s : Multiset α) : Nodup (dedup s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.dedup_idem`：dedup_idem {m : Multiset α} : m.dedup.dedup = m.ded
up
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mk.congr_simp`：∀ {α : Type u_4} (val val_1 : Multiset α) (e_val :
 val = val_1) (nodup : val.Nodup),   { val := val, nodup := nodup } = { val := v
al_1, nodu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinset_dedup (m : Multiset α) : m.dedup.toFinset = m.toFinset := by
  simp_rw [toFinset, dedup_idem]
/-
**Multiset.isWellFounded_ssubset** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：isWellFounded_ssubset : IsWellFounded (Multiset β) (· ⊂ ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.isWellFounded`：Subrelation.isWellFounded (r : α -> α -> Prop
) [IsWellFounded α r] {s : α -> α -> Prop} (h : Subrelation s r) : IsWellFounded
 α s
· 使用定理 `instIsWellFoundedInvImage`：∀ {α : Type u} {β : Type v} (r : α → α → Prop
) [IsWellFounded α r] (f : β → α), IsWellFounded β (InvImage r f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.toFinset_ssubset`：toFinset_ssubset : s.toFinset ⊂ t.toFinset ↔ 
s ⊂ t
-/
instance isWellFounded_ssubset : IsWellFounded (Multiset β) (· ⊂ ·) := by
  classical
  exact Subrelation.isWellFounded (InvImage _ toFinset) toFinset_ssubset.2

end Multiset

namespace Finset

@[simp]
/-
**Finset.val_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_toFinset [DecidableEq α] (s : Finset α) : s.val.toFinset = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_toFinset [DecidableEq α] (s : Finset α) : s.val.toFinset = s := by
  ext
  rw [Multiset.mem_toFinset, ← mem_def]
/-
**Finset.val_le_iff_val_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_le_iff_val_subset {a : Finset α} {b : Multiset α} : a.val <= b ↔ a.val
 subseteq b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.le_iff_subset`：le_iff_subset {s t : Multiset α} : Nodup s -> (s
 <= t ↔ s subseteq t)
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem val_le_iff_val_subset {a : Finset α} {b : Multiset α} : a.val ≤ b ↔ a.val ⊆ b :=
  Multiset.le_iff_subset a.nodup

end Finset

namespace List

variable [DecidableEq α] {l l' : List α} {a : α} {f : α → β}
  {s : Finset α} {t : Set β} {t' : Finset β}

/-- `toFinset l` removes duplicates from the list `l` to produce a finset. -/
/-
**List.toFinset** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：toFinset (l : List α) : Finset α
参数：l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toFinset l` removes duplicates from the list `l` to produce a finset.
-/
def toFinset (l : List α) : Finset α :=
  Multiset.toFinset l

@[simp]
/-
**List.toFinset_val** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_val (l : List α) : l.toFinset.1 = (l.dedup : Multiset α)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_val (l : List α) : l.toFinset.1 = (l.dedup : Multiset α) :=
  rfl

@[simp]
/-
**List.toFinset_coe** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_coe (l : List α) : (l : Multiset α).toFinset = l.toFinset
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_coe (l : List α) : (l : Multiset α).toFinset = l.toFinset :=
  rfl
/-
**List.toFinset_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_eq (n : Nodup l) : @Finset.mk α l n = l.toFinset
参数：n : Nodup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.toFinset_eq`：toFinset_eq {s : Multiset α} (n : Nodup s) : Finse
t.mk s n = s.toFinset
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_nodup`：coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup
-/
theorem toFinset_eq (n : Nodup l) : @Finset.mk α l n = l.toFinset :=
  Multiset.toFinset_eq <| by rwa [Multiset.coe_nodup]

@[simp]
/-
**List.mem_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_toFinset : a in l.toFinset ↔ a in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_dedup`：mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l
-/
theorem mem_toFinset : a ∈ l.toFinset ↔ a ∈ l :=
  mem_dedup

@[simp, norm_cast]
/-
**List.coe_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：coe_toFinset (l : List α) : (l.toFinset : Set α) = { a | a in l }
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
-/
theorem coe_toFinset (l : List α) : (l.toFinset : Set α) = { a | a ∈ l } :=
  Set.ext fun _ => List.mem_toFinset
/-
**List.toFinset_surj_on** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_surj_on : Set.SurjOn toFinset { l : List α | l.Nodup } Set.univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.toFinset_eq`：toFinset_eq (n : Nodup l) : @Finset.mk α l n = l.toFin
set
-/
theorem toFinset_surj_on : Set.SurjOn toFinset { l : List α | l.Nodup } Set.univ := by
  rintro ⟨⟨l⟩, hl⟩ _
  exact ⟨l, hl, (toFinset_eq hl).symm⟩
/-
**List.toFinset_surjective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_surjective : Surjective (toFinset : List α -> Finset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.toFinset_surj_on`：toFinset_surj_on : Set.SurjOn toFinset { l : List
 α | l.Nodup } Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem toFinset_surjective : Surjective (toFinset : List α → Finset α) := fun s =>
  let ⟨l, _, hls⟩ := toFinset_surj_on (Set.mem_univ s)
  ⟨l, hls⟩
/-
**List.toFinset_eq_iff_perm_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_eq_iff_perm_dedup : l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup
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
· 使用定理 `List.perm_ext_iff_of_nodup`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup 
→ l₂.Nodup → (l₁.Perm l₂ ↔ ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.nodup_dedup`：nodup_dedup : forall l : List α, Nodup (dedup l)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_eq_iff_perm_dedup : l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup := by
  simp [Finset.ext_iff, perm_ext_iff_of_nodup (nodup_dedup _) (nodup_dedup _)]
/-
**List.toFinset.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.toFinset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {a b : List α}, a.toFinset = b.toF
inset ↔ ∀ (x : α), x ∈ a ↔ x ∈ b
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset.ext_iff {a b : List α} : a.toFinset = b.toFinset ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [Finset.ext_iff, mem_toFinset]
/-
**List.toFinset.ext** 是 Mathlib 中的一个定理，位于命名空间 `List.toFinset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l l' : List α}, (∀ (x : α), x ∈ l
 ↔ x ∈ l') → l.toFinset = l'.toFinset
参数：∀ (x : α), x ∈ l ↔ x ∈ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.toFinset.ext_iff`：∀ {α : Type u_1} [inst : DecidableEq α] {a b : Li
st α}, a.toFinset = b.toFinset ↔ ∀ (x : α), x ∈ a ↔ x ∈ b
-/
theorem toFinset.ext : (∀ x, x ∈ l ↔ x ∈ l') → l.toFinset = l'.toFinset :=
  toFinset.ext_iff.mpr
/-
**List.toFinset_eq_of_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_eq_of_perm (l l' : List α) (h : l ~ l') : l.toFinset = l'.toFinse
t
参数：l l' : List α；h : l ~ l'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.toFinset_eq_iff_perm_dedup`：toFinset_eq_iff_perm_dedup : l.toFinset
 = l'.toFinset ↔ l.dedup ~ l'.dedup
· 使用定理 `List.Perm.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂ : List α
}, l₁.Perm l₂ → l₁.dedup.Perm l₂.dedup
-/
theorem toFinset_eq_of_perm (l l' : List α) (h : l ~ l') : l.toFinset = l'.toFinset :=
  toFinset_eq_iff_perm_dedup.mpr h.dedup
/-
**List.perm_of_nodup_nodup_toFinset_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_of_nodup_nodup_toFinset_eq (hl : Nodup l) (hl' : Nodup l') (h : l.toF
inset = l'.toFinset) : l ~ l'
参数：hl : Nodup l；hl' : Nodup l'；h : l.toFinset = l'.toFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `Multiset.Nodup.toFinset_inj`：∀ {α : Type u_1} [inst : DecidableEq α] {l 
l' : Multiset α}, l.Nodup → l'.Nodup → l.toFinset = l'.toFinset → l = l'
-/
theorem perm_of_nodup_nodup_toFinset_eq (hl : Nodup l) (hl' : Nodup l')
    (h : l.toFinset = l'.toFinset) : l ~ l' := by
  rw [← Multiset.coe_eq_coe]
  exact Multiset.Nodup.toFinset_inj hl hl' h

@[simp]
/-
**List.toFinset_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_reverse {l : List α} : toFinset l.reverse = l.toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.toFinset_eq_of_perm`：toFinset_eq_of_perm (l l' : List α) (h : l ~ l
') : l.toFinset = l'.toFinset
· 使用定理 `List.reverse_perm`：∀ {α : Type u_1} (l : List α), l.reverse.Perm l
-/
theorem toFinset_reverse {l : List α} : toFinset l.reverse = l.toFinset :=
  toFinset_eq_of_perm _ _ (reverse_perm l)

end List

namespace Finset

section ToList

/-- Produce a list of the elements in the finite set using choice. -/
/-
**Finset.toList** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：toList (s : Finset α) : List α
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce a list of the elements in the finite set using choice.
-/
noncomputable def toList (s : Finset α) : List α :=
  s.1.toList
/-
**Finset.nodup_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nodup_toList (s : Finset α) : s.toList.Nodup
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.toList.eq_1`：∀ {α : Type u_1} (s : Finset α), s.toList = s.val.to
List
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_nodup`：coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem nodup_toList (s : Finset α) : s.toList.Nodup := by
  rw [toList, ← Multiset.coe_nodup, Multiset.coe_toList]
  exact s.nodup

@[simp]
/-
**Finset.mem_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_toList {a : α} {s : Finset α} : a in s.toList ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_toList`：mem_toList {a : α} {s : Multiset α} : a in s.toList
 ↔ a in s
-/
theorem mem_toList {a : α} {s : Finset α} : a ∈ s.toList ↔ a ∈ s :=
  Multiset.mem_toList

@[simp, norm_cast]
/-
**Finset.coe_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_toList (s : Finset α) : (s.toList : Multiset α) = s.val
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
-/
theorem coe_toList (s : Finset α) : (s.toList : Multiset α) = s.val :=
  s.val.coe_toList

@[simp]
/-
**Finset.toList_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toList_toFinset [DecidableEq α] (s : Finset α) : s.toList.toFinset = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toList_toFinset [DecidableEq α] (s : Finset α) : s.toList.toFinset = s := by
  ext
  simp
/-
**Finset._root_.List.toFinset_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.toFinset_toList [DecidableEq α] {s : List α} (hs : s.Nodup) :
    s.toFinset.toList.Perm s := by
  apply List.perm_of_nodup_nodup_toFinset_eq (nodup_toList _) hs
  rw [toList_toFinset]
/-
**Finset.exists_list_nodup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_list_nodup_eq [DecidableEq α] (s : Finset α) : exists l : List α, l
.Nodup ∧ l.toFinset = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nodup_toList`：nodup_toList (s : Finset α) : s.toList.Nodup
· 使用定理 `Finset.toList_toFinset`：toList_toFinset [DecidableEq α] (s : Finset α) :
 s.toList.toFinset = s
-/
theorem exists_list_nodup_eq [DecidableEq α] (s : Finset α) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s :=
  ⟨s.toList, s.nodup_toList, s.toList_toFinset⟩

@[simp]
/-
**Finset.perm_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {f₁ f₂ : Finset α}, f₁.toList.Perm f₂.toList ↔ f₁ = f₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.Perm.of_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ = l₂ → l₁.Perm l₂
-/
protected theorem perm_toList {f₁ f₂ : Finset α} : f₁.toList.Perm f₂.toList ↔ f₁ = f₂ where
  mp h := Finset.ext fun x => by simp [← Finset.mem_toList, h.mem_iff]
  mpr h := .of_eq <| congrArg Finset.toList h

end ToList

end Finset

