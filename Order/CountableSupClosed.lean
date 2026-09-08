/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.SupClosed

import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Bounds.Lattice

/-!
# Sets closed under countable join/meet

This file defines predicates for sets closed under countable supremum and dually for countable
infimum.

## Main declarations

* `CountableSupClosed`: Predicate for a set to be closed under countable supremum.
* `CountableInfClosed`: Predicate for a set to be closed under countable infimum.
* `countableSupClosure`: countable Sup-closure. Smallest countable sup-closed set containing
  a given set.
* `countableInfClosure`: countable Inf-closure. Smallest countable inf-closed set containing
  a given set.

## Implementation notes

The list of properties in this file is copied and adapted from the file about `SupClosed`.
We should keep these files in sync.

-/

public section

variable {ι : Sort*} {α β : Type*} {S : Set (Set α)} {s t : Set α} {a b : α}

section Set
open Set

/-- A set `s` is closed under countable supremum if for every nonempty countable subset of `s`, any
least upper bound of that subset is in `s`. -/
/-
**CountableSupClosed** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_2} → [LE α] → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is closed under countable supremum if for every nonempty countable sub
set of `s`, any
least upper bound of that subset is in `s`.
-/
structure CountableSupClosed [LE α] (s : Set α) : Prop where
  isLUB_mem : ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ x, IsLUB t x → x ∈ s

/-- A set `s` is closed under countable infimum if for every nonempty countable subset of `s`, any
greatest lower bound of that subset is in `s`. -/
@[to_dual existing]
/-
**CountableInfClosed** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_2} → [LE α] → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is closed under countable infimum if for every nonempty countable subs
et of `s`, any
greatest lower bound of that subset is in `s`.
-/
structure CountableInfClosed [LE α] (s : Set α) : Prop where
  isGLB_mem : ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ x, IsGLB t x → x ∈ s

@[to_dual]
/-
**CountableSupClosed.iSup_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CountableSupClosed.iSup_mem [CompleteLattice α] [Countable ι] [Nonempty ι]
 (hs : CountableSupClosed s) {A : ι -> α} (hA : forall n, A n in s) : ⨆ n, A n i
n s
参数：hs : CountableSupClosed s；hA : forall n, A n in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.isLUB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableSupClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsLUB 
t x → x ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `isLUB_iSup`：isLUB_iSup : IsLUB (range f) (⨆ j, f j)
-/
lemma CountableSupClosed.iSup_mem [CompleteLattice α] [Countable ι] [Nonempty ι]
    (hs : CountableSupClosed s) {A : ι → α} (hA : ∀ n, A n ∈ s) :
    ⨆ n, A n ∈ s := by
  let i₀ := Nonempty.some (α := ι) inferInstance
  exact hs.isLUB_mem (range A) (by simp [range]; grind) ⟨A i₀, by simp⟩ (countable_range A) _
    isLUB_iSup

@[to_dual]
/-
**CountableSupClosed.of_iSup_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CountableSupClosed.of_iSup_mem [CompleteLattice α] (hs : forall A : Nat ->
 α, (forall n, A n in s) -> ⨆ n, A n in s) : CountableSupClosed s where isLUB_me
m A hAs hA_ne hAc x hx
参数：hs : forall A : Nat -> α, (forall n, A n in s) -> ⨆ n, A n in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `isLUB_iSup`：isLUB_iSup : IsLUB (range f) (⨆ j, f j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma CountableSupClosed.of_iSup_mem [CompleteLattice α]
    (hs : ∀ A : ℕ → α, (∀ n, A n ∈ s) → ⨆ n, A n ∈ s) :
    CountableSupClosed s where
  isLUB_mem A hAs hA_ne hAc x hx := by
    obtain ⟨f, rfl⟩ := hAc.exists_eq_range hA_ne
    rw [(IsLUB.unique hx isLUB_iSup : x = ⨆ n, f n)]
    exact hs f (by grind)

@[to_dual]
/-
**CountableSupClosed.sSup_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CountableSupClosed.sSup_mem [CompleteLattice α] (hs : CountableSupClosed s
) {A : Set α} (hA_c : A.Countable) (hA_ne : A.Nonempty) (hA : forall a in A, a i
n s) : sSup A in s
参数：hs : CountableSupClosed s；hA_c : A.Countable；hA_ne : A.Nonempty；hA : forall a
 in A, a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用引理 `CountableSupClosed.iSup_mem`：CountableSupClosed.iSup_mem [CompleteLattic
e α] [Countable ι] [Nonempty ι] (hs : CountableSupClosed s) {A : ι -> α} (hA : f
orall n, A n in s…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma CountableSupClosed.sSup_mem [CompleteLattice α] (hs : CountableSupClosed s)
    {A : Set α} (hA_c : A.Countable) (hA_ne : A.Nonempty) (hA : ∀ a ∈ A, a ∈ s) :
    sSup A ∈ s := by
  rw [sSup_eq_iSup']
  have : Countable A := hA_c
  have : Nonempty A := nonempty_coe_sort.mpr hA_ne
  exact hs.iSup_mem fun a ↦ hA a a.2

@[to_dual]
/-
**CountableSupClosed.supClosed** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {α : Type u_2} {s : Set α} [inst : SemilatticeSup α], CountableSupClosed
 s → SupClosed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.isLUB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableSupClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsLUB 
t x → x ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isLUB_pair`：isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ 
b)
-/
protected lemma CountableSupClosed.supClosed [SemilatticeSup α] (hs : CountableSupClosed s) :
    SupClosed s := fun a ha b hb ↦ hs.isLUB_mem {a, b} (by grind) (by simp) (by simp) _ isLUB_pair

@[to_dual (attr := simp)]
/-
**CountableSupClosed.singleton** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] {x : α}, CountableSupClosed {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a
-/
protected lemma CountableSupClosed.singleton [PartialOrder α] {x : α} :
    CountableSupClosed ({x} : Set α) where
  isLUB_mem s hs_subset hs_ne _ y hy := by
    have h_eq : s = {x} := by
      ext y
      simp_all only [subset_singleton_iff, mem_singleton_iff]
      refine ⟨hs_subset y, ?_⟩
      rintro rfl
      obtain ⟨z, hzs⟩ := hs_ne
      rwa [hs_subset z hzs] at hzs
    simp_all only [subset_refl, singleton_nonempty, countable_singleton, mem_singleton_iff]
    exact IsLUB.unique hy isLUB_singleton

@[to_dual (attr := simp)]
/-
**CountableSupClosed.univ** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {α : Type u_2} [inst : LE α], CountableSupClosed Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
protected lemma CountableSupClosed.univ [LE α] :
    CountableSupClosed (univ : Set α) where
  isLUB_mem _ _ _ _ _ _ := by simp

@[to_dual (attr := simp)]
/-
**CountableSupClosed.empty** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {α : Type u_2} [inst : LE α], CountableSupClosed ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected lemma CountableSupClosed.empty [LE α] :
    CountableSupClosed (∅ : Set α) where
  isLUB_mem _ _ _ _ _ _ := by simp_all

@[to_dual]
/-
**CountableSupClosed.inter** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {α : Type u_2} {s t : Set α} [inst : LE α], CountableSupClosed s → Count
ableSupClosed t → CountableSupClosed (s ∩ t)
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.isLUB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableSupClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsLUB 
t x → x ∈ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
protected lemma CountableSupClosed.inter [LE α]
    (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ∩ t) where
  isLUB_mem A hAst hA_ne hAc x hx :=
    ⟨hs.isLUB_mem A (hAst.trans Set.inter_subset_left) hA_ne hAc x hx,
      ht.isLUB_mem A (hAst.trans Set.inter_subset_right) hA_ne hAc x hx⟩

@[to_dual]
/-
**CountableSupClosed.sInter** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {α : Type u_2} {S : Set (Set α)} [inst : LE α], (∀ s ∈ S, CountableSupCl
osed s) → CountableSupClosed (⋂₀ S)
参数：Set α；∀ s ∈ S, CountableSupClosed s；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.isLUB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableSupClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsLUB 
t x → x ∈ s
-/
protected lemma CountableSupClosed.sInter [LE α] (hS : ∀ s ∈ S, CountableSupClosed s) :
    CountableSupClosed (⋂₀ S) where
  isLUB_mem A hAS hA_ne hAc x hx := by
    simp only [subset_sInter_iff, mem_sInter] at hAS ⊢
    exact fun s hs ↦ (hS s hs).isLUB_mem A (hAS s hs) hA_ne hAc x hx

@[to_dual]
/-
**CountableSupClosed.iInter** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : LE α] {f : ι → Set α},   (∀ (i : ι
), CountableSupClosed (f i)) → CountableSupClosed (⋂ i, f i)
参数：∀ (i : ι), CountableSupClosed (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.sInter`：∀ {α : Type u_2} {S : Set (Set α)} [inst : LE
 α], (∀ s ∈ S, CountableSupClosed s) → CountableSupClosed (⋂₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma CountableSupClosed.iInter [LE α]
    {f : ι → Set α} (hf : ∀ i, CountableSupClosed (f i)) :
    CountableSupClosed (⋂ i, f i) :=
  .sInter <| forall_mem_range.2 hf

@[to_dual]
/-
**CountableSupClosed.directedOn** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {α : Type u_2} {s : Set α} [inst : SemilatticeSup α], CountableSupClosed
 s → DirectedOn (fun x1 x2 => x1 ≤ x2) s
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SupClosed.directedOn`：SupClosed.directedOn (hs : SupClosed s) : Directed
On (· <= ·) s
· 使用定理 `CountableSupClosed.supClosed`：∀ {α : Type u_2} {s : Set α} [inst : Semil
atticeSup α], CountableSupClosed s → SupClosed s
-/
protected lemma CountableSupClosed.directedOn [SemilatticeSup α] (hs : CountableSupClosed s) :
    DirectedOn (· ≤ ·) s := hs.supClosed.directedOn

@[to_dual]
/-
**CountableSupClosed.prod** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClosed`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {s : Set α} [inst : Preorder α] [inst_1 : 
Preorder β] {t : Set β},   CountableSupClosed s → CountableSupClosed t → Countab
leSupClosed (s ×ˢ t)
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.isLUB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableSupClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsLUB 
t x → x ∈ s
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLUB_prod`：isLUB_prod {s : Set (α × β)} {p : α × β} : IsLUB s p ↔ IsLUB
 (Prod.fst '' s) p.1 ∧ IsLUB (Prod.snd '' s) p.2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma CountableSupClosed.prod [Preorder α] [Preorder β]
    {t : Set β} (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ×ˢ t) where
  isLUB_mem A hAst hA_ne hAc := by
    intro (x, y) hxy
    rw [isLUB_prod] at hxy
    exact ⟨hs.isLUB_mem (Prod.fst '' A) (by grind) (by simpa) (hAc.image Prod.fst) _ hxy.1,
      ht.isLUB_mem (Prod.snd '' A) (by grind) (by simpa) (hAc.image Prod.snd) _ hxy.2⟩

end Set

section Finset
variable {ι : Type*} {f : ι → α} {t : Finset ι}

@[to_dual]
/-
**CountableSupClosed.finsetSup'_mem** 是 Mathlib 中的一个定理，位于命名空间 `CountableSupClose
d`。
形式化陈述：∀ {α : Type u_2} {s : Set α} {ι : Type u_4} {f : ι → α} {t : Finset ι} [in
st : SemilatticeSup α],   CountableSupClosed s → ∀ (ht : t.Nonempty), (∀ i ∈ t, 
f i ∈ s) → t.sup' ht f ∈ s
参数：ht : t.Nonempty；∀ i ∈ t, f i ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupClosed.finsetSup'_mem`：∀ {α : Type u_3} [inst : SemilatticeSup α] {ι 
: Type u_5} {f : ι → α} {s : Set α} {t : Finset ι},   SupClosed s → ∀ (ht : t.No
nempty), (∀ i …
· 使用定理 `CountableSupClosed.supClosed`：∀ {α : Type u_2} {s : Set α} [inst : Semil
atticeSup α], CountableSupClosed s → SupClosed s
-/
lemma CountableSupClosed.finsetSup'_mem [SemilatticeSup α]
    (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s :=
  hs.supClosed.finsetSup'_mem ht

@[to_dual]
/-
**CountableSupClosed.finsetSup_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CountableSupClosed.finsetSup_mem [SemilatticeSup α] [OrderBot α] (hs : Cou
ntableSupClosed s) (ht : t.Nonempty) : (forall i in t, f i in s) -> t.sup f in s
参数：hs : CountableSupClosed s；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `CountableSupClosed.finsetSup'_mem`：∀ {α : Type u_2} {s : Set α} {ι : Typ
e u_4} {f : ι → α} {t : Finset ι} [inst : SemilatticeSup α],   CountableSupClose
d s → ∀ (ht : t.Nonempt…
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
-/
lemma CountableSupClosed.finsetSup_mem [SemilatticeSup α] [OrderBot α]
    (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup f ∈ s :=
  Finset.sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

end Finset

open OrderDual

/-
**countableSupClosed_preimage_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : LE α] {s : Set αᵒᵈ}, CountableSupClosed (⇑OrderDu
al.toDual ⁻¹' s) ↔ CountableInfClosed s
参数：⇑OrderDual.toDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.isLUB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableSupClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsLUB 
t x → x ∈ s
· 使用定理 `CountableInfClosed.isGLB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableInfClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsGLB 
t x → x ∈ s
-/
@[to_dual (attr := simp)] lemma countableSupClosed_preimage_toDual [LE α] {s : Set αᵒᵈ} :
    CountableSupClosed (toDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h ↦ ⟨h.isLUB_mem⟩, fun h ↦ ⟨h.isGLB_mem⟩⟩
/-
**countableSupClosed_preimage_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : LE α] {s : Set α}, CountableSupClosed (⇑OrderDual
.ofDual ⁻¹' s) ↔ CountableInfClosed s
参数：⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.isLUB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableSupClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsLUB 
t x → x ∈ s
· 使用定理 `CountableInfClosed.isGLB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableInfClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsGLB 
t x → x ∈ s
-/
@[to_dual (attr := simp)] lemma countableSupClosed_preimage_ofDual [LE α] {s : Set α} :
    CountableSupClosed (ofDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h ↦ ⟨h.isLUB_mem⟩, fun h ↦ ⟨h.isGLB_mem⟩⟩

@[to_dual] alias ⟨_, CountableSupClosed.dual⟩ := countableInfClosed_preimage_ofDual

/-! ### Closure -/

section Preorder

variable [Preorder α]

/-- Every set generates a set closed under countable supremum. -/
@[to_dual /-- Every set generates a set closed under countable infimum. -/]
/-
**countableSupClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：countableSupClosure : ClosureOperator (Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every set generates a set closed under countable supremum.
-/
def countableSupClosure : ClosureOperator (Set α) := .ofPred
  (fun s ↦ {a | ∃ (A : Set α) (_ : A ⊆ s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a})
  CountableSupClosed
  (fun s x hxs ↦ ⟨{x}, by simp; grind, by simp, by simp, by simp⟩)
  (fun s ↦ by
    constructor
    intro A hA hA_ne hAc x hx
    choose B hB hB_ne hBc hB_lub using hA
    refine ⟨⋃ a : A, B a.2, by simp; grind, ?_, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hA_ne
      simp
      grind
    · have : Countable A := Set.countable_coe_iff.mpr hAc
      exact Set.countable_iUnion fun a ↦ hBc a.2
    · have : Nonempty A := Set.nonempty_coe_sort.mpr hA_ne
      rw [← isLUB_iUnion_iff_of_isLUB (u := fun a : A ↦ a.1) (fun a ↦ hB_lub a.2)]
      simpa)
  (fun s t (hst : s ⊆ t) ht a ⟨A, hAs, hA_ne, hA_c, hA_lub⟩ ↦
    ht.isLUB_mem A (hAs.trans hst) hA_ne hA_c _ hA_lub)
/-
**subset_countableSupClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {s : Set α} [inst : Preorder α], s ⊆ countableSupClosure 
s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
@[to_dual (attr := simp)] lemma subset_countableSupClosure :
    s ⊆ countableSupClosure s := countableSupClosure.le_closure _

@[to_dual countableInfClosure_min]
/-
**countableSupClosure_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：countableSupClosure_min (hst : s subseteq t) (ht : CountableSupClosed t) :
 countableSupClosure s subseteq t
参数：hst : s subseteq t；ht : CountableSupClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
-/
lemma countableSupClosure_min (hst : s ⊆ t) (ht : CountableSupClosed t) :
    countableSupClosure s ⊆ t := countableSupClosure.closure_min hst ht
/-
**countableSupClosed_countableSupClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {s : Set α} [inst : Preorder α], CountableSupClosed (coun
tableSupClosure s)
参数：countableSupClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
@[to_dual (attr := simp)] lemma countableSupClosed_countableSupClosure :
    CountableSupClosed (countableSupClosure s) := countableSupClosure.isClosed_closure _

@[to_dual (attr := gcongr)]
/-
**countableSupClosure_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：countableSupClosure_mono : Monotone (countableSupClosure : Set α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
lemma countableSupClosure_mono : Monotone (countableSupClosure : Set α → Set α) :=
  countableSupClosure.mono
/-
**countableSupClosure_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {s : Set α} [inst : Preorder α], countableSupClosure s = 
s ↔ CountableSupClosed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
-/
@[to_dual (attr := simp)] lemma countableSupClosure_eq_self :
    countableSupClosure s = s ↔ CountableSupClosed s := countableSupClosure.isClosed_iff.symm

@[to_dual]
alias ⟨_, CountableSupClosed.countableSupClosure_eq⟩ := countableSupClosure_eq_self

@[to_dual]
/-
**countableSupClosure_idem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：countableSupClosure_idem (s : Set α) : countableSupClosure (countableSupCl
osure s) = countableSupClosure s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
-/
lemma countableSupClosure_idem (s : Set α) :
    countableSupClosure (countableSupClosure s) = countableSupClosure s :=
  countableSupClosure.idempotent _

@[to_dual]
/-
**countableSupClosure_eq_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：countableSupClosure_eq_sInter (s : Set α) : countableSupClosure s = ⋂₀ {t 
| s subseteq t ∧ CountableSupClosed t}
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CountableSupClosed.isLUB_mem`：∀ {α : Type u_2} [inst : LE α] {s : Set α}
,   CountableSupClosed s → ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ (x : α), IsLUB 
t x → x ∈ s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `countableSupClosure_min`：countableSupClosure_min (hst : s subseteq t) (h
t : CountableSupClosed t) : countableSupClosure s subseteq t
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `subset_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Preorde
r α], s ⊆ countableSupClosure s
· 使用定理 `countableSupClosed_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [in
st : Preorder α], CountableSupClosed (countableSupClosure s)
-/
lemma countableSupClosure_eq_sInter (s : Set α) :
    countableSupClosure s = ⋂₀ {t | s ⊆ t ∧ CountableSupClosed t} := by
  have : CountableSupClosed (⋂₀ {t | s ⊆ t ∧ CountableSupClosed t}) := by
    constructor
    simp only [Set.subset_sInter_iff, Set.mem_ofPred_eq, and_imp, Set.mem_sInter]
    intro t ht ht_ne ht_c x hx t' hst' ht'
    exact ht'.isLUB_mem t (ht t' hst' ht') ht_ne ht_c x hx
  refine le_antisymm (countableSupClosure_min (by grind) (by grind)) (Set.sInter_subset_of_mem ?_)
  exact ⟨subset_countableSupClosure, countableSupClosed_countableSupClosure⟩

@[to_dual]
/-
**mem_countableSupClosure_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_countableSupClosure_iff : a in countableSupClosure s ↔ exists (A : Set
 α) (_ : A subseteq s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_countableSupClosure_iff :
    a ∈ countableSupClosure s ↔
      ∃ (A : Set α) (_ : A ⊆ s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a := by rfl
/-
**countableSupClosure_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α], countableSupClosure Set.univ = Set.u
niv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_dual (attr := simp)] lemma countableSupClosure_univ :
    countableSupClosure (Set.univ : Set α) = Set.univ := by simp
/-
**countableSupClosure_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α], countableSupClosure ∅ = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_dual (attr := simp)] lemma countableSupClosure_empty :
    countableSupClosure (∅ : Set α) = ∅ := by simp
/-
**upperBounds_countableSupClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (s : Set α), upperBounds (countableSu
pClosure s) = upperBounds s
参数：s : Set α；countableSupClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
· 使用定理 `subset_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Preorde
r α], s ⊆ countableSupClosure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_countableSupClosure_iff`：mem_countableSupClosure_iff : a in countabl
eSupClosure s ↔ exists (A : Set α) (_ : A subseteq s) (_ : A.Nonempty) (_ : A.Co
untable), IsLUB A…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
-/
@[to_dual (attr := simp)] lemma upperBounds_countableSupClosure (s : Set α) :
    upperBounds (countableSupClosure s) = upperBounds s :=
  (upperBounds_mono_set subset_countableSupClosure).antisymm <| by
    intro a ha b hb
    rw [mem_countableSupClosure_iff] at hb
    obtain ⟨t, hts, ht_ne, ht_c, ht_lub⟩ := hb
    have hat : a ∈ upperBounds t := fun x hx ↦ ha (hts hx)
    exact (isLUB_le_iff ht_lub).mpr hat
/-
**isLUB_countableSupClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {s : Set α} {a : α} [inst : Preorder α], IsLUB (countable
SupClosure s) a ↔ IsLUB s a
参数：countableSupClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `upperBounds_countableSupClosure`：∀ {α : Type u_2} [inst : Preorder α] (s
 : Set α), upperBounds (countableSupClosure s) = upperBounds s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_dual (attr := simp)] lemma isLUB_countableSupClosure :
    IsLUB (countableSupClosure s) a ↔ IsLUB s a := by simp [IsLUB]
/-
**countableSupClosure_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(s : Set α) (t : Set β),   countableSupClosure (s ×ˢ t) = countableSupClosure s 
×ˢ countableSupClosure t
参数：s : Set α；t : Set β；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `countableSupClosure_min`：countableSupClosure_min (hst : s subseteq t) (h
t : CountableSupClosed t) : countableSupClosure s subseteq t
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `subset_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Preorde
r α], s ⊆ countableSupClosure s
· 使用定理 `CountableSupClosed.prod`：∀ {α : Type u_2} {β : Type u_3} {s : Set α} [in
st : Preorder α] [inst_1 : Preorder β] {t : Set β},   CountableSupClosed s → Cou
ntableSupClos…
· 使用定理 `countableSupClosed_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [in
st : Preorder α], CountableSupClosed (countableSupClosure s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.Countable.prod`：∀ {α : Type u} {β : Type v} {s : Set α} {t : Set β},
 s.Countable → t.Countable → (s ×ˢ t).Countable
· 使用引理 `IsLUB.prod`：IsLUB.prod {b : β} (hs : s.Nonempty) (ht : t.Nonempty) (ha :
 IsLUB s a) (hb : IsLUB t b) : IsLUB (s ×ˢ t) (a, b)
-/
@[to_dual (attr := simp)] lemma countableSupClosure_prod [Preorder β]
    (s : Set α) (t : Set β) :
    countableSupClosure (s ×ˢ t) = countableSupClosure s ×ˢ countableSupClosure t :=
  le_antisymm (countableSupClosure_min
    (Set.prod_mono subset_countableSupClosure subset_countableSupClosure) <|
    countableSupClosed_countableSupClosure.prod countableSupClosed_countableSupClosure) <| by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [mem_countableSupClosure_iff] at ha hb ⊢
      obtain ⟨u, hu, hu_ne, hu_c, hu_lub⟩ := ha
      obtain ⟨v, hv, hv_ne, hv_c, hv_lub⟩ := hb
      refine ⟨u ×ˢ v, by grind, by simp [hu_ne, hv_ne], hu_c.prod hv_c, ?_⟩
      exact IsLUB.prod hu_ne hv_ne hu_lub hv_lub

end Preorder

@[to_dual]
/-
**mem_countableSupClosure_iff_iSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_countableSupClosure_iff_iSup [CompleteLattice α] : a in countableSupCl
osure s ↔ exists (t : Nat -> α), (forall n, t n in s) ∧ ⨆ n, t n = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CountableSupClosed.of_iSup_mem`：CountableSupClosed.of_iSup_mem [Complete
Lattice α] (hs : forall A : Nat -> α, (forall n, A n in s) -> ⨆ n, A n in s) : C
ountableSupClosed s …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_unpair`：iSup_unpair {α} [CompleteLattice α] (f : Nat -> Nat -> α) :
 ⨆ n : Nat, f n.unpair.1 n.unpair.2 = ⨆ (i : Nat) (j : Nat), f i j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `countableSupClosure_min`：countableSupClosure_min (hst : s subseteq t) (h
t : CountableSupClosed t) : countableSupClosure s subseteq t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `CountableSupClosed.iSup_mem`：CountableSupClosed.iSup_mem [CompleteLattic
e α] [Countable ι] [Nonempty ι] (hs : CountableSupClosed s) {A : ι -> α} (hA : f
orall n, A n in s…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `countableSupClosed_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [in
st : Preorder α], CountableSupClosed (countableSupClosure s)
· 使用定理 `subset_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Preorde
r α], s ⊆ countableSupClosure s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_countableSupClosure_iff_iSup [CompleteLattice α] :
    a ∈ countableSupClosure s ↔ ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a := by
  suffices countableSupClosure s = {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a} by simp [this]
  have h_csc : CountableSupClosed {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a} := by
    refine .of_iSup_mem fun A hA ↦ ?_
    choose B hB hB_eq using hA
    refine ⟨fun n ↦ B (Nat.unpair n).1 (Nat.unpair n).2, fun _ ↦ hB _ _, ?_⟩
    simp [iSup_unpair, ← hB_eq]
  refine le_antisymm (countableSupClosure_min ?_ h_csc) ?_
  · exact fun a ha ↦ ⟨fun _ ↦ a, by simp [ha]⟩
  · rintro _ ⟨u, hus, rfl⟩
    exact countableSupClosed_countableSupClosure.iSup_mem fun n ↦ subset_countableSupClosure (hus n)
/-
**supClosed_countableSupClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {s : Set α} [inst : SemilatticeSup α], SupClosed (countab
leSupClosure s)
参数：countableSupClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableSupClosed.supClosed`：∀ {α : Type u_2} {s : Set α} [inst : Semil
atticeSup α], CountableSupClosed s → SupClosed s
· 使用定理 `countableSupClosed_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [in
st : Preorder α], CountableSupClosed (countableSupClosure s)
-/
@[to_dual (attr := simp)] lemma supClosed_countableSupClosure [SemilatticeSup α] :
    SupClosed (countableSupClosure s) :=
  countableSupClosed_countableSupClosure.supClosed
/-
**countableSupClosure_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : PartialOrder α] {x : α}, countableSupClosure {x} 
= {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_dual (attr := simp)] lemma countableSupClosure_singleton [PartialOrder α] {x : α} :
    countableSupClosure {x} = {x} := by simp

@[to_dual]
/-
**sup_mem_countableSupClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_mem_countableSupClosure [SemilatticeSup α] (ha : a in s) (hb : b in s)
 : a ⊔ b in countableSupClosure s
参数：ha : a in s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supClosed_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Semi
latticeSup α], SupClosed (countableSupClosure s)
· 使用定理 `subset_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Preorde
r α], s ⊆ countableSupClosure s
-/
lemma sup_mem_countableSupClosure [SemilatticeSup α] (ha : a ∈ s) (hb : b ∈ s) :
    a ⊔ b ∈ countableSupClosure s :=
  supClosed_countableSupClosure (subset_countableSupClosure ha) (subset_countableSupClosure hb)

@[to_dual]
/-
**iSup_mem_countableSupClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_mem_countableSupClosure [CompleteLattice α] [Countable ι] [Nonempty ι
] {A : ι -> α} (hA : forall n, A n in s) : ⨆ n, A n in countableSupClosure s
参数：hA : forall n, A n in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CountableSupClosed.iSup_mem`：CountableSupClosed.iSup_mem [CompleteLattic
e α] [Countable ι] [Nonempty ι] (hs : CountableSupClosed s) {A : ι -> α} (hA : f
orall n, A n in s…
· 使用定理 `countableSupClosed_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [in
st : Preorder α], CountableSupClosed (countableSupClosure s)
· 使用定理 `subset_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Preorde
r α], s ⊆ countableSupClosure s
-/
lemma iSup_mem_countableSupClosure [CompleteLattice α] [Countable ι] [Nonempty ι] {A : ι → α}
    (hA : ∀ n, A n ∈ s) :
    ⨆ n, A n ∈ countableSupClosure s :=
  countableSupClosed_countableSupClosure.iSup_mem (fun n ↦ subset_countableSupClosure (hA n))

@[to_dual]
/-
**finsetSup'_mem_countableSupClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {s : Set α} {ι : Type u_4} [inst : SemilatticeSup α] {t :
 Finset ι} (ht : t.Nonempty) {f : ι → α},   (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ c
ountableSupClosure s
参数：ht : t.Nonempty；∀ i ∈ t, f i ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupClosed.finsetSup'_mem`：∀ {α : Type u_3} [inst : SemilatticeSup α] {ι 
: Type u_5} {f : ι → α} {s : Set α} {t : Finset ι},   SupClosed s → ∀ (ht : t.No
nempty), (∀ i …
· 使用定理 `supClosed_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Semi
latticeSup α], SupClosed (countableSupClosure s)
· 使用定理 `subset_countableSupClosure`：∀ {α : Type u_2} {s : Set α} [inst : Preorde
r α], s ⊆ countableSupClosure s
-/
lemma finsetSup'_mem_countableSupClosure {ι : Type*} [SemilatticeSup α]
    {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.sup' ht f ∈ countableSupClosure s :=
  supClosed_countableSupClosure.finsetSup'_mem _ fun _i hi ↦ subset_countableSupClosure <| hf _ hi

/-- If a set is closed under binary suprema, then its countable infimum closure is also closed under
binary suprema. -/
@[to_dual
/-- If a set is closed under binary infima, then its countable supremum closure is also closed under
binary infima. -/]
/-
**SupClosed.countableInfClosure** 是 Mathlib 中的一个定理，位于命名空间 `SupClosed`。
形式化陈述：∀ {α : Type u_2} {s : Set α} [inst : Order.Coframe α], SupClosed s → SupCl
osed (countableInfClosure s)
参数：countableInfClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_countableInfClosure_iff_iInf`：∀ {α : Type u_2} {s : Set α} {a : α} [
inst : CompleteLattice α],   a ∈ countableInfClosure s ↔ ∃ t, (∀ (n : ℕ), t n ∈ 
s) ∧ ⨅ n, t n = a
· 使用定理 `iInf_sup_iInf`：∀ {α : Type u} [inst : Order.Coframe α] {ι : Type u_1} {ι
' : Type u_2} {f : ι → α} {g : ι' → α},   (⨅ i, f i) ⊔ ⨅ j, g j = ⨅ i, f i.1 ⊔ g
 i.…
· 使用定理 `iInf_unpair`：∀ {α : Type u_1} [inst : CompleteLattice α] (f : ℕ → ℕ → α)
, ⨅ n, f (Nat.unpair n).1 (Nat.unpair n).2 = ⨅ i, ⨅ j, f i j
· 使用定理 `iInf_prod'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Compl
eteLattice α] (f : β → γ → α),   ⨅ i, ⨅ j, f i j = ⨅ x, f x.1 x.2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected lemma SupClosed.countableInfClosure [Order.Coframe α] (hs : SupClosed s) :
    SupClosed (countableInfClosure s) := by
  rintro a ha b hb
  rw [mem_countableInfClosure_iff_iInf] at ha hb ⊢
  obtain ⟨t, ht, hts, rfl⟩ := ha
  obtain ⟨u, hu, hus, rfl⟩ := hb
  rw [iInf_sup_iInf]
  refine ⟨fun n ↦ t (Nat.unpair n).1 ⊔ u (Nat.unpair n).2, fun n ↦ ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpair n).2)
  · rw [iInf_unpair (f := (fun n m ↦ t n ⊔ u m)), iInf_prod']
