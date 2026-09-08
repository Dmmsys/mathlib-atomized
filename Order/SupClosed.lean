/-
Copyright (c) 2023 Yaël Dillies, Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
module

public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Closure
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Sets closed under join/meet

This file defines predicates for sets closed under `⊔` and shows that each set in a join-semilattice
generates a join-closed set and that a semilattice where every directed set has a least upper bound
is automatically complete. All dually for `⊓`.

## Main declarations

* `SupClosed`: Predicate for a set to be closed under join (`a ∈ s` and `b ∈ s` imply `a ⊔ b ∈ s`).
* `InfClosed`: Predicate for a set to be closed under meet (`a ∈ s` and `b ∈ s` imply `a ⊓ b ∈ s`).
* `IsSublattice`: Predicate for a set to be closed under meet and join.
* `supClosure`: Sup-closure. Smallest sup-closed set containing a given set.
* `infClosure`: Inf-closure. Smallest inf-closed set containing a given set.
* `latticeClosure`: Smallest sublattice containing a given set.
* `SemilatticeSup.toCompleteSemilatticeSup`: A join-semilattice where every sup-closed set has a
  least upper bound is automatically complete.
* `SemilatticeInf.toCompleteSemilatticeInf`: A meet-semilattice where every inf-closed set has a
  greatest lower bound is automatically complete.
-/

@[expose] public section

variable {ι : Sort*} {F α β : Type*}

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β]

section Set
variable {ι : Sort*} {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}
open Set

/-- A set `s` is *sup-closed* if `a ⊔ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
@[to_dual /-- A set `s` is *inf-closed* if `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/]
/-
**SupClosed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SupClosed (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is *sup-closed* if `a ⊔ b ∈ s` for all `a ∈ s`, `b ∈ s`.
-/
def SupClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊔ b ∈ s
/-
**supClosed_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : SemilatticeSup α], SupClosed ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[to_dual (attr := simp)] lemma supClosed_empty : SupClosed (∅ : Set α) := by simp [SupClosed]
/-
**supClosed_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : SemilatticeSup α] {a : α}, SupClosed {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
@[to_dual (attr := simp)] lemma supClosed_singleton : SupClosed ({a} : Set α) := by simp [SupClosed]
/-
**supClosed_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : SemilatticeSup α], SupClosed Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[to_dual (attr := simp)] lemma supClosed_univ : SupClosed (univ : Set α) := by simp [SupClosed]

@[to_dual]
/-
**SupClosed.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.inter (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s inter
 t)
参数：hs : SupClosed s；ht : SupClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma SupClosed.inter (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ∩ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

@[to_dual]
/-
**supClosed_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosed_sInter (hS : forall s in S, SupClosed s) : SupClosed (⋂₀ S)
参数：hS : forall s in S, SupClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma supClosed_sInter (hS : ∀ s ∈ S, SupClosed s) : SupClosed (⋂₀ S) :=
  fun _a ha _b hb _s hs ↦ hS _ hs (ha _ hs) (hb _ hs)

@[to_dual]
/-
**supClosed_iInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosed_iInter (hf : forall i, SupClosed (f i)) : SupClosed (⋂ i, f i)
参数：hf : forall i, SupClosed (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `supClosed_sInter`：supClosed_sInter (hS : forall s in S, SupClosed s) : S
upClosed (⋂₀ S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
lemma supClosed_iInter (hf : ∀ i, SupClosed (f i)) : SupClosed (⋂ i, f i) :=
  supClosed_sInter <| forall_mem_range.2 hf

@[to_dual InfClosed.codirectedOn]
/-
**SupClosed.directedOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.directedOn (hs : SupClosed s) : DirectedOn (· <= ·) s
参数：hs : SupClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma SupClosed.directedOn (hs : SupClosed s) : DirectedOn (· ≤ ·) s :=
  fun _a ha _b hb ↦ ⟨_, hs ha hb, le_sup_left, le_sup_right⟩

@[to_dual]
/-
**IsUpperSet.supClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.supClosed (hs : IsUpperSet s) : SupClosed s
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma IsUpperSet.supClosed (hs : IsUpperSet s) : SupClosed s := fun _a _ _b ↦ hs le_sup_right

@[to_dual]
/-
**SupClosed.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.preimage [FunLike F β α] [SupHomClass F β α] (hs : SupClosed s) 
(f : F) : SupClosed (f ⁻¹' s)
参数：hs : SupClosed s；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
-/
lemma SupClosed.preimage [FunLike F β α] [SupHomClass F β α] (hs : SupClosed s) (f : F) :
    SupClosed (f ⁻¹' s) :=
  fun a ha b hb ↦ by simpa [map_sup] using hs ha hb

@[to_dual]
/-
**SupClosed.image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.image [FunLike F α β] [SupHomClass F α β] (hs : SupClosed s) (f 
: F) : SupClosed (f '' s)
参数：hs : SupClosed s；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma SupClosed.image [FunLike F α β] [SupHomClass F α β] (hs : SupClosed s) (f : F) :
    SupClosed (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_sup]
  exact Set.mem_image_of_mem _ <| hs ha hb

@[to_dual]
/-
**supClosed_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosed_range [FunLike F α β] [SupHomClass F α β] (f : F) : SupClosed (S
et.range f)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `SupClosed.image`：SupClosed.image [FunLike F α β] [SupHomClass F α β] (hs
 : SupClosed s) (f : F) : SupClosed (f '' s)
· 使用定理 `supClosed_univ`：∀ {α : Type u_3} [inst : SemilatticeSup α], SupClosed Se
t.univ
-/
lemma supClosed_range [FunLike F α β] [SupHomClass F α β] (f : F) : SupClosed (Set.range f) := by
  simpa using supClosed_univ.image f

@[to_dual]
/-
**SupClosed.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.prod {t : Set β} (hs : SupClosed s) (ht : SupClosed t) : SupClos
ed (s ×ˢ t)
参数：hs : SupClosed s；ht : SupClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma SupClosed.prod {t : Set β} (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ×ˢ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

@[to_dual]
/-
**supClosed_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosed_pi {ι : Type*} {α : ι -> Type*} [forall i, SemilatticeSup (α i)]
 {s : Set ι} {t : forall i, Set (α i)} (ht : forall i in s, SupClosed (t i)) : S
upClosed (s.pi t)
参数：α i；α i；ht : forall i in s, SupClosed (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma supClosed_pi {ι : Type*} {α : ι → Type*} [∀ i, SemilatticeSup (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, SupClosed (t i)) : SupClosed (s.pi t) :=
  fun _a ha _b hb _i hi ↦ ht _ hi (ha _ hi) (hb _ hi)

@[to_dual]
/-
**SupClosed.insert_upperBounds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.insert_upperBounds {s : Set α} {a : α} (hs : SupClosed s) (ha : 
a in upperBounds s) : SupClosed (insert a s)
参数：hs : SupClosed s；ha : a in upperBounds s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SupClosed.eq_1`：∀ {α : Type u_3} [inst : SemilatticeSup α] (s : Set α), 
SupClosed s = ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → a ⊔ b ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma SupClosed.insert_upperBounds {s : Set α} {a : α} (hs : SupClosed s) (ha : a ∈ upperBounds s) :
    SupClosed (insert a s) := by
  rw [SupClosed]
  aesop

@[to_dual]
/-
**SupClosed.insert_lowerBounds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.insert_lowerBounds {s : Set α} {a : α} (h : SupClosed s) (ha : a
 in lowerBounds s) : SupClosed (insert a s)
参数：h : SupClosed s；ha : a in lowerBounds s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SupClosed.eq_1`：∀ {α : Type u_3} [inst : SemilatticeSup α] (s : Set α), 
SupClosed s = ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → a ⊔ b ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma SupClosed.insert_lowerBounds {s : Set α} {a : α} (h : SupClosed s) (ha : a ∈ lowerBounds s) :
    SupClosed (insert a s) := by
  rw [SupClosed]
  have ha' : ∀ b ∈ s, a ≤ b := fun _ a ↦ ha a
  aesop

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

@[to_dual]
/-
**SupClosed.finsetSup'_mem** 是 Mathlib 中的一个定理，位于命名空间 `SupClosed`。
形式化陈述：∀ {α : Type u_3} [inst : SemilatticeSup α] {ι : Type u_5} {f : ι → α} {s :
 Set α} {t : Finset ι},   SupClosed s → ∀ (ht : t.Nonempty), (∀ i ∈ t, f i ∈ s) 
→ t.sup' ht f ∈ s
参数：ht : t.Nonempty；∀ i ∈ t, f i ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_induction`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatti
ceSup α] {s : Finset β} (H : s.Nonempty) (f : β → α) {p : α → Prop},   (∀ (a₁ : 
α), p a₁ → …
-/
lemma SupClosed.finsetSup'_mem (hs : SupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s :=
  sup'_induction _ _ hs

@[to_dual]
/-
**SupClosed.finsetSup_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.finsetSup_mem [OrderBot α] (hs : SupClosed s) (ht : t.Nonempty) 
: (forall i in t, f i in s) -> t.sup f in s
参数：hs : SupClosed s；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `SupClosed.finsetSup'_mem`：∀ {α : Type u_3} [inst : SemilatticeSup α] {ι 
: Type u_5} {f : ι → α} {s : Set α} {t : Finset ι},   SupClosed s → ∀ (ht : t.No
nempty), (∀ i …
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
-/
lemma SupClosed.finsetSup_mem [OrderBot α] (hs : SupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup f ∈ s :=
  sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

end Finset
end SemilatticeSup

open Finset OrderDual

section Lattice
variable {ι : Sort*} [Lattice α] [Lattice β] {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}

open Set

/-- A set `s` is a *sublattice* if `a ⊔ b ∈ s` and `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`.
Note: This is not the preferred way to declare a sublattice. One should instead use `Sublattice`.
TODO: Define `Sublattice`. -/
/-
**IsSublattice** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：IsSublattice (s : Set α) : Prop where supClosed : SupClosed s infClosed : 
InfClosed s  attribute [to_dual existing] IsSublattice.infClosed attribute [to_d
ual self (reorder
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is a *sublattice* if `a ⊔ b ∈ s` and `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈
 s`.
Note: This is not the preferred way to declare a sublattice. One should instead 
use `Sublattice`.
TODO: Define `Sublattice`.
-/
structure IsSublattice (s : Set α) : Prop where
  supClosed : SupClosed s
  infClosed : InfClosed s

attribute [to_dual existing] IsSublattice.infClosed
attribute [to_dual self (reorder := supClosed infClosed)] IsSublattice.mk
/-
**isSublattice_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α], IsSublattice ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supClosed_empty`：∀ {α : Type u_3} [inst : SemilatticeSup α], SupClosed ∅
· 使用定理 `infClosed_empty`：∀ {α : Type u_3} [inst : SemilatticeInf α], InfClosed ∅
-/
@[simp] lemma isSublattice_empty : IsSublattice (∅ : Set α) := ⟨supClosed_empty, infClosed_empty⟩
/-
**isSublattice_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] {a : α}, IsSublattice {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supClosed_singleton`：∀ {α : Type u_3} [inst : SemilatticeSup α] {a : α},
 SupClosed {a}
· 使用定理 `infClosed_singleton`：∀ {α : Type u_3} [inst : SemilatticeInf α] {a : α},
 InfClosed {a}
-/
@[simp] lemma isSublattice_singleton : IsSublattice ({a} : Set α) :=
  ⟨supClosed_singleton, infClosed_singleton⟩
/-
**isSublattice_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α], IsSublattice Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supClosed_univ`：∀ {α : Type u_3} [inst : SemilatticeSup α], SupClosed Se
t.univ
· 使用定理 `infClosed_univ`：∀ {α : Type u_3} [inst : SemilatticeInf α], InfClosed Se
t.univ
-/
@[simp] lemma isSublattice_univ : IsSublattice (Set.univ : Set α) :=
  ⟨supClosed_univ, infClosed_univ⟩
/-
**IsSublattice.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSublattice.inter (hs : IsSublattice s) (ht : IsSublattice t) : IsSublatt
ice (s inter t)
参数：hs : IsSublattice s；ht : IsSublattice t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SupClosed.inter`：SupClosed.inter (hs : SupClosed s) (ht : SupClosed t) :
 SupClosed (s inter t)
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `InfClosed.inter`：∀ {α : Type u_3} [inst : SemilatticeInf α] {s t : Set α
}, InfClosed s → InfClosed t → InfClosed (s ∩ t)
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
-/
lemma IsSublattice.inter (hs : IsSublattice s) (ht : IsSublattice t) : IsSublattice (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
/-
**isSublattice_sInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSublattice_sInter (hS : forall s in S, IsSublattice s) : IsSublattice (⋂
₀ S)
参数：hS : forall s in S, IsSublattice s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `supClosed_sInter`：supClosed_sInter (hS : forall s in S, SupClosed s) : S
upClosed (⋂₀ S)
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `infClosed_sInter`：∀ {α : Type u_3} [inst : SemilatticeInf α] {S : Set (S
et α)}, (∀ s ∈ S, InfClosed s) → InfClosed (⋂₀ S)
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
-/
lemma isSublattice_sInter (hS : ∀ s ∈ S, IsSublattice s) : IsSublattice (⋂₀ S) :=
  ⟨supClosed_sInter fun _s hs ↦ (hS _ hs).1, infClosed_sInter fun _s hs ↦ (hS _ hs).2⟩
/-
**isSublattice_iInter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSublattice_iInter (hf : forall i, IsSublattice (f i)) : IsSublattice (⋂ 
i, f i)
参数：hf : forall i, IsSublattice (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `supClosed_iInter`：supClosed_iInter (hf : forall i, SupClosed (f i)) : Su
pClosed (⋂ i, f i)
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `infClosed_iInter`：∀ {α : Type u_3} [inst : SemilatticeInf α] {ι : Sort u
_5} {f : ι → Set α},   (∀ (i : ι), InfClosed (f i)) → InfClosed (⋂ i, f i)
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
-/
lemma isSublattice_iInter (hf : ∀ i, IsSublattice (f i)) : IsSublattice (⋂ i, f i) :=
  ⟨supClosed_iInter fun _i ↦ (hf _).1, infClosed_iInter fun _i ↦ (hf _).2⟩
/-
**IsSublattice.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSublattice.preimage [FunLike F β α] [LatticeHomClass F β α] (hs : IsSubl
attice s) (f : F) : IsSublattice (f ⁻¹' s)
参数：hs : IsSublattice s；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SupClosed.preimage`：SupClosed.preimage [FunLike F β α] [SupHomClass F β 
α] (hs : SupClosed s) (f : F) : SupClosed (f ⁻¹' s)
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `InfClosed.preimage`：∀ {F : Type u_2} {α : Type u_3} {β : Type u_4} [inst
 : SemilatticeInf α] [inst_1 : SemilatticeInf β] {s : Set α}   [inst_2 : FunLike
 F β α] …
· 使用定理 `LatticeHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
-/
lemma IsSublattice.preimage [FunLike F β α] [LatticeHomClass F β α]
    (hs : IsSublattice s) (f : F) :
    IsSublattice (f ⁻¹' s) := ⟨hs.1.preimage _, hs.2.preimage _⟩
/-
**IsSublattice.image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSublattice.image [FunLike F α β] [LatticeHomClass F α β] (hs : IsSublatt
ice s) (f : F) : IsSublattice (f '' s)
参数：hs : IsSublattice s；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SupClosed.image`：SupClosed.image [FunLike F α β] [SupHomClass F α β] (hs
 : SupClosed s) (f : F) : SupClosed (f '' s)
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `InfClosed.image`：∀ {F : Type u_2} {α : Type u_3} {β : Type u_4} [inst : 
SemilatticeInf α] [inst_1 : SemilatticeInf β] {s : Set α}   [inst_2 : FunLike F 
α β] …
· 使用定理 `LatticeHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
-/
lemma IsSublattice.image [FunLike F α β] [LatticeHomClass F α β] (hs : IsSublattice s) (f : F) :
    IsSublattice (f '' s) := ⟨hs.1.image _, hs.2.image _⟩
/-
**IsSublattice_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSublattice_range [FunLike F α β] [LatticeHomClass F α β] (f : F) : IsSub
lattice (Set.range f)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `supClosed_range`：supClosed_range [FunLike F α β] [SupHomClass F α β] (f 
: F) : SupClosed (Set.range f)
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `infClosed_range`：∀ {F : Type u_2} {α : Type u_3} {β : Type u_4} [inst : 
SemilatticeInf α] [inst_1 : SemilatticeInf β]   [inst_2 : FunLike F α β] [InfHom
Class…
· 使用定理 `LatticeHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
-/
lemma IsSublattice_range [FunLike F α β] [LatticeHomClass F α β] (f : F) :
    IsSublattice (Set.range f) :=
  ⟨supClosed_range _, infClosed_range _⟩
/-
**IsSublattice.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSublattice.prod {t : Set β} (hs : IsSublattice s) (ht : IsSublattice t) 
: IsSublattice (s ×ˢ t)
参数：hs : IsSublattice s；ht : IsSublattice t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SupClosed.prod`：SupClosed.prod {t : Set β} (hs : SupClosed s) (ht : SupC
losed t) : SupClosed (s ×ˢ t)
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `InfClosed.prod`：∀ {α : Type u_3} {β : Type u_4} [inst : SemilatticeInf α
] [inst_1 : SemilatticeInf β] {s : Set α} {t : Set β},   InfClosed s → InfClosed
 t →…
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
-/
lemma IsSublattice.prod {t : Set β} (hs : IsSublattice s) (ht : IsSublattice t) :
    IsSublattice (s ×ˢ t) := ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
/-
**isSublattice_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSublattice_pi {ι : Type*} {α : ι -> Type*} [forall i, Lattice (α i)] {s 
: Set ι} {t : forall i, Set (α i)} (ht : forall i in s, IsSublattice (t i)) : Is
Sublattice (s.pi t)
参数：α i；α i；ht : forall i in s, IsSublattice (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `supClosed_pi`：supClosed_pi {ι : Type*} {α : ι -> Type*} [forall i, Semil
atticeSup (α i)] {s : Set ι} {t : forall i, Set (α i)} (ht : forall i in s, SupC
lo…
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `infClosed_pi`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : (i : ι) → Semi
latticeInf (α i)] {s : Set ι} {t : (i : ι) → Set (α i)},   (∀ i ∈ s, InfClosed (
t …
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
-/
lemma isSublattice_pi {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, IsSublattice (t i)) : IsSublattice (s.pi t) :=
  ⟨supClosed_pi fun _i hi ↦ (ht _ hi).1, infClosed_pi fun _i hi ↦ (ht _ hi).2⟩
/-
**supClosed_preimage_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] {s : Set αᵒᵈ}, SupClosed (⇑OrderDual.t
oDual ⁻¹' s) ↔ InfClosed s
参数：⇑OrderDual.toDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_dual (attr := simp)] lemma supClosed_preimage_toDual {s : Set αᵒᵈ} :
    SupClosed (toDual ⁻¹' s) ↔ InfClosed s := Iff.rfl
/-
**supClosed_preimage_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, SupClosed (⇑OrderDual.ofD
ual ⁻¹' s) ↔ InfClosed s
参数：⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_dual (attr := simp)] lemma supClosed_preimage_ofDual {s : Set α} :
    SupClosed (ofDual ⁻¹' s) ↔ InfClosed s := Iff.rfl
/-
**isSublattice_preimage_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] {s : Set αᵒᵈ}, IsSublattice (⇑OrderDua
l.toDual ⁻¹' s) ↔ IsSublattice s
参数：⇑OrderDual.toDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
-/
@[simp] lemma isSublattice_preimage_toDual {s : Set αᵒᵈ} :
    IsSublattice (toDual ⁻¹' s) ↔ IsSublattice s := ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
/-
**isSublattice_preimage_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, IsSublattice (⇑OrderDual.
ofDual ⁻¹' s) ↔ IsSublattice s
参数：⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
-/
@[simp] lemma isSublattice_preimage_ofDual :
    IsSublattice (ofDual ⁻¹' s) ↔ IsSublattice s := ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

@[to_dual] alias ⟨_, InfClosed.dual⟩ := supClosed_preimage_ofDual
alias ⟨_, IsSublattice.dual⟩ := isSublattice_preimage_ofDual
alias ⟨_, IsSublattice.of_dual⟩ := isSublattice_preimage_toDual

end Lattice

section LinearOrder
variable [LinearOrder α]

/-
**LinearOrder.supClosed** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrder`。
形式化陈述：∀ {α : Type u_3} [inst : LinearOrder α] (s : Set α), SupClosed s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
@[to_dual (attr := simp)] protected lemma LinearOrder.supClosed (s : Set α) : SupClosed s :=
  fun a ha b hb ↦ by cases le_total a b <;> simp [*]
/-
**LinearOrder.isSublattice** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrder`。
形式化陈述：∀ {α : Type u_3} [inst : LinearOrder α] (s : Set α), IsSublattice s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrder.supClosed`：∀ {α : Type u_3} [inst : LinearOrder α] (s : Set 
α), SupClosed s
· 使用定理 `LinearOrder.infClosed`：∀ {α : Type u_3} [inst : LinearOrder α] (s : Set 
α), InfClosed s
-/
@[simp] protected lemma LinearOrder.isSublattice (s : Set α) : IsSublattice s :=
  ⟨LinearOrder.supClosed _, LinearOrder.infClosed _⟩

end LinearOrder

/-! ## Closure -/

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] {s t : Set α} {a b : α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[to_dual (attr := simps! isClosed)
/-- Every set in a meet-semilattice generates a set closed under meet. -/]
/-
**supClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：supClosure : ClosureOperator (Set α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
-/
def supClosure : ClosureOperator (Set α) := .ofPred
  (fun s ↦ {a | ∃ (t : Finset α) (ht : t.Nonempty), ↑t ⊆ s ∧ t.sup' ht id = a})
  SupClosed
  (fun s a ha ↦ ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine ⟨_, ht.mono subset_union_left, ?_, sup'_union ht hu _⟩
    rw [coe_union]
    exact Set.union_subset hts hus)
  (by rintro s₁ s₂ hs h₂ _ ⟨t, ht, hts, rfl⟩; exact h₂.finsetSup'_mem ht fun i hi ↦ hs <| hts hi)

@[to_dual (attr := simp)]
/-
**subset_supClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subset_supClosure {s : Set α} : s subseteq supClosure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
lemma subset_supClosure {s : Set α} : s ⊆ supClosure s := supClosure.le_closure _

@[to_dual (attr := simp)]
/-
**supClosed_supClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosed_supClosure : SupClosed (supClosure s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
lemma supClosed_supClosure : SupClosed (supClosure s) := supClosure.isClosed_closure _

@[to_dual]
/-
**supClosure_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosure_mono : Monotone (supClosure : Set α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
lemma supClosure_mono : Monotone (supClosure : Set α → Set α) := supClosure.monotone

@[to_dual (attr := simp)]
/-
**supClosure_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosure_eq_self : supClosure s = s ↔ SupClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
-/
lemma supClosure_eq_self : supClosure s = s ↔ SupClosed s := supClosure.isClosed_iff.symm

@[to_dual] alias ⟨_, SupClosed.supClosure_eq⟩ := supClosure_eq_self

@[to_dual]
/-
**supClosure_idem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosure_idem (s : Set α) : supClosure (supClosure s) = supClosure s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
-/
lemma supClosure_idem (s : Set α) : supClosure (supClosure s) = supClosure s :=
  supClosure.idempotent _
/-
**supClosure_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : SemilatticeSup α], supClosure ∅ = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_dual (attr := simp)] lemma supClosure_empty : supClosure (∅ : Set α) = ∅ := by simp
/-
**supClosure_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : SemilatticeSup α] {a : α}, supClosure {a} = {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_dual (attr := simp)] lemma supClosure_singleton : supClosure {a} = {a} := by simp
@[to_dual (attr := simp)]
/-
**supClosure_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosure_univ : supClosure (Set.univ : Set α) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma supClosure_univ : supClosure (Set.univ : Set α) = Set.univ := by simp

@[to_dual (attr := simp)]
/-
**upperBounds_supClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperBounds_supClosure (s : Set α) : upperBounds (supClosure s) = upperBou
nds s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
-/
lemma upperBounds_supClosure (s : Set α) : upperBounds (supClosure s) = upperBounds s :=
  (upperBounds_mono_set subset_supClosure).antisymm <| by
    rintro a ha _ ⟨t, ht, hts, rfl⟩
    exact sup'_le _ _ fun b hb ↦ ha <| hts hb

@[to_dual (attr := simp)]
/-
**isLUB_supClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLUB_supClosure : IsLUB (supClosure s) a ↔ IsLUB s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperBounds_supClosure`：upperBounds_supClosure (s : Set α) : upperBounds
 (supClosure s) = upperBounds s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isLUB_supClosure : IsLUB (supClosure s) a ↔ IsLUB s a := by simp [IsLUB]

@[to_dual]
/-
**sup_mem_supClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_mem_supClosure (ha : a in s) (hb : b in s) : a ⊔ b in supClosure s
参数：ha : a in s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `supClosed_supClosure`：supClosed_supClosure : SupClosed (supClosure s)
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
-/
lemma sup_mem_supClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊔ b ∈ supClosure s :=
  supClosed_supClosure (subset_supClosure ha) (subset_supClosure hb)

@[to_dual]
/-
**finsetSup'_mem_supClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : SemilatticeSup α] {s : Set α} {ι : Type u_5} {t :
 Finset ι} (ht : t.Nonempty) {f : ι → α},   (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s
upClosure s
参数：ht : t.Nonempty；∀ i ∈ t, f i ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupClosed.finsetSup'_mem`：∀ {α : Type u_3} [inst : SemilatticeSup α] {ι 
: Type u_5} {f : ι → α} {s : Set α} {t : Finset ι},   SupClosed s → ∀ (ht : t.No
nempty), (∀ i …
· 使用引理 `supClosed_supClosure`：supClosed_supClosure : SupClosed (supClosure s)
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
-/
lemma finsetSup'_mem_supClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.sup' ht f ∈ supClosure s :=
  supClosed_supClosure.finsetSup'_mem _ fun _i hi ↦ subset_supClosure <| hf _ hi

@[to_dual infClosure_min]
/-
**supClosure_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosure_min : s subseteq t -> SupClosed t -> supClosure s subseteq t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
-/
lemma supClosure_min : s ⊆ t → SupClosed t → supClosure s ⊆ t := supClosure.closure_min

/-- The semilattice generated by a finite set is finite. -/
@[to_dual /-- The semilattice generated by a finite set is finite. -/]
/-
**Set.Finite.supClosure** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_3} [inst : SemilatticeSup α] {s : Set α}, s.Finite → (supClo
sure s).Finite
参数：supClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯

--- 原说明 ---
The semilattice generated by a finite set is finite.
-/
protected lemma Set.Finite.supClosure (hs : s.Finite) : (supClosure s).Finite := by
  lift s to Finset α using hs
  classical
  refine ({t ∈ s.powerset | t.Nonempty}.attach.image
    fun t ↦ t.1.sup' (mem_filter.1 t.2).2 id).finite_toSet.subset ?_
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.mem_powerset, mem_filter]
  exact ⟨t, ⟨hts, ht⟩, rfl⟩
/-
**supClosure_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : SemilatticeSup α] [inst_1 : Semila
tticeSup β] (s : Set α) (t : Set β),   supClosure (s ×ˢ t) = supClosure s ×ˢ sup
Closure t
参数：s : Set α；t : Set β；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `supClosure_min`：supClosure_min : s subseteq t -> SupClosed t -> supClosu
re s subseteq t
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
· 使用引理 `SupClosed.prod`：SupClosed.prod {t : Set β} (hs : SupClosed s) (ht : SupC
losed t) : SupClosed (s ×ˢ t)
· 使用引理 `supClosed_supClosure`：supClosed_supClosure : SupClosed (supClosure s)
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.product`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.prodMk_sup'_sup'`：∀ {ι : Type u_7} {κ : Type u_8} {α : Type u_9} 
{β : Type u_10} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   {s : Fin
set ι} {t : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_dual (attr := simp)] lemma supClosure_prod (s : Set α) (t : Set β) :
    supClosure (s ×ˢ t) = supClosure s ×ˢ supClosure t :=
  le_antisymm (supClosure_min (Set.prod_mono subset_supClosure subset_supClosure) <|
    supClosed_supClosure.prod supClosed_supClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prodMk_sup'_sup']

end SemilatticeSup

section Lattice
variable [Lattice α] [Lattice β] {s t : Set α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[simps! isClosed]
/-
**latticeClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：latticeClosure : ClosureOperator (Set α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `isSublattice_sInter`：isSublattice_sInter (hS : forall s in S, IsSublatti
ce s) : IsSublattice (⋂₀ S)

--- 原说明 ---
Every set in a join-semilattice generates a set closed under join.
-/
def latticeClosure : ClosureOperator (Set α) :=
  .ofCompletePred IsSublattice fun _ ↦ isSublattice_sInter
/-
**subset_latticeClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, s ⊆ latticeClosure s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
@[simp] lemma subset_latticeClosure : s ⊆ latticeClosure s := latticeClosure.le_closure _
/-
**isSublattice_latticeClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, IsSublattice (latticeClos
ure s)
参数：latticeClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
@[simp] lemma isSublattice_latticeClosure : IsSublattice (latticeClosure s) :=
  latticeClosure.isClosed_closure _
/-
**latticeClosure_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：latticeClosure_min : s subseteq t -> IsSublattice t -> latticeClosure s su
bseteq t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
-/
lemma latticeClosure_min : s ⊆ t → IsSublattice t → latticeClosure s ⊆ t :=
  latticeClosure.closure_min

@[to_dual self (reorder := sup inf)]
/-
**latticeClosure_sup_inf_induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：latticeClosure_sup_inf_induction (p : (a : α) -> a in latticeClosure s -> 
Prop) (mem : forall (a : α) (has : a in s), p a (subset_latticeClosure has)) (su
p : forall (a : α) (has : a in latticeClosure s) (b : α) (hbs : b in latticeClos
ure s), p a has -> p b hbs -> p (a ⊔ b) (isSublattice_latticeClosure.supClosed h
as hbs)) (inf : forall (a : α) (has : a in latticeClosure s) (b : α) (hbs : b in
 latticeClosure s), p a has -> p b hbs -> p (a ⊓ b) (isSublattice_latticeClosure
.infClosed has hbs)) {a : 
参数：p : (a : α) -> a in latticeClosure s -> Prop；mem : forall (a : α) (has : a in
 s), p a (subset_latticeClosure has)；sup : forall (a : α) (has : a in latticeClo
sure s) (b : α) (hbs : b in latticeClosure s), p a has -> p b hbs -> p (a ⊔ b) (
isSublattice_latticeClosure.supClosed has hbs)；inf : forall (a : α) (has : a in 
latticeClosure s) (b : α) (hbs : b in latticeClosure s), p a has -> p b hbs -> p
 (a ⊓ b) (isSublattice_latticeClosure.infClosed has hbs)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, 
s ⊆ latticeClosure s
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `isSublattice_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Se
t α}, IsSublattice (latticeClosure s)
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `latticeClosure_min`：latticeClosure_min : s subseteq t -> IsSublattice t 
-> latticeClosure s subseteq t
-/
lemma latticeClosure_sup_inf_induction (p : (a : α) → a ∈ latticeClosure s → Prop)
    (mem : ∀ (a : α) (has : a ∈ s), p a (subset_latticeClosure has))
    (sup : ∀ (a : α) (has : a ∈ latticeClosure s) (b : α) (hbs : b ∈ latticeClosure s),
      p a has → p b hbs → p (a ⊔ b) (isSublattice_latticeClosure.supClosed has hbs))
    (inf : ∀ (a : α) (has : a ∈ latticeClosure s) (b : α) (hbs : b ∈ latticeClosure s),
      p a has → p b hbs → p (a ⊓ b) (isSublattice_latticeClosure.infClosed has hbs))
    {a : α} (has : a ∈ latticeClosure s) :
    p a has := by
  have h : IsSublattice { a : α | ∃ has : a ∈ latticeClosure s, p a has } := {
    supClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosure.supClosed has hbs, sup a has b hbs hpa hpb⟩
    infClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosure.infClosed has hbs, inf a has b hbs hpa hpb⟩ }
  refine (latticeClosure_min (fun a ha ↦ ?_) h has).choose_spec
  exact ⟨subset_latticeClosure ha, mem a ha⟩
/-
**latticeClosure_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：latticeClosure_mono : Monotone (latticeClosure : Set α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
lemma latticeClosure_mono : Monotone (latticeClosure : Set α → Set α) := latticeClosure.monotone
/-
**latticeClosure_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, latticeClosure s = s ↔ Is
Sublattice s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
-/
@[simp] lemma latticeClosure_eq_self : latticeClosure s = s ↔ IsSublattice s :=
  latticeClosure.isClosed_iff.symm

alias ⟨_, IsSublattice.latticeClosure_eq⟩ := latticeClosure_eq_self
/-
**latticeClosure_idem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：latticeClosure_idem (s : Set α) : latticeClosure (latticeClosure s) = latt
iceClosure s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
-/
lemma latticeClosure_idem (s : Set α) : latticeClosure (latticeClosure s) = latticeClosure s :=
  latticeClosure.idempotent _
/-
**latticeClosure_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α], latticeClosure ∅ = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma latticeClosure_empty : latticeClosure (∅ : Set α) = ∅ := by simp
/-
**latticeClosure_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α] (a : α), latticeClosure {a} = {a}
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma latticeClosure_singleton (a : α) : latticeClosure {a} = {a} := by simp
/-
**latticeClosure_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} [inst : Lattice α], latticeClosure Set.univ = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma latticeClosure_univ : latticeClosure (Set.univ : Set α) = Set.univ := by simp

@[to_dual self (reorder := map_sup map_inf)]
/-
**image_latticeClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：image_latticeClosure (s : Set α) (f : α -> β) (map_sup : forall a b, f (a 
⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b) : f '' latticeCl
osure s = latticeClosure (f '' s)
参数：s : Set α；f : α -> β；map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b；map_inf : fo
rall a b, f (a ⊓ b) = f a ⊓ f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `latticeClosure_sup_inf_induction`：latticeClosure_sup_inf_induction (p : 
(a : α) -> a in latticeClosure s -> Prop) (mem : forall (a : α) (has : a in s), 
p a (subset_latticeClo…
· 使用定理 `subset_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, 
s ⊆ latticeClosure s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `isSublattice_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Se
t α}, IsSublattice (latticeClosure s)
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma image_latticeClosure (s : Set α) (f : α → β)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    f '' latticeClosure s = latticeClosure (f '' s) := by
  simp only [subset_antisymm_iff, Set.image_subset_iff]
  constructor <;> apply latticeClosure_sup_inf_induction
  · exact fun a ha ↦ subset_latticeClosure <| Set.mem_image_of_mem _ ha
  · rintro a - b - ha hb
    simpa [map_sup] using isSublattice_latticeClosure.supClosed ha hb
  · rintro a - b - ha hb
    simpa [map_inf] using isSublattice_latticeClosure.infClosed ha hb
  · exact Set.image_mono subset_latticeClosure
  · rintro _ - _ - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ⊔ b, isSublattice_latticeClosure.supClosed ha hb, map_sup ..⟩
  · rintro _ - _ - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ⊓ b, isSublattice_latticeClosure.infClosed ha hb, map_inf ..⟩

set_option backward.isDefEq.respectTransparency false in
/-
**ofDual_preimage_latticeClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ofDual_preimage_latticeClosure (s : Set α) : ofDual ⁻¹' latticeClosure s =
 latticeClosure (ofDual ⁻¹' s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ClosureOperator.ofCompletePred_apply`：∀ {α : Type u_1} [inst : CompleteL
attice α] (p : α → Prop) (hsinf : ∀ (s : Set α), (∀ a ∈ s, p a) → p (sInf s)) (a
 : α),   (ClosureOperator.…
· 使用引理 `isSublattice_sInter`：isSublattice_sInter (hS : forall s in S, IsSublatti
ce s) : IsSublattice (⋂₀ S)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Set.congr_apply`：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s : 
Set α), (Equiv.Set.congr e) s = ⇑e '' s
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofDual_preimage_latticeClosure (s : Set α) :
    ofDual ⁻¹' latticeClosure s = latticeClosure (ofDual ⁻¹' s) := by
  ext
  simp [latticeClosure, (Equiv.Set.congr toDual).surjective.forall, Equiv.image_eq_preimage_symm]

@[to_dual self (reorder := map_sup map_inf)]
/-
**image_latticeClosure'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：image_latticeClosure' (s : Set α) (f : α -> β) (map_sup : forall a b, f (a
 ⊔ b) = f a ⊓ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊔ f b) : f '' latticeC
losure s = latticeClosure (f '' s)
参数：s : Set α；f : α -> β；map_sup : forall a b, f (a ⊔ b) = f a ⊓ f b；map_inf : fo
rall a b, f (a ⊓ b) = f a ⊔ f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
· 使用引理 `image_latticeClosure`：image_latticeClosure (s : Set α) (f : α -> β) (map
_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a
 ⊓ f b) : …
-/
lemma image_latticeClosure' (s : Set α) (f : α → β)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊓ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊔ f b) :
    f '' latticeClosure s = latticeClosure (f '' s) := by
  simpa only [Set.image_comp, Equiv.image_symm_eq_preimage, ← ofDual_preimage_latticeClosure]
    using! image_latticeClosure s (ofDual.symm ∘ f) map_sup map_inf

end Lattice

section DistribLattice
variable [DistribLattice α] [DistribLattice β] {s : Set α}

@[to_dual]
/-
**SupClosed.infClosure** 是 Mathlib 中的一个定理，位于命名空间 `SupClosed`。
形式化陈述：∀ {α : Type u_3} [inst : DistribLattice α] {s : Set α}, SupClosed s → SupC
losed (infClosure s)
参数：infClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.product`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf'_sup_inf'`：∀ {α : Type u_2} {ι : Type u_5} {κ : Type u_6} [in
st : DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty)   (ht : t
.Nonempty)…
· 使用定理 `finsetInf'_mem_infClosure`：∀ {α : Type u_3} [inst : SemilatticeInf α] {s
 : Set α} {ι : Type u_5} {t : Finset ι} (ht : t.Nonempty) {f : ι → α},   (∀ i ∈ 
t, f i ∈ s) → t…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma SupClosed.infClosure (hs : SupClosed s) : SupClosed (infClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [inf'_sup_inf']
  exact finsetInf'_mem_infClosure _
    fun i hi ↦ hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

@[to_dual (attr := simp)]
/-
**supClosure_infClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：supClosure_infClosure (s : Set α) : supClosure (infClosure s) = latticeClo
sure s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `supClosure_min`：supClosure_min : s subseteq t -> SupClosed t -> supClosu
re s subseteq t
· 使用定理 `infClosure_min`：∀ {α : Type u_3} [inst : SemilatticeInf α] {s t : Set α}
, s ⊆ t → InfClosed t → infClosure s ⊆ t
· 使用定理 `subset_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, 
s ⊆ latticeClosure s
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
· 使用定理 `isSublattice_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Se
t α}, IsSublattice (latticeClosure s)
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用引理 `latticeClosure_min`：latticeClosure_min : s subseteq t -> IsSublattice t 
-> latticeClosure s subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_infClosure`：∀ {α : Type u_3} [inst : SemilatticeInf α] {s : Set α
}, s ⊆ infClosure s
· 使用引理 `subset_supClosure`：subset_supClosure {s : Set α} : s subseteq supClosure
 s
· 使用引理 `supClosed_supClosure`：supClosed_supClosure : SupClosed (supClosure s)
· 使用定理 `InfClosed.supClosure`：∀ {α : Type u_3} [inst : DistribLattice α] {s : Se
t α}, InfClosed s → InfClosed (supClosure s)
· 使用定理 `infClosed_infClosure`：∀ {α : Type u_3} [inst : SemilatticeInf α] {s : Se
t α}, InfClosed (infClosure s)
-/
lemma supClosure_infClosure (s : Set α) : supClosure (infClosure s) = latticeClosure s :=
  le_antisymm (supClosure_min (infClosure_min subset_latticeClosure isSublattice_latticeClosure.2)
    isSublattice_latticeClosure.1) <| latticeClosure_min (subset_infClosure.trans subset_supClosure)
      ⟨supClosed_supClosure, infClosed_infClosure.supClosure⟩
/-
**Set.Finite.latticeClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.latticeClosure (hs : s.Finite) : (latticeClosure s).Finite
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `supClosure_infClosure`：supClosure_infClosure (s : Set α) : supClosure (i
nfClosure s) = latticeClosure s
· 使用定理 `Set.Finite.supClosure`：∀ {α : Type u_3} [inst : SemilatticeSup α] {s : S
et α}, s.Finite → (supClosure s).Finite
· 使用定理 `Set.Finite.infClosure`：∀ {α : Type u_3} [inst : SemilatticeInf α] {s : S
et α}, s.Finite → (infClosure s).Finite
-/
lemma Set.Finite.latticeClosure (hs : s.Finite) : (latticeClosure s).Finite := by
  rw [← supClosure_infClosure]; exact hs.infClosure.supClosure
/-
**latticeClosure_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : DistribLattice α] [inst_1 : Distri
bLattice β] (s : Set α) (t : Set β),   latticeClosure (s ×ˢ t) = latticeClosure 
s ×ˢ latticeClosure t
参数：s : Set α；t : Set β；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `infClosure_prod`：∀ {α : Type u_3} {β : Type u_4} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] (s : Set α) (t : Set β),   infClosure (s ×ˢ t) = 
infCl…
· 使用定理 `supClosure_prod`：∀ {α : Type u_3} {β : Type u_4} [inst : SemilatticeSup 
α] [inst_1 : SemilatticeSup β] (s : Set α) (t : Set β),   supClosure (s ×ˢ t) = 
supCl…
· 使用引理 `supClosure_infClosure`：supClosure_infClosure (s : Set α) : supClosure (i
nfClosure s) = latticeClosure s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma latticeClosure_prod (s : Set α) (t : Set β) :
    latticeClosure (s ×ˢ t) = latticeClosure s ×ˢ latticeClosure t := by
  simp_rw [← supClosure_infClosure]; simp

end DistribLattice

/-- A join-semilattice where every sup-closed set has a least upper bound is automatically complete.
-/
@[to_dual (attr := instance_reducible) /--
A meet-semilattice where every inf-closed set has a greatest lower bound is automatically
complete. -/]
/-
**SemilatticeSup.toCompleteSemilatticeSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemilatticeSup.toCompleteSemilatticeSup [SemilatticeSup α] (sSup : Set α -
> α) (h : forall s, SupClosed s -> IsLUB s (sSup s)) : CompleteSemilatticeSup α 
where sSup
参数：sSup : Set α -> α；h : forall s, SupClosed s -> IsLUB s (sSup s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def SemilatticeSup.toCompleteSemilatticeSup [SemilatticeSup α] (sSup : Set α → α)
    (h : ∀ s, SupClosed s → IsLUB s (sSup s)) : CompleteSemilatticeSup α where
  sSup := fun s => sSup (supClosure s)
  isLUB_sSup _ := isLUB_supClosure.mp <| h _ supClosed_supClosure

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] {f : ι → α} {s t : Set α}

@[to_dual]
/-
**SupClosed.iSup_mem_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.iSup_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : SupClosed s) 
(hf : forall i, f i in s) : ⨆ i, f i in s
参数：hs : SupClosed s；hf : forall i, f i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_plift_down`：iSup_plift_down (f : ι -> α) : ⨆ i, f (PLift.down i) = 
⨆ i, f i
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `PLift.instNonempty_mathlib`：∀ {α : Sort u} [Nonempty α], Nonempty (PLift
 α)
· 使用定理 `Finset.sup'_univ_eq_ciSup`：∀ {ι : Type u_1} {α : Type u_2} [inst : Condi
tionallyCompleteLattice α] [inst_1 : Fintype ι] [inst_2 : Nonempty ι]   (f : ι →
 α), Finset.uni…
· 使用定理 `SupClosed.finsetSup'_mem`：∀ {α : Type u_3} [inst : SemilatticeSup α] {ι 
: Type u_5} {f : ι → α} {s : Set α} {t : Finset ι},   SupClosed s → ∀ (ht : t.No
nempty), (∀ i …
-/
lemma SupClosed.iSup_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : SupClosed s)
    (hf : ∀ i, f i ∈ s) : ⨆ i, f i ∈ s := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup'_univ_eq_ciSup]
  exact hs.finsetSup'_mem Finset.univ_nonempty fun _ _ ↦ hf _

@[to_dual]
/-
**SupClosed.sSup_mem_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.sSup_mem_of_nonempty (hs : SupClosed s) (ht : t.Finite) (ht' : t
.Nonempty) (hts : t subseteq s) : sSup t in s
参数：hs : SupClosed s；ht : t.Finite；ht' : t.Nonempty；hts : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用引理 `SupClosed.iSup_mem_of_nonempty`：SupClosed.iSup_mem_of_nonempty [Finite ι
] [Nonempty ι] (hs : SupClosed s) (hf : forall i, f i in s) : ⨆ i, f i in s
-/
lemma SupClosed.sSup_mem_of_nonempty (hs : SupClosed s) (ht : t.Finite) (ht' : t.Nonempty)
    (hts : t ⊆ s) : sSup t ∈ s := by
  have := ht.to_subtype
  have := ht'.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem_of_nonempty (by simpa)

end ConditionallyCompleteLattice

section BooleanAlgebra
variable [BooleanAlgebra α] {s : Set α}

/-
**compl_image_latticeClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compl_image_latticeClosure (s : Set α) : compl '' latticeClosure s = latti
ceClosure (compl '' s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `image_latticeClosure'`：image_latticeClosure' (s : Set α) (f : α -> β) (m
ap_sup : forall a b, f (a ⊔ b) = f a ⊓ f b) (map_inf : forall a b, f (a ⊓ b) = f
 a ⊔ f b) :…
· 使用定理 `compl_sup_distrib`：compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
-/
lemma compl_image_latticeClosure (s : Set α) :
    compl '' latticeClosure s = latticeClosure (compl '' s) :=
  image_latticeClosure' s _ compl_sup_distrib (fun _ _ => compl_inf)
/-
**compl_image_latticeClosure_eq_of_compl_image_eq_self** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：compl_image_latticeClosure_eq_of_compl_image_eq_self (hs : compl '' s = s)
 : compl '' latticeClosure s = latticeClosure s
参数：hs : compl '' s = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `compl_image_latticeClosure`：compl_image_latticeClosure (s : Set α) : com
pl '' latticeClosure s = latticeClosure (compl '' s)
-/
lemma compl_image_latticeClosure_eq_of_compl_image_eq_self (hs : compl '' s = s) :
    compl '' latticeClosure s = latticeClosure s :=
  compl_image_latticeClosure s ▸ hs.symm ▸ rfl

end BooleanAlgebra

variable [CompleteLattice α] {f : ι → α} {s t : Set α}

@[to_dual]
/-
**SupClosed.biSup_mem_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.biSup_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι -> α} (hs :
 SupClosed s) (ht : t.Finite) (ht' : t.Nonempty) (hf : forall i in t, f i in s) 
: ⨆ i in t, f i in s
参数：hs : SupClosed s；ht : t.Finite；ht' : t.Nonempty；hf : forall i in t, f i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用引理 `SupClosed.sSup_mem_of_nonempty`：SupClosed.sSup_mem_of_nonempty (hs : Sup
Closed s) (ht : t.Finite) (ht' : t.Nonempty) (hts : t subseteq s) : sSup t in s
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
lemma SupClosed.biSup_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι → α} (hs : SupClosed s)
    (ht : t.Finite) (ht' : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) : ⨆ i ∈ t, f i ∈ s := by
  rw [← sSup_image]
  exact hs.sSup_mem_of_nonempty (ht.image _) (by simpa) (by simpa)

@[to_dual]
/-
**SupClosed.iSup_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hbot : ⊥ in s) (hf : for
all i, f i in s) : ⨆ i, f i in s
参数：hs : SupClosed s；hbot : ⊥ in s；hf : forall i, f i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty`：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
· 使用引理 `SupClosed.iSup_mem_of_nonempty`：SupClosed.iSup_mem_of_nonempty [Finite ι
] [Nonempty ι] (hs : SupClosed s) (hf : forall i, f i in s) : ⨆ i, f i in s
-/
lemma SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hbot : ⊥ ∈ s) (hf : ∀ i, f i ∈ s) :
    ⨆ i, f i ∈ s := by
  cases isEmpty_or_nonempty ι
  · simpa [iSup_of_empty]
  · exact hs.iSup_mem_of_nonempty hf

@[to_dual]
/-
**SupClosed.sSup_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite) (hbot : ⊥ in s) (hts
 : t subseteq s) : sSup t in s
参数：hs : SupClosed s；ht : t.Finite；hbot : ⊥ in s；hts : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用引理 `SupClosed.iSup_mem`：SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hb
ot : ⊥ in s) (hf : forall i, f i in s) : ⨆ i, f i in s
-/
lemma SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite) (hbot : ⊥ ∈ s) (hts : t ⊆ s) :
    sSup t ∈ s := by
  have := ht.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem hbot (by simpa)

@[to_dual]
/-
**SupClosed.biSup_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SupClosed.biSup_mem {ι : Type*} {t : Set ι} {f : ι -> α} (hs : SupClosed s
) (ht : t.Finite) (hbot : ⊥ in s) (hf : forall i in t, f i in s) : ⨆ i in t, f i
 in s
参数：hs : SupClosed s；ht : t.Finite；hbot : ⊥ in s；hf : forall i in t, f i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用引理 `SupClosed.sSup_mem`：SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite
) (hbot : ⊥ in s) (hts : t subseteq s) : sSup t in s
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
lemma SupClosed.biSup_mem {ι : Type*} {t : Set ι} {f : ι → α} (hs : SupClosed s)
    (ht : t.Finite) (hbot : ⊥ ∈ s) (hf : ∀ i ∈ t, f i ∈ s) : ⨆ i ∈ t, f i ∈ s := by
  rw [← sSup_image]
  exact hs.sSup_mem (ht.image _) hbot (by simpa)
