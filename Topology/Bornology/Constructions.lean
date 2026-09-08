/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Topology.Bornology.Basic

/-!
# Bornology structure on products and subtypes

In this file we define `Bornology` and `BoundedSpace` instances on `α × β`, `Π i, X i`, and
`{x // p x}`. We also prove basic lemmas about `Bornology.cobounded` and `Bornology.IsBounded`
on these types.
-/

public section


open Set Filter Bornology Function

open Filter

variable {α β ι : Type*} {X : ι → Type*} [Bornology α] [Bornology β]
  [∀ i, Bornology (X i)]

/-
**Prod.instBornology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instBornology : Bornology (α × β) where cobounded
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instBornology : Bornology (α × β) where
  cobounded := (cobounded α).coprod (cobounded β)
  le_cofinite :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite
/-
**Pi.instBornology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instBornology : Bornology (forall i, X i) where cobounded
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.instBornology : Bornology (∀ i, X i) where
  cobounded := Filter.coprodᵢ fun i => cobounded (X i)
  le_cofinite := iSup_le fun _ ↦ (comap_mono (Bornology.le_cofinite _)).trans (comap_cofinite_le _)

/-- Inverse image of a bornology. -/
/-
**Bornology.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Bornology.induced {α β : Type*} [Bornology β] (f : α -> β) : Bornology α w
here cobounded
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse image of a bornology.
-/
abbrev Bornology.induced {α β : Type*} [Bornology β] (f : α → β) : Bornology α where
  cobounded := comap f (cobounded β)
  le_cofinite := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : α → Prop} : Bornology (Subtype p) :=
  Bornology.induced (Subtype.val : Subtype p → α)

namespace Bornology

/-!
### Bounded sets in `α × β`
-/


/-
**Bornology.cobounded_prod** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Bounded sets in `α × β`
-/
theorem cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) :=
  rfl
/-
**Bornology.isBounded_image_fst_and_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_image_fst_and_snd {s : Set (α × β)} : IsBounded (Prod.fst '' s) 
∧ IsBounded (Prod.snd '' s) ↔ IsBounded s
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.compl_mem_coprod`：compl_mem_coprod {s : Set (α × β)} {la : Filter
 α} {lb : Filter β} : sᶜ in la.coprod lb ↔ (Prod.fst '' s)ᶜ in la ∧ (Prod.snd ''
 s)ᶜ in lb
-/
theorem isBounded_image_fst_and_snd {s : Set (α × β)} :
    IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded s :=
  compl_mem_coprod.symm
/-
**Bornology.IsBounded.image_fst** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Bornology α] [inst_1 : Bornology β
] {s : Set (α × β)},   Bornology.IsBounded s → Bornology.IsBounded (Prod.fst '' 
s)
参数：α × β；Prod.fst '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.isBounded_image_fst_and_snd`：isBounded_image_fst_and_snd {s : 
Set (α × β)} : IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded
 s
-/
lemma IsBounded.image_fst {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.fst '' s) :=
  (isBounded_image_fst_and_snd.2 hs).1
/-
**Bornology.IsBounded.image_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Bornology α] [inst_1 : Bornology β
] {s : Set (α × β)},   Bornology.IsBounded s → Bornology.IsBounded (Prod.snd '' 
s)
参数：α × β；Prod.snd '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.isBounded_image_fst_and_snd`：isBounded_image_fst_and_snd {s : 
Set (α × β)} : IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded
 s
-/
lemma IsBounded.image_snd {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.snd '' s) :=
  (isBounded_image_fst_and_snd.2 hs).2

variable {s : Set α} {t : Set β} {S : ∀ i, Set (X i)}
/-
**Bornology.IsBounded.fst_of_prod** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Bornology α] [inst_1 : Bornology β
] {s : Set α} {t : Set β},   Bornology.IsBounded (s ×ˢ t) → t.Nonempty → Bornolo
gy.IsBounded s
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.image_fst`：∀ {α : Type u_1} {β : Type u_2} [inst : B
ornology α] [inst_1 : Bornology β] {s : Set (α × β)},   Bornology.IsBounded s → 
Bornology.IsBounded…
· 使用定理 `Set.fst_image_prod`：fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonem
pty) : Prod.fst '' s ×ˢ t = s
-/
theorem IsBounded.fst_of_prod (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty) : IsBounded s :=
  fst_image_prod s ht ▸ h.image_fst
/-
**Bornology.IsBounded.snd_of_prod** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Bornology α] [inst_1 : Bornology β
] {s : Set α} {t : Set β},   Bornology.IsBounded (s ×ˢ t) → s.Nonempty → Bornolo
gy.IsBounded t
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.image_snd`：∀ {α : Type u_1} {β : Type u_2} [inst : B
ornology α] [inst_1 : Bornology β] {s : Set (α × β)},   Bornology.IsBounded s → 
Bornology.IsBounded…
· 使用定理 `Set.snd_image_prod`：snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Se
t β) : Prod.snd '' s ×ˢ t = t
-/
theorem IsBounded.snd_of_prod (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty) : IsBounded t :=
  snd_image_prod hs t ▸ h.image_snd
/-
**Bornology.IsBounded.prod** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Bornology α] [inst_1 : Bornology β
] {s : Set α} {t : Set β},   Bornology.IsBounded s → Bornology.IsBounded t → Bor
nology.IsBounded (s ×ˢ t)
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bornology.isBounded_image_fst_and_snd`：isBounded_image_fst_and_snd {s : 
Set (α × β)} : IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded
 s
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Set.fst_image_prod_subset`：fst_image_prod_subset (s : Set α) (t : Set β)
 : Prod.fst '' s ×ˢ t subseteq s
· 使用定理 `Set.snd_image_prod_subset`：snd_image_prod_subset (s : Set α) (t : Set β)
 : Prod.snd '' s ×ˢ t subseteq t
-/
theorem IsBounded.prod (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ˢ t) :=
  isBounded_image_fst_and_snd.1
    ⟨hs.subset <| fst_image_prod_subset _ _, ht.subset <| snd_image_prod_subset _ _⟩
/-
**Bornology.isBounded_prod_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) : IsBounded (s ×ˢ
 t) ↔ IsBounded s ∧ IsBounded t
参数：hne : Set.Nonempty (s ×ˢ t)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.fst_of_prod`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Bornology α] [inst_1 : Bornology β] {s : Set α} {t : Set β},   Bornology.IsBoun
ded (s ×ˢ t) → t.None…
· 使用定理 `Set.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `Bornology.IsBounded.snd_of_prod`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Bornology α] [inst_1 : Bornology β] {s : Set α} {t : Set β},   Bornology.IsBoun
ded (s ×ˢ t) → s.None…
· 使用定理 `Set.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `Bornology.IsBounded.prod`：∀ {α : Type u_1} {β : Type u_2} [inst : Bornol
ogy α] [inst_1 : Bornology β] {s : Set α} {t : Set β},   Bornology.IsBounded s →
 Bornology.IsB…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isBounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) :
    IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t :=
  ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩
/-
**Bornology.isBounded_prod** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBoun
ded t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Bornology.isBounded_prod_of_nonempty`：isBounded_prod_of_nonempty (hne : 
Set.Nonempty (s ×ˢ t)) : IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t
· 使用定理 `Set.Nonempty.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem isBounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or]
/-
**Bornology.isBounded_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Bornology.isBounded_prod_of_nonempty`：isBounded_prod_of_nonempty (hne : 
Set.Nonempty (s ×ˢ t)) : IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t
· 使用定理 `Set.Nonempty.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
-/
theorem isBounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  exact (isBounded_prod_of_nonempty (hs.prod hs)).trans and_self_iff

/-!
### Bounded sets in `Π i, X i`
-/


/-
**Bornology.cobounded_pi** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：cobounded_pi : cobounded (forall i, X i) = Filter.coprodᵢ fun i => cobound
ed (X i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Bounded sets in `Π i, X i`
-/
theorem cobounded_pi : cobounded (∀ i, X i) = Filter.coprodᵢ fun i => cobounded (X i) :=
  rfl
/-
**Bornology.forall_isBounded_image_eval_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bornology
`。
形式化陈述：forall_isBounded_image_eval_iff {s : Set (forall i, X i)} : (forall i, IsB
ounded (eval i '' s)) ↔ IsBounded s
参数：forall i, X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.compl_mem_coprodᵢ`：compl_mem_coprodᵢ {s : Set (forall i, α i)} : 
sᶜ in Filter.coprodᵢ f ↔ forall i, (eval i '' s)ᶜ in f i
-/
theorem forall_isBounded_image_eval_iff {s : Set (∀ i, X i)} :
    (∀ i, IsBounded (eval i '' s)) ↔ IsBounded s :=
  compl_mem_coprodᵢ.symm
/-
**Bornology.IsBounded.image_eval** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`
。
形式化陈述：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) → Bornology (X i)] {s 
: Set ((i : ι) → X i)},   Bornology.IsBounded s → ∀ (i : ι), Bornology.IsBounded
 (Function.eval i '' s)
参数：i : ι；X i；(i : ι) → X i；i : ι；Function.eval i '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.forall_isBounded_image_eval_iff`：forall_isBounded_image_eval_i
ff {s : Set (forall i, X i)} : (forall i, IsBounded (eval i '' s)) ↔ IsBounded s
-/
lemma IsBounded.image_eval {s : Set (∀ i, X i)} (hs : IsBounded s) (i : ι) :
    IsBounded (eval i '' s) :=
  forall_isBounded_image_eval_iff.2 hs i
/-
**Bornology.IsBounded.pi** 是 Mathlib 中的一个定理，位于命名空间 `Bornology.IsBounded`。
形式化陈述：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) → Bornology (X i)] {S 
: (i : ι) → Set (X i)},   (∀ (i : ι), Bornology.IsBounded (S i)) → Bornology.IsB
ounded (Set.univ.pi S)
参数：i : ι；X i；i : ι；X i；∀ (i : ι), Bornology.IsBounded (S i)；Set.univ.pi S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bornology.forall_isBounded_image_eval_iff`：forall_isBounded_image_eval_i
ff {s : Set (forall i, X i)} : (forall i, IsBounded (eval i '' s)) ↔ IsBounded s
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Set.eval_image_univ_pi_subset`：eval_image_univ_pi_subset : eval i '' pi 
univ t subseteq t i
-/
theorem IsBounded.pi (h : ∀ i, IsBounded (S i)) : IsBounded (pi univ S) :=
  forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset
/-
**Bornology.isBounded_pi_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_pi_of_nonempty (hne : (pi univ S).Nonempty) : IsBounded (pi univ
 S) ↔ forall i, IsBounded (S i)
参数：hne : (pi univ S).Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bornology.forall_isBounded_image_eval_iff`：forall_isBounded_image_eval_i
ff {s : Set (forall i, X i)} : (forall i, IsBounded (eval i '' s)) ↔ IsBounded s
· 使用定理 `Set.eval_image_univ_pi`：eval_image_univ_pi (ht : (pi univ t).Nonempty) :
 (fun f : forall i, α i => f i) '' pi univ t = t i
· 使用定理 `Bornology.IsBounded.pi`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i :
 ι) → Bornology (X i)] {S : (i : ι) → Set (X i)},   (∀ (i : ι), Bornology.IsBoun
ded (S i)) →…
-/
theorem isBounded_pi_of_nonempty (hne : (pi univ S).Nonempty) :
    IsBounded (pi univ S) ↔ ∀ i, IsBounded (S i) :=
  ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_isBounded_image_eval_iff.2 H i, IsBounded.pi⟩
/-
**Bornology.isBounded_pi** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_pi : IsBounded (pi univ S) ↔ (exists i, S i = ∅) ∨ forall i, IsB
ounded (S i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.univ_pi_eq_empty_iff`：univ_pi_eq_empty_iff : pi univ t = ∅ ↔ exists 
i, t i = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Bornology.isBounded_pi_of_nonempty`：isBounded_pi_of_nonempty (hne : (pi 
univ S).Nonempty) : IsBounded (pi univ S) ↔ forall i, IsBounded (S i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem isBounded_pi : IsBounded (pi univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, IsBounded (S i) := by
  by_cases hne : ∃ i, S i = ∅
  · simp [hne, univ_pi_eq_empty_iff.2 hne]
  · simp only [hne, false_or]
    simp only [not_exists, ← nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne
    exact isBounded_pi_of_nonempty hne

/-!
### Bounded sets in `{x // p x}`
-/


/-
**Bornology.isBounded_induced** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_induced {α β : Type*} [Bornology β] {f : α -> β} {s : Set α} : @
IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.compl_mem_comap`：compl_mem_comap : sᶜ in comap f l ↔ (f '' s)ᶜ in
 l

--- 原说明 ---
### Bounded sets in `{x // p x}`
-/
theorem isBounded_induced {α β : Type*} [Bornology β] {f : α → β} {s : Set α} :
    @IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s) :=
  compl_mem_comap
/-
**Bornology.isBounded_image_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 `Bornology`。
形式化陈述：isBounded_image_subtype_val {p : α -> Prop} {s : Set { x // p x }} : IsBou
nded (Subtype.val '' s) ↔ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Bornology.isBounded_induced`：isBounded_induced {α β : Type*} [Bornology 
β] {f : α -> β} {s : Set α} : @IsBounded α (Bornology.induced f) s ↔ IsBounded (
f '' s)
-/
theorem isBounded_image_subtype_val {p : α → Prop} {s : Set { x // p x }} :
    IsBounded (Subtype.val '' s) ↔ IsBounded s :=
  isBounded_induced.symm

end Bornology

/-!
### Bounded spaces
-/


open Bornology

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BoundedSpace α] [BoundedSpace β] : BoundedSpace (α × β) := by
  simp [← cobounded_eq_bot_iff, cobounded_prod]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, BoundedSpace (X i)] : BoundedSpace (∀ i, X i) := by
  simp [← cobounded_eq_bot_iff, cobounded_pi]
/-
**boundedSpace_induced_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：boundedSpace_induced_iff {α β : Type*} [Bornology β] {f : α -> β} : @Bound
edSpace α (Bornology.induced f) ↔ IsBounded (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isBounded_univ`：isBounded_univ : IsBounded (univ : Set α) ↔ Bo
undedSpace α
· 使用定理 `Bornology.isBounded_induced`：isBounded_induced {α β : Type*} [Bornology 
β] {f : α -> β} {s : Set α} : @IsBounded α (Bornology.induced f) s ↔ IsBounded (
f '' s)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem boundedSpace_induced_iff {α β : Type*} [Bornology β] {f : α → β} :
    @BoundedSpace α (Bornology.induced f) ↔ IsBounded (range f) := by
  rw [← @isBounded_univ, isBounded_induced, image_univ]
/-
**boundedSpace_subtype_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：boundedSpace_subtype_iff {p : α -> Prop} : BoundedSpace (Subtype p) ↔ IsBo
unded { x | p x }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `boundedSpace_induced_iff`：boundedSpace_induced_iff {α β : Type*} [Bornol
ogy β] {f : α -> β} : @BoundedSpace α (Bornology.induced f) ↔ IsBounded (range f
)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem boundedSpace_subtype_iff {p : α → Prop} :
    BoundedSpace (Subtype p) ↔ IsBounded { x | p x } := by
  rw [boundedSpace_induced_iff, Subtype.range_coe_subtype]
/-
**boundedSpace_val_set_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：boundedSpace_val_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `boundedSpace_subtype_iff`：boundedSpace_subtype_iff {p : α -> Prop} : Bou
ndedSpace (Subtype p) ↔ IsBounded { x | p x }
-/
theorem boundedSpace_val_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s :=
  boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_subtype⟩ := boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_val⟩ := boundedSpace_val_set_iff
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BoundedSpace α] {p : α → Prop} : BoundedSpace (Subtype p) :=
  (IsBounded.all { x | p x }).boundedSpace_subtype

/-!
### `Additive`, `Multiplicative`

The bornology on those type synonyms is inherited without change.
-/


/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `Additive`, `Multiplicative`

The bornology on those type synonyms is inherited without change.
-/
instance : Bornology (Additive α) :=
  ‹Bornology α›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bornology (Multiplicative α) :=
  ‹Bornology α›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BoundedSpace α] : BoundedSpace (Additive α) :=
  ‹BoundedSpace α›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BoundedSpace α] : BoundedSpace (Multiplicative α) :=
  ‹BoundedSpace α›

/-!
### Order dual

The bornology on this type synonym is inherited without change.
-/


/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Order dual

The bornology on this type synonym is inherited without change.
-/
instance : Bornology αᵒᵈ :=
  ‹Bornology α›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BoundedSpace α] : BoundedSpace αᵒᵈ :=
  ‹BoundedSpace α›
