/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Patrick Massot
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.SProd
public import Mathlib.Data.Sum.Basic

/-!
# Sets in product and pi types

This file proves basic properties of product of sets in `α × β` and in `Π i, α i`, and of the
diagonal of a type.

## Main declarations

This file contains basic results on the following notions, which are defined in `Set.Operations`.

* `Set.prod`: Binary product of sets. For `s : Set α`, `t : Set β`, we have
  `s.prod t : Set (α × β)`. Denoted by `s ×ˢ t`.
* `Set.diagonal`: Diagonal of a type. `Set.diagonal α = {(x, x) | x : α}`.
* `Set.offDiag`: Off-diagonal. `s ×ˢ s` without the diagonal.
* `Set.pi`: Arbitrary product of sets.
-/

@[expose] public section


open Function

namespace Set

/-! ### Cartesian binary product of sets -/


section Prod

variable {α β γ δ : Type*} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

/-
**Set.Subsingleton.prod** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, s.Subsingleton → 
t.Subsingleton → (s ×ˢ t).Subsingleton
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Subsingleton.prod (hs : s.Subsingleton) (ht : t.Subsingleton) :
    (s ×ˢ t).Subsingleton := fun _x hx _y hy ↦
  Prod.ext (hs hx.1 hy.1) (ht hx.2 hy.2)
/-
**Set.decidableMemProd** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemProd [DecidablePred (· in s)] [DecidablePred (· in t)] : Decid
ablePred (· in s ×ˢ t)
参数：· in s；· in t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemProd [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ×ˢ t) := fun x => inferInstanceAs (Decidable (x.1 ∈ s ∧ x.2 ∈ t))

@[gcongr]
/-
**Set.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s₁ ×ˢ t₁ subseteq 
s₂ ×ˢ t₂
参数：hs : s₁ subseteq s₂；ht : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ :=
  fun _ ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩
/-
**Set.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_mono_left (hs : s₁ subseteq s₂) : s₁ ×ˢ t subseteq s₂ ×ˢ t
参数：hs : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem prod_mono_left (hs : s₁ ⊆ s₂) : s₁ ×ˢ t ⊆ s₂ ×ˢ t :=
  prod_mono hs Subset.rfl

alias prod_subset_prod_left := prod_mono_left
/-
**Set.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_mono_right (ht : t₁ subseteq t₂) : s ×ˢ t₁ subseteq s ×ˢ t₂
参数：ht : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem prod_mono_right (ht : t₁ ⊆ t₂) : s ×ˢ t₁ ⊆ s ×ˢ t₂ :=
  prod_mono Subset.rfl ht

alias prod_subset_prod_right := prod_mono_right

@[simp]
/-
**Set.prod_self_subset_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_self_subset_prod_self : s₁ ×ˢ s₁ subseteq s₂ ×ˢ s₂ ↔ s₁ subseteq s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_self_subset_prod_self : s₁ ×ˢ s₁ ⊆ s₂ ×ˢ s₂ ↔ s₁ ⊆ s₂ :=
  ⟨fun h _ hx => (h (mk_mem_prod hx hx)).1, fun h _ hx => ⟨h hx.1, h hx.2⟩⟩

@[simp]
/-
**Set.prod_self_ssubset_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_self_ssubset_prod_self : s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Set.prod_self_subset_prod_self`：prod_self_subset_prod_self : s₁ ×ˢ s₁ su
bseteq s₂ ×ˢ s₂ ↔ s₁ subseteq s₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
theorem prod_self_ssubset_prod_self : s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂ :=
  and_congr prod_self_subset_prod_self <| not_congr prod_self_subset_prod_self
/-
**Set.prod_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_subset_iff {P : Set (α × β)} : s ×ˢ t subseteq P ↔ forall x in s, for
all y in t, (x, y) in P
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_subset_iff {P : Set (α × β)} : s ×ˢ t ⊆ P ↔ ∀ x ∈ s, ∀ y ∈ t, (x, y) ∈ P :=
  ⟨fun h _ hx _ hy => h (mk_mem_prod hx hy), fun h ⟨_, _⟩ hp => h _ hp.1 _ hp.2⟩
/-
**Set.forall_prod_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_prod_set {p : α × β -> Prop} : (forall x in s ×ˢ t, p x) ↔ forall x
 in s, forall y in t, p (x, y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_subset_iff`：prod_subset_iff {P : Set (α × β)} : s ×ˢ t subseteq
 P ↔ forall x in s, forall y in t, (x, y) in P
-/
theorem forall_prod_set {p : α × β → Prop} : (∀ x ∈ s ×ˢ t, p x) ↔ ∀ x ∈ s, ∀ y ∈ t, p (x, y) :=
  prod_subset_iff
/-
**Set.exists_prod_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_prod_set {p : α × β -> Prop} : (exists x in s ×ˢ t, p x) ↔ exists x
 in s, exists y in t, p (x, y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_prod_set {p : α × β → Prop} : (∃ x ∈ s ×ˢ t, p x) ↔ ∃ x ∈ s, ∃ y ∈ t, p (x, y) := by
  simp [and_assoc]

@[simp]
/-
**Set.prod_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_empty : s ×ˢ (∅ : Set β) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem prod_empty : s ×ˢ (∅ : Set β) = ∅ := by
  ext
  exact iff_of_eq (and_false _)

@[simp]
/-
**Set.empty_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_prod : (∅ : Set α) ×ˢ t = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem empty_prod : (∅ : Set α) ×ˢ t = ∅ := by
  ext
  exact iff_of_eq (false_and _)

@[simp, mfld_simps]
/-
**Set.univ_prod_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_prod_univ : @univ α ×ˢ @univ β = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem univ_prod_univ : @univ α ×ˢ @univ β = univ := by
  ext
  exact iff_of_eq (true_and _)
/-
**Set.univ_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t := by simp [prod_eq]
/-
**Set.prod_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s := by simp [prod_eq]
/-
**Set.prod_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} [Nonempty α] [None
mpty β],   s ×ˢ t = Set.univ ↔ s = Set.univ ∧ t = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma prod_eq_univ [Nonempty α] [Nonempty β] : s ×ˢ t = univ ↔ s = univ ∧ t = univ := by
  simp [eq_univ_iff_forall, forall_and]
/-
**Set.singleton_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
/-
**Set.prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]
/-
**Set.singleton_prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_prod_singleton : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_prod_singleton : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := by ext ⟨c, d⟩; simp

@[simp]
/-
**Set.union_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_prod : (s₁ union s₂) ×ˢ t = s₁ ×ˢ t union s₂ ×ˢ t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem union_prod : (s₁ ∪ s₂) ×ˢ t = s₁ ×ˢ t ∪ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp [or_and_right]

@[simp]
/-
**Set.prod_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_union : s ×ˢ (t₁ union t₂) = s ×ˢ t₁ union s ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_union : s ×ˢ (t₁ ∪ t₂) = s ×ˢ t₁ ∪ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp [and_or_left]
/-
**Set.inter_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_prod : (s₁ inter s₂) ×ˢ t = s₁ ×ˢ t inter s₂ ×ˢ t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inter_prod : (s₁ ∩ s₂) ×ˢ t = s₁ ×ˢ t ∩ s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp only [← and_and_right, mem_inter_iff, mem_prod]
/-
**Set.prod_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_inter : s ×ˢ (t₁ inter t₂) = s ×ˢ t₁ inter s ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_inter : s ×ˢ (t₁ ∩ t₂) = s ×ˢ t₁ ∩ s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp only [← and_and_left, mem_inter_iff, mem_prod]

@[mfld_simps]
/-
**Set.prod_inter_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ inter s₂) ×ˢ (t₁ inter t₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_inter_prod : s₁ ×ˢ t₁ ∩ s₂ ×ˢ t₂ = (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]
/-
**Set.compl_prod_eq_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：compl_prod_eq_union {α β : Type*} (s : Set α) (t : Set β) : (s ×ˢ t)ᶜ = (s
ᶜ ×ˢ univ) union (univ ×ˢ tᶜ)
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compl_prod_eq_union {α β : Type*} (s : Set α) (t : Set β) :
    (s ×ˢ t)ᶜ = (sᶜ ×ˢ univ) ∪ (univ ×ˢ tᶜ) := by
  grind

@[simp]
/-
**Set.disjoint_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint
 t₁ t₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_left, mem_prod, Prod.forall]
  grind
/-
**Set.Disjoint.set_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Disjoint`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α}, Disjoint s₁ s₂ → ∀ (t₁ t₂
 : Set β), Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂)
参数：t₁ t₂ : Set β；s₁ ×ˢ t₁；s₂ ×ˢ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Disjoint.set_prod_left (hs : Disjoint s₁ s₂) (t₁ t₂ : Set β) :
    Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) :=
  disjoint_left.2 fun ⟨_a, _b⟩ ⟨ha₁, _⟩ ⟨ha₂, _⟩ => disjoint_left.1 hs ha₁ ha₂
/-
**Set.Disjoint.set_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Disjoint`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {t₁ t₂ : Set β}, Disjoint t₁ t₂ → ∀ (s₁ s₂
 : Set α), Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂)
参数：s₁ s₂ : Set α；s₁ ×ˢ t₁；s₂ ×ˢ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Disjoint.set_prod_right (ht : Disjoint t₁ t₂) (s₁ s₂ : Set α) :
    Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) :=
  disjoint_left.2 fun ⟨_a, _b⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩ => disjoint_left.1 ht hb₁ hb₂
/-
**Set.prodMap_image_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prodMap_image_prod (f : α -> β) (g : γ -> δ) (s : Set α) (t : Set γ) : (Pr
od.map f g) '' (s ×ˢ t) = (f '' s) ×ˢ (g '' t)
参数：f : α -> β；g : γ -> δ；s : Set α；t : Set γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodMap_image_prod (f : α → β) (g : γ → δ) (s : Set α) (t : Set γ) :
    (Prod.map f g) '' (s ×ˢ t) = (f '' s) ×ˢ (g '' t) := by
  ext
  aesop
/-
**Set.insert_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_prod : insert a s ×ˢ t = Prod.mk a '' t union s ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_prod`：union_prod : (s₁ union s₂) ×ˢ t = s₁ ×ˢ t union s₂ ×ˢ t
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_prod : insert a s ×ˢ t = Prod.mk a '' t ∪ s ×ˢ t := by
  simp only [insert_eq, union_prod, singleton_prod]
/-
**Set.prod_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_insert : s ×ˢ insert b t = (fun a => (a, b)) '' s union s ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_union`：prod_union : s ×ˢ (t₁ union t₂) = s ×ˢ t₁ union s ×ˢ t₂
· 使用定理 `Set.prod_singleton`：prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, 
b)) '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_insert : s ×ˢ insert b t = (fun a => (a, b)) '' s ∪ s ×ˢ t := by
  simp only [insert_eq, prod_union, prod_singleton]
/-
**Set.prod_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_preimage_eq {f : γ -> α} {g : δ -> β} : (f ⁻¹' s) ×ˢ (g ⁻¹' t) = (fun
 p : γ × δ => (f p.1, g p.2)) ⁻¹' s ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
    (f ⁻¹' s) ×ˢ (g ⁻¹' t) = (fun p : γ × δ => (f p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl
/-
**Set.prod_preimage_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_preimage_left {f : γ -> α} : (f ⁻¹' s) ×ˢ t = (fun p : γ × β => (f p.
1, p.2)) ⁻¹' s ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_preimage_left {f : γ → α} :
    (f ⁻¹' s) ×ˢ t = (fun p : γ × β => (f p.1, p.2)) ⁻¹' s ×ˢ t :=
  rfl
/-
**Set.prod_preimage_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_preimage_right {g : δ -> β} : s ×ˢ (g ⁻¹' t) = (fun p : α × δ => (p.1
, g p.2)) ⁻¹' s ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_preimage_right {g : δ → β} :
    s ×ˢ (g ⁻¹' t) = (fun p : α × δ => (p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl
/-
**Set.preimage_prod_map_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_prod_map_prod (f : α -> β) (g : γ -> δ) (s : Set β) (t : Set δ) :
 Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t)
参数：f : α -> β；g : γ -> δ；s : Set β；t : Set δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_prod_map_prod (f : α → β) (g : γ → δ) (s : Set β) (t : Set δ) :
    Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) :=
  rfl
/-
**Set.mk_preimage_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod (f : γ -> α) (g : γ -> β) : (fun x => (f x, g x)) ⁻¹' s ×
ˢ t = f ⁻¹' s inter g ⁻¹' t
参数：f : γ -> α；g : γ -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod (f : γ → α) (g : γ → β) :
    (fun x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl

@[simp]
/-
**Set.mk_preimage_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod_left (hb : b in t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = s
参数：hb : b in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod_left (hb : b ∈ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = s := by grind

@[simp]
/-
**Set.mk_preimage_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod_right (ha : a in s) : Prod.mk a ⁻¹' s ×ˢ t = t
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod_right (ha : a ∈ s) : Prod.mk a ⁻¹' s ×ˢ t = t := by grind

@[simp]
/-
**Set.mk_preimage_prod_left_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t
 = ∅
参数：hb : b ∉ t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅ := by grind

@[simp]
/-
**Set.mk_preimage_prod_right_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod_right_eq_empty (ha : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod_right_eq_empty (ha : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅ := by grind
/-
**Set.mk_preimage_prod_left_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod_left_eq_if [DecidablePred (· in t)] : (fun a => (a, b)) ⁻
¹' s ×ˢ t = if b in t then s else ∅
参数：· in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod_left_eq_if [DecidablePred (· ∈ t)] :
    (fun a => (a, b)) ⁻¹' s ×ˢ t = if b ∈ t then s else ∅ := by grind
/-
**Set.mk_preimage_prod_right_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod_right_eq_if [DecidablePred (· in s)] : Prod.mk a ⁻¹' s ×ˢ
 t = if a in s then t else ∅
参数：· in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod_right_eq_if [DecidablePred (· ∈ s)] :
    Prod.mk a ⁻¹' s ×ˢ t = if a ∈ s then t else ∅ := by grind
/-
**Set.mk_preimage_prod_left_fn_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod_left_fn_eq_if [DecidablePred (· in t)] (f : γ -> α) : (fu
n a => (f a, b)) ⁻¹' s ×ˢ t = if b in t then f ⁻¹' s else ∅
参数：· in t；f : γ -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod_left_fn_eq_if [DecidablePred (· ∈ t)] (f : γ → α) :
    (fun a => (f a, b)) ⁻¹' s ×ˢ t = if b ∈ t then f ⁻¹' s else ∅ := by grind
/-
**Set.mk_preimage_prod_right_fn_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_preimage_prod_right_fn_eq_if [DecidablePred (· in s)] (g : δ -> β) : (f
un b => (a, g b)) ⁻¹' s ×ˢ t = if a in s then g ⁻¹' t else ∅
参数：· in s；g : δ -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_preimage_prod_right_fn_eq_if [DecidablePred (· ∈ s)] (g : δ → β) :
    (fun b => (a, g b)) ⁻¹' s ×ˢ t = if a ∈ s then g ⁻¹' t else ∅ := by grind

@[simp]
/-
**Set.preimage_swap_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_swap_prod (s : Set α) (t : Set β) : Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_swap_prod (s : Set α) (t : Set β) : Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s := by grind

@[simp]
/-
**Set.image_swap_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_swap_prod (s : Set α) (t : Set β) : Prod.swap '' s ×ˢ t = t ×ˢ s
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_swap_eq_preimage_swap`：image_swap_eq_preimage_swap : image (@P
rod.swap α β) = preimage Prod.swap
· 使用定理 `Set.preimage_swap_prod`：preimage_swap_prod (s : Set α) (t : Set β) : Pro
d.swap ⁻¹' s ×ˢ t = t ×ˢ s
-/
theorem image_swap_prod (s : Set α) (t : Set β) : Prod.swap '' s ×ˢ t = t ×ˢ s := by
  rw [image_swap_eq_preimage_swap, preimage_swap_prod]
/-
**Set.mapsTo_swap_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_swap_prod (s : Set α) (t : Set β) : MapsTo Prod.swap (s ×ˢ t) (t ×ˢ
 s)
参数：s : Set α；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapsTo_swap_prod (s : Set α) (t : Set β) : MapsTo Prod.swap (s ×ˢ t) (t ×ˢ s) :=
  fun _ ⟨hx, hy⟩ ↦ ⟨hy, hx⟩
/-
**Set.prod_image_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_image_image_eq {m₁ : α -> γ} {m₂ : β -> δ} : (m₁ '' s) ×ˢ (m₂ '' t) =
 (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `exists_and_right`：∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, p x 
∧ b) ↔ (∃ x, p x) ∧ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
    (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t :=
  ext <| by
    simp [-exists_and_right, exists_and_right.symm, and_left_comm, and_assoc, and_comm]
/-
**Set.prod_range_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_range_range_eq {m₁ : α -> γ} {m₂ : β -> δ} : range m₁ ×ˢ range m₂ = r
ange fun p : α × β => (m₁ p.1, m₂ p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_range_range_eq {m₁ : α → γ} {m₂ : β → δ} :
    range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2) :=
  ext <| by simp [range]

@[simp, mfld_simps]
/-
**Set.range_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Prod.map m₁ m₂) = range
 m₁ ×ˢ range m₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_range_range_eq`：prod_range_range_eq {m₁ : α -> γ} {m₂ : β -> δ}
 : range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2)
-/
theorem range_prodMap {m₁ : α → γ} {m₂ : β → δ} : range (Prod.map m₁ m₂) = range m₁ ×ˢ range m₂ :=
  prod_range_range_eq.symm
/-
**Set.prod_range_univ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_range_univ_eq {m₁ : α -> γ} : range m₁ ×ˢ (univ : Set β) = range fun 
p : α × β => (m₁ p.1, p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_range_univ_eq {m₁ : α → γ} :
    range m₁ ×ˢ (univ : Set β) = range fun p : α × β => (m₁ p.1, p.2) :=
  ext <| by simp [range]
/-
**Set.prod_univ_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_univ_range_eq {m₂ : β -> δ} : (univ : Set α) ×ˢ range m₂ = range fun 
p : α × β => (p.1, m₂ p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_univ_range_eq {m₂ : β → δ} :
    (univ : Set α) ×ˢ range m₂ = range fun p : α × β => (p.1, m₂ p.2) :=
  ext <| by simp [range]
/-
**Set.range_pair_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_pair_subset (f : α -> β) (g : α -> γ) : (range fun x => (f x, g x)) 
subseteq range f ×ˢ range g
参数：f : α -> β；g : α -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_pair_subset (f : α → β) (g : α → γ) :
    (range fun x => (f x, g x)) ⊆ range f ×ˢ range g := by grind
/-
**Set.Nonempty.prod** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, s.Nonempty → t.No
nempty → (s ×ˢ t).Nonempty
参数：s ×ˢ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.prod : s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty := fun ⟨x, hx⟩ ⟨y, hy⟩ =>
  ⟨(x, y), ⟨hx, hy⟩⟩
/-
**Set.Nonempty.fst** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, (s ×ˢ t).Nonempty
 → s.Nonempty
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Nonempty.fst : (s ×ˢ t).Nonempty → s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩
/-
**Set.Nonempty.snd** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}, (s ×ˢ t).Nonempty
 → t.Nonempty
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Nonempty.snd : (s ×ˢ t).Nonempty → t.Nonempty := fun ⟨x, hx⟩ => ⟨x.2, hx.2⟩

@[simp]
/-
**Set.prod_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `Set.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `Set.Nonempty.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod h.2⟩

@[simp]
/-
**Set.prod_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_or]
/-
**Set.prod_sub_preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_sub_preimage_iff {W : Set γ} {f : α × β -> γ} : s ×ˢ t subseteq f ⁻¹'
 W ↔ forall a b, a in s -> b in t -> f (a, b) in W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_sub_preimage_iff {W : Set γ} {f : α × β → γ} :
    s ×ˢ t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W := by simp [subset_def]
/-
**Set.image_prodMk_subset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_prodMk_subset_prod {f : α -> β} {g : α -> γ} {s : Set α} : (fun x =>
 (f x, g x)) '' s subseteq (f '' s) ×ˢ (g '' s)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_prodMk_subset_prod {f : α → β} {g : α → γ} {s : Set α} :
    (fun x => (f x, g x)) '' s ⊆ (f '' s) ×ˢ (g '' s) := by grind
/-
**Set.image_prodMk_subset_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_prodMk_subset_prod_left (hb : b in t) : (fun a => (a, b)) '' s subse
teq s ×ˢ t
参数：hb : b in t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_prodMk_subset_prod_left (hb : b ∈ t) : (fun a => (a, b)) '' s ⊆ s ×ˢ t := by grind
/-
**Set.image_prodMk_subset_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_prodMk_subset_prod_right (ha : a in s) : Prod.mk a '' t subseteq s ×
ˢ t
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_prodMk_subset_prod_right (ha : a ∈ s) : Prod.mk a '' t ⊆ s ×ˢ t := by grind
/-
**Set.prod_subset_preimage_fst** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_subset_preimage_fst (s : Set α) (t : Set β) : s ×ˢ t subseteq Prod.fs
t ⁻¹' s
参数：s : Set α；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem prod_subset_preimage_fst (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.fst ⁻¹' s :=
  inter_subset_left
/-
**Set.fst_image_prod_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：fst_image_prod_subset (s : Set α) (t : Set β) : Prod.fst '' s ×ˢ t subsete
q s
参数：s : Set α；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.prod_subset_preimage_fst`：prod_subset_preimage_fst (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s
-/
theorem fst_image_prod_subset (s : Set α) (t : Set β) : Prod.fst '' s ×ˢ t ⊆ s :=
  image_subset_iff.2 <| prod_subset_preimage_fst s t
/-
**Set.fst_image_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonempty) : Prod.fst '' s ×
ˢ t = s
参数：s : Set β；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.fst_image_prod_subset`：fst_image_prod_subset (s : Set α) (t : Set β)
 : Prod.fst '' s ×ˢ t subseteq s
-/
theorem fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonempty) : Prod.fst '' s ×ˢ t = s :=
  (fst_image_prod_subset _ _).antisymm fun y hy =>
    let ⟨x, hx⟩ := ht
    ⟨(y, x), ⟨hy, hx⟩, rfl⟩
/-
**Set.mapsTo_fst_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Prod.fst (s ×ˢ t) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
-/
lemma mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Prod.fst (s ×ˢ t) s :=
  fun _ hx ↦ (mem_prod.1 hx).1
/-
**Set.prod_subset_preimage_snd** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_subset_preimage_snd (s : Set α) (t : Set β) : s ×ˢ t subseteq Prod.sn
d ⁻¹' t
参数：s : Set α；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem prod_subset_preimage_snd (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.snd ⁻¹' t :=
  inter_subset_right
/-
**Set.snd_image_prod_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：snd_image_prod_subset (s : Set α) (t : Set β) : Prod.snd '' s ×ˢ t subsete
q t
参数：s : Set α；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.prod_subset_preimage_snd`：prod_subset_preimage_snd (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t
-/
theorem snd_image_prod_subset (s : Set α) (t : Set β) : Prod.snd '' s ×ˢ t ⊆ t :=
  image_subset_iff.2 <| prod_subset_preimage_snd s t
/-
**Set.snd_image_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Set β) : Prod.snd '' s ×
ˢ t = t
参数：hs : s.Nonempty；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.snd_image_prod_subset`：snd_image_prod_subset (s : Set α) (t : Set β)
 : Prod.snd '' s ×ˢ t subseteq t
-/
theorem snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Set β) : Prod.snd '' s ×ˢ t = t :=
  (snd_image_prod_subset _ _).antisymm fun y y_in =>
    let ⟨x, x_in⟩ := hs
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩
/-
**Set.subset_fst_image_prod_snd_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_fst_image_prod_snd_image {s : Set (α × β)} : s subseteq (Prod.fst '
' s) ×ˢ (Prod.snd '' s)
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem subset_fst_image_prod_snd_image {s : Set (α × β)} :
    s ⊆ (Prod.fst '' s) ×ˢ (Prod.snd '' s) := fun ⟨p₁, p₂⟩ _ => by aesop
/-
**Set.mapsTo_snd_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Prod.snd (s ×ˢ t) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
-/
lemma mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Prod.snd (s ×ˢ t) t :=
  fun _ hx ↦ (mem_prod.1 hx).2
/-
**Set.prod_sdiff_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_sdiff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) union (s \ s₁) ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_sdiff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t := by grind

@[deprecated (since := "2026-06-03")] alias prod_diff_prod := prod_sdiff_prod

/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
/-
**Set.prod_subset_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t₁ ↔ s subseteq s₁ ∧ t subset
eq t₁ ∨ s = ∅ ∨ t = ∅
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.prod_eq_empty_iff`：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.prod_nonempty_iff`：prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempt
y ∧ t.Nonempty
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.fst_image_prod`：fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonem
pty) : Prod.fst '' s ×ˢ t = s
· 使用定理 `Set.Nonempty.snd`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
}, (s ×ˢ t).Nonempty → t.Nonempty
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.snd_image_prod`：snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Se
t β) : Prod.snd '' s ×ˢ t = t
· 使用定理 `Set.Nonempty.fst`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
}, (s ×ˢ t).Nonempty → s.Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
A product set is included in a product set if and only factors are included, or 
a factor of the
first set is empty.
-/
theorem prod_subset_prod_iff : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  have st : s.Nonempty ∧ t.Nonempty := by rwa [prod_nonempty_iff] at h
  refine ⟨fun H => Or.inl ⟨?_, ?_⟩, ?_⟩
  · have := image_mono (f := Prod.fst) H
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H).snd] at this
  · have := image_mono (f := Prod.snd) H
    rwa [snd_image_prod st.1, snd_image_prod (h.mono H).fst] at this
  · intro H
    simp only [st.1.ne_empty, st.2.ne_empty, or_false] at H
    exact prod_mono H.1 H.2
/-
**Set.prod_subset_prod_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_subset_prod_iff' (h : (s ×ˢ t).Nonempty) : s ×ˢ t subseteq s₁ ×ˢ t₁ ↔
 s subseteq s₁ ∧ t subseteq t₁
参数：h : (s ×ˢ t).Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_eq_empty_iff`：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_subset_prod_iff' (h : (s ×ˢ t).Nonempty) : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ := by
  rw [prod_subset_prod_iff, or_iff_left]
  rw [← Set.prod_eq_empty_iff]
  exact h.ne_empty
/-
**Set.prod_subset_prod_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_subset_prod_iff_left (h : t.Nonempty) : s ×ˢ t subseteq s₁ ×ˢ t ↔ s s
ubseteq s₁
参数：h : t.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_subset_prod_iff_left (h : t.Nonempty) : s ×ˢ t ⊆ s₁ ×ˢ t ↔ s ⊆ s₁ := by
  simp +contextual [prod_subset_prod_iff, or_iff_left h.ne_empty]
/-
**Set.prod_subset_prod_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_subset_prod_iff_right (h : s.Nonempty) : s ×ˢ t subseteq s ×ˢ t₁ ↔ t 
subseteq t₁
参数：h : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_subset_prod_iff_right (h : s.Nonempty) : s ×ˢ t ⊆ s ×ˢ t₁ ↔ t ⊆ t₁ := by
  simp +contextual [prod_subset_prod_iff, or_comm (a := s = ∅), or_iff_left h.ne_empty]
/-
**Set.prod_eq_prod_iff_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_eq_prod_iff_of_nonempty (h : (s ×ˢ t).Nonempty) : s ×ˢ t = s₁ ×ˢ t₁ ↔
 s = s₁ ∧ t = t₁
参数：h : (s ×ˢ t).Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.fst_image_prod`：fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonem
pty) : Prod.fst '' s ×ˢ t = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.prod_nonempty_iff`：prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempt
y ∧ t.Nonempty
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.snd_image_prod`：snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Se
t β) : Prod.snd '' s ×ˢ t = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem prod_eq_prod_iff_of_nonempty (h : (s ×ˢ t).Nonempty) :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ := by
  constructor
  · intro heq
    have h₁ : (s₁ ×ˢ t₁ : Set _).Nonempty := by rwa [← heq]
    rw [prod_nonempty_iff] at h h₁
    rw [← fst_image_prod s h.2, ← fst_image_prod s₁ h₁.2, heq, eq_self_iff_true, true_and, ←
      snd_image_prod h.1 t, ← snd_image_prod h₁.1 t₁, heq]
  · grind
/-
**Set.prod_eq_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_eq_prod_iff : s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧
 (s₁ = ∅ ∨ t₁ = ∅)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.prod_eq_empty_iff`：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.prod_eq_prod_iff_of_nonempty`：prod_eq_prod_iff_of_nonempty (h : (s ×
ˢ t).Nonempty) : s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_prod_iff :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) := by
  symm
  rcases eq_empty_or_nonempty (s ×ˢ t) with h | h
  · simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_and,
      or_iff_right_iff_imp]
    rintro ⟨rfl, rfl⟩
    exact prod_eq_empty_iff.mp h
  rw [prod_eq_prod_iff_of_nonempty h]
  rw [nonempty_iff_ne_empty, Ne, prod_eq_empty_iff] at h
  simp_rw [h, false_and, or_false]

@[simp]
/-
**Set.prod_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁
参数：ht : t.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ := by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, and_true, or_iff_left_iff_imp, or_false]
  rintro ⟨rfl, rfl⟩
  rfl
/-
**Set.subset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_prod {s : Set (α × β)} : s subseteq (Prod.fst '' s) ×ˢ (Prod.snd ''
 s)
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem subset_prod {s : Set (α × β)} : s ⊆ (Prod.fst '' s) ×ˢ (Prod.snd '' s) :=
  fun _ hp ↦ mem_prod.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

section Mono

variable [Preorder α] {f : α → Set β} {g : α → Set γ}

/-
**Set._root_.Monotone.set_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Monotone.set_prod (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ×ˢ g x :=
  fun _ _ h => prod_mono (hf h) (hg h)
/-
**Set._root_.Antitone.set_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Antitone.set_prod (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ×ˢ g x :=
  fun _ _ h => prod_mono (hf h) (hg h)
/-
**Set._root_.MonotoneOn.set_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MonotoneOn.set_prod (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x ×ˢ g x) s := fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)
/-
**Set._root_.AntitoneOn.set_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AntitoneOn.set_prod (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x ×ˢ g x) s := fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

end Mono

/-
**Set.eqOn_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eqOn_prod_iff {a b : α -> γ × δ} : EqOn a b s ↔ EqOn (Prod.fst ∘ a) (Prod.
fst ∘ b) s ∧ EqOn (Prod.snd ∘ a) (Prod.snd ∘ b) s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqOn_prod_iff {a b : α → γ × δ} :
    EqOn a b s ↔ EqOn (Prod.fst ∘ a) (Prod.fst ∘ b) s ∧ EqOn (Prod.snd ∘ a) (Prod.snd ∘ b) s := by
  grind [EqOn]
/-
**Set.EqOn.left_of_eqOn_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {s : Set α} 
{t : Set β} {f f' : α → γ} {g g' : β → δ},   Set.EqOn (Prod.map f g) (Prod.map f
' g') (s ×ˢ t) → t.Nonempty → Set.EqOn f f' s
参数：Prod.map f g；Prod.map f' g'；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
-/
lemma EqOn.left_of_eqOn_prodMap {f f' : α → γ} {g g' : β → δ}
    (h : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t)) (ht : t.Nonempty) : EqOn f f' s := by
  obtain ⟨x, hxt⟩ := ht
  intro x hxs
  have h' := h <| mk_mem_prod hxs hxt
  grind
/-
**Set.EqOn.right_of_eqOn_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {s : Set α} 
{t : Set β} {f f' : α → γ} {g g' : β → δ},   Set.EqOn (Prod.map f g) (Prod.map f
' g') (s ×ˢ t) → s.Nonempty → Set.EqOn g g' t
参数：Prod.map f g；Prod.map f' g'；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
-/
lemma EqOn.right_of_eqOn_prodMap {f f' : α → γ} {g g' : β → δ}
    (h : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t)) (hs : Set.Nonempty s) : EqOn g g' t := by
  obtain ⟨x, hxs⟩ := hs
  intro x hxt
  have h' := h <| mk_mem_prod hxs hxt
  grind
/-
**Set.EqOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {s : Set α} 
{t : Set β} {f f' : α → γ} {g g' : β → δ},   Set.EqOn f f' s → Set.EqOn g g' t →
 Set.EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t)
参数：Prod.map f g；Prod.map f' g'；s ×ˢ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma EqOn.prodMap {f f' : α → γ} {g g' : β → δ}
    (hf : EqOn f f' s) (hg : EqOn g g' t) : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) := by
  grind [EqOn]
/-
**Set.eqOn_prodMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eqOn_prodMap_iff {f f' : α -> γ} {g g' : β -> δ} {s : Set α} {t : Set β} (
hs : Set.Nonempty s) (ht : Set.Nonempty t) : EqOn (Prod.map f g) (Prod.map f' g'
) (s ×ˢ t) ↔ EqOn f f' s ∧ EqOn g g' t
参数：hs : Set.Nonempty s；ht : Set.Nonempty t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.left_of_eqOn_prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {δ : Type u_4} {s : Set α} {t : Set β} {f f' : α → γ} {g g' : β → δ},   Se
t.EqOn (Prod.map f …
· 使用定理 `Set.EqOn.right_of_eqOn_prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {δ : Type u_4} {s : Set α} {t : Set β} {f f' : α → γ} {g g' : β → δ},   S
et.EqOn (Prod.map f …
· 使用定理 `Set.EqOn.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Ty
pe u_4} {s : Set α} {t : Set β} {f f' : α → γ} {g g' : β → δ},   Set.EqOn f f' s
 → Set…
-/
lemma eqOn_prodMap_iff {f f' : α → γ} {g g' : β → δ}
    {s : Set α} {t : Set β} (hs : Set.Nonempty s) (ht : Set.Nonempty t) :
    EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) ↔ EqOn f f' s ∧ EqOn g g' t :=
  ⟨fun h ↦ ⟨h.left_of_eqOn_prodMap ht, h.right_of_eqOn_prodMap hs⟩, fun ⟨h, h'⟩ ↦ h.prodMap h'⟩

end Prod

/-! ### Diagonal

In this section we prove some lemmas about the diagonal set `{p | p.1 = p.2}` and the diagonal map
`fun x ↦ (x, x)`.
-/


section Diagonal

variable {α : Type*} {s t : Set α}

/-
**Set.diagonal_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：diagonal_nonempty [Nonempty α] : (diagonal α).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Set.mem_diagonal`：mem_diagonal (x : α) : (x, x) in diagonal α
-/
lemma diagonal_nonempty [Nonempty α] : (diagonal α).Nonempty :=
  Nonempty.elim ‹_› fun x => ⟨_, mem_diagonal x⟩
/-
**Set.decidableMemDiagonal** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemDiagonal [h : DecidableEq α] (x : α × α) : Decidable (x in dia
gonal α)
参数：x : α × α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemDiagonal [h : DecidableEq α] (x : α × α) : Decidable (x ∈ diagonal α) :=
  h x.1 x.2
/-
**Set.preimage_coe_coe_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_coe_coe_diagonal (s : Set α) : Prod.map (fun x : s => (x : α)) (f
un x : s => (x : α)) ⁻¹' diagonal α = diagonal s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_coe_coe_diagonal (s : Set α) :
    Prod.map (fun x : s => (x : α)) (fun x : s => (x : α)) ⁻¹' diagonal α = diagonal s := by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [Set.diagonal]

@[simp]
/-
**Set.range_diag** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_diag : range Function.diag = diagonal α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_diag : range Function.diag = diagonal α := by
  ext ⟨x, y⟩
  simp [diagonal, eq_comm]
/-
**Set.diagonal_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：diagonal_subset_iff {s} : diagonal α subseteq s ↔ forall x, (x, x) in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_subset_iff {s} : diagonal α ⊆ s ↔ ∀ x, (x, x) ∈ s := by grind

@[simp]
/-
**Set.prod_subset_compl_diagonal_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_subset_compl_diagonal_iff_disjoint : s ×ˢ t subseteq (diagonal α)ᶜ ↔ 
Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.prod_subset_iff`：prod_subset_iff {P : Set (α × β)} : s ×ˢ t subseteq
 P ↔ forall x in s, forall y in t, (x, y) in P
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
-/
theorem prod_subset_compl_diagonal_iff_disjoint : s ×ˢ t ⊆ (diagonal α)ᶜ ↔ Disjoint s t :=
  prod_subset_iff.trans disjoint_iff_forall_ne.symm

@[simp]
/-
**Set.diag_preimage_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：diag_preimage_prod (s t : Set α) : Function.diag ⁻¹' s ×ˢ t = s inter t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_preimage_prod (s t : Set α) : Function.diag ⁻¹' s ×ˢ t = s ∩ t :=
  rfl
/-
**Set.diag_preimage_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：diag_preimage_prod_self (s : Set α) : Function.diag ⁻¹' s ×ˢ s = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
theorem diag_preimage_prod_self (s : Set α) : Function.diag ⁻¹' s ×ˢ s = s :=
  inter_self s
/-
**Set.diag_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：diag_image (s : Set α) : Function.diag '' s = diagonal α inter s ×ˢ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_diag`：range_diag : range Function.diag = diagonal α
· 使用定理 `Set.image_preimage_eq_range_inter`：image_preimage_eq_range_inter {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = range f inter t
· 使用定理 `Set.diag_preimage_prod_self`：diag_preimage_prod_self (s : Set α) : Funct
ion.diag ⁻¹' s ×ˢ s = s
-/
theorem diag_image (s : Set α) : Function.diag '' s = diagonal α ∩ s ×ˢ s := by
  rw [← range_diag, ← image_preimage_eq_range_inter, diag_preimage_prod_self]
/-
**Set.diagonal_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：diagonal_eq_univ_iff : diagonal α = univ ↔ Subsingleton α
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem diagonal_eq_univ_iff : diagonal α = univ ↔ Subsingleton α := by
  simp only [subsingleton_iff, eq_univ_iff_forall, Prod.forall, mem_diagonal_iff]
/-
**Set.diagonal_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：diagonal_eq_univ [Subsingleton α] : diagonal α = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.diagonal_eq_univ_iff`：diagonal_eq_univ_iff : diagonal α = univ ↔ Sub
singleton α
-/
theorem diagonal_eq_univ [Subsingleton α] : diagonal α = univ := diagonal_eq_univ_iff.2 ‹_›

end Diagonal

/-- A function is `Function.const α a` for some `a` if and only if `∀ x y, f x = f y`. -/
/-
**Set.range_const_eq_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_const_eq_diagonal {α β : Type*} [hβ : Nonempty β] : range (const α) 
= {f : α -> β | forall x y, f x = f y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_iff`：range_eq_iff (f : α -> β) (s : Set β) : range f = s ↔ 
(forall a, f a in s) ∧ forall b in s, exists a, f a = b
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A function is `Function.const α a` for some `a` if and only if `∀ x y, f x = f y
`.
-/
theorem range_const_eq_diagonal {α β : Type*} [hβ : Nonempty β] :
    range (const α) = {f : α → β | ∀ x y, f x = f y} := by
  refine (range_eq_iff _ _).mpr ⟨fun _ _ _ ↦ rfl, fun f hf ↦ ?_⟩
  rcases isEmpty_or_nonempty α with h | ⟨⟨a⟩⟩
  · exact hβ.elim fun b ↦ ⟨b, Subsingleton.elim _ _⟩
  · exact ⟨f a, funext fun x ↦ hf _ _⟩

end Set

section Pullback

open Set

variable {X Y Z}

/-- The fiber product $X \times_Y Z$. -/
/-
**Function.Pullback** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Pullback (f : X -> Y) (g : Z -> Y)
参数：f : X -> Y；g : Z -> Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber product $X \times_Y Z$.
-/
abbrev Function.Pullback (f : X → Y) (g : Z → Y) := {p : X × Z // f p.1 = g p.2}

/-- The fiber product $X \times_Y X$. -/
/-
**Function.PullbackSelf** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.PullbackSelf (f : X -> Y)
参数：f : X -> Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber product $X \times_Y X$.
-/
abbrev Function.PullbackSelf (f : X → Y) := f.Pullback f

/-- The projection from the fiber product to the first factor. -/
/-
**Function.Pullback.fst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.Pullback.fst {f : X -> Y} {g : Z -> Y} (p : f.Pullback g) : X
参数：p : f.Pullback g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the fiber product to the first factor.
-/
def Function.Pullback.fst {f : X → Y} {g : Z → Y} (p : f.Pullback g) : X := p.val.1

/-- The projection from the fiber product to the second factor. -/
/-
**Function.Pullback.snd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.Pullback.snd {f : X -> Y} {g : Z -> Y} (p : f.Pullback g) : Z
参数：p : f.Pullback g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the fiber product to the second factor.
-/
def Function.Pullback.snd {f : X → Y} {g : Z → Y} (p : f.Pullback g) : Z := p.val.2

open Function.Pullback in
/-
**Function.pullback_comm_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.pullback_comm_sq (f : X -> Y) (g : Z -> Y) : f ∘ @fst X Y Z f g =
 g ∘ @snd X Y Z f g
参数：f : X -> Y；g : Z -> Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Function.pullback_comm_sq (f : X → Y) (g : Z → Y) :
    f ∘ @fst X Y Z f g = g ∘ @snd X Y Z f g := funext fun p ↦ p.2

/-- The diagonal map $\Delta: X \to X \times_Y X$. -/
@[simps]
/-
**toPullbackDiag** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toPullbackDiag (f : X -> Y) (x : X) : f.Pullback f
参数：f : X -> Y；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal map $\Delta: X \to X \times_Y X$.
-/
def toPullbackDiag (f : X → Y) (x : X) : f.Pullback f := ⟨(x, x), rfl⟩

/-- The diagonal $\Delta(X) \subseteq X \times_Y X$. -/
/-
**Function.pullbackDiagonal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.pullbackDiagonal (f : X -> Y) : Set (f.Pullback f)
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal $\Delta(X) \subseteq X \times_Y X$.
-/
def Function.pullbackDiagonal (f : X → Y) : Set (f.Pullback f) := {p | p.fst = p.snd}

/-- Three functions between the three pairs of spaces $X_i, Y_i, Z_i$ that are compatible
  induce a function $X_1 \times_{Y_1} Z_1 \to X_2 \times_{Y_2} Z_2$. -/
/-
**Function.mapPullback** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂} {f₁ : X₁ -> Y₁} {g₁ : Z₁ -> Y₁} {
f₂ : X₂ -> Y₂} {g₂ : Z₂ -> Y₂} (mapX : X₁ -> X₂) (mapY : Y₁ -> Y₂) (mapZ : Z₁ ->
 Z₂) (commX : f₂ ∘ mapX = mapY ∘ f₁) (commZ : g₂ ∘ mapZ = mapY ∘ g₁) (p : f₁.Pul
lback g₁) : f₂.Pullback g₂
参数：mapX : X₁ -> X₂；mapY : Y₁ -> Y₂；mapZ : Z₁ -> Z₂；commX : f₂ ∘ mapX = mapY ∘ f₁
；commZ : g₂ ∘ mapZ = mapY ∘ g₁；p : f₁.Pullback g₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Three functions between the three pairs of spaces $X_i, Y_i, Z_i$ that are compa
tible
  induce a function $X_1 \times_{Y_1} Z_1 \to X_2 \times_{Y_2} Z_2$.
-/
def Function.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
    {f₁ : X₁ → Y₁} {g₁ : Z₁ → Y₁} {f₂ : X₂ → Y₂} {g₂ : Z₂ → Y₂}
    (mapX : X₁ → X₂) (mapY : Y₁ → Y₂) (mapZ : Z₁ → Z₂)
    (commX : f₂ ∘ mapX = mapY ∘ f₁) (commZ : g₂ ∘ mapZ = mapY ∘ g₁)
    (p : f₁.Pullback g₁) : f₂.Pullback g₂ :=
  ⟨(mapX p.fst, mapZ p.snd),
    (congr_fun commX _).trans <| (congr_arg mapY p.2).trans <| congr_fun commZ.symm _⟩

open Function.Pullback in
/-- The projection $(X \times_Y Z) \times_Z (X \times_Y Z) \to X \times_Y X$. -/
/-
**Function.PullbackSelf.map_fst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.PullbackSelf.map_fst {f : X -> Y} {g : Z -> Y} : (@snd X Y Z f g)
.PullbackSelf -> f.PullbackSelf
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Function.pullback_comm_sq`：Function.pullback_comm_sq (f : X -> Y) (g : Z
 -> Y) : f ∘ @fst X Y Z f g = g ∘ @snd X Y Z f g

--- 原说明 ---
The projection $(X \times_Y Z) \times_Z (X \times_Y Z) \to X \times_Y X$.
-/
def Function.PullbackSelf.map_fst {f : X → Y} {g : Z → Y} :
    (@snd X Y Z f g).PullbackSelf → f.PullbackSelf :=
  mapPullback fst g fst (pullback_comm_sq f g) (pullback_comm_sq f g)

open Function.Pullback in
/-- The projection $(X \times_Y Z) \times_X (X \times_Y Z) \to Z \times_Y Z$. -/
/-
**Function.PullbackSelf.map_snd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.PullbackSelf.map_snd {f : X -> Y} {g : Z -> Y} : (@fst X Y Z f g)
.PullbackSelf -> g.PullbackSelf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection $(X \times_Y Z) \times_X (X \times_Y Z) \to Z \times_Y Z$.
-/
def Function.PullbackSelf.map_snd {f : X → Y} {g : Z → Y} :
    (@fst X Y Z f g).PullbackSelf → g.PullbackSelf :=
  mapPullback snd f snd (pullback_comm_sq f g).symm (pullback_comm_sq f g).symm

open Function.PullbackSelf Function.Pullback
/-
**preimage_map_fst_pullbackDiagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_map_fst_pullbackDiagonal {f : X -> Y} {g : Z -> Y} : @map_fst X Y
 Z f g ⁻¹' pullbackDiagonal f = pullbackDiagonal (@snd X Y Z f g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
-/
theorem preimage_map_fst_pullbackDiagonal {f : X → Y} {g : Z → Y} :
    @map_fst X Y Z f g ⁻¹' pullbackDiagonal f = pullbackDiagonal (@snd X Y Z f g) := by
  ext ⟨⟨p₁, p₂⟩, he⟩
  simp_rw [pullbackDiagonal, mem_ofPred, Subtype.ext_iff, Prod.ext_iff]
  exact (and_iff_left he).symm
/-
**Function.Injective.preimage_pullbackDiagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.preimage_pullbackDiagonal {f : X -> Y} {g : Z -> X} (in
j : g.Injective) : mapPullback g id g (by rfl) (by rfl) ⁻¹' pullbackDiagonal f =
 pullbackDiagonal (f ∘ g)
参数：inj : g.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
theorem Function.Injective.preimage_pullbackDiagonal {f : X → Y} {g : Z → X} (inj : g.Injective) :
    mapPullback g id g (by rfl) (by rfl) ⁻¹' pullbackDiagonal f = pullbackDiagonal (f ∘ g) :=
  ext fun _ ↦ inj.eq_iff
/-
**image_toPullbackDiag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_toPullbackDiag (f : X -> Y) (s : Set X) : toPullbackDiag f '' s = pu
llbackDiagonal f inter Subtype.val ⁻¹' s ×ˢ s
参数：f : X -> Y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem image_toPullbackDiag (f : X → Y) (s : Set X) :
    toPullbackDiag f '' s = pullbackDiagonal f ∩ Subtype.val ⁻¹' s ×ˢ s := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx, hx⟩
  · obtain ⟨⟨x, y⟩, h⟩ := x
    rintro ⟨rfl : x = y, h2x⟩
    exact mem_image_of_mem _ h2x.1
/-
**range_toPullbackDiag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_toPullbackDiag (f : X -> Y) : range (toPullbackDiag f) = pullbackDia
gonal f
参数：f : X -> Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `image_toPullbackDiag`：image_toPullbackDiag (f : X -> Y) (s : Set X) : to
PullbackDiag f '' s = pullbackDiagonal f inter Subtype.val ⁻¹' s ×ˢ s
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem range_toPullbackDiag (f : X → Y) : range (toPullbackDiag f) = pullbackDiagonal f := by
  rw [← image_univ, image_toPullbackDiag, univ_prod_univ, preimage_univ, inter_univ]
/-
**injective_toPullbackDiag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_toPullbackDiag (f : X -> Y) : (toPullbackDiag f).Injective
参数：f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_toPullbackDiag (f : X → Y) : (toPullbackDiag f).Injective :=
  fun _ _ h ↦ congr_arg Prod.fst (congr_arg Subtype.val h)

end Pullback

namespace Set

section OffDiag

variable {α : Type*} {s t : Set α} {a : α}

/-
**Set.offDiag_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_mono : Monotone (offDiag : Set α -> Set (α × α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
-/
theorem offDiag_mono : Monotone (offDiag : Set α → Set (α × α)) := fun _ _ h _ =>
  And.imp (@h _) <| And.imp_left <| @h _

@[simp]
/-
**Set.offDiag_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivial := by
  simp [offDiag, Set.Nonempty, Set.Nontrivial]

@[simp]
/-
**Set.offDiag_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_eq_empty : s.offDiag = ∅ ↔ s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.offDiag_nonempty`：offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivi
al
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem offDiag_eq_empty : s.offDiag = ∅ ↔ s.Subsingleton := by
  rw [← not_nonempty_iff_eq_empty, ← not_nontrivial_iff, offDiag_nonempty.not]

alias ⟨_, Nontrivial.offDiag_nonempty⟩ := offDiag_nonempty

alias ⟨_, Subsingleton.offDiag_eq_empty⟩ := offDiag_eq_empty

variable (s t)
/-
**Set.offDiag_subset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_subset_prod : s.offDiag subseteq s ×ˢ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem offDiag_subset_prod : s.offDiag ⊆ s ×ˢ s := fun _ hx => ⟨hx.1, hx.2.1⟩
/-
**Set.offDiag_eq_sep_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_eq_sep_prod : s.offDiag = { x in s ×ˢ s | x.1 != x.2 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
-/
theorem offDiag_eq_sep_prod : s.offDiag = { x ∈ s ×ˢ s | x.1 ≠ x.2 } :=
  ext fun _ => and_assoc.symm

@[simp]
/-
**Set.offDiag_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_empty : (∅ : Set α).offDiag = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem offDiag_empty : (∅ : Set α).offDiag = ∅ := by simp

@[simp]
/-
**Set.offDiag_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_singleton (a : α) : ({a} : Set α).offDiag = ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem offDiag_singleton (a : α) : ({a} : Set α).offDiag = ∅ := by simp

@[simp]
/-
**Set.offDiag_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_univ : (univ : Set α).offDiag = (diagonal α)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem offDiag_univ : (univ : Set α).offDiag = (diagonal α)ᶜ :=
  ext <| by simp

@[simp]
/-
**Set.prod_sdiff_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_sdiff_diagonal : s ×ˢ s \ diagonal α = s.offDiag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
-/
theorem prod_sdiff_diagonal : s ×ˢ s \ diagonal α = s.offDiag :=
  ext fun _ => and_assoc

@[simp]
/-
**Set.disjoint_diagonal_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_diagonal_offDiag : Disjoint (diagonal α) s.offDiag
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem disjoint_diagonal_offDiag : Disjoint (diagonal α) s.offDiag :=
  disjoint_left.mpr fun _ hd ho => ho.2.2 hd
/-
**Set.offDiag_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_inter : (s inter t).offDiag = s.offDiag inter t.offDiag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem offDiag_inter : (s ∩ t).offDiag = s.offDiag ∩ t.offDiag :=
  ext fun x => by
    simp only [mem_offDiag, mem_inter_iff]
    tauto

variable {s t}
/-
**Set.offDiag_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_union (h : Disjoint s t) : (s union t).offDiag = s.offDiag union t
.offDiag union s ×ˢ t union t ×ˢ s
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
-/
theorem offDiag_union (h : Disjoint s t) :
    (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s := by
  ext x
  simp only [mem_offDiag, mem_union, ne_eq, mem_prod]
  constructor
  · rintro ⟨h0 | h0, h1 | h1, h2⟩ <;> simp [h0, h1, h2]
  · rintro (((⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) | ⟨h0, h1⟩) | ⟨h0, h1⟩) <;>
      simp [*, h.ne_of_mem, Ne.symm]
/-
**Set.offDiag_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：offDiag_insert (ha : a ∉ s) : (insert a s).offDiag = s.offDiag union {a} ×
ˢ s union s ×ˢ {a}
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem offDiag_insert (ha : a ∉ s) : (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  grind

end OffDiag

/-! ### Cartesian set-indexed product of sets -/


section Pi

variable {ι : Type*} {α β : ι → Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)} {i : ι}

@[simp]
/-
**Set.empty_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_pi (s : forall i, Set (α i)) : pi ∅ s = univ
参数：s : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_pi (s : ∀ i, Set (α i)) : pi ∅ s = univ := by grind
/-
**Set.subsingleton_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_univ_pi (ht : forall i, (t i).Subsingleton) : (univ.pi t).Sub
singleton
参数：ht : forall i, (t i).Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem subsingleton_univ_pi (ht : ∀ i, (t i).Subsingleton) :
    (univ.pi t).Subsingleton := fun _f hf _g hg ↦ funext fun i ↦
  (ht i) (hf _ <| mem_univ _) (hg _ <| mem_univ _)

@[simp]
/-
**Set.pi_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = univ
参数：s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = univ :=
  eq_univ_of_forall fun _ _ _ => mem_univ _

@[simp]
/-
**Set.pi_univ_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_univ_ite (s : Set ι) [DecidablePred (· in s)] (t : forall i, Set (α i))
 : (pi univ fun i => if i in s then t i else univ) = s.pi t
参数：s : Set ι；· in s；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_univ_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by grind

@[gcongr]
/-
**Set.pi_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_mono' (h : forall i in s₂, t₁ i subseteq t₂ i) (h' : s₂ subseteq s₁) : 
pi s₁ t₁ subseteq pi s₂ t₂
参数：h : forall i in s₂, t₁ i subseteq t₂ i；h' : s₂ subseteq s₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_mono' (h : ∀ i ∈ s₂, t₁ i ⊆ t₂ i) (h' : s₂ ⊆ s₁) : pi s₁ t₁ ⊆ pi s₂ t₂ :=
  fun _ hx i hi ↦ h i hi (hx i (h' hi))
/-
**Set.pi_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ subseteq pi s t₂
参数：h : forall i in s, t₁ i subseteq t₂ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_mono'`：pi_mono' (h : forall i in s₂, t₁ i subseteq t₂ i) (h' : s₂
 subseteq s₁) : pi s₁ t₁ subseteq pi s₂ t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem pi_mono (h : ∀ i ∈ s, t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ := pi_mono' h Subset.rfl
/-
**Set.pi_inter_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_inter_distrib : (s.pi fun i => t i inter t₁ i) = s.pi t inter s.pi t₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_inter_distrib : (s.pi fun i => t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ := by grind
/-
**Set.pi_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_congr (h : s₁ = s₂) (h' : forall i in s₁, t₁ i = t₂ i) : s₁.pi t₁ = s₂.
pi t₂
参数：h : s₁ = s₂；h' : forall i in s₁, t₁ i = t₂ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_congr (h : s₁ = s₂) (h' : ∀ i ∈ s₁, t₁ i = t₂ i) : s₁.pi t₁ = s₂.pi t₂ := by grind
/-
**Set.pi_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_eq_empty (hs : i in s) (ht : t i = ∅) : s.pi t = ∅
参数：hs : i in s；ht : t i = ∅。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_eq_empty (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ := by grind
/-
**Set.univ_pi_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅
参数：ht : t i = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_eq_empty`：pi_eq_empty (hs : i in s) (ht : t i = ∅) : s.pi t = ∅
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht
/-
**Set.pi_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_nonempty_iff : (s.pi t).Nonempty ↔ forall i, exists x, i in s -> x in t
 i
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_nonempty_iff : (s.pi t).Nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i := by
  simp [Classical.skolem, Set.Nonempty]
/-
**Set.univ_pi_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ forall i, (t i).Nonempty
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ ∀ i, (t i).Nonempty := by
  simp [Classical.skolem, Set.Nonempty]
/-
**Set.pi_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_eq_empty_iff : s.pi t = ∅ ↔ exists i, IsEmpty (α i) ∨ i in s ∧ t i = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Set.pi_nonempty_iff`：pi_nonempty_iff : (s.pi t).Nonempty ↔ forall i, exi
sts x, i in s -> x in t i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅ := by
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff]
  push Not
  refine exists_congr fun i => ?_
  cases isEmpty_or_nonempty (α i) <;> simp [*, forall_and, eq_empty_iff_forall_notMem]

@[simp]
/-
**Set.univ_pi_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_eq_empty_iff : pi univ t = ∅ ↔ exists i, t i = ∅
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ := by
  simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

@[simp]
/-
**Set.univ_pi_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_empty [h : Nonempty ι] : pi univ (fun _ => ∅ : forall i, Set (α i)
) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.univ_pi_eq_empty_iff`：univ_pi_eq_empty_iff : pi univ t = ∅ ↔ exists 
i, t i = ∅
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
theorem univ_pi_empty [h : Nonempty ι] : pi univ (fun _ => ∅ : ∀ i, Set (α i)) = ∅ :=
  univ_pi_eq_empty_iff.2 <| h.elim fun x => ⟨x, rfl⟩

@[simp]
/-
**Set.disjoint_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_univ_pi : Disjoint (pi univ t₁) (pi univ t₂) ↔ exists i, Disjoint
 (t₁ i) (t₂ i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_univ_pi : Disjoint (pi univ t₁) (pi univ t₂) ↔ ∃ i, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, univ_pi_eq_empty_iff]
/-
**Set.Disjoint.set_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set.Disjoint`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {s : Set ι} {t₁ t₂ : (i : ι) → Set (α 
i)} {i : ι},   i ∈ s → Disjoint (t₁ i) (t₂ i) → Disjoint (s.pi t₁) (s.pi t₂)
参数：i : ι；α i；t₁ i；t₂ i；s.pi t₁；s.pi t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Disjoint.set_pi (hi : i ∈ s) (ht : Disjoint (t₁ i) (t₂ i)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_left.2 fun _ h₁ h₂ => disjoint_left.1 ht (h₁ _ hi) (h₂ _ hi)
/-
**Set.uniqueElim_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：uniqueElim_preimage [Unique ι] (t : forall i, Set (α i)) : uniqueElim ⁻¹' 
pi univ t = t (default : ι)
参数：t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem uniqueElim_preimage [Unique ι] (t : ∀ i, Set (α i)) :
    uniqueElim ⁻¹' pi univ t = t (default : ι) := by ext; simp [Unique.forall_iff]

section Nonempty

variable [∀ i, Nonempty (α i)]

/-
**Set.pi_eq_empty_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_eq_empty_iff' : s.pi t = ∅ ↔ exists i in s, t i = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_eq_empty_iff' : s.pi t = ∅ ↔ ∃ i ∈ s, t i = ∅ := by simp [pi_eq_empty_iff]

@[simp]
/-
**Set.disjoint_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_pi : Disjoint (s.pi t₁) (s.pi t₂) ↔ exists i in s, Disjoint (t₁ i
) (t₂ i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_pi : Disjoint (s.pi t₁) (s.pi t₂) ↔ ∃ i ∈ s, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, pi_eq_empty_iff']

end Nonempty

@[simp]
/-
**Set.insert_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_pi (i : ι) (s : Set ι) (t : forall i, Set (α i)) : pi (insert i s) 
t = eval i ⁻¹' t i inter pi s t
参数：i : ι；s : Set ι；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_pi (i : ι) (s : Set ι) (t : ∀ i, Set (α i)) :
    pi (insert i s) t = eval i ⁻¹' t i ∩ pi s t := by grind

@[simp]
/-
**Set.singleton_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_pi (i : ι) (t : forall i, Set (α i)) : pi {i} t = eval i ⁻¹' t i
参数：i : ι；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_pi (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = eval i ⁻¹' t i := by grind
/-
**Set.singleton_pi'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_pi' (i : ι) (t : forall i, Set (α i)) : pi {i} t = { x | x i in 
t i }
参数：i : ι；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.singleton_pi`：singleton_pi (i : ι) (t : forall i, Set (α i)) : pi {i
} t = eval i ⁻¹' t i
-/
theorem singleton_pi' (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = { x | x i ∈ t i } :=
  singleton_pi i t
/-
**Set.univ_pi_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_singleton (f : forall i, α i) : (pi univ fun i => {f i}) = ({f} : 
Set (forall i, α i))
参数：f : forall i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem univ_pi_singleton (f : ∀ i, α i) : (pi univ fun i => {f i}) = ({f} : Set (∀ i, α i)) :=
  ext fun g => by simp [funext_iff]
/-
**Set.preimage_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_pi (s : Set ι) (t : forall i, Set (β i)) (f : forall i, α i -> β 
i) : (fun (g : forall i, α i) i => f _ (g i)) ⁻¹' s.pi t = s.pi fun i => f i ⁻¹'
 t i
参数：s : Set ι；t : forall i, Set (β i)；f : forall i, α i -> β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_pi (s : Set ι) (t : ∀ i, Set (β i)) (f : ∀ i, α i → β i) :
    (fun (g : ∀ i, α i) i => f _ (g i)) ⁻¹' s.pi t = s.pi fun i => f i ⁻¹' t i :=
  rfl
/-
**Set.pi_if** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_if {p : ι -> Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : forall i,
 Set (α i)) : (pi s fun i => if p i then t₁ i else t₂ i) = pi ({ i in s | p i })
 t₁ inter pi ({ i in s | ¬p i }) t₂
参数：s : Set ι；t₁ t₂ : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem pi_if {p : ι → Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : ∀ i, Set (α i)) :
    (pi s fun i => if p i then t₁ i else t₂ i) =
      pi ({ i ∈ s | p i }) t₁ ∩ pi ({ i ∈ s | ¬p i }) t₂ := by
  ext f
  refine ⟨fun h => ?_, ?_⟩
  · constructor <;>
      · rintro i ⟨his, hpi⟩
        simpa [*] using h i
  · rintro ⟨ht₁, ht₂⟩ i his
    by_cases p i <;> simp_all
/-
**Set.union_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_pi : (s₁ union s₂).pi t = s₁.pi t inter s₂.pi t
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem union_pi : (s₁ ∪ s₂).pi t = s₁.pi t ∩ s₂.pi t := by
  simp [pi, or_imp, forall_and, ofPred_and]
/-
**Set.union_pi_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_pi_inter (ht₁ : forall i ∉ s₁, t₁ i = univ) (ht₂ : forall i ∉ s₂, t₂
 i = univ) : (s₁ union s₂).pi (fun i => t₁ i inter t₂ i) = s₁.pi t₁ inter s₂.pi 
t₂
参数：ht₁ : forall i ∉ s₁, t₁ i = univ；ht₂ : forall i ∉ s₂, t₂ i = univ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_pi_inter
    (ht₁ : ∀ i ∉ s₁, t₁ i = univ) (ht₂ : ∀ i ∉ s₂, t₂ i = univ) :
    (s₁ ∪ s₂).pi (fun i ↦ t₁ i ∩ t₂ i) = s₁.pi t₁ ∩ s₂.pi t₂ := by
  grind

@[simp]
/-
**Set.pi_inter_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_inter_compl (s : Set ι) : pi s t inter pi sᶜ t = pi univ t
参数：s : Set ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_inter_compl (s : Set ι) : pi s t ∩ pi sᶜ t = pi univ t := by grind
/-
**Set.pi_update_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_update_of_notMem [DecidableEq ι] (hi : i ∉ s) (f : forall j, α j) (a : 
α i) (t : forall j, α j -> Set (β j)) : (s.pi fun j => t j (update f i a j)) = s
.pi fun j => t j (f j)
参数：hi : i ∉ s；f : forall j, α j；a : α i；t : forall j, α j -> Set (β j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_congr`：pi_congr (h : s₁ = s₂) (h' : forall i in s₁, t₁ i = t₂ i) 
: s₁.pi t₁ = s₂.pi t₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem pi_update_of_notMem [DecidableEq ι] (hi : i ∉ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) : (s.pi fun j => t j (update f i a j)) = s.pi fun j => t j (f j) :=
  (pi_congr rfl) fun j hj => by
    rw [update_of_ne]
    exact fun h => hi (h ▸ hj)
/-
**Set.pi_update_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_update_of_mem [DecidableEq ι] (hi : i in s) (f : forall j, α j) (a : α 
i) (t : forall j, α j -> Set (β j)) : (s.pi fun j => t j (update f i a j)) = { x
 | x i in t i a } inter (s \ {i}).pi fun j => t j (f j)
参数：hi : i in s；f : forall j, α j；a : α i；t : forall j, α j -> Set (β j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.union_pi`：union_pi : (s₁ union s₂).pi t = s₁.pi t inter s₂.pi t
· 使用定理 `Set.singleton_pi'`：singleton_pi' (i : ι) (t : forall i, Set (α i)) : pi 
{i} t = { x | x i in t i }
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Set.pi_update_of_notMem`：pi_update_of_notMem [DecidableEq ι] (hi : i ∉ s
) (f : forall j, α j) (a : α i) (t : forall j, α j -> Set (β j)) : (s.pi fun j =
> t j (update…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem pi_update_of_mem [DecidableEq ι] (hi : i ∈ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (s.pi fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
  calc
    (s.pi fun j => t j (update f i a j)) = ({i} ∪ s \ {i}).pi fun j => t j (update f i a j) := by
        rw [union_sdiff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) := by
        rw [union_pi, singleton_pi', update_self, pi_update_of_notMem]; simp
/-
**Set.univ_pi_update** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_update [DecidableEq ι] {β : ι -> Type*} (i : ι) (f : forall j, α j
) (a : α i) (t : forall j, α j -> Set (β j)) : (pi univ fun j => t j (update f i
 a j)) = { x | x i in t i a } inter pi {i}ᶜ fun j => t j (f j)
参数：i : ι；f : forall j, α j；a : α i；t : forall j, α j -> Set (β j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_update_of_mem`：pi_update_of_mem [DecidableEq ι] (hi : i in s) (f 
: forall j, α j) (a : α i) (t : forall j, α j -> Set (β j)) : (s.pi fun j => t j
 (update f…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem univ_pi_update [DecidableEq ι] {β : ι → Type*} (i : ι) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (pi univ fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ pi {i}ᶜ fun j => t j (f j) := by
  rw [compl_eq_univ_sdiff, ← pi_update_of_mem (mem_univ _)]
/-
**Set.univ_pi_update_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) : pi univ (upd
ate (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻¹' s
参数：i : ι；s : Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_pi_update`：univ_pi_update [DecidableEq ι] {β : ι -> Type*} (i :
 ι) (f : forall j, α j) (a : α i) (t : forall j, α j -> Set (β j)) : (pi univ fu
n j => t…
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.preimage.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set β), 
f ⁻¹' s = {x | f x ∈ s}
-/
theorem univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) :
    pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻¹' s := by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t, pi_univ, inter_univ, preimage]
/-
**Set.eval_image_pi_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eval_image_pi_subset (hs : i in s) : eval i '' s.pi t subseteq t i
参数：hs : i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem eval_image_pi_subset (hs : i ∈ s) : eval i '' s.pi t ⊆ t i :=
  image_subset_iff.2 fun _ hf => hf i hs
/-
**Set.eval_image_univ_pi_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eval_image_univ_pi_subset : eval i '' pi univ t subseteq t i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eval_image_pi_subset`：eval_image_pi_subset (hs : i in s) : eval i ''
 s.pi t subseteq t i
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem eval_image_univ_pi_subset : eval i '' pi univ t ⊆ t i :=
  eval_image_pi_subset (mem_univ i)
/-
**Set.subset_eval_image_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_eval_image_pi (ht : (s.pi t).Nonempty) (i : ι) : t i subseteq eval 
i '' s.pi t
参数：ht : (s.pi t).Nonempty；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem subset_eval_image_pi (ht : (s.pi t).Nonempty) (i : ι) : t i ⊆ eval i '' s.pi t := by
  classical
  obtain ⟨f, hf⟩ := ht
  refine fun y hy => ⟨update f i y, fun j hj => ?_, update_self ..⟩
  obtain rfl | hji := eq_or_ne j i <;> simp [*, hf _ hj]
/-
**Set.eval_image_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eval_image_pi (hs : i in s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = 
t i
参数：hs : i in s；ht : (s.pi t).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.eval_image_pi_subset`：eval_image_pi_subset (hs : i in s) : eval i ''
 s.pi t subseteq t i
· 使用定理 `Set.subset_eval_image_pi`：subset_eval_image_pi (ht : (s.pi t).Nonempty) 
(i : ι) : t i subseteq eval i '' s.pi t
-/
theorem eval_image_pi (hs : i ∈ s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = t i :=
  (eval_image_pi_subset hs).antisymm (subset_eval_image_pi ht i)
/-
**Set.eval_image_pi_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eval_image_pi_of_notMem [Decidable (s.pi t).Nonempty] (hi : i ∉ s) : eval 
i '' s.pi t = if (s.pi t).Nonempty then univ else ∅
参数：s.pi t；hi : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_image_pi_of_notMem [Decidable (s.pi t).Nonempty] (hi : i ∉ s) :
    eval i '' s.pi t = if (s.pi t).Nonempty then univ else ∅ := by
  classical
  ext xᵢ
  simp only [eval, mem_image, mem_pi, Set.Nonempty, mem_ite_empty_right, mem_univ, and_true]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨Function.update x i xᵢ, ?_⟩
    simpa +contextual [(ne_of_mem_of_not_mem · hi)]

@[simp]
/-
**Set.eval_image_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eval_image_univ_pi (ht : (pi univ t).Nonempty) : (fun f : forall i, α i =>
 f i) '' pi univ t = t i
参数：ht : (pi univ t).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eval_image_pi`：eval_image_pi (hs : i in s) (ht : (s.pi t).Nonempty) 
: eval i '' s.pi t = t i
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem eval_image_univ_pi (ht : (pi univ t).Nonempty) :
    (fun f : ∀ i, α i => f i) '' pi univ t = t i :=
  eval_image_pi (mem_univ i) ht
/-
**Set.piMap_mapsTo_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piMap_mapsTo_pi {I : Set ι} {f : forall i, α i -> β i} {s : forall i, Set 
(α i)} {t : forall i, Set (β i)} (h : forall i in I, MapsTo (f i) (s i) (t i)) :
 MapsTo (Pi.map f) (I.pi s) (I.pi t)
参数：α i；β i；h : forall i in I, MapsTo (f i) (s i) (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piMap_mapsTo_pi {I : Set ι} {f : ∀ i, α i → β i} {s : ∀ i, Set (α i)} {t : ∀ i, Set (β i)}
    (h : ∀ i ∈ I, MapsTo (f i) (s i) (t i)) :
    MapsTo (Pi.map f) (I.pi s) (I.pi t) :=
  fun _x hx i hi => h i hi (hx i hi)
/-
**Set.piMap_image_pi_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piMap_image_pi_subset {f : forall i, α i -> β i} (t : forall i, Set (α i))
 : Pi.map f '' s.pi t subseteq s.pi fun i => f i '' t i
参数：t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.piMap_mapsTo_pi`：piMap_mapsTo_pi {I : Set ι} {f : forall i, α i -> β
 i} {s : forall i, Set (α i)} {t : forall i, Set (β i)} (h : forall i in I, Maps
To (f i) …
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem piMap_image_pi_subset {f : ∀ i, α i → β i} (t : ∀ i, Set (α i)) :
    Pi.map f '' s.pi t ⊆ s.pi fun i ↦ f i '' t i :=
  image_subset_iff.2 <| piMap_mapsTo_pi fun _ _ => mapsTo_image _ _
/-
**Set.piMap_image_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piMap_image_pi {f : forall i, α i -> β i} (hf : forall i ∉ s, Surjective (
f i)) (t : forall i, Set (α i)) : Pi.map f '' s.pi t = s.pi fun i => f i '' t i
参数：hf : forall i ∉ s, Surjective (f i)；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.piMap_image_pi_subset`：piMap_image_pi_subset {f : forall i, α i -> β
 i} (t : forall i, Set (α i)) : Pi.map f '' s.pi t subseteq s.pi fun i => f i ''
 t i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem piMap_image_pi {f : ∀ i, α i → β i} (hf : ∀ i ∉ s, Surjective (f i)) (t : ∀ i, Set (α i)) :
    Pi.map f '' s.pi t = s.pi fun i ↦ f i '' t i := by
  refine Subset.antisymm (piMap_image_pi_subset _) fun b hb => ?_
  have (i : ι) : ∃ a, f i a = b i ∧ (i ∈ s → a ∈ t i) := by
    if hi : i ∈ s then
      exact (hb i hi).imp fun a ⟨hat, hab⟩ ↦ ⟨hab, fun _ ↦ hat⟩
    else
      exact (hf i hi (b i)).imp fun a ha ↦ ⟨ha, (absurd · hi)⟩
  choose a hab hat using this
  exact ⟨a, hat, funext hab⟩
/-
**Set.piMap_image_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piMap_image_univ_pi (f : forall i, α i -> β i) (t : forall i, Set (α i)) :
 Pi.map f '' univ.pi t = univ.pi fun i => f i '' t i
参数：f : forall i, α i -> β i；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piMap_image_pi`：piMap_image_pi {f : forall i, α i -> β i} (hf : fora
ll i ∉ s, Surjective (f i)) (t : forall i, Set (α i)) : Pi.map f '' s.pi t = s.p
i fun i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem piMap_image_univ_pi (f : ∀ i, α i → β i) (t : ∀ i, Set (α i)) :
    Pi.map f '' univ.pi t = univ.pi fun i ↦ f i '' t i :=
  piMap_image_pi (by simp) t

@[simp]
/-
**Set.range_piMap** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_piMap (f : forall i, α i -> β i) : range (Pi.map f) = pi univ fun i 
=> range (f i)
参数：f : forall i, α i -> β i。
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
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_piMap (f : ∀ i, α i → β i) : range (Pi.map f) = pi univ fun i ↦ range (f i) := by
  simp only [← image_univ, ← piMap_image_univ_pi, pi_univ]
/-
**Set.subset_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_pi_iff {s'} : s' subseteq pi s t ↔ forall i in s, s' subseteq (· i)
 ⁻¹' t i
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_pi_iff {s'} : s' ⊆ pi s t ↔ ∀ i ∈ s, s' ⊆ (· i) ⁻¹' t i := by
  grind
/-
**Set.update_mem_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：update_mem_pi_iff [DecidableEq ι] {a : forall i, α i} {i : ι} {b : α i} : 
update a i b in pi s t ↔ a in pi (s \ {i}) t ∧ (i in s -> b in t i)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem update_mem_pi_iff [DecidableEq ι] {a : ∀ i, α i} {i : ι} {b : α i} :
    update a i b ∈ pi s t ↔ a ∈ pi (s \ {i}) t ∧ (i ∈ s → b ∈ t i) := by grind
/-
**Set.update_mem_pi_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：update_mem_pi_iff_of_mem [DecidableEq ι] {a : forall i, α i} {i : ι} {b : 
α i} (ha : a in pi s t) : update a i b in pi s t ↔ i in s -> b in t i
参数：ha : a in pi s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.update_mem_pi_iff`：update_mem_pi_iff [DecidableEq ι] {a : forall i, 
α i} {i : ι} {b : α i} : update a i b in pi s t ↔ a in pi (s \ {i}) t ∧ (i in s 
-> b in t i…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem update_mem_pi_iff_of_mem [DecidableEq ι] {a : ∀ i, α i} {i : ι} {b : α i}
    (ha : a ∈ pi s t) : update a i b ∈ pi s t ↔ i ∈ s → b ∈ t i := by
  rw [update_mem_pi_iff, and_iff_right]
  exact fun j hj => ha j hj.1
/-
**Set.univ_pi_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_eq_singleton_iff {a} : pi univ t = {a} ↔ forall i, t i = {a i}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.update_mem_pi_iff_of_mem`：update_mem_pi_iff_of_mem [DecidableEq ι] {
a : forall i, α i} {i : ι} {b : α i} (ha : a in pi s t) : update a i b in pi s t
 ↔ i in s -> b in …
· 使用定理 `trivial`：True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem univ_pi_eq_singleton_iff {a} : pi univ t = {a} ↔ ∀ i, t i = {a i} := by
  classical
  simp only [eq_singleton_iff_unique_mem]
  refine ⟨fun ⟨h₁, h₂⟩ i => ⟨by grind, fun x hx => ?_⟩, by grind⟩
  rw [← h₂ _ fun j _ => (update_mem_pi_iff_of_mem h₁).mpr (fun _ => hx) j trivial, update_self]
/-
**Set.pi_subset_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_subset_pi_iff : pi s t₁ subseteq pi s t₂ ↔ (forall i in s, t₁ i subsete
q t₂ i) ∨ pi s t₁ = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.eval_image_pi`：eval_image_pi (hs : i in s) (ht : (s.pi t).Nonempty) 
: eval i '' s.pi t = t i
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.pi_mono`：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ s
ubseteq pi s t₂
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem pi_subset_pi_iff : pi s t₁ ⊆ pi s t₂ ↔ (∀ i ∈ s, t₁ i ⊆ t₂ i) ∨ pi s t₁ = ∅ := by
  refine
    ⟨fun h => or_iff_not_imp_right.2 ?_, fun h => h.elim pi_mono fun h' => h'.symm ▸ empty_subset _⟩
  rw [← Ne, ← nonempty_iff_ne_empty]
  intro hne i hi
  simpa only [eval_image_pi hi hne, eval_image_pi hi (hne.mono h)] using
    image_mono (f := fun f : ∀ i, α i => f i) h
/-
**Set.univ_pi_subset_univ_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_subset_univ_pi_iff : pi univ t₁ subseteq pi univ t₂ ↔ (forall i, t
₁ i subseteq t₂ i) ∨ exists i, t₁ i = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem univ_pi_subset_univ_pi_iff :
    pi univ t₁ ⊆ pi univ t₂ ↔ (∀ i, t₁ i ⊆ t₂ i) ∨ ∃ i, t₁ i = ∅ := by simp [pi_subset_pi_iff]
/-
**Set.eval_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eval_preimage [DecidableEq ι] {s : Set (α i)} : eval i ⁻¹' s = pi univ (up
date (fun _ => univ) i s)
参数：α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eval_preimage [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun _ => univ) i s) := by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]
/-
**Set.eval_preimage'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eval_preimage' [DecidableEq ι] {s : Set (α i)} : eval i ⁻¹' s = pi {i} (up
date (fun _ => univ) i s)
参数：α i。
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
· 使用定理 `Set.singleton_pi`：singleton_pi (i : ι) (t : forall i, Set (α i)) : pi {i
} t = eval i ⁻¹' t i
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eval_preimage' [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun _ => univ) i s) := by
  ext
  simp
/-
**Set.update_preimage_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：update_preimage_pi [DecidableEq ι] {f : forall i, α i} (hi : i in s) (hf :
 forall j in s, j != i -> f j in t j) : update f i ⁻¹' s.pi t = t i
参数：hi : i in s；hf : forall j in s, j != i -> f j in t j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem update_preimage_pi [DecidableEq ι] {f : ∀ i, α i} (hi : i ∈ s)
    (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) : update f i ⁻¹' s.pi t = t i := by
  ext x
  refine ⟨fun h => ?_, fun hx j hj => ?_⟩
  · convert! h i hi
    simp
  · obtain rfl | h := eq_or_ne j i
    · simpa
    · rw [update_of_ne h]
      exact hf j hj h
/-
**Set.update_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：update_image [DecidableEq ι] (x : (i : ι) -> β i) (i : ι) (s : Set (β i)) 
: update x i '' s = Set.univ.pi (update (fun j => {x j}) i s)
参数：x : (i : ι) -> β i；i : ι；s : Set (β i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem update_image [DecidableEq ι] (x : (i : ι) → β i) (i : ι) (s : Set (β i)) :
    update x i '' s = Set.univ.pi (update (fun j ↦ {x j}) i s) := by
  ext y
  simp only [mem_image, update_eq_iff, ne_eq, and_left_comm (a := _ ∈ s), exists_eq_left, mem_pi,
    mem_univ, true_implies]
  rw [forall_update_iff (p := fun x s => y x ∈ s)]
  simp [eq_comm]
/-
**Set.update_preimage_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：update_preimage_univ_pi [DecidableEq ι] {f : forall i, α i} (hf : forall j
 != i, f j in t j) : update f i ⁻¹' pi univ t = t i
参数：hf : forall j != i, f j in t j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.update_preimage_pi`：update_preimage_pi [DecidableEq ι] {f : forall i
, α i} (hi : i in s) (hf : forall j in s, j != i -> f j in t j) : update f i ⁻¹'
 s.pi t = t …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem update_preimage_univ_pi [DecidableEq ι] {f : ∀ i, α i} (hf : ∀ j ≠ i, f j ∈ t j) :
    update f i ⁻¹' pi univ t = t i :=
  update_preimage_pi (mem_univ i) fun j _ => hf j
/-
**Set.subset_pi_eval_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_pi_eval_image (s : Set ι) (u : Set (forall i, α i)) : u subseteq pi
 s fun i => eval i '' u
参数：s : Set ι；u : Set (forall i, α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_pi_eval_image (s : Set ι) (u : Set (∀ i, α i)) : u ⊆ pi s fun i => eval i '' u :=
  fun f hf _ _ => ⟨f, hf, rfl⟩
/-
**Set.univ_pi_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_ite (s : Set ι) [DecidablePred (· in s)] (t : forall i, Set (α i))
 : (pi univ fun i => if i in s then t i else univ) = s.pi t
参数：s : Set ι；· in s；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem univ_pi_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t := by grind
/-
**Set.uncurry_preimage_prod_pi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：uncurry_preimage_prod_pi {κ α : Type*} (s : Set ι) (t : Set κ) (u : ι × κ 
-> Set α) : Function.uncurry ⁻¹' (s ×ˢ t).pi u = s.pi (fun i => t.pi fun j => u 
⟨i, j⟩)
参数：s : Set ι；t : Set κ；u : ι × κ -> Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uncurry_preimage_prod_pi {κ α : Type*} (s : Set ι) (t : Set κ) (u : ι × κ → Set α) :
    Function.uncurry ⁻¹' (s ×ˢ t).pi u = s.pi (fun i ↦ t.pi fun j ↦ u ⟨i, j⟩) := by grind

end Pi

end Set

namespace Equiv

open Set
variable {ι ι' : Type*} {α : ι → Type*}

/-
**Equiv.piCongrLeft_symm_preimage_pi** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_symm_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : forall i, Set 
(α i)) : (f.piCongrLeft α).symm ⁻¹' s.pi (fun i' => t <| f i') = (f '' s).pi t
参数：f : ι' ≃ ι；s : Set ι'；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
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
· 使用引理 `Equiv.piCongrLeft_symm_apply`：piCongrLeft_symm_apply (g : forall b, P b)
 (a : α) : (piCongrLeft P e).symm g a = g (e a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem piCongrLeft_symm_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : ∀ i, Set (α i)) :
    (f.piCongrLeft α).symm ⁻¹' s.pi (fun i' => t <| f i') = (f '' s).pi t := by
  ext; simp
/-
**Equiv.piCongrLeft_symm_preimage_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_symm_preimage_univ_pi (f : ι' ≃ ι) (t : forall i, Set (α i)) :
 (f.piCongrLeft α).symm ⁻¹' univ.pi (fun i' => t <| f i') = univ.pi t
参数：f : ι' ≃ ι；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.piCongrLeft_symm_preimage_pi`：piCongrLeft_symm_preimage_pi (f : ι'
 ≃ ι) (s : Set ι') (t : forall i, Set (α i)) : (f.piCongrLeft α).symm ⁻¹' s.pi (
fun i' => t <| f i') = (…
-/
theorem piCongrLeft_symm_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    (f.piCongrLeft α).symm ⁻¹' univ.pi (fun i' => t <| f i') = univ.pi t := by
  simpa [f.surjective.range_eq] using piCongrLeft_symm_preimage_pi f univ t
/-
**Equiv.piCongrLeft_preimage_pi** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : forall i, Set (α i)
) : f.piCongrLeft α ⁻¹' (f '' s).pi t = s.pi fun i => t (f i)
参数：f : ι' ≃ ι；s : Set ι'；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Equiv.piCongrLeft_symm_apply`：piCongrLeft_symm_apply (g : forall b, P b)
 (a : α) : (piCongrLeft P e).symm g a = g (e a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem piCongrLeft_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : ∀ i, Set (α i)) :
    f.piCongrLeft α ⁻¹' (f '' s).pi t = s.pi fun i => t (f i) := by
  apply Set.ext
  rw [← (f.piCongrLeft α).symm.forall_congr_right]
  simp
/-
**Equiv.piCongrLeft_preimage_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：piCongrLeft_preimage_univ_pi (f : ι' ≃ ι) (t : forall i, Set (α i)) : f.pi
CongrLeft α ⁻¹' univ.pi t = univ.pi fun i => t (f i)
参数：f : ι' ≃ ι；t : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.piCongrLeft_preimage_pi`：piCongrLeft_preimage_pi (f : ι' ≃ ι) (s :
 Set ι') (t : forall i, Set (α i)) : f.piCongrLeft α ⁻¹' (f '' s).pi t = s.pi fu
n i => t (f i)
-/
theorem piCongrLeft_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    f.piCongrLeft α ⁻¹' univ.pi t = univ.pi fun i => t (f i) := by
  simpa [f.surjective.range_eq] using piCongrLeft_preimage_pi f univ t
/-
**Equiv.sumPiEquivProdPi_symm_preimage_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`
。
形式化陈述：sumPiEquivProdPi_symm_preimage_univ_pi (π : ι oplus ι' -> Type*) (t : fora
ll i, Set (π i)) : (sumPiEquivProdPi π).symm ⁻¹' univ.pi t = univ.pi (fun i => t
 (.inl i)) ×ˢ univ.pi fun i => t (.inr i)
参数：π : ι oplus ι' -> Type*；t : forall i, Set (π i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
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
· 使用定理 `Equiv.sumPiEquivProdPi_symm_apply`：∀ {ι : Type u_10} {ι' : Type u_11} (π
 : ι ⊕ ι' → Type u_9)   (g : ((i : ι) → π (Sum.inl i)) × ((i' : ι') → π (Sum.inr
 i'))) (t : ι ⊕ ι'),   …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sumPiEquivProdPi_symm_preimage_univ_pi (π : ι ⊕ ι' → Type*) (t : ∀ i, Set (π i)) :
    (sumPiEquivProdPi π).symm ⁻¹' univ.pi t =
    univ.pi (fun i => t (.inl i)) ×ˢ univ.pi fun i => t (.inr i) := by
  ext
  simp

end Equiv

namespace Set

variable {α β γ δ : Type*} {s : Set α} {f : α → β}

section graphOn
variable {x : α × β}

/-
**Set.mem_graphOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x : α × β}, x ∈ S
et.graphOn f s ↔ x.1 ∈ s ∧ f x.1 = x.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_graphOn : x ∈ s.graphOn f ↔ x.1 ∈ s ∧ f x.1 = x.2 := by aesop (add simp graphOn)
/-
**Set.graphOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β), Set.graphOn f ∅ = ∅
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
-/
@[simp] lemma graphOn_empty (f : α → β) : graphOn f ∅ = ∅ := image_empty _
/-
**Set.graphOn_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.graphOn f s =
 ∅ ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_eq_empty`：image_eq_empty {α β} {f : α -> β} {s : Set α} : f ''
 s = ∅ ↔ s = ∅
-/
@[simp] lemma graphOn_eq_empty : graphOn f s = ∅ ↔ s = ∅ := image_eq_empty
/-
**Set.graphOn_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, (Set.graphOn f s)
.Nonempty ↔ s.Nonempty
参数：Set.graphOn f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
-/
@[simp] lemma graphOn_nonempty : (s.graphOn f).Nonempty ↔ s.Nonempty := image_nonempty

protected alias ⟨_, Nonempty.graphOn⟩ := graphOn_nonempty

@[simp]
/-
**Set.graphOn_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_union (f : α -> β) (s t : Set α) : graphOn f (s union t) = graphOn
 f s union graphOn f t
参数：f : α -> β；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
-/
lemma graphOn_union (f : α → β) (s t : Set α) : graphOn f (s ∪ t) = graphOn f s ∪ graphOn f t :=
  image_union ..

@[simp]
/-
**Set.graphOn_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_singleton (f : α -> β) (x : α) : graphOn f {x} = {(x, f x)}
参数：f : α -> β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
-/
lemma graphOn_singleton (f : α → β) (x : α) : graphOn f {x} = {(x, f x)} :=
  image_singleton ..

@[simp]
/-
**Set.graphOn_insert** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_insert (f : α -> β) (x : α) (s : Set α) : graphOn f (insert x s) =
 insert (x, f x) (graphOn f s)
参数：f : α -> β；x : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
-/
lemma graphOn_insert (f : α → β) (x : α) (s : Set α) :
    graphOn f (insert x s) = insert (x, f x) (graphOn f s) :=
  image_insert_eq ..

@[simp]
/-
**Set.image_fst_graphOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_fst_graphOn (f : α -> β) (s : Set α) : Prod.fst '' graphOn f s = s
参数：f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image_fst_graphOn (f : α → β) (s : Set α) : Prod.fst '' graphOn f s = s := by
  simp [graphOn, image_image]
/-
**Set.image_snd_graphOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} (f : α → β), Prod.snd '' Set.g
raphOn f s = f '' s
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma image_snd_graphOn (f : α → β) : Prod.snd '' s.graphOn f = f '' s := by ext x; simp
/-
**Set.fst_injOn_graph** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：fst_injOn_graph : (s.graphOn f).InjOn Prod.fst
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma fst_injOn_graph : (s.graphOn f).InjOn Prod.fst := by aesop (add simp InjOn)
/-
**Set.graphOn_comp** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_comp (s : Set α) (f : α -> β) (g : β -> γ) : s.graphOn (g ∘ f) = (
fun x => (x.1, g x.2)) '' s.graphOn f
参数：s : Set α；f : α -> β；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
lemma graphOn_comp (s : Set α) (f : α → β) (g : β → γ) :
    s.graphOn (g ∘ f) = (fun x ↦ (x.1, g x.2)) '' s.graphOn f := by
  simpa using! image_comp (fun x ↦ (x.1, g x.2)) (fun x ↦ (x, f x)) _
/-
**Set.graphOn_univ_eq_range** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_univ_eq_range : univ.graphOn f = range fun x => (x, f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma graphOn_univ_eq_range : univ.graphOn f = range fun x ↦ (x, f x) := image_univ
/-
**Set.graphOn_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f g : α → β}, Set.graphOn f s
 = Set.graphOn g s ↔ Set.EqOn f g s
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma graphOn_inj {g : α → β} : s.graphOn f = s.graphOn g ↔ s.EqOn f g := by
  simp [Set.ext_iff, forall_comm, EqOn]
/-
**Set.graphOn_prod_graphOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_prod_graphOn (s : Set α) (t : Set β) (f : α -> γ) (g : β -> δ) : s
.graphOn f ×ˢ t.graphOn g = Equiv.prodProdProdComm .. ⁻¹' (s ×ˢ t).graphOn (Prod
.map f g)
参数：s : Set α；t : Set β；f : α -> γ；g : β -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.prodProdProdComm_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type
 u_11) (δ : Type u_12) (abcd : (α × β) × γ × δ),   (Equiv.prodProdProdComm α β γ
 δ) abcd = ((abcd.…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma graphOn_prod_graphOn (s : Set α) (t : Set β) (f : α → γ) (g : β → δ) :
    s.graphOn f ×ˢ t.graphOn g = Equiv.prodProdProdComm .. ⁻¹' (s ×ˢ t).graphOn (Prod.map f g) := by
  aesop
/-
**Set.graphOn_prod_prodMap** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_prod_prodMap (s : Set α) (t : Set β) (f : α -> γ) (g : β -> δ) : (
s ×ˢ t).graphOn (Prod.map f g) = Equiv.prodProdProdComm .. ⁻¹' s.graphOn f ×ˢ t.
graphOn g
参数：s : Set α；t : Set β；f : α -> γ；g : β -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.prodProdProdComm_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type
 u_11) (δ : Type u_12) (abcd : (α × β) × γ × δ),   (Equiv.prodProdProdComm α β γ
 δ) abcd = ((abcd.…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma graphOn_prod_prodMap (s : Set α) (t : Set β) (f : α → γ) (g : β → δ) :
    (s ×ˢ t).graphOn (Prod.map f g) = Equiv.prodProdProdComm .. ⁻¹' s.graphOn f ×ˢ t.graphOn g := by
  aesop

end graphOn

/-! ### Vertical line test -/

/-- **Vertical line test** for functions.

Let `f : α → β × γ` be a function to a product. Assume that `f` is surjective on the first factor
and that the image of `f` intersects every "vertical line" `{(b, c) | c : γ}` at most once.
Then the image of `f` is the graph of some monoid homomorphism `f' : β → γ`. -/
/-
**Set.exists_range_eq_graphOn_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_range_eq_graphOn_univ {f : α -> β × γ} (hf₁ : Surjective (Prod.fst 
∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f g₁).2 = (f g₂).2) : exists f
' : β -> γ, range f = univ.graphOn f'
参数：hf₁ : Surjective (Prod.fst ∘ f)；hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f 
g₁).2 = (f g₂).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y

--- 原说明 ---
**Vertical line test** for functions.

Let `f : α → β × γ` be a function to a product. Assume that `f` is surjective on
 the first factor
and that the image of `f` intersects every "vertical line" `{(b, c) | c : γ}` at
 most once.
Then the image of `f` is the graph of some monoid homomorphism `f' : β → γ`.
-/
lemma exists_range_eq_graphOn_univ {f : α → β × γ} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : β → γ, range f = univ.graphOn f' := by
  refine ⟨fun h ↦ (f (hf₁ h).choose).snd, ?_⟩
  ext x
  simp only [mem_range, comp_apply, mem_graphOn, mem_univ, true_and]
  refine ⟨?_, fun hi ↦ ⟨(hf₁ x.1).choose, Prod.ext (hf₁ x.1).choose_spec hi⟩⟩
  rintro ⟨g, rfl⟩
  exact hf _ _ (hf₁ (f g).1).choose_spec

/-- **Line test** for equivalences.

Let `f : α → β × γ` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(b, c) | c : γ}` and every
"horizontal line" `{(b, c) | b : β}` at most once. Then the image of `f` is the graph of some
equivalence `f' : β ≃ γ`. -/
/-
**Set.exists_equiv_range_eq_graphOn_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_equiv_range_eq_graphOn_univ {f : α -> β × γ} (hf₁ : Surjective (Pro
d.fst ∘ f)) (hf₂ : Surjective (Prod.snd ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f 
g₂).1 ↔ (f g₁).2 = (f g₂).2) : exists e : β ≃ γ, range f = univ.graphOn e
参数：hf₁ : Surjective (Prod.fst ∘ f)；hf₂ : Surjective (Prod.snd ∘ f)；hf : forall g
₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_range_eq_graphOn_univ`：exists_range_eq_graphOn_univ {f : α ->
 β × γ} (hf₁ : Surjective (Prod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).
1 -> (f g₁).2 = (f g₂)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
**Line test** for equivalences.

Let `f : α → β × γ` be a homomorphism to a product of monoids. Assume that `f` i
s surjective on both
factors and that the image of `f` intersects every "vertical line" `{(b, c) | c 
: γ}` and every
"horizontal line" `{(b, c) | b : β}` at most once. Then the image of `f` is the 
graph of some
equivalence `f' : β ≃ γ`.
-/
lemma exists_equiv_range_eq_graphOn_univ {f : α → β × γ} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : β ≃ γ, range f = univ.graphOn e := by
  obtain ⟨e₁, he₁⟩ := exists_range_eq_graphOn_univ hf₁ fun _ _ ↦ (hf _ _).1
  obtain ⟨e₂, he₂⟩ := exists_range_eq_graphOn_univ (f := Equiv.prodComm _ _ ∘ f) (by simpa) <|
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [Set.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff_eq_swap])
  exact ⟨
  { toFun := e₁
    invFun := e₂
    left_inv := fun h ↦ by rw [← he₁₂]
    right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

/-- **Vertical line test** for functions.

Let `s : Set (β × γ)` be a set in a product. Assume that `s` maps bijectively to the first factor.
Then `s` is the graph of some function `f : β → γ`. -/
/-
**Set.exists_eq_mgraphOn_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_eq_mgraphOn_univ {s : Set (β × γ)} (hs₁ : Bijective (Prod.fst ∘ (Su
btype.val : s -> β × γ))) : exists f : β -> γ, s = univ.graphOn f
参数：β × γ；hs₁ : Bijective (Prod.fst ∘ (Subtype.val : s -> β × γ))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用引理 `Set.exists_range_eq_graphOn_univ`：exists_range_eq_graphOn_univ {f : α ->
 β × γ} (hf₁ : Surjective (Prod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).
1 -> (f g₁).2 = (f g₂)…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f

--- 原说明 ---
**Vertical line test** for functions.

Let `s : Set (β × γ)` be a set in a product. Assume that `s` maps bijectively to
 the first factor.
Then `s` is the graph of some function `f : β → γ`.
-/
lemma exists_eq_mgraphOn_univ {s : Set (β × γ)}
    (hs₁ : Bijective (Prod.fst ∘ (Subtype.val : s → β × γ))) : ∃ f : β → γ, s = univ.graphOn f := by
  simpa using exists_range_eq_graphOn_univ hs₁.surjective
    fun a b h ↦ congr_arg (Prod.snd ∘ (Subtype.val : s → β × γ)) (hs₁.injective h)

end Set

