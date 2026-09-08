/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Notation
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Directed
public import Mathlib.Order.Hom.Set

/-!
# Chains and flags

This file defines chains for an arbitrary relation and flags for an order.

## Main declarations

* `IsChain s`: A chain `s` is a set of comparable elements.
* `Flag`: The type of flags, aka maximal chains, of an order.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

@[expose] public section

assert_not_exists CompleteLattice

open Set Set.Notation

variable {α β F : Type*}

/-! ### Chains -/


section Chain

variable (r : α → α → Prop)

/-- In this file, we use `≺` as a local notation for any relation `r`. -/
local infixl:50 " ≺ " => r

/-- A chain is a set `s` satisfying `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ s`. -/
/-
**IsChain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsChain (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chain is a set `s` satisfying `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ s`.
-/
def IsChain (s : Set α) : Prop :=
  s.Pairwise fun x y => x ≺ y ∨ y ≺ x

/-- `SuperChain s t` means that `t` is a chain that strictly includes `s`. -/
/-
**SuperChain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SuperChain (s t : Set α) : Prop
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SuperChain s t` means that `t` is a chain that strictly includes `s`.
-/
def SuperChain (s t : Set α) : Prop :=
  IsChain r t ∧ s ⊂ t

/-- A chain `s` is a maximal chain if there does not exists a chain strictly including `s`. -/
/-
**IsMaxChain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMaxChain (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chain `s` is a maximal chain if there does not exists a chain strictly includi
ng `s`.
-/
def IsMaxChain (s : Set α) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t

variable {r} {c c₁ c₂ s t : Set α} {a b x y : α}
/-
**IsChain.empty** 是 Mathlib 中的一个定理，位于命名空间 `IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, IsChain r ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_empty`：pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pa
irwise r
-/
@[simp] lemma IsChain.empty : IsChain r ∅ := pairwise_empty _
/-
**IsChain.singleton** 是 Mathlib 中的一个定理，位于命名空间 `IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a : α}, IsChain r {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_singleton`：pairwise_singleton (a : α) (r : α -> α -> Prop) 
: Set.Pairwise {a} r
-/
@[simp] lemma IsChain.singleton : IsChain r {a} := pairwise_singleton ..
/-
**Set.Subsingleton.isChain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isChain (hs : s.Subsingleton) : IsChain r s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
theorem Set.Subsingleton.isChain (hs : s.Subsingleton) : IsChain r s :=
  hs.pairwise _
/-
**IsChain.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.mono : s subseteq t -> IsChain r t -> IsChain r s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
-/
theorem IsChain.mono : s ⊆ t → IsChain r t → IsChain r s :=
  Set.Pairwise.mono
/-
**IsChain.mono_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.mono_rel {r' : α -> α -> Prop} (h : IsChain r s) (h_imp : forall x
 y, r x y -> r' x y) : IsChain r' s
参数：h : IsChain r s；h_imp : forall x y, r x y -> r' x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
-/
theorem IsChain.mono_rel {r' : α → α → Prop} (h : IsChain r s) (h_imp : ∀ x y, r x y → r' x y) :
    IsChain r' s :=
  h.mono' fun x y => Or.imp (h_imp x y) (h_imp y x)

/-- This can be used to turn `IsChain (≥)` into `IsChain (≤)` and vice-versa. -/
/-
**IsChain.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.symm (h : IsChain r s) : IsChain (flip r) s
参数：h : IsChain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a

--- 原说明 ---
This can be used to turn `IsChain (≥)` into `IsChain (≤)` and vice-versa.
-/
theorem IsChain.symm (h : IsChain r s) : IsChain (flip r) s :=
  h.mono' fun _ _ => Or.symm
/-
**isChain_of_trichotomous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isChain_of_trichotomous [Std.Trichotomous r] (s : Set α) : IsChain r s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
-/
theorem isChain_of_trichotomous [Std.Trichotomous r] (s : Set α) : IsChain r s :=
  fun a _ b _ hab => (trichotomous_of r a b).imp_right fun h => h.resolve_left hab
/-
**IsChain.insert** 是 Mathlib 中的一个定理，位于命名空间 `IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},   IsChain r s → (
∀ b ∈ s, a ≠ b → r a b ∨ r b a) → IsChain r (insert a s)
参数：∀ b ∈ s, a ≠ b → r a b ∨ r b a；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Set.Pairwise.insert_of_symm`：∀ {α : Type u_1} {r : α → α → Prop} {s : Se
t α} {a : α} [Std.Symm r],   s.Pairwise r → (∀ b ∈ s, a ≠ b → r a b) → (insert a
 s).Pairwise r
-/
protected theorem IsChain.insert (hs : IsChain r s) (ha : ∀ b ∈ s, a ≠ b → a ≺ b ∨ b ≺ a) :
    IsChain r (insert a s) :=
  have : Std.Symm fun a b ↦ a ≺ b ∨ b ≺ a := { symm _ _ := Or.symm }
  hs.insert_of_symm ha
/-
**IsChain.pair** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsChain.pair (h : r a b) : IsChain r {a, b}
参数：h : r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.insert`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},
   IsChain r s → (∀ b ∈ s, a ≠ b → r a b ∨ r b a) → IsChain r (insert a s)
· 使用定理 `IsChain.singleton`：∀ {α : Type u_1} {r : α → α → Prop} {a : α}, IsChain 
r {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
-/
lemma IsChain.pair (h : r a b) : IsChain r {a, b} :=
  IsChain.singleton.insert fun _ hb _ ↦ .inl <| (eq_of_mem_singleton hb).symm.recOn ‹_›
/-
**isChain_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isChain_univ_iff : IsChain r (univ : Set α) ↔ Std.Trichotomous r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `isChain_of_trichotomous`：isChain_of_trichotomous [Std.Trichotomous r] (s
 : Set α) : IsChain r s
-/
theorem isChain_univ_iff : IsChain r (univ : Set α) ↔ Std.Trichotomous r := by
  refine ⟨fun h => ⟨fun a b => ?_⟩, fun h => @isChain_of_trichotomous _ _ h univ⟩
  have : a ≠ b → (r a b ∨ r b a) := h trivial trivial
  grind
/-
**IsChain.image_of_map_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_of_map_rel (r : α -> α -> Prop) (s : β -> β -> Prop) (f : α 
-> β) (h : forall x y, r x y -> s (f x) (f y)) {c : Set α} (hrc : IsChain r c) :
 IsChain s (f '' c)
参数：r : α -> α -> Prop；s : β -> β -> Prop；f : α -> β；h : forall x y, r x y -> s (
f x) (f y)；hrc : IsChain r c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem IsChain.image_of_map_rel (r : α → α → Prop) (s : β → β → Prop) (f : α → β)
    (h : ∀ x y, r x y → s (f x) (f y)) {c : Set α} (hrc : IsChain r c) : IsChain s (f '' c) :=
  fun _ ⟨_, ha₁, ha₂⟩ _ ⟨_, hb₁, hb₂⟩ =>
  ha₂ ▸ hb₂ ▸ fun hxy => (hrc ha₁ hb₁ <| ne_of_apply_ne f hxy).imp (h _ _) (h _ _)
/-
**IsChain.preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.preimage (r : α -> α -> Prop) (s : β -> β -> Prop) (f : α -> β) (h
f : Function.Injective f) (h : forall x y, s (f x) (f y) -> r x y) {c : Set β} (
hrc : IsChain s c) : IsChain r (f ⁻¹' c)
参数：r : α -> α -> Prop；s : β -> β -> Prop；f : α -> β；hf : Function.Injective f；h 
: forall x y, s (f x) (f y) -> r x y；hrc : IsChain s c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsChain.preimage (r : α → α → Prop) (s : β → β → Prop) (f : α → β)
    (hf : Function.Injective f) (h : ∀ x y, s (f x) (f y) → r x y) {c : Set β} (hrc : IsChain s c) :
    IsChain r (f ⁻¹' c) := by
  intro _ ha _ hb hne
  have := hrc ha hb (fun h ↦ hne (hf h))
  grind
/-
**isChain_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isChain_union {s t : Set α} : IsChain r (s union t) ↔ IsChain r s ∧ IsChai
n r t ∧ forall a in s, forall b in t, a != b -> r a b ∨ r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsChain.eq_1`：∀ {α : Type u_1} (r : α → α → Prop) (s : Set α), IsChain r
 s = s.Pairwise fun x y => r x y ∨ r y x
· 使用定理 `Set.pairwise_union_of_symm`：pairwise_union_of_symm [Std.Symm r] : (s uni
on t).Pairwise r ↔ s.Pairwise r ∧ t.Pairwise r ∧ forall a in s, forall b in t, a
 != b -> r a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isChain_union {s t : Set α} :
    IsChain r (s ∪ t) ↔ IsChain r s ∧ IsChain r t ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → r a b ∨ r b a := by
  have : Std.Symm fun a b ↦ a ≺ b ∨ b ≺ a := { symm _ _ := Or.symm }
  rw [IsChain, IsChain, IsChain, pairwise_union_of_symm]
/-
**Monotone.isChain_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.isChain_image [Preorder α] [Preorder β] {s : Set α} {f : α -> β} 
(hf : Monotone f) (hs : IsChain (· <= ·) s) : IsChain (· <= ·) (f '' s)
参数：hf : Monotone f；hs : IsChain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image_of_map_rel`：IsChain.image_of_map_rel (r : α -> α -> Prop) 
(s : β -> β -> Prop) (f : α -> β) (h : forall x y, r x y -> s (f x) (f y)) {c : 
Set α} (hrc : …
-/
lemma Monotone.isChain_image [Preorder α] [Preorder β] {s : Set α} {f : α → β}
    (hf : Monotone f) (hs : IsChain (· ≤ ·) s) : IsChain (· ≤ ·) (f '' s) :=
  hs.image_of_map_rel _ _ _ (fun _ _ a ↦ hf a)
/-
**Monotone.isChain_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.isChain_range [LinearOrder α] [Preorder β] {f : α -> β} (hf : Mon
otone f) : IsChain (· <= ·) (range f)
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `Monotone.isChain_image`：Monotone.isChain_image [Preorder α] [Preorder β]
 {s : Set α} {f : α -> β} (hf : Monotone f) (hs : IsChain (· <= ·) s) : IsChain 
(· <= ·) (f …
· 使用定理 `isChain_of_trichotomous`：isChain_of_trichotomous [Std.Trichotomous r] (s
 : Set α) : IsChain r s
-/
theorem Monotone.isChain_range [LinearOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    IsChain (· ≤ ·) (range f) := by
  rw [← image_univ]
  exact hf.isChain_image (isChain_of_trichotomous _)
/-
**Antitone.isChain_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.isChain_image [Preorder α] [Preorder β] {s : Set α} {f : α -> β} 
(hf : Antitone f) (hs : IsChain (· <= ·) s) : IsChain (· <= ·) (f '' s)
参数：hf : Antitone f；hs : IsChain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Monotone.isChain_image`：Monotone.isChain_image [Preorder α] [Preorder β]
 {s : Set α} {f : α -> β} (hf : Monotone f) (hs : IsChain (· <= ·) s) : IsChain 
(· <= ·) (f …
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
· 使用定理 `IsChain.symm`：IsChain.symm (h : IsChain r s) : IsChain (flip r) s
-/
lemma Antitone.isChain_image [Preorder α] [Preorder β] {s : Set α} {f : α → β}
    (hf : Antitone f) (hs : IsChain (· ≤ ·) s) : IsChain (· ≤ ·) (f '' s) :=
  hf.dual_left.isChain_image hs.symm
/-
**Antitone.isChain_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.isChain_range [LinearOrder α] [Preorder β] {f : α -> β} (hf : Ant
itone f) : IsChain (· <= ·) (range f)
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.isChain_range`：Monotone.isChain_range [LinearOrder α] [Preorder
 β] {f : α -> β} (hf : Monotone f) : IsChain (· <= ·) (range f)
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem Antitone.isChain_range [LinearOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    IsChain (· ≤ ·) (range f) :=
  hf.dual_left.isChain_range
/-
**IsChain.lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.lt_of_le [PartialOrder α] {s : Set α} (h : IsChain (· <= ·) s) : I
sChain (· < ·) s
参数：h : IsChain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用定理 `Ne.lt_of_le'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≠ b 
→ b ≤ a → b < a
-/
theorem IsChain.lt_of_le [PartialOrder α] {s : Set α} (h : IsChain (· ≤ ·) s) :
    IsChain (· < ·) s := fun _a ha _b hb hne ↦
  (h ha hb hne).imp hne.lt_of_le hne.lt_of_le'
/-
**IsChain.diff** 是 Mathlib 中的一个定理，位于命名空间 `IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, IsChain r s → IsChain r
 (s \ t)
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.mono`：IsChain.mono : s subseteq t -> IsChain r t -> IsChain r s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
@[simp] protected theorem IsChain.diff {s t : Set α} (h : IsChain r s) : IsChain r (s \ t) :=
  h.mono Set.sdiff_subset
/-
**isChain_preimage_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isChain_preimage_subtypeVal (s t : Set α) : @IsChain ↑s (r · ·) (s ↓inter 
t) ↔ IsChain r (s inter t)
参数：s t : Set α。
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
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isChain_preimage_subtypeVal (s t : Set α) :
    @IsChain ↑s (r · ·) (s ↓∩ t) ↔ IsChain r (s ∩ t) := by
  simp [IsChain, Set.Pairwise]
/-
**isChain_coe_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isChain_coe_univ_iff {s : Set α} : @IsChain ↑s (r · ·) univ ↔ IsChain r s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `isChain_preimage_subtypeVal`：isChain_preimage_subtypeVal (s t : Set α) :
 @IsChain ↑s (r · ·) (s ↓inter t) ↔ IsChain r (s inter t)
-/
theorem isChain_coe_univ_iff {s : Set α} : @IsChain ↑s (r · ·) univ ↔ IsChain r s := by
  simpa using isChain_preimage_subtypeVal s univ

section Rel

variable {r : α → α → Prop} {r' : β → β → Prop} {s : Set α}

/-
**IsChain.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : IsChain r s) (φ :
 F) : IsChain r' (φ '' s)
参数：hs : IsChain r s；φ : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image_of_map_rel`：IsChain.image_of_map_rel (r : α -> α -> Prop) 
(s : β -> β -> Prop) (f : α -> β) (h : forall x y, r x y -> s (f x) (f y)) {c : 
Set α} (hrc : …
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
theorem IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : IsChain r s) (φ : F) :
    IsChain r' (φ '' s) :=
  hs.image_of_map_rel _ _ _ (fun _ _ h ↦ map_rel φ h)

@[deprecated IsChain.image (since := "2026-02-26")]
/-
**IsChain.image_relEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_relEmbedding (hs : IsChain r s) (φ : r ↪r r') : IsChain r' (
φ '' s)
参数：hs : IsChain r s；φ : r ↪r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image`：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : 
IsChain r s) (φ : F) : IsChain r' (φ '' s)
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
-/
theorem IsChain.image_relEmbedding (hs : IsChain r s) (φ : r ↪r r') : IsChain r' (φ '' s) :=
  hs.image _
/-
**IsChain.preimage_relEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.preimage_relEmbedding {t : Set β} (ht : IsChain r' t) (φ : r ↪r r'
) : IsChain r (φ ⁻¹' t)
参数：ht : IsChain r' t；φ : r ↪r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.preimage`：IsChain.preimage (r : α -> α -> Prop) (s : β -> β -> P
rop) (f : α -> β) (hf : Function.Injective f) (h : forall x y, s (f x) (f y) -> 
r x y)…
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem IsChain.preimage_relEmbedding {t : Set β} (ht : IsChain r' t) (φ : r ↪r r') :
    IsChain r (φ ⁻¹' t) :=
  ht.preimage _ _ _ φ.injective (fun _ _ h ↦ φ.map_rel_iff.mp h)

@[deprecated IsChain.image (since := "2026-02-26")]
/-
**IsChain.image_relIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_relIso (hs : IsChain r s) (φ : r ≃r r') : IsChain r' (φ '' s
)
参数：hs : IsChain r s；φ : r ≃r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image`：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : 
IsChain r s) (φ : F) : IsChain r' (φ '' s)
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
-/
theorem IsChain.image_relIso (hs : IsChain r s) (φ : r ≃r r') : IsChain r' (φ '' s) :=
  hs.image φ.toRelEmbedding
/-
**IsChain.preimage_relIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.preimage_relIso {t : Set β} (hs : IsChain r' t) (φ : r ≃r r') : Is
Chain r (φ ⁻¹' t)
参数：hs : IsChain r' t；φ : r ≃r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.preimage_relEmbedding`：IsChain.preimage_relEmbedding {t : Set β}
 (ht : IsChain r' t) (φ : r ↪r r') : IsChain r (φ ⁻¹' t)
-/
theorem IsChain.preimage_relIso {t : Set β} (hs : IsChain r' t) (φ : r ≃r r') :
    IsChain r (φ ⁻¹' t) :=
  hs.preimage_relEmbedding φ.toRelEmbedding
/-
**IsChain.image_relEmbedding_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_relEmbedding_iff {φ : r ↪r r'} : IsChain r' (φ '' s) ↔ IsCha
in r s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `IsChain.preimage_relEmbedding`：IsChain.preimage_relEmbedding {t : Set β}
 (ht : IsChain r' t) (φ : r ↪r r') : IsChain r (φ ⁻¹' t)
· 使用定理 `IsChain.image`：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : 
IsChain r s) (φ : F) : IsChain r' (φ '' s)
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
-/
theorem IsChain.image_relEmbedding_iff {φ : r ↪r r'} : IsChain r' (φ '' s) ↔ IsChain r s :=
  ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h => h.image φ⟩
/-
**IsChain.image_relIso_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_relIso_iff {φ : r ≃r r'} : IsChain r' (φ '' s) ↔ IsChain r s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image_relEmbedding_iff`：IsChain.image_relEmbedding_iff {φ : r ↪r
 r'} : IsChain r' (φ '' s) ↔ IsChain r s
-/
theorem IsChain.image_relIso_iff {φ : r ≃r r'} : IsChain r' (φ '' s) ↔ IsChain r s :=
  @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')

@[deprecated IsChain.image (since := "2026-02-26")]
/-
**IsChain.image_embedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_embedding [LE α] [LE β] (hs : IsChain (· <= ·) s) (φ : α ↪o 
β) : IsChain (· <= ·) (φ '' s)
参数：hs : IsChain (· <= ·) s；φ : α ↪o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image`：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : 
IsChain r s) (φ : F) : IsChain r' (φ '' s)
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
-/
theorem IsChain.image_embedding [LE α] [LE β] (hs : IsChain (· ≤ ·) s) (φ : α ↪o β) :
    IsChain (· ≤ ·) (φ '' s) :=
  image hs _
/-
**IsChain.preimage_embedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsChain (· <= ·
) t) (φ : α ↪o β) : IsChain (· <= ·) (φ ⁻¹' t)
参数：ht : IsChain (· <= ·) t；φ : α ↪o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.preimage_relEmbedding`：IsChain.preimage_relEmbedding {t : Set β}
 (ht : IsChain r' t) (φ : r ↪r r') : IsChain r (φ ⁻¹' t)
-/
theorem IsChain.preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsChain (· ≤ ·) t) (φ : α ↪o β) :
    IsChain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _
/-
**IsChain.image_embedding_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_embedding_iff [LE α] [LE β] {φ : α ↪o β} : IsChain (· <= ·) 
(φ '' s) ↔ IsChain (· <= ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image_relEmbedding_iff`：IsChain.image_relEmbedding_iff {φ : r ↪r
 r'} : IsChain r' (φ '' s) ↔ IsChain r s
-/
theorem IsChain.image_embedding_iff [LE α] [LE β] {φ : α ↪o β} :
    IsChain (· ≤ ·) (φ '' s) ↔ IsChain (· ≤ ·) s :=
  image_relEmbedding_iff

@[deprecated IsChain.image (since := "2026-02-26")]
/-
**IsChain.image_iso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_iso [LE α] [LE β] (hs : IsChain (· <= ·) s) (φ : α ≃o β) : I
sChain (· <= ·) (φ '' s)
参数：hs : IsChain (· <= ·) s；φ : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image`：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : 
IsChain r s) (φ : F) : IsChain r' (φ '' s)
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
-/
theorem IsChain.image_iso [LE α] [LE β] (hs : IsChain (· ≤ ·) s) (φ : α ≃o β) :
    IsChain (· ≤ ·) (φ '' s) :=
  image hs _
/-
**IsChain.image_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.image_iso_iff [LE α] [LE β] {φ : α ≃o β} : IsChain (· <= ·) (φ '' 
s) ↔ IsChain (· <= ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image_relEmbedding_iff`：IsChain.image_relEmbedding_iff {φ : r ↪r
 r'} : IsChain r' (φ '' s) ↔ IsChain r s
-/
theorem IsChain.image_iso_iff [LE α] [LE β] {φ : α ≃o β} :
    IsChain (· ≤ ·) (φ '' s) ↔ IsChain (· ≤ ·) s :=
  image_relEmbedding_iff
/-
**IsChain.preimage_iso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.preimage_iso [LE α] [LE β] {t : Set β} (ht : IsChain (· <= ·) t) (
φ : α ≃o β) : IsChain (· <= ·) (φ ⁻¹' t)
参数：ht : IsChain (· <= ·) t；φ : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.preimage_relEmbedding`：IsChain.preimage_relEmbedding {t : Set β}
 (ht : IsChain r' t) (φ : r ↪r r') : IsChain r (φ ⁻¹' t)
-/
theorem IsChain.preimage_iso [LE α] [LE β] {t : Set β} (ht : IsChain (· ≤ ·) t) (φ : α ≃o β) :
    IsChain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _
/-
**IsChain.preimage_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} : IsChain 
(· <= ·) (φ ⁻¹' t) ↔ IsChain (· <= ·) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `OrderIso.image_preimage`：image_preimage (e : α ≃o β) (s : Set β) : e '' 
e ⁻¹' s = s
· 使用定理 `IsChain.image`：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : 
IsChain r s) (φ : F) : IsChain r' (φ '' s)
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
· 使用定理 `IsChain.preimage_iso`：IsChain.preimage_iso [LE α] [LE β] {t : Set β} (ht
 : IsChain (· <= ·) t) (φ : α ≃o β) : IsChain (· <= ·) (φ ⁻¹' t)
-/
theorem IsChain.preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} :
    IsChain (· ≤ ·) (φ ⁻¹' t) ↔ IsChain (· ≤ ·) t :=
  ⟨fun h => (φ.image_preimage t).subst (h.image φ), fun h => h.preimage_iso _⟩

end Rel

section Total

variable [Std.Refl r]

/-
**IsChain.total** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in s) : x ≺ y ∨ y ≺ 
x
参数：h : IsChain r s；hx : x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem IsChain.total (h : IsChain r s) (hx : x ∈ s) (hy : y ∈ s) : x ≺ y ∨ y ≺ x :=
  (eq_or_ne x y).elim (fun e => Or.inl <| e ▸ refl _) (h hx hy)
/-
**IsChain.directedOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.directedOn (H : IsChain r s) : DirectedOn r s
参数：H : IsChain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem IsChain.directedOn (H : IsChain r s) : DirectedOn r s := fun x hx y hy =>
  ((H.total hx hy).elim fun h => ⟨y, hy, h, refl _⟩) fun h => ⟨x, hx, refl _, h⟩
/-
**IsChain.directed** 是 Mathlib 中的一个定理，位于命名空间 `IsChain`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [Std.Refl r] {f : β → α
} {c : Set β},   IsChain (f ⁻¹'o r) c → Directed r fun x => f ↑x
参数：f ⁻¹'o r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
protected theorem IsChain.directed {f : β → α} {c : Set β} (h : IsChain (f ⁻¹'o r) c) :
    Directed r fun x : { a : β // a ∈ c } => f x :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    (by_cases fun hab : a = b => by
      simp only [hab, exists_prop, and_self_iff, Subtype.exists]
      exact ⟨b, hb, refl _⟩)
    fun hab => ((h ha hb hab).elim fun h => ⟨⟨b, hb⟩, h, refl _⟩) fun h => ⟨⟨a, ha⟩, refl _, h⟩
/-
**IsChain.exists3** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.exists3 (hchain : IsChain r s) [IsTrans α r] {a b c} (mem1 : a in 
s) (mem2 : b in s) (mem3 : c in s) : exists (z : _) (_ : z in s), r a z ∧ r b z 
∧ r c z
参数：hchain : IsChain r s；mem1 : a in s；mem2 : b in s；mem3 : c in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `IsChain.directed`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [St
d.Refl r] {f : β → α} {c : Set β},   IsChain (f ⁻¹'o r) c → Directed r fun x => 
f ↑x
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem IsChain.exists3 (hchain : IsChain r s) [IsTrans α r] {a b c} (mem1 : a ∈ s) (mem2 : b ∈ s)
    (mem3 : c ∈ s) : ∃ (z : _) (_ : z ∈ s), r a z ∧ r b z ∧ r c z := by
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) a mem1 b mem2 with ⟨z, mem4, H1, H2⟩
  rcases directedOn_iff_directed.mpr (IsChain.directed hchain) z mem4 c mem3 with
    ⟨z', mem5, H3, H4⟩
  exact ⟨z', mem5, _root_.trans H1 H3, _root_.trans H2 H3, H4⟩

end Total

/-- A chain in a partial order is a linear order. -/
@[implicit_reducible]
/-
**IsChain.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsChain.linearOrder [PartialOrder α] [DecidableLE α] {s : Set α} (hs : IsC
hain (· <= ·) s) : LinearOrder s where le_total
参数：hs : IsChain (· <= ·) s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chain in a partial order is a linear order.
-/
def IsChain.linearOrder [PartialOrder α] [DecidableLE α] {s : Set α} (hs : IsChain (· ≤ ·) s) :
    LinearOrder s where
  le_total := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact hs.total ha hb
  toDecidableLE x y := inferInstanceAs (Decidable (x.1 ≤ y.1))
/-
**IsChain.le_of_not_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsChain.le_of_not_gt [Preorder α] (hs : IsChain (· <= ·) s) {x y : α} (hx 
: x in s) (hy : y in s) (h : ¬ x < y) : y <= x
参数：hs : IsChain (· <= ·) s；hx : x in s；hy : y in s；h : ¬ x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma IsChain.le_of_not_gt [Preorder α] (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x < y) : y ≤ x := by
  cases hs.total hx hy with
  | inr h' => exact h'
  | inl h' => simpa [lt_iff_le_not_ge, h'] using h
/-
**IsChain.not_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsChain.not_lt [Preorder α] (hs : IsChain (· <= ·) s) {x y : α} (hx : x in
 s) (hy : y in s) : ¬ x < y ↔ y <= x
参数：hs : IsChain (· <= ·) s；hx : x in s；hy : y in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsChain.le_of_not_gt`：IsChain.le_of_not_gt [Preorder α] (hs : IsChain (·
 <= ·) s) {x y : α} (hx : x in s) (hy : y in s) (h : ¬ x < y) : y <= x
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
lemma IsChain.not_lt [Preorder α] (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : ¬ x < y ↔ y ≤ x :=
  ⟨(hs.le_of_not_gt hx hy ·), fun h h' ↦ h'.not_ge h⟩
/-
**IsChain.lt_of_not_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsChain.lt_of_not_ge [Preorder α] (hs : IsChain (· <= ·) s) {x y : α} (hx 
: x in s) (hy : y in s) (h : ¬ x <= y) : y < x
参数：hs : IsChain (· <= ·) s；hx : x in s；hy : y in s；h : ¬ x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
-/
lemma IsChain.lt_of_not_ge [Preorder α] (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x ≤ y) : y < x :=
  (hs.total hx hy).elim (h · |>.elim) (lt_of_le_not_ge · h)
/-
**IsChain.not_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsChain.not_le [Preorder α] (hs : IsChain (· <= ·) s) {x y : α} (hx : x in
 s) (hy : y in s) : ¬ x <= y ↔ y < x
参数：hs : IsChain (· <= ·) s；hx : x in s；hy : y in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsChain.lt_of_not_ge`：IsChain.lt_of_not_ge [Preorder α] (hs : IsChain (·
 <= ·) s) {x y : α} (hx : x in s) (hy : y in s) (h : ¬ x <= y) : y < x
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
lemma IsChain.not_le [Preorder α] (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : ¬ x ≤ y ↔ y < x :=
  ⟨(hs.lt_of_not_ge hx hy ·), fun h h' ↦ h'.not_gt h⟩
/-
**IsMaxChain.isChain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxChain.isChain (h : IsMaxChain r s) : IsChain r s
参数：h : IsMaxChain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsMaxChain.isChain (h : IsMaxChain r s) : IsChain r s :=
  h.1
/-
**IsMaxChain.not_superChain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxChain.not_superChain (h : IsMaxChain r s) : ¬SuperChain r s t
参数：h : IsMaxChain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsMaxChain.not_superChain (h : IsMaxChain r s) : ¬SuperChain r s t := fun ht =>
  ht.2.ne <| h.2 ht.1 ht.2.1
/-
**IsMaxChain.bot_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxChain.bot_mem [LE α] [OrderBot α] (h : IsMaxChain (· <= ·) s) : ⊥ in 
s
参数：h : IsMaxChain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsChain.insert`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},
   IsChain r s → (∀ b ∈ s, a ≠ b → r a b ∨ r b a) → IsChain r (insert a s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem IsMaxChain.bot_mem [LE α] [OrderBot α] (h : IsMaxChain (· ≤ ·) s) : ⊥ ∈ s :=
  (h.2 (h.1.insert fun _ _ _ => Or.inl bot_le) <| subset_insert _ _).symm ▸ mem_insert _ _
/-
**IsMaxChain.top_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxChain.top_mem [LE α] [OrderTop α] (h : IsMaxChain (· <= ·) s) : ⊤ in 
s
参数：h : IsMaxChain (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsChain.insert`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},
   IsChain r s → (∀ b ∈ s, a ≠ b → r a b ∨ r b a) → IsChain r (insert a s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem IsMaxChain.top_mem [LE α] [OrderTop α] (h : IsMaxChain (· ≤ ·) s) : ⊤ ∈ s :=
  (h.2 (h.1.insert fun _ _ _ => Or.inr le_top) <| subset_insert _ _).symm ▸ mem_insert _ _
/-
**IsMaxChain.image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMaxChain.image {s : β -> β -> Prop} (e : r ≃r s) {c : Set α} (hc : IsMax
Chain r c) : IsMaxChain s (e '' c) where left
参数：e : r ≃r s；hc : IsMaxChain r c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.image`：IsChain.image [FunLike F α β] [RelHomClass F r r'] (hs : 
IsChain r s) (φ : F) : IsChain r' (φ '' s)
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
· 使用定理 `IsMaxChain.isChain`：IsMaxChain.isChain (h : IsMaxChain r s) : IsChain r 
s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelIso.coe_fn_toEquiv`：coe_fn_toEquiv (f : r ≃r s) : (f.toEquiv : α -> β
) = f
· 使用定理 `Equiv.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {α β} (e : α ≃ 
β) (s t) : s = e ⁻¹' t ↔ e '' s = t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.subset_symm_image`：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s 
: Set α) (t : Set β), s ⊆ ⇑e.symm '' t ↔ ⇑e '' s ⊆ t
-/
lemma IsMaxChain.image {s : β → β → Prop} (e : r ≃r s) {c : Set α} (hc : IsMaxChain r c) :
    IsMaxChain s (e '' c) where
  left := hc.isChain.image e
  right t ht hf := by
    rw [← e.coe_fn_toEquiv, ← e.toEquiv.eq_preimage_iff_image_eq, ← Equiv.image_symm_eq_preimage]
    exact hc.2 (ht.image e.symm) ((e.toEquiv.subset_symm_image _ _).2 hf)
/-
**IsMaxChain.isEmpty_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsMaxChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsMaxChain r s → (IsEmpty
 α ↔ s = ∅)
参数：IsEmpty α ↔ s = ∅。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Set.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Set α) != ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `IsChain.singleton`：∀ {α : Type u_1} {r : α → α → Prop} {a : α}, IsChain 
r {a}
-/
protected theorem IsMaxChain.isEmpty_iff (h : IsMaxChain r s) : IsEmpty α ↔ s = ∅ := by
  refine ⟨fun _ ↦ s.eq_empty_of_isEmpty, fun h' ↦ ?_⟩
  constructor
  intro x
  simp only [IsMaxChain, h', IsChain.empty, empty_subset, forall_const, true_and] at h
  exact singleton_ne_empty x (h IsChain.singleton).symm
/-
**IsMaxChain.nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsMaxChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsMaxChain r s → (Nonempt
y α ↔ s.Nonempty)
参数：Nonempty α ↔ s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMaxChain.isEmpty_iff`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α},
 IsMaxChain r s → (IsEmpty α ↔ s = ∅)
-/
protected theorem IsMaxChain.nonempty_iff (h : IsMaxChain r s) : Nonempty α ↔ s.Nonempty :=
  not_iff_not.mp <| by simpa [Set.not_nonempty_iff_eq_empty] using h.isEmpty_iff
/-
**IsMaxChain.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxChain.symm (h : IsMaxChain r s) : IsMaxChain (flip r) s
参数：h : IsMaxChain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.symm`：IsChain.symm (h : IsChain r s) : IsChain (flip r) s
· 使用定理 `IsMaxChain.isChain`：IsMaxChain.isChain (h : IsMaxChain r s) : IsChain r 
s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsMaxChain.symm (h : IsMaxChain r s) : IsMaxChain (flip r) s :=
  ⟨h.isChain.symm, fun _ ht₁ ht₂ ↦ h.2 ht₁.symm ht₂⟩

open scoped Classical in
/-- Given a set `s`, if there exists a chain `t` strictly including `s`, then `SuccChain s`
is one of these chains. Otherwise it is `s`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**SuccChain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SuccChain (r : α -> α -> Prop) (s : Set α) : Set α
参数：r : α -> α -> Prop；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def SuccChain (r : α → α → Prop) (s : Set α) : Set α :=
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then h.choose else s
/-
**succChain_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：succChain_spec (h : exists t, IsChain r s ∧ SuperChain r s t) : SuperChain
 r s (SuccChain r s)
参数：h : exists t, IsChain r s ∧ SuperChain r s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `exists_and_left`：∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, b ∧ p
 x) ↔ b ∧ ∃ x, p x
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem succChain_spec (h : ∃ t, IsChain r s ∧ SuperChain r s t) :
    SuperChain r s (SuccChain r s) := by
  have : IsChain r s ∧ SuperChain r s h.choose := h.choose_spec
  simpa [SuccChain, dif_pos, exists_and_left.mp h] using this.2
/-
**IsChain.succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.succ (hs : IsChain r s) : IsChain r (SuccChain r s)
参数：hs : IsChain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `succChain_spec`：succChain_spec (h : exists t, IsChain r s ∧ SuperChain r
 s t) : SuperChain r s (SuccChain r s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `exists_and_left`：∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, b ∧ p
 x) ↔ b ∧ ∃ x, p x
-/
theorem IsChain.succ (hs : IsChain r s) : IsChain r (SuccChain r s) := by
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then exact (succChain_spec h).1
  else
    rw [exists_and_left] at h
    simpa [SuccChain, dif_neg, h] using hs
/-
**IsChain.superChain_succChain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsChain.superChain_succChain (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s) :
 SuperChain r s (SuccChain r s)
参数：hs₁ : IsChain r s；hs₂ : ¬IsMaxChain r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `succChain_spec`：succChain_spec (h : exists t, IsChain r s ∧ SuperChain r
 s t) : SuperChain r s (SuccChain r s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ssubset_iff_subset_ne`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [ins
t : PartialOrder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ a ≠ b
-/
theorem IsChain.superChain_succChain (hs₁ : IsChain r s) (hs₂ : ¬IsMaxChain r s) :
    SuperChain r s (SuccChain r s) := by
  simp only [IsMaxChain, _root_.not_and, not_forall, exists_prop] at hs₂
  obtain ⟨t, ht, hst⟩ := hs₂ hs₁
  exact succChain_spec ⟨t, hs₁, ht, ssubset_iff_subset_ne.2 hst⟩
/-
**subset_succChain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_succChain : s subseteq SuccChain r s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `succChain_spec`：succChain_spec (h : exists t, IsChain r s ∧ SuperChain r
 s t) : SuperChain r s (SuccChain r s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem subset_succChain : s ⊆ SuccChain r s := by
  if h : ∃ t, IsChain r s ∧ SuperChain r s t then exact (succChain_spec h).2.1
  else
    simp [SuccChain, h]

end Chain

/-! ### Flags -/


/-- The type of flags, aka maximal chains, of an order. -/
/-
**Flag** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_4) → [LE α] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of flags, aka maximal chains, of an order.
-/
structure Flag (α : Type*) [LE α] where
  /-- The `carrier` of a flag is the underlying set. -/
  carrier : Set α
  /-- By definition, a flag is a chain -/
  Chain' : IsChain (· ≤ ·) carrier
  /-- By definition, a flag is a maximal chain -/
  max_chain' : ∀ ⦃s⦄, IsChain (· ≤ ·) s → carrier ⊆ s → carrier = s

namespace Flag

section LE

variable [LE α] {s t : Flag α} {a : α}

/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Flag α) α where
  coe := carrier
  coe_injective s t h := by
    cases s
    cases t
    congr
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Flag α) := .ofSetLike (Flag α) α

@[ext]
/-
**Flag.ext** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：ext : (s : Set α) = t -> s = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
theorem ext : (s : Set α) = t → s = t :=
  SetLike.ext'
/-
**Flag.mem_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：mem_coe_iff : a in (s : Set α) ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe_iff : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
/-
**Flag.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：coe_mk (s : Set α) (h₁ h₂) : (mk s h₁ h₂ : Set α) = s
参数：s : Set α；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Set α) (h₁ h₂) : (mk s h₁ h₂ : Set α) = s :=
  rfl

@[simp]
/-
**Flag.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：mk_coe (s : Flag α) : mk (s : Set α) s.Chain' s.max_chain' = s
参数：s : Flag α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flag.ext`：ext : (s : Set α) = t -> s = t
· 使用定理 `Flag.Chain'`：∀ {α : Type u_4} [inst : LE α] (self : Flag α), IsChain (fu
n x1 x2 => x1 ≤ x2) self.carrier
· 使用定理 `Flag.max_chain'`：∀ {α : Type u_4} [inst : LE α] (self : Flag α) ⦃s : Set
 α⦄,   IsChain (fun x1 x2 => x1 ≤ x2) s → self.carrier ⊆ s → self.carrier = s
-/
theorem mk_coe (s : Flag α) : mk (s : Set α) s.Chain' s.max_chain' = s :=
  ext rfl
/-
**Flag.chain_le** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：chain_le (s : Flag α) : IsChain (· <= ·) (s : Set α)
参数：s : Flag α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flag.Chain'`：∀ {α : Type u_4} [inst : LE α] (self : Flag α), IsChain (fu
n x1 x2 => x1 ≤ x2) self.carrier
-/
theorem chain_le (s : Flag α) : IsChain (· ≤ ·) (s : Set α) :=
  s.Chain'
/-
**Flag.maxChain** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] (s : Flag α), IsMaxChain (fun x1 x2 => x1 ≤
 x2) ↑s
参数：s : Flag α；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flag.chain_le`：chain_le (s : Flag α) : IsChain (· <= ·) (s : Set α)
· 使用定理 `Flag.max_chain'`：∀ {α : Type u_4} [inst : LE α] (self : Flag α) ⦃s : Set
 α⦄,   IsChain (fun x1 x2 => x1 ≤ x2) s → self.carrier ⊆ s → self.carrier = s
-/
protected theorem maxChain (s : Flag α) : IsMaxChain (· ≤ ·) (s : Set α) :=
  ⟨s.chain_le, s.max_chain'⟩
/-
**Flag.top_mem** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：top_mem [OrderTop α] (s : Flag α) : (⊤ : α) in s
参数：s : Flag α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxChain.top_mem`：IsMaxChain.top_mem [LE α] [OrderTop α] (h : IsMaxCha
in (· <= ·) s) : ⊤ in s
· 使用定理 `Flag.maxChain`：∀ {α : Type u_1} [inst : LE α] (s : Flag α), IsMaxChain (
fun x1 x2 => x1 ≤ x2) ↑s
-/
theorem top_mem [OrderTop α] (s : Flag α) : (⊤ : α) ∈ s :=
  s.maxChain.top_mem
/-
**Flag.bot_mem** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：bot_mem [OrderBot α] (s : Flag α) : (⊥ : α) in s
参数：s : Flag α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxChain.bot_mem`：IsMaxChain.bot_mem [LE α] [OrderBot α] (h : IsMaxCha
in (· <= ·) s) : ⊥ in s
· 使用定理 `Flag.maxChain`：∀ {α : Type u_1} [inst : LE α] (s : Flag α), IsMaxChain (
fun x1 x2 => x1 ≤ x2) ↑s
-/
theorem bot_mem [OrderBot α] (s : Flag α) : (⊥ : α) ∈ s :=
  s.maxChain.bot_mem

/-- Reinterpret a maximal chain as a flag. -/
/-
**Flag.ofIsMaxChain** 是 Mathlib 中的一个定义，位于命名空间 `Flag`。
形式化陈述：ofIsMaxChain (c : Set α) (hc : IsMaxChain (· <= ·) c) : Flag α
参数：c : Set α；hc : IsMaxChain (· <= ·) c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a maximal chain as a flag.
-/
def ofIsMaxChain (c : Set α) (hc : IsMaxChain (· ≤ ·) c) : Flag α := ⟨c, hc.isChain, hc.2⟩

@[simp, norm_cast]
/-
**Flag.coe_ofIsMaxChain** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：coe_ofIsMaxChain (c : Set α) (hc) : ofIsMaxChain c hc = c
参数：c : Set α；hc。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofIsMaxChain (c : Set α) (hc) : ofIsMaxChain c hc = c := rfl

end LE

section Preorder

variable [Preorder α] [Preorder β] {a b : α} {s : Flag α}

/-
**Flag.le_or_le** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α} (s : Flag α), a ∈ s → b ∈ s
 → a ≤ b ∨ b ≤ a
参数：s : Flag α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `Flag.chain_le`：chain_le (s : Flag α) : IsChain (· <= ·) (s : Set α)
-/
protected theorem le_or_le (s : Flag α) (ha : a ∈ s) (hb : b ∈ s) : a ≤ b ∨ b ≤ a :=
  s.chain_le.total ha hb
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OrderTop α] (s : Flag α) : OrderTop s :=
  Subtype.orderTop s.top_mem
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OrderBot α] (s : Flag α) : OrderBot s :=
  Subtype.orderBot s.bot_mem
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BoundedOrder α] (s : Flag α) : BoundedOrder s :=
  Subtype.boundedOrder s.bot_mem s.top_mem
/-
**Flag.mem_iff_forall_le_or_ge** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：mem_iff_forall_le_or_ge : a in s ↔ forall ⦃b⦄, b in s -> a <= b ∨ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flag.le_or_le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α} (s : Flag 
α), a ∈ s → b ∈ s → a ≤ b ∨ b ≤ a
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Set.ne_insert_of_notMem`：ne_insert_of_notMem {s : Set α} (t : Set α) {a 
: α} : a ∉ s -> s != insert a t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Flag.maxChain`：∀ {α : Type u_1} [inst : LE α] (s : Flag α), IsMaxChain (
fun x1 x2 => x1 ≤ x2) ↑s
· 使用定理 `IsChain.insert`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},
   IsChain r s → (∀ b ∈ s, a ≠ b → r a b ∨ r b a) → IsChain r (insert a s)
· 使用定理 `Flag.chain_le`：chain_le (s : Flag α) : IsChain (· <= ·) (s : Set α)
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
lemma mem_iff_forall_le_or_ge : a ∈ s ↔ ∀ ⦃b⦄, b ∈ s → a ≤ b ∨ b ≤ a :=
  ⟨fun ha b => s.le_or_le ha, fun hb =>
    of_not_not fun ha =>
      Set.ne_insert_of_notMem _ ‹_› <|
        s.maxChain.2 (s.chain_le.insert fun c hc _ => hb hc) <| Set.subset_insert _ _⟩

/-- Flags are preserved under order isomorphisms. -/
/-
**Flag.map** 是 Mathlib 中的一个定义，位于命名空间 `Flag`。
形式化陈述：map (e : α ≃o β) : Flag α ≃ Flag β where toFun s
参数：e : α ≃o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flags are preserved under order isomorphisms.
-/
def map (e : α ≃o β) : Flag α ≃ Flag β where
  toFun s := ofIsMaxChain _ (s.maxChain.image e)
  invFun s := ofIsMaxChain _ (s.maxChain.image e.symm)
  left_inv s := ext <| e.symm_image_image s
  right_inv s := ext <| e.image_symm_image s
/-
**Flag.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ≃o β) (s : Flag α),   ↑((Flag.map e) s) = ⇑e '' ↑s
参数：e : α ≃o β；s : Flag α；(Flag.map e) s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_map (e : α ≃o β) (s : Flag α) : ↑(map e s) = e '' s := rfl
/-
**Flag.symm_map** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ≃o β),   (Flag.map e).symm = Flag.map e.symm
参数：e : α ≃o β；Flag.map e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma symm_map (e : α ≃o β) : (map e).symm = map e.symm := rfl

end Preorder

section PartialOrder

variable [PartialOrder α]

/-
**Flag.chain_lt** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：chain_lt (s : Flag α) : IsChain (· < ·) (s : Set α)
参数：s : Flag α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsChain.lt_of_le`：IsChain.lt_of_le [PartialOrder α] {s : Set α} (h : IsC
hain (· <= ·) s) : IsChain (· < ·) s
· 使用定理 `Flag.chain_le`：chain_le (s : Flag α) : IsChain (· <= ·) (s : Set α)
-/
theorem chain_lt (s : Flag α) : IsChain (· < ·) (s : Set α) := s.chain_le.lt_of_le
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableLE α] [DecidableLT α] [DecidableEq α] (s : Flag α) : LinearOrder s :=
  { Subtype.partialOrder _ with
    le_total := fun a b => s.le_or_le a.2 b.2
    toDecidableLE := Subtype.decidableLE
    toDecidableLT := Subtype.decidableLT
    toDecidableEq := Subtype.instDecidableEq }

end PartialOrder

/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder α] : Unique (Flag α) where
  default := ⟨univ, isChain_of_trichotomous _, fun s _ => s.subset_univ.antisymm'⟩
  uniq s := SetLike.coe_injective <| s.3 (isChain_of_trichotomous _) <| subset_univ _

end Flag

