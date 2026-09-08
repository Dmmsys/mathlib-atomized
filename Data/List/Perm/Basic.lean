/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.InsertIdx

/-!
# List Permutations

This file develops theory about the `List.Perm` relation.

## Notation

The notation `~` is used for permutation equivalence.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid Preorder

open Nat

namespace List
variable {α β : Type*} {l : List α}

open Perm (swap)

/-
**List.perm_rfl** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：perm_rfl : l ~ l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
-/
lemma perm_rfl : l ~ l := Perm.refl _

attribute [symm] Perm.symm
attribute [trans] Perm.trans
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (α := List α) Perm := ⟨fun _ _ ↦ .symm⟩
/-
**List.Perm.subset_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Perm l₂ → (l₁ ⊆ l₃ ↔ l₂ ⊆ l₃)
参数：l₁ ⊆ l₃ ↔ l₂ ⊆ l₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Subset.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁ ⊆ l₂ → l₂ ⊆ 
l₃ → l₁ ⊆ l₃
· 使用定理 `List.Perm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁ ⊆ l
₂
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
-/
theorem Perm.subset_congr_left {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₁ ⊆ l₃ ↔ l₂ ⊆ l₃ :=
  ⟨h.symm.subset.trans, h.subset.trans⟩
/-
**List.Perm.subset_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Perm l₂ → (l₃ ⊆ l₁ ↔ l₃ ⊆ l₂)
参数：l₃ ⊆ l₁ ↔ l₃ ⊆ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Subset.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁ ⊆ l₂ → l₂ ⊆ 
l₃ → l₁ ⊆ l₃
· 使用定理 `List.Perm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁ ⊆ l
₂
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
-/
theorem Perm.subset_congr_right {l₁ l₂ l₃ : List α} (h : l₁ ~ l₂) : l₃ ⊆ l₁ ↔ l₃ ⊆ l₂ :=
  ⟨fun h' => h'.trans h.subset, fun h' => h'.trans h.symm.subset⟩
/-
**List.set_perm_cons_eraseIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：set_perm_cons_eraseIdx {n : Nat} (h : n < l.length) (a : α) : l.set n a ~ 
a :: l.eraseIdx n
参数：h : n < l.length；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.insertIdx_eraseIdx_self`：insertIdx_eraseIdx_self {l : List α} {n : 
Nat} (hn : n != length l) (a : α) : (l.eraseIdx n).insertIdx n a = l.set n a
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `List.perm_insertIdx`：∀ {α : Type u_1} (x : α) (l : List α) {i : ℕ}, i ≤ 
l.length → (l.insertIdx i x).Perm (x :: l)
· 使用定理 `List.length_eraseIdx_of_lt`：∀ {α : Type u_1} {l : List α} {i : ℕ}, i < l
.length → (l.eraseIdx i).length = l.length - 1
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
-/
theorem set_perm_cons_eraseIdx {n : ℕ} (h : n < l.length) (a : α) :
    l.set n a ~ a :: l.eraseIdx n := by
  rw [← insertIdx_eraseIdx_self (Nat.ne_of_lt h)]
  apply perm_insertIdx
  rw [length_eraseIdx_of_lt h]
  exact Nat.le_sub_one_of_lt h
/-
**List.getElem_cons_eraseIdx_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_cons_eraseIdx_perm {n : Nat} (h : n < l.length) : l[n] :: l.eraseI
dx n ~ l
参数：h : n < l.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.set_getElem_self`：∀ {α : Type u_1} {as : List α} {i : ℕ} (h : i < a
s.length), as.set i as[i] = as
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.set_perm_cons_eraseIdx`：set_perm_cons_eraseIdx {n : Nat} (h : n < l
.length) (a : α) : l.set n a ~ a :: l.eraseIdx n
-/
theorem getElem_cons_eraseIdx_perm {n : ℕ} (h : n < l.length) :
    l[n] :: l.eraseIdx n ~ l := by
  simpa [h] using (set_perm_cons_eraseIdx h l[n]).symm
/-
**List.perm_insertIdx_iff_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_insertIdx_iff_of_le {l₁ l₂ : List α} {m n : Nat} (hm : m <= l₁.length
) (hn : n <= l₂.length) (a : α) : l₁.insertIdx m a ~ l₂.insertIdx n a ↔ l₁ ~ l₂
参数：hm : m <= l₁.length；hn : n <= l₂.length；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rel_congr_left`：rel_congr_left [Std.Symm r] [IsTrans α r] {a b c : α} (h
 : r a b) : r a c ↔ r b c
· 使用定理 `List.instSymmPerm_mathlib`：∀ {α : Type u_1}, Std.Symm List.Perm
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `List.perm_insertIdx`：∀ {α : Type u_1} (x : α) (l : List α) {i : ℕ}, i ≤ 
l.length → (l.insertIdx i x).Perm (x :: l)
· 使用定理 `rel_congr_right`：rel_congr_right [Std.Symm r] [IsTrans α r] {a b c : α} 
(h : r b c) : r a b ↔ r a c
· 使用定理 `List.perm_cons`：∀ {α : Type u_1} (a : α) {l₁ l₂ : List α}, (a :: l₁).Per
m (a :: l₂) ↔ l₁.Perm l₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem perm_insertIdx_iff_of_le {l₁ l₂ : List α} {m n : ℕ} (hm : m ≤ l₁.length)
    (hn : n ≤ l₂.length) (a : α) : l₁.insertIdx m a ~ l₂.insertIdx n a ↔ l₁ ~ l₂ := by
  rw [rel_congr_left (perm_insertIdx _ _ hm), rel_congr_right (perm_insertIdx _ _ hn), perm_cons]

alias ⟨_, Perm.insertIdx_of_le⟩ := perm_insertIdx_iff_of_le

@[simp]
/-
**List.perm_insertIdx_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_insertIdx_iff {l₁ l₂ : List α} {n : Nat} {a : α} : l₁.insertIdx n a ~
 l₂.insertIdx n a ↔ l₁ ~ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.insertIdx_of_length_lt`：∀ {α : Type u} {l : List α} {x : α} {i : ℕ}
, l.length < i → l.insertIdx i x = l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `List.perm_insertIdx_iff_of_le`：perm_insertIdx_iff_of_le {l₁ l₂ : List α}
 {m n : Nat} (hm : m <= l₁.length) (hn : n <= l₂.length) (a : α) : l₁.insertIdx 
m a ~ l₂.insertIdx …
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `List.perm_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ ↔ l₂.Perm 
l₁
· 使用定理 `Nat.le_of_not_ge`：∀ {a b : ℕ}, ¬a ≥ b → a ≤ b
-/
theorem perm_insertIdx_iff {l₁ l₂ : List α} {n : ℕ} {a : α} :
    l₁.insertIdx n a ~ l₂.insertIdx n a ↔ l₁ ~ l₂ := by
  wlog hle : length l₁ ≤ length l₂ generalizing l₁ l₂
  · rw [perm_comm, this (Nat.le_of_not_ge hle), perm_comm]
  cases Nat.lt_or_ge (length l₁) n with
  | inl hn₁ =>
    rw [insertIdx_of_length_lt hn₁]
    cases Nat.lt_or_ge (length l₂) n with
    | inl hn₂ => rw [insertIdx_of_length_lt hn₂]
    | inr hn₂ =>
      apply iff_of_false
      · intro h
        rw [h.length_eq] at hn₁
        grind
      · grind [Perm.length_eq]
  | inr hn₁ =>
    exact perm_insertIdx_iff_of_le hn₁ (Nat.le_trans hn₁ hle) _

@[gcongr]
/-
**List.Perm.insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → ∀ (n : ℕ) (a : α), (l₁.ins
ertIdx n a).Perm (l₂.insertIdx n a)
参数：n : ℕ；a : α；l₁.insertIdx n a；l₂.insertIdx n a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.perm_insertIdx_iff`：perm_insertIdx_iff {l₁ l₂ : List α} {n : Nat} {
a : α} : l₁.insertIdx n a ~ l₂.insertIdx n a ↔ l₁ ~ l₂
-/
protected theorem Perm.insertIdx {l₁ l₂ : List α} (h : l₁ ~ l₂) (n : ℕ) (a : α) :
    l₁.insertIdx n a ~ l₂.insertIdx n a :=
  perm_insertIdx_iff.mpr h
/-
**List.perm_eraseIdx_of_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_eraseIdx_of_getElem?_eq {l₁ l₂ : List α} {m n : Nat} (h : l₁[m]? = l₂
[n]?) : eraseIdx l₁ m ~ eraseIdx l₂ n ↔ l₁ ~ l₂
参数：h : l₁[m]? = l₂[n]?。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem perm_eraseIdx_of_getElem?_eq {l₁ l₂ : List α} {m n : ℕ} (h : l₁[m]? = l₂[n]?) :
    eraseIdx l₁ m ~ eraseIdx l₂ n ↔ l₁ ~ l₂ := by
  cases Nat.lt_or_ge m l₁.length with
  | inl hm =>
    rw [getElem?_eq_getElem hm, eq_comm, getElem?_eq_some_iff] at h
    cases h with
    | intro hn hnm =>
      rw [← perm_cons l₁[m], rel_congr_left (getElem_cons_eraseIdx_perm ..), ← hnm,
        rel_congr_right (getElem_cons_eraseIdx_perm ..)]
  | inr hm =>
    rw [getElem?_eq_none hm, eq_comm, getElem?_eq_none_iff] at h
    rw [eraseIdx_of_length_le h, eraseIdx_of_length_le hm]

alias ⟨_, Perm.eraseIdx_of_getElem?_eq⟩ := perm_eraseIdx_of_getElem?_eq

section Rel

open Relator

variable {r : α → β → Prop}

local infixr:80 " ∘r " => Relation.Comp

/-
**List.perm_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_comp_perm : (Perm ∘r Perm : List α -> List α -> Prop) = Perm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
-/
theorem perm_comp_perm : (Perm ∘r Perm : List α → List α → Prop) = Perm := by
  funext a c; apply propext
  constructor
  · exact fun ⟨b, hab, hba⟩ => Perm.trans hab hba
  · exact fun h => ⟨a, Perm.refl a, h⟩
/-
**List.perm_comp_forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem perm_comp_forall₂ {l u v} (hlu : Perm l u) (huv : Forall₂ r u v) :
    (Forall₂ r ∘r Perm) l v := by
  induction hlu generalizing v with
  | nil => cases huv; exact ⟨[], Forall₂.nil, Perm.nil⟩
  | cons u _hlu ih =>
    obtain - | ⟨hab, huv'⟩ := huv
    rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
    exact ⟨_ :: l₂, Forall₂.cons hab h₁₂, h₂₃.cons _⟩
  | swap a₁ a₂ h₂₃ =>
    obtain - | ⟨h₁, hr₂₃⟩ := huv
    obtain - | ⟨h₂, h₁₂⟩ := hr₂₃
    exact ⟨_, Forall₂.cons h₂ (Forall₂.cons h₁ h₁₂), Perm.swap _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
    rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩
    rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩
    exact ⟨lb₁, hab₁, Perm.trans h₁₂ h₂₃⟩
/-
**List.forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_comp_perm_eq_perm_comp_forall₂ : Forall₂ r ∘r Perm = Perm ∘r Forall₂ r := by
  funext l₁ l₃; apply propext
  constructor
  · intro h
    rcases h with ⟨l₂, h₁₂, h₂₃⟩
    have : Forall₂ (flip r) l₂ l₁ := h₁₂.flip
    rcases perm_comp_forall₂ h₂₃.symm this with ⟨l', h₁, h₂⟩
    exact ⟨l', h₂.symm, h₁.flip⟩
  · exact fun ⟨l₂, h₁₂, h₂₃⟩ => perm_comp_forall₂ h₁₂ h₂₃
/-
**List.eq_map_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：eq_map_comp_perm (f : α -> β) : (· = map f ·) ∘r (· ~ ·) = (· ~ map f ·)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.comp_eq_fun`：comp_eq_fun (f : γ -> β) : r ∘r (· = f ·) = (r · <
| f ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.forall₂_comp_perm_eq_perm_comp_forall₂`：forall₂_comp_perm_eq_perm_c
omp_forall₂ : Forall₂ r ∘r Perm = Perm ∘r Forall₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_map_comp_perm (f : α → β) : (· = map f ·) ∘r (· ~ ·) = (· ~ map f ·) := by
  conv_rhs => rw [← Relation.comp_eq_fun (map f)]
  simp only [← forall₂_eq_eq_eq, forall₂_map_right_iff, forall₂_comp_perm_eq_perm_comp_forall₂]
/-
**List.rel_perm_imp** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rel_perm_imp (hr : RightUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· -> ·)) Per
m Perm
参数：hr : RightUnique r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.comp_assoc`：comp_assoc : (r ∘r p) ∘r q = r ∘r p ∘r q
· 使用定理 `List.forall₂_comp_perm_eq_perm_comp_forall₂`：forall₂_comp_perm_eq_perm_c
omp_forall₂ : Forall₂ r ∘r Perm = Perm ∘r Forall₂ r
· 使用定理 `List.right_unique_forall₂'`：∀ {α : Type u_1} {β : Type u_2} {R : α → β →
 Prop},   Relator.RightUnique R → ∀ {a : List α} {b c : List β}, List.Forall₂ R 
a b → List.Foral…
-/
theorem rel_perm_imp (hr : RightUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· → ·)) Perm Perm :=
  fun a b h₁ c d h₂ h =>
  have : (flip (Forall₂ r) ∘r Perm ∘r Forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
  have : ((flip (Forall₂ r) ∘r Forall₂ r) ∘r Perm) b d := by
    rwa [← forall₂_comp_perm_eq_perm_comp_forall₂, ← Relation.comp_assoc] at this
  let ⟨b', ⟨_, hbc, hcb⟩, hbd⟩ := this
  have : b' = b := right_unique_forall₂' hr hcb hbc
  this ▸ hbd
/-
**List.rel_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rel_perm (hr : BiUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) Perm Perm
参数：hr : BiUnique r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rel_perm_imp`：rel_perm_imp (hr : RightUnique r) : (Forall₂ r ⇒ Fora
ll₂ r ⇒ (· -> ·)) Perm Perm
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Relator.LeftUnique.flip`：∀ {α : Type u_1} {β : Type u_2} {r : α → β → Pr
op}, Relator.LeftUnique r → Relator.RightUnique (flip r)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.Forall₂.flip`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} {a
 : List α} {b : List β},   List.Forall₂ (flip R) b a → List.Forall₂ R a b
-/
theorem rel_perm (hr : BiUnique r) : (Forall₂ r ⇒ Forall₂ r ⇒ (· ↔ ·)) Perm Perm :=
  fun _a _b hab _c _d hcd =>
  Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)

end Rel

/-
**List.count_eq_count_filter_add** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：count_eq_count_filter_add [DecidableEq α] (P : α -> Prop) [DecidablePred P
] (l : List α) (a : α) : count a l = count a (l.filter P) + count a (l.filter (¬
 P ·))
参数：P : α -> Prop；l : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.countP_eq_countP_filter_add`：∀ {α : Type u_1} (l : List α) (p q : α
 → Bool),   List.countP p l = List.countP p (List.filter q l) + List.countP p (L
ist.filter (fun a => !…
-/
lemma count_eq_count_filter_add [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (l : List α) (a : α) :
    count a l = count a (l.filter P) + count a (l.filter (¬ P ·)) := by
  unfold count
  convert countP_eq_countP_filter_add l _ P
  simp only [decide_not]
/-
**List.Perm.foldl_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {l₁ l₂ : List α} [rcomm : 
RightCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldl f b l₁ = List.foldl f 
b l₂
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.foldl_eq'`：∀ {β : Type u_1} {α : Type u_2} {f : β → α → β} {l₁
 l₂ : List α},   l₁.Perm l₂ →     (∀ x ∈ l₁, ∀ y ∈ l₁, ∀ (z : β), f (f z x) y = 
f (f z y)…
· 使用定理 `RightCommutative.right_comm`：∀ {α : Sort u} {β : Sort v} {op : β → α → β
} [self : RightCommutative op] (b : β) (a₁ a₂ : α),   op (op b a₁) a₂ = op (op b
 a₂) a₁
-/
theorem Perm.foldl_eq {f : β → α → β} {l₁ l₂ : List α} [rcomm : RightCommutative f] (p : l₁ ~ l₂) :
    ∀ b, foldl f b l₁ = foldl f b l₂ :=
  p.foldl_eq' fun x _hx y _hy z => rcomm.right_comm z x y
/-
**List.Perm.foldr_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {l₁ l₂ : List α} [lcomm : 
LeftCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldr f b l₁ = List.foldr f b
 l₂
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.recOnSwap'`：∀ {α : Type u_1} {motive : (l₁ l₂ : List α) → l₁.P
erm l₂ → Prop} {l₁ l₂ : List α} (p : l₁.Perm l₂),   motive [] [] ⋯ →     (∀ (x :
 α) {l₁ l₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LeftCommutative.left_comm`：∀ {α : Sort u} {β : Sort v} {op : α → β → β} 
[self : LeftCommutative op] (a₁ a₂ : α) (b : β),   op a₁ (op a₂ b) = op a₂ (op a
₁ b)
-/
theorem Perm.foldr_eq {f : α → β → β} {l₁ l₂ : List α} [lcomm : LeftCommutative f] (p : l₁ ~ l₂) :
    ∀ b, foldr f b l₁ = foldr f b l₂ := by
  intro b
  induction p using Perm.recOnSwap' generalizing b with
  | nil => rfl
  | cons _ _ r => simp [r b]
  | swap' _ _ _ r => simp only [foldr_cons]; rw [lcomm.left_comm, r b]
  | trans _ _ r₁ r₂ => exact Eq.trans (r₁ b) (r₂ b)

section

variable {op : α → α → α} [IA : Std.Associative op] [IC : Std.Commutative op]

local notation a " * " b => op a b

local notation l " <*> " a => foldl op a l

/-
**List.Perm.foldl_op_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {op : α → α → α} [IA : Std.Associative op] [IC : Std.Comm
utative op] {l₁ l₂ : List α} {a : α},   l₁.Perm l₂ → List.foldl op a l₁ = List.f
oldl op a l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.foldl_eq`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {l₁ 
l₂ : List α} [rcomm : RightCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldl 
f b l₁ =…
· 使用定理 `instRightCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → 
α → α} [hc : Std.Commutative f] [ha : Std.Associative f], RightCommutative f
-/
theorem Perm.foldl_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : (l₁ <*> a) = l₂ <*> a :=
  h.foldl_eq _
/-
**List.Perm.foldr_op_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {op : α → α → α} [IA : Std.Associative op] [IC : Std.Comm
utative op] {l₁ l₂ : List α} {a : α},   l₁.Perm l₂ → List.foldr op a l₁ = List.f
oldr op a l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.foldr_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {l₁ 
l₂ : List α} [lcomm : LeftCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldr f
 b l₁ = …
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
-/
theorem Perm.foldr_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : l₁.foldr op a = l₂.foldr op a :=
  h.foldr_eq _

end

/-
**List.perm_option_toList** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_option_toList {o₁ o₂ : Option α} : o₁.toList ~ o₂.toList ↔ o₁ = o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.mem_toList`：∀ {α : Type u_1} {a : α} {o : Option α}, a ∈ o.toList
 ↔ o = some a
· 使用定理 `List.Perm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁ ⊆ l
₂
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
-/
theorem perm_option_toList {o₁ o₂ : Option α} : o₁.toList ~ o₂.toList ↔ o₁ = o₂ := by
  refine ⟨fun p => ?_, fun e => e ▸ Perm.refl _⟩
  rcases o₁ with - | a <;> rcases o₂ with - | b; · rfl
  · cases p.length_eq
  · cases p.length_eq
  · exact Option.mem_toList.1 (p.symm.subset <| by simp)
/-
**List.perm_replicate_append_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_replicate_append_replicate [DecidableEq α] {l : List α} {a b : α} {m 
n : Nat} (h : a != b) : l ~ replicate m a ++ replicate n b ↔ count a l = m ∧ cou
nt b l = n ∧ l subseteq [a, b]
参数：h : a != b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.perm_iff_count`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ l
₂ : List α},   l₁.Perm l₂ ↔ ∀ (a : α), List.count a l₁ = List.count a l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.and_forall_ne`：Decidable.and_forall_ne [DecidableEq α] (a : α)
 {p : α -> Prop} : (p a ∧ forall b, b != a -> p b) ↔ forall b, p b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
· 使用定理 `List.count_replicate_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α]
 {a : α} {n : ℕ}, List.count a (List.replicate n a) = n
· 使用定理 `List.count_replicate`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a b
 : α} {n : ℕ},   List.count a (List.replicate n b) = if (b == a) = true then n e
lse 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.true_eq`：∀ (b : Bool), (true = b) = (b = true)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem perm_replicate_append_replicate
    [DecidableEq α] {l : List α} {a b : α} {m n : ℕ} (h : a ≠ b) :
    l ~ replicate m a ++ replicate n b ↔ count a l = m ∧ count b l = n ∧ l ⊆ [a, b] := by
  rw [perm_iff_count, ← Decidable.and_forall_ne a, ← Decidable.and_forall_ne b]
  suffices l ⊆ [a, b] ↔ ∀ c, c ≠ b → c ≠ a → c ∉ l by
    simp +contextual [count_replicate, h, this, count_eq_zero, Ne.symm]
  trans ∀ c, c ∈ l → c = b ∨ c = a
  · simp [subset_def, or_comm]
  · exact forall_congr' fun _ => by rw [← and_imp, ← not_or, not_imp_not]
/-
**List.map_perm_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_perm_map_iff {l' : List α} {f : α -> β} (hf : f.Injective) : map f l ~
 map f l' ↔ l ~ l'
参数：hf : f.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.eq_map_comp_perm`：eq_map_comp_perm (f : α -> β) : (· = map f ·) ∘r 
(· ~ ·) = (· ~ map f ·)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_inj_right`：∀ {α : Type u_1} {β : Type u_2} {l l' : List α} {f :
 α → β},   (∀ (x y : α), f x = f y → x = y) → (List.map f l = List.map f l' ↔ l 
= l')
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_perm_map_iff {l' : List α} {f : α → β} (hf : f.Injective) :
    map f l ~ map f l' ↔ l ~ l' := calc
  map f l ~ map f l' ↔ Relation.Comp (· = map f ·) (· ~ ·) (map f l) l' := by rw [eq_map_comp_perm]
  _ ↔ l ~ l' := by simp [Relation.Comp, map_inj_right hf]
/-
**List.Perm.flatMap_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (l : List α) {f g : α → List β},   (∀ a ∈ 
l, (f a).Perm (g a)) → (List.flatMap f l).Perm (List.flatMap g l)
参数：l : List α；∀ a ∈ l, (f a).Perm (g a)；List.flatMap f l；List.flatMap g l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.flatten_congr`：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, List.
Forall₂ (fun x1 x2 => x1.Perm x2) l₁ l₂ → l₁.flatten.Perm l₂.flatten
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.forall₂_map_right_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {R : α → β → Prop} {f : γ → β} {l : List α} {u : List γ},   List.Forall₂ R l 
(List.map f u) ↔…
· 使用定理 `List.forall₂_map_left_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} {R : α → β → Prop} {f : γ → α} {l : List γ} {u : List β},   List.Forall₂ R (Li
st.map f l) u ↔…
· 使用定理 `List.forall₂_same`：∀ {α : Type u_1} {Rₐ : α → α → Prop} {l : List α}, Li
st.Forall₂ Rₐ l l ↔ ∀ x ∈ l, Rₐ x x
-/
theorem Perm.flatMap_left (l : List α) {f g : α → List β} (h : ∀ a ∈ l, f a ~ g a) :
    l.flatMap f ~ l.flatMap g :=
  Perm.flatten_congr <| by
    rwa [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]

@[gcongr]
/-
**List.Perm.flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α} {f g : α → List β},   l₁.
Perm l₂ → (∀ a ∈ l₁, (f a).Perm (g a)) → (List.flatMap f l₁).Perm (List.flatMap 
g l₂)
参数：∀ a ∈ l₁, (f a).Perm (g a)；List.flatMap f l₁；List.flatMap g l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.flatMap_left`：∀ {α : Type u_1} {β : Type u_2} (l : List α) {f 
g : α → List β},   (∀ a ∈ l, (f a).Perm (g a)) → (List.flatMap f l).Perm (List.f
latMap g l)
· 使用定理 `List.Perm.flatMap_right`：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α
} (f : α → List β),   l₁.Perm l₂ → (List.flatMap f l₁).Perm (List.flatMap f l₂)
-/
protected theorem Perm.flatMap {l₁ l₂ : List α} {f g : α → List β} (h : l₁ ~ l₂)
    (hfg : ∀ a ∈ l₁, f a ~ g a) : l₁.flatMap f ~ l₂.flatMap g :=
  .trans (.flatMap_left _ hfg) (h.flatMap_right _)
/-
**List.flatMap_append_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：flatMap_append_perm (l : List α) (f g : α -> List β) : l.flatMap f ++ l.fl
atMap g ~ l.flatMap fun x => f x ++ g x
参数：l : List α；f g : α -> List β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatMap_nil`：∀ {α : Type u} {β : Type v} {f : α → List β}, List.fla
tMap f [] = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.Perm.append_left`：∀ {α : Type u_1} {t₁ t₂ : List α} (l : List α), t
₁.Perm t₂ → (l ++ t₁).Perm (l ++ t₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Perm.append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (t₁ : List α),
 l₁.Perm l₂ → (l₁ ++ t₁).Perm (l₂ ++ t₁)
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
-/
theorem flatMap_append_perm (l : List α) (f g : α → List β) :
    l.flatMap f ++ l.flatMap g ~ l.flatMap fun x => f x ++ g x := by
  induction l with | nil => simp | cons a l IH => ?_
  simp only [flatMap_cons, append_assoc]
  refine (Perm.trans ?_ (IH.append_left _)).append_left _
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append_right _
/-
**List.map_append_flatMap_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_append_flatMap_perm (l : List α) (f : α -> β) (g : α -> List β) : l.ma
p f ++ l.flatMap g ~ l.flatMap fun x => f x :: g x
参数：l : List α；f : α -> β；g : α -> List β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatMap_append_perm`：flatMap_append_perm (l : List α) (f g : α -> L
ist β) : l.flatMap f ++ l.flatMap g ~ l.flatMap fun x => f x ++ g x
-/
theorem map_append_flatMap_perm (l : List α) (f : α → β) (g : α → List β) :
    l.map f ++ l.flatMap g ~ l.flatMap fun x => f x :: g x := by
  simpa [← map_eq_flatMap] using flatMap_append_perm l (fun x => [f x]) g
/-
**List.Perm.product_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α} (t₁ : List β), l₁.Perm l₂
 → (l₁.product t₁).Perm (l₂.product t₁)
参数：t₁ : List β；l₁.product t₁；l₂.product t₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.flatMap_right`：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α
} (f : α → List β),   l₁.Perm l₂ → (List.flatMap f l₁).Perm (List.flatMap f l₂)
-/
theorem Perm.product_right {l₁ l₂ : List α} (t₁ : List β) (p : l₁ ~ l₂) :
    product l₁ t₁ ~ product l₂ t₁ :=
  p.flatMap_right _
/-
**List.Perm.product_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (l : List α) {t₁ t₂ : List β}, t₁.Perm t₂ 
→ (l.product t₁).Perm (l.product t₂)
参数：l : List α；l.product t₁；l.product t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.flatMap_left`：∀ {α : Type u_1} {β : Type u_2} (l : List α) {f 
g : α → List β},   (∀ a ∈ l, (f a).Perm (g a)) → (List.flatMap f l).Perm (List.f
latMap g l)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
-/
theorem Perm.product_left (l : List α) {t₁ t₂ : List β} (p : t₁ ~ t₂) :
    product l t₁ ~ product l t₂ :=
  (Perm.flatMap_left _) fun _ _ => p.map _

@[gcongr]
/-
**List.Perm.product** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α} {t₁ t₂ : List β},   l₁.Pe
rm l₂ → t₁.Perm t₂ → (l₁.product t₁).Perm (l₂.product t₂)
参数：l₁.product t₁；l₂.product t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.product_right`：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α
} (t₁ : List β), l₁.Perm l₂ → (l₁.product t₁).Perm (l₂.product t₁)
· 使用定理 `List.Perm.product_left`：∀ {α : Type u_1} {β : Type u_2} (l : List α) {t₁
 t₂ : List β}, t₁.Perm t₂ → (l.product t₁).Perm (l.product t₂)
-/
theorem Perm.product {l₁ l₂ : List α} {t₁ t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) :
    product l₁ t₁ ~ product l₂ t₂ :=
  (p₁.product_right t₁).trans (p₂.product_left l₂)

end List

