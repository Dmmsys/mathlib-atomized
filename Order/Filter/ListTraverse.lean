/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Control.Traversable.Instances
public import Mathlib.Order.Filter.Map
/-!
# Properties of `Traversable.traverse` on `List`s and `Filter`s

In this file we prove basic properties (monotonicity, membership)
for `Traversable.traverse f l`, where `f : β → Filter α` and `l : List β`.
-/

public section

open Set List

namespace Filter

universe u

variable {α β γ : Type u} {f : β → Filter α} {s : γ → Set α}

/-
**Filter.sequence_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} (as bs : List (Filter α)), List.Forall₂ (fun x1 x2 => x1 ≤ 
x2) as bs → sequence as ≤ sequence bs
参数：as bs : List (Filter α)；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.seq_mono`：seq_mono {f₁ f₂ : Filter (α -> β)} {g₁ g₂ : Filter α} (
hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.seq g₁ <= f₂.seq g₂
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem sequence_mono : ∀ as bs : List (Filter α), Forall₂ (· ≤ ·) as bs → sequence as ≤ sequence bs
  | [], [], Forall₂.nil => le_rfl
  | _::as, _::bs, Forall₂.cons h hs => seq_mono (map_mono h) (sequence_mono as bs hs)
/-
**Filter.mem_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α β γ : Type u} {f : β → Filter α} {s : γ → Set α} (fs : List β) (us : 
List γ),   List.Forall₂ (fun b c => s c ∈ f b) fs us → traverse s us ∈ traverse 
f fs
参数：fs : List β；us : List γ；fun b c => s c ∈ f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_pure`：mem_pure {a : α} {s : Set α} : s in (pure a : Filter α)
 ↔ a in s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Filter.seq_mem_seq`：seq_mem_seq {f : Filter (α -> β)} {g : Filter α} {s 
: Set (α -> β)} {t : Set α} (hs : s in f) (ht : t in g) : s.seq t in f.seq g
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem mem_traverse :
    ∀ (fs : List β) (us : List γ),
      Forall₂ (fun b c => s c ∈ f b) fs us → traverse s us ∈ traverse f fs
  | [], [], Forall₂.nil => mem_pure.2 <| mem_singleton _
  | _::fs, _::us, Forall₂.cons h hs => seq_mem_seq (image_mem_map h) (mem_traverse fs us hs)

-- TODO: add a `Filter.HasBasis` statement
/-
**Filter.mem_traverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_traverse_iff (fs : List β) (t : Set (List α)) : t in traverse f fs ↔ e
xists us : List (Set α), Forall₂ (fun b (s : Set α) => s in f b) fs us ∧ sequenc
e us subseteq t
参数：fs : List β；t : Set (List α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_seq_iff`：mem_seq_iff {f : Filter (α -> β)} {g : Filter α} {s 
: Set β} : s in f.seq g ↔ exists u in f, exists t in g, Set.seq u t subseteq s
· 使用定理 `Filter.mem_map_iff_exists_image`：mem_map_iff_exists_image : t in map m f
 ↔ exists s in f, m '' s subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.seq_mono`：seq_mono {s₀ s₁ : Set (α -> β)} {t₀ t₁ : Set α} (hs : s₀ s
ubseteq s₁) (ht : t₀ subseteq t₁) : seq s₀ t₀ subseteq seq s₁ t₁
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.mem_traverse`：∀ {α β γ : Type u} {f : β → Filter α} {s : γ → Set 
α} (fs : List β) (us : List γ),   List.Forall₂ (fun b c => s c ∈ f b) fs us → tr
averse s …
-/
theorem mem_traverse_iff (fs : List β) (t : Set (List α)) :
    t ∈ traverse f fs ↔
      ∃ us : List (Set α), Forall₂ (fun b (s : Set α) => s ∈ f b) fs us ∧ sequence us ⊆ t := by
  constructor
  · induction fs generalizing t with
    | nil =>
      simp only [sequence, mem_pure, imp_self, forall₂_nil_left_iff, exists_eq_left, Set.pure_def,
        singleton_subset_iff, traverse_nil]
    | cons b fs ih =>
      intro ht
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
      rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hwu⟩
      rcases ih v hv with ⟨us, hus, hu⟩
      exact ⟨w::us, Forall₂.cons hw hus, (Set.seq_mono hwu hu).trans ht⟩
  · rintro ⟨us, hus, hs⟩
    exact mem_of_superset (mem_traverse _ _ hus) hs

end Filter

