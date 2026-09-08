/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Kevin H. Wilson, Heather Macbeth
-/
module

public import Mathlib.Order.Filter.Tendsto

/-!
# Product and coproduct filters

In this file we prove some basic properties of `f ×ˢ g` and `Filter.coprod f g`. The product
of two filters is the largest filter `l` such that `Filter.Tendsto Prod.fst l f` and
`Filter.Tendsto Prod.snd l g`.

## Implementation details

The product filter cannot be defined using the monad structure on filters. For example:

```lean
F := do {x ← seq, y ← top, return (x, y)}
G := do {y ← top, x ← seq, return (x, y)}
```
hence:
```lean
s ∈ F  ↔  ∃ n, [n..∞] × univ ⊆ s
s ∈ G  ↔  ∀ i:ℕ, ∃ n, [n..∞] × {i} ⊆ s
```
Now `⋃ i, [i..∞] × {i}` is in `G` but not in `F`.
As product filter we want to have `F` as result.

-/

public section

open Set

open Filter

namespace Filter

variable {α β γ δ : Type*} {ι : Sort*}

section Prod

variable {s : Set α} {t : Set β} {f : Filter α} {g : Filter β}

/-
**Filter.prod_mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t in f ×ˢ g
参数：hs : s in f；ht : t in g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
-/
theorem prod_mem_prod (hs : s ∈ f) (ht : t ∈ g) : s ×ˢ t ∈ f ×ˢ g :=
  inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)
/-
**Filter.mem_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} : s in f ×ˢ g
 ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_inf_of_inter`：mem_inf_of_inter {f g : Filter α} {s t u : Set 
α} (hs : s in f) (ht : t in g) (h : s inter t subseteq u) : u in f ⊓ g
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
-/
theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f ×ˢ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s := by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h

@[simp]
/-
**Filter.compl_diagonal_mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_diagonal_mem_prod {l₁ l₂ : Filter α} : (diagonal α)ᶜ in l₁ ×ˢ l₂ ↔ D
isjoint l₁ l₂
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
theorem compl_diagonal_mem_prod {l₁ l₂ : Filter α} : (diagonal α)ᶜ ∈ l₁ ×ˢ l₂ ↔ Disjoint l₁ l₂ := by
  simp only [mem_prod_iff, Filter.disjoint_iff, prod_subset_compl_diagonal_iff_disjoint]

@[simp]
/-
**Filter.prod_mem_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_mem_prod_iff [f.NeBot] [g.NeBot] : s ×ˢ t in f ×ˢ g ↔ s in f ∧ t in g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_mem_prod_iff [f.NeBot] [g.NeBot] : s ×ˢ t ∈ f ×ˢ g ↔ s ∈ f ∧ t ∈ g :=
  ⟨fun h =>
    let ⟨_s', hs', _t', ht', H⟩ := mem_prod_iff.1 h
    (prod_subset_prod_iff.1 H).elim
      (fun ⟨hs's, ht't⟩ => ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩) fun h =>
      h.elim (fun hs'e => absurd hs'e (nonempty_of_mem hs').ne_empty) fun ht'e =>
        absurd ht'e (nonempty_of_mem ht').ne_empty,
    fun h => prod_mem_prod h.1 h.2⟩
/-
**Filter.mem_prod_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_prod_principal {s : Set (α × β)} : s in f ×ˢ 𝓟 t ↔ { a | forall b in t
, (a, b) in s } in f
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.exists_mem_subset_iff`：exists_mem_subset_iff : (exists t in f, t 
subseteq s) ↔ s in f
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
-/
theorem mem_prod_principal {s : Set (α × β)} :
    s ∈ f ×ˢ 𝓟 t ↔ { a | ∀ b ∈ t, (a, b) ∈ s } ∈ f := by
  rw [← @exists_mem_subset_iff _ f, mem_prod_iff]
  refine exists_congr fun u => Iff.rfl.and ⟨?_, fun h => ⟨t, mem_principal_self t, ?_⟩⟩
  · rintro ⟨v, v_in, hv⟩ a a_in b b_in
    exact hv (mk_mem_prod a_in <| v_in b_in)
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h hx y hy
/-
**Filter.mem_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_prod_top {s : Set (α × β)} : s in f ×ˢ (⊤ : Filter β) ↔ { a | forall b
, (a, b) in s } in f
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `Filter.mem_prod_principal`：mem_prod_principal {s : Set (α × β)} : s in f
 ×ˢ 𝓟 t ↔ { a | forall b in t, (a, b) in s } in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_prod_top {s : Set (α × β)} :
    s ∈ f ×ˢ (⊤ : Filter β) ↔ { a | ∀ b, (a, b) ∈ s } ∈ f := by
  rw [← principal_univ, mem_prod_principal]
  simp only [mem_univ, forall_true_left]
/-
**Filter.eventually_prod_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_prod_principal_iff {p : α × β -> Prop} {s : Set β} : (forallᶠ x
 : α × β in f ×ˢ 𝓟 s, p x) ↔ forallᶠ x : α in f, forall y : β, y in s -> p (x, y
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
· 使用定理 `Filter.mem_prod_principal`：mem_prod_principal {s : Set (α × β)} : s in f
 ×ˢ 𝓟 t ↔ { a | forall b in t, (a, b) in s } in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_prod_principal_iff {p : α × β → Prop} {s : Set β} :
    (∀ᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ ∀ᶠ x : α in f, ∀ y : β, y ∈ s → p (x, y) := by
  rw [eventually_iff, eventually_iff, mem_prod_principal]
  simp only [mem_ofPred_eq]
/-
**Filter.comap_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_prod (f : α -> β × γ) (b : Filter β) (c : Filter γ) : comap f (b ×ˢ 
c) = comap (Prod.fst ∘ f) b ⊓ comap (Prod.snd ∘ f) c
参数：f : α -> β × γ；b : Filter β；c : Filter γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_eq_inf`：prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g =
 f.comap Prod.fst ⊓ g.comap Prod.snd
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
-/
theorem comap_prod (f : α → β × γ) (b : Filter β) (c : Filter γ) :
    comap f (b ×ˢ c) = comap (Prod.fst ∘ f) b ⊓ comap (Prod.snd ∘ f) c := by
  rw [prod_eq_inf, comap_inf, Filter.comap_comap, Filter.comap_comap]
/-
**Filter.comap_prodMap_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_prodMap_prod (f : α -> β) (g : γ -> δ) (lb : Filter β) (ld : Filter 
δ) : comap (Prod.map f g) (lb ×ˢ ld) = comap f lb ×ˢ comap g ld
参数：f : α -> β；g : γ -> δ；lb : Filter β；ld : Filter δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_prodMap_prod (f : α → β) (g : γ → δ) (lb : Filter β) (ld : Filter δ) :
    comap (Prod.map f g) (lb ×ˢ ld) = comap f lb ×ˢ comap g ld := by
  simp [prod_eq_inf, comap_comap, Function.comp_def]
/-
**Filter.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_top : f ×ˢ (⊤ : Filter β) = f.comap Prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_eq_inf`：prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g =
 f.comap Prod.fst ⊓ g.comap Prod.snd
· 使用定理 `Filter.comap_top`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.co
map m ⊤ = ⊤
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
-/
theorem prod_top : f ×ˢ (⊤ : Filter β) = f.comap Prod.fst := by
  rw [prod_eq_inf, comap_top, inf_top_eq]
/-
**Filter.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：top_prod : (⊤ : Filter α) ×ˢ g = g.comap Prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_eq_inf`：prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g =
 f.comap Prod.fst ⊓ g.comap Prod.snd
· 使用定理 `Filter.comap_top`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.co
map m ⊤ = ⊤
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
-/
theorem top_prod : (⊤ : Filter α) ×ˢ g = g.comap Prod.snd := by
  rw [prod_eq_inf, comap_top, top_inf_eq]
/-
**Filter.sup_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sup_prod (f₁ f₂ : Filter α) (g : Filter β) : (f₁ ⊔ f₂) ×ˢ g = (f₁ ×ˢ g) ⊔ 
(f₂ ×ˢ g)
参数：f₁ f₂ : Filter α；g : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_sup`：comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g
₂
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_prod (f₁ f₂ : Filter α) (g : Filter β) : (f₁ ⊔ f₂) ×ˢ g = (f₁ ×ˢ g) ⊔ (f₂ ×ˢ g) := by
  simp only [prod_eq_inf, comap_sup, inf_sup_right]
/-
**Filter.prod_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_sup (f : Filter α) (g₁ g₂ : Filter β) : f ×ˢ (g₁ ⊔ g₂) = (f ×ˢ g₁) ⊔ 
(f ×ˢ g₂)
参数：f : Filter α；g₁ g₂ : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_sup`：comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g
₂
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_sup (f : Filter α) (g₁ g₂ : Filter β) : f ×ˢ (g₁ ⊔ g₂) = (f ×ˢ g₁) ⊔ (f ×ˢ g₂) := by
  simp only [prod_eq_inf, comap_sup, inf_sup_left]

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.eventually_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_prod_iff {p : α × β -> Prop} : (forallᶠ x in f ×ˢ g, p x) ↔ exi
sts pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exists pb : β -> Prop, (forallᶠ y i
n g, pb y) ∧ forall {x}, pa x -> forall {y}, pb y -> p (x, y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
-/
theorem eventually_prod_iff {p : α × β → Prop} :
    (∀ᶠ x in f ×ˢ g, p x) ↔
      ∃ pa : α → Prop, (∀ᶠ x in f, pa x) ∧ ∃ pb : β → Prop, (∀ᶠ y in g, pb y) ∧
        ∀ {x}, pa x → ∀ {y}, pb y → p (x, y) := by
  simpa only [Set.prod_subset_iff] using! @mem_prod_iff α β p f g
/-
**Filter.tendsto_fst** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
theorem tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f :=
  tendsto_inf_left tendsto_comap
/-
**Filter.tendsto_snd** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_inf_right`：tendsto_inf_right {f : α -> β} {x₁ x₂ : Filter
 α} {y : Filter β} (h : Tendsto f x₂ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
theorem tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g :=
  tendsto_inf_right tendsto_comap

/-- If a function tends to a product `g ×ˢ h` of filters, then its first component tends to
`g`. See also `Filter.Tendsto.fst_nhds` for the special case of converging to a point in a
product of two topological spaces. -/
/-
**Filter.Tendsto.fst** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Filter 
β} {h : Filter γ} {m : α → β × γ},   Filter.Tendsto m f (g ×ˢ h) → Filter.Tendst
o (fun a => (m a).1) f g
参数：g ×ˢ h；fun a => (m a).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f

--- 原说明 ---
If a function tends to a product `g ×ˢ h` of filters, then its first component t
ends to
`g`. See also `Filter.Tendsto.fst_nhds` for the special case of converging to a 
point in a
product of two topological spaces.
-/
theorem Tendsto.fst {h : Filter γ} {m : α → β × γ} (H : Tendsto m f (g ×ˢ h)) :
    Tendsto (fun a ↦ (m a).1) f g :=
  tendsto_fst.comp H

/-- If a function tends to a product `g ×ˢ h` of filters, then its second component tends to
`h`. See also `Filter.Tendsto.snd_nhds` for the special case of converging to a point in a
product of two topological spaces. -/
/-
**Filter.Tendsto.snd** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Filter 
β} {h : Filter γ} {m : α → β × γ},   Filter.Tendsto m f (g ×ˢ h) → Filter.Tendst
o (fun a => (m a).2) f h
参数：g ×ˢ h；fun a => (m a).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g

--- 原说明 ---
If a function tends to a product `g ×ˢ h` of filters, then its second component 
tends to
`h`. See also `Filter.Tendsto.snd_nhds` for the special case of converging to a 
point in a
product of two topological spaces.
-/
theorem Tendsto.snd {h : Filter γ} {m : α → β × γ} (H : Tendsto m f (g ×ˢ h)) :
    Tendsto (fun a ↦ (m a).2) f h :=
  tendsto_snd.comp H
/-
**Filter.Tendsto.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Filter 
β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.Tendsto m₁ f g → Filter.Te
ndsto m₂ f h → Filter.Tendsto (fun x => (m₁ x, m₂ x)) f (g ×ˢ h)
参数：fun x => (m₁ x, m₂ x)；g ×ˢ h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
-/
theorem Tendsto.prodMk {h : Filter γ} {m₁ : α → β} {m₂ : α → γ}
    (h₁ : Tendsto m₁ f g) (h₂ : Tendsto m₂ f h) : Tendsto (fun x => (m₁ x, m₂ x)) f (g ×ˢ h) :=
  tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩
/-
**Filter.tendsto_prod_swap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_prod_swap : Tendsto (Prod.swap : α × β -> β × α) (f ×ˢ g) (g ×ˢ f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
-/
theorem tendsto_prod_swap : Tendsto (Prod.swap : α × β → β × α) (f ×ˢ g) (g ×ˢ f) :=
  tendsto_snd.prodMk tendsto_fst
/-
**Filter.Eventually.prod_inl** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {p : α → Prop},   (∀ᶠ (x :
 α) in la, p x) → ∀ (lb : Filter β), ∀ᶠ (x : α × β) in la ×ˢ lb, p x.1
参数：∀ᶠ (x : α) in la, p x；lb : Filter β；x : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
-/
theorem Eventually.prod_inl {la : Filter α} {p : α → Prop} (h : ∀ᶠ x in la, p x) (lb : Filter β) :
    ∀ᶠ x in la ×ˢ lb, p (x : α × β).1 :=
  tendsto_fst.eventually h
/-
**Filter.Eventually.prod_inr** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {lb : Filter β} {p : β → Prop},   (∀ᶠ (x :
 β) in lb, p x) → ∀ (la : Filter α), ∀ᶠ (x : α × β) in la ×ˢ lb, p x.2
参数：∀ᶠ (x : β) in lb, p x；la : Filter α；x : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
-/
theorem Eventually.prod_inr {lb : Filter β} {p : β → Prop} (h : ∀ᶠ x in lb, p x) (la : Filter α) :
    ∀ᶠ x in la ×ˢ lb, p (x : α × β).2 :=
  tendsto_snd.eventually h
/-
**Filter.Eventually.prod_mk** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {pa : α → Prop},   (∀ᶠ (x 
: α) in la, pa x) →     ∀ {lb : Filter β} {pb : β → Prop}, (∀ᶠ (y : β) in lb, pb
 y) → ∀ᶠ (p : α × β) in la ×ˢ lb, pa p.1 ∧ pb p.2
参数：∀ᶠ (x : α) in la, pa x；∀ᶠ (y : β) in lb, pb y；p : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Eventually.prod_inl`：∀ {α : Type u_1} {β : Type u_2} {la : Filter
 α} {p : α → Prop},   (∀ᶠ (x : α) in la, p x) → ∀ (lb : Filter β), ∀ᶠ (x : α × β
) in la ×ˢ lb, p…
· 使用定理 `Filter.Eventually.prod_inr`：∀ {α : Type u_1} {β : Type u_2} {lb : Filter
 β} {p : β → Prop},   (∀ᶠ (x : β) in lb, p x) → ∀ (la : Filter α), ∀ᶠ (x : α × β
) in la ×ˢ lb, p…
-/
theorem Eventually.prod_mk {la : Filter α} {pa : α → Prop} (ha : ∀ᶠ x in la, pa x) {lb : Filter β}
    {pb : β → Prop} (hb : ∀ᶠ y in lb, pb y) : ∀ᶠ p in la ×ˢ lb, pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl lb).and (hb.prod_inr la)
/-
**Filter.EventuallyEq.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_6} {la : Filter
 α} {fa ga : α → γ},   fa =ᶠ[la] ga → ∀ {lb : Filter β} {fb gb : β → δ}, fb =ᶠ[l
b] gb → Prod.map fa fb =ᶠ[la ×ˢ lb] Prod.map ga gb
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem EventuallyEq.prodMap {δ} {la : Filter α} {fa ga : α → γ} (ha : fa =ᶠ[la] ga)
    {lb : Filter β} {fb gb : β → δ} (hb : fb =ᶠ[lb] gb) :
    Prod.map fa fb =ᶠ[la ×ˢ lb] Prod.map ga gb :=
  (Eventually.prod_mk ha hb).mono fun _ h => Prod.ext h.1 h.2
/-
**Filter.EventuallyLE.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyLE`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_6} [inst : LE γ
] [inst_1 : LE δ] {la : Filter α}   {fa ga : α → γ},   fa ≤ᶠ[la] ga → ∀ {lb : Fi
lter β} {fb gb : β → δ}, fb ≤ᶠ[lb] gb → Prod.map fa fb ≤ᶠ[la ×ˢ lb] Prod.map ga 
gb
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
-/
theorem EventuallyLE.prodMap {δ} [LE γ] [LE δ] {la : Filter α} {fa ga : α → γ} (ha : fa ≤ᶠ[la] ga)
    {lb : Filter β} {fb gb : β → δ} (hb : fb ≤ᶠ[lb] gb) :
    Prod.map fa fb ≤ᶠ[la ×ˢ lb] Prod.map ga gb :=
  Eventually.prod_mk ha hb
/-
**Filter.Eventually.curry** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {p : α × β
 → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x : α) in la, ∀ᶠ (y : β) in 
lb, p (x, y)
参数：∀ᶠ (x : α × β) in la ×ˢ lb, p x；x : α；y : β；x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem Eventually.curry {la : Filter α} {lb : Filter β} {p : α × β → Prop}
    (h : ∀ᶠ x in la ×ˢ lb, p x) : ∀ᶠ x in la, ∀ᶠ y in lb, p (x, y) := by
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩
  exact ha.mono fun a ha => hb.mono fun b hb => h ha hb
/-
**Filter.Frequently.uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Frequently`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {p : α → β
 → Prop},   (∃ᶠ (x : α) in la, ∃ᶠ (y : β) in lb, p x y) → ∃ᶠ (xy : α × β) in la 
×ˢ lb, p xy.1 xy.2
参数：∃ᶠ (x : α) in la, ∃ᶠ (y : β) in lb, p x y；xy : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
-/
protected lemma Frequently.uncurry {la : Filter α} {lb : Filter β} {p : α → β → Prop}
    (h : ∃ᶠ x in la, ∃ᶠ y in lb, p x y) : ∃ᶠ xy in la ×ˢ lb, p xy.1 xy.2 := by
  contrapose! h
  exact h.curry
/-
**Filter.Frequently.of_curry** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Frequently`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {lb : Filter β} {p : α × β
 → Prop},   (∃ᶠ (x : α) in la, ∃ᶠ (y : β) in lb, p (x, y)) → ∃ᶠ (xy : α × β) in 
la ×ˢ lb, p xy
参数：∃ᶠ (x : α) in la, ∃ᶠ (y : β) in lb, p (x, y)；xy : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.uncurry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {lb : Filter β} {p : α → β → Prop},   (∃ᶠ (x : α) in la, ∃ᶠ (y : β) in lb, p 
x y) → ∃ᶠ (xy :…
-/
lemma Frequently.of_curry {la : Filter α} {lb : Filter β} {p : α × β → Prop}
    (h : ∃ᶠ x in la, ∃ᶠ y in lb, p (x, y)) : ∃ᶠ xy in la ×ˢ lb, p xy :=
  h.uncurry
/-
**Filter.Eventually.image_of_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : Filter β} {y : α → β} 
{r : α → β → Prop},   Filter.Tendsto y f g → (∀ᶠ (p : α × β) in f ×ˢ g, r p.1 p.
2) → ∀ᶠ (x : α) in f, r x (y x)
参数：∀ᶠ (p : α × β) in f ×ˢ g, r p.1 p.2；x : α；y x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem Eventually.image_of_prod {y : α → β} {r : α → β → Prop}
    (hy : Tendsto y f g) (hr : ∀ᶠ p in f ×ˢ g, r p.1 p.2) : ∀ᶠ x in f, r x (y x) := by
  obtain ⟨p, hp, q, hq, hr⟩ := eventually_prod_iff.mp hr
  filter_upwards [hp, hy.eventually hq] with _ hp hq using hr hp hq

/-- A fact that is eventually true about all pairs `l ×ˢ l` is eventually true about
all diagonal pairs `(i, i)` -/
/-
**Filter.Eventually.diag_of_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} {p : α × α → Prop}, (∀ᶠ (i : α × α) in f ×
ˢ f, p i) → ∀ᶠ (i : α) in f, p (i, i)
参数：∀ᶠ (i : α × α) in f ×ˢ f, p i；i : α；i, i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.image_of_prod`：∀ {α : Type u_1} {β : Type u_2} {f : Fi
lter α} {g : Filter β} {y : α → β} {r : α → β → Prop},   Filter.Tendsto y f g → 
(∀ᶠ (p : α × β) in f …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
A fact that is eventually true about all pairs `l ×ˢ l` is eventually true about
all diagonal pairs `(i, i)`
-/
theorem Eventually.diag_of_prod {p : α × α → Prop} (h : ∀ᶠ i in f ×ˢ f, p i) :
    ∀ᶠ i in f, p (i, i) :=
  h.image_of_prod (r := p.curry) tendsto_id
/-
**Filter.Eventually.diag_of_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
ly`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {f : Filter α} {g : Filter γ} {p : (α × α)
 × γ → Prop},   (∀ᶠ (x : (α × α) × γ) in (f ×ˢ f) ×ˢ g, p x) → ∀ᶠ (x : α × γ) in
 f ×ˢ g, p ((x.1, x.1), x.2)
参数：α × α；∀ᶠ (x : (α × α) × γ) in (f ×ˢ f) ×ˢ g, p x；x : α × γ；(x.1, x.1), x.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Filter.Eventually.diag_of_prod`：∀ {α : Type u_1} {f : Filter α} {p : α ×
 α → Prop}, (∀ᶠ (i : α × α) in f ×ˢ f, p i) → ∀ᶠ (i : α) in f, p (i, i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Eventually.diag_of_prod_left {f : Filter α} {g : Filter γ} {p : (α × α) × γ → Prop} :
    (∀ᶠ x in (f ×ˢ f) ×ˢ g, p x) → ∀ᶠ x : α × γ in f ×ˢ g, p ((x.1, x.1), x.2) := by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.diag_of_prod.prod_mk hs).mono fun x hx => by simp only [hst hx.1 hx.2]
/-
**Filter.Eventually.diag_of_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
lly`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {f : Filter α} {g : Filter γ} {p : α × γ ×
 γ → Prop},   (∀ᶠ (x : α × γ × γ) in f ×ˢ g ×ˢ g, p x) → ∀ᶠ (x : α × γ) in f ×ˢ 
g, p (x.1, x.2, x.2)
参数：∀ᶠ (x : α × γ × γ) in f ×ˢ g ×ˢ g, p x；x : α × γ；x.1, x.2, x.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Filter.Eventually.diag_of_prod`：∀ {α : Type u_1} {f : Filter α} {p : α ×
 α → Prop}, (∀ᶠ (i : α × α) in f ×ˢ f, p i) → ∀ᶠ (i : α) in f, p (i, i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Eventually.diag_of_prod_right {f : Filter α} {g : Filter γ} {p : α × γ × γ → Prop} :
    (∀ᶠ x in f ×ˢ (g ×ˢ g), p x) → ∀ᶠ x : α × γ in f ×ˢ g, p (x.1, x.2, x.2) := by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.prod_mk hs.diag_of_prod).mono fun x hx => by simp only [hst hx.1 hx.2]
/-
**Filter.tendsto_diag** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_diag : Tendsto Function.diag f (f ×ˢ f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iff_eventually`：tendsto_iff_eventually {f : α -> β} {l₁ :
 Filter α} {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ forall ⦃p : β -> Prop⦄, (forallᶠ 
y in l₂, p y) -> fo…
· 使用定理 `Filter.Eventually.diag_of_prod`：∀ {α : Type u_1} {f : Filter α} {p : α ×
 α → Prop}, (∀ᶠ (i : α × α) in f ×ˢ f, p i) → ∀ᶠ (i : α) in f, p (i, i)
-/
theorem tendsto_diag : Tendsto Function.diag f (f ×ˢ f) :=
  tendsto_iff_eventually.mpr fun _ hpr => hpr.diag_of_prod
/-
**Filter.prod_iInf_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_iInf_left [Nonempty ι] {f : ι -> Filter α} {g : Filter β} : (⨅ i, f i
) ×ˢ g = ⨅ i, f i ×ˢ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `iInf_inf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] [No
nempty ι] {f : ι → α} {a : α},   (⨅ x, f x) ⊓ a = ⨅ x, f x ⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_iInf_left [Nonempty ι] {f : ι → Filter α} {g : Filter β} :
    (⨅ i, f i) ×ˢ g = ⨅ i, f i ×ˢ g := by
  simp only [prod_eq_inf, comap_iInf, iInf_inf]
/-
**Filter.prod_iInf_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_iInf_right [Nonempty ι] {f : Filter α} {g : ι -> Filter β} : (f ×ˢ ⨅ 
i, g i) = ⨅ i, f ×ˢ g i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `inf_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] [No
nempty ι] {f : ι → α} {a : α}, a ⊓ ⨅ x, f x = ⨅ x, a ⊓ f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_iInf_right [Nonempty ι] {f : Filter α} {g : ι → Filter β} :
    (f ×ˢ ⨅ i, g i) = ⨅ i, f ×ˢ g i := by
  simp only [prod_eq_inf, comap_iInf, inf_iInf]

@[mono, gcongr]
/-
**Filter.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ <= f₂) (hg : g₁ <
= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
参数：hf : f₁ <= f₂；hg : g₁ <= g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
-/
theorem prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁ ×ˢ g₁ ≤ f₂ ×ˢ g₂ :=
  inf_le_inf (comap_mono hf) (comap_mono hg)
/-
**Filter.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} (hf : f₁ <= f₂) : f₁ ×ˢ g
 <= f₂ ×ˢ g
参数：g : Filter β；hf : f₁ <= f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} (hf : f₁ ≤ f₂) : f₁ ×ˢ g ≤ f₂ ×ˢ g :=
  Filter.prod_mono hf rfl.le
/-
**Filter.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_mono_right (f : Filter α) {g₁ g₂ : Filter β} (hf : g₁ <= g₂) : f ×ˢ g
₁ <= f ×ˢ g₂
参数：f : Filter α；hf : g₁ <= g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem prod_mono_right (f : Filter α) {g₁ g₂ : Filter β} (hf : g₁ ≤ g₂) : f ×ˢ g₁ ≤ f ×ˢ g₂ :=
  Filter.prod_mono rfl.le hf
/-
**Filter.prod_comap_comap_eq.** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comap_comap_eq.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
    comap m₁ f₁ ×ˢ comap m₂ f₂ = comap (fun p : β₁ × β₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ˢ f₂) := by
  simp only [prod_eq_inf, comap_comap, comap_inf, Function.comp_def]
/-
**Filter.prod_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_comm' : f ×ˢ g = comap Prod.swap (g ×ˢ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_comm' : f ×ˢ g = comap Prod.swap (g ×ˢ f) := by
  simp only [prod_eq_inf, comap_comap, Function.comp_def, inf_comm, Prod.swap, comap_inf]
/-
**Filter.prod_comm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_comm'`：prod_comm' : f ×ˢ g = comap Prod.swap (g ×ˢ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_swap_eq_comap_swap`：map_swap_eq_comap_swap {f : Filter (α × β
)} : map Prod.swap f = comap Prod.swap f
-/
theorem prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f) := by
  rw [prod_comm', ← map_swap_eq_comap_swap]
/-
**Filter.mem_prod_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_prod_iff_left {s : Set (α × β)} : s in f ×ˢ g ↔ exists t in f, forallᶠ
 y in g, forall x in t, (x, y) in s
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
· 使用定理 `Filter.exists_mem_subset_iff`：exists_mem_subset_iff : (exists t in f, t 
subseteq s) ↔ s in f
-/
theorem mem_prod_iff_left {s : Set (α × β)} :
    s ∈ f ×ˢ g ↔ ∃ t ∈ f, ∀ᶠ y in g, ∀ x ∈ t, (x, y) ∈ s := by
  simp only [mem_prod_iff, prod_subset_iff]
  refine exists_congr fun _ => Iff.rfl.and <| Iff.trans ?_ exists_mem_subset_iff
  exact exists_congr fun _ => Iff.rfl.and forall₂_comm
/-
**Filter.mem_prod_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_prod_iff_right {s : Set (α × β)} : s in f ×ˢ g ↔ exists t in g, forall
ᶠ x in f, forall y in t, (x, y) in s
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_comm`：prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f)
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_prod_iff_left`：mem_prod_iff_left {s : Set (α × β)} : s in f ×
ˢ g ↔ exists t in f, forallᶠ y in g, forall x in t, (x, y) in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod_iff_right {s : Set (α × β)} :
    s ∈ f ×ˢ g ↔ ∃ t ∈ g, ∀ᶠ x in f, ∀ y ∈ t, (x, y) ∈ s := by
  rw [prod_comm, mem_map, mem_prod_iff_left]; rfl

@[simp]
/-
**Filter.map_fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_fst_prod (f : Filter α) (g : Filter β) [NeBot g] : map Prod.fst (f ×ˢ 
g) = f
参数：f : Filter α；g : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_fst_prod (f : Filter α) (g : Filter β) [NeBot g] : map Prod.fst (f ×ˢ g) = f := by
  ext s
  simp only [mem_map, mem_prod_iff_left, mem_preimage, eventually_const, ← subset_def,
    exists_mem_subset_iff]

@[simp]
/-
**Filter.map_snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_snd_prod (f : Filter α) (g : Filter β) [NeBot f] : map Prod.snd (f ×ˢ 
g) = g
参数：f : Filter α；g : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_comm`：prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f)
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.map_fst_prod`：map_fst_prod (f : Filter α) (g : Filter β) [NeBot g
] : map Prod.fst (f ×ˢ g) = f
-/
theorem map_snd_prod (f : Filter α) (g : Filter β) [NeBot f] : map Prod.snd (f ×ˢ g) = g := by
  rw [prod_comm, map_map]; apply map_fst_prod

@[simp]
/-
**Filter.prod_le_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_le_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
 f₁ ×ˢ g₁ <= f₂ ×ˢ g₂ ↔ f₁ <= f₂ ∧ g₁ <= g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.map_fst_prod`：map_fst_prod (f : Filter α) (g : Filter β) [NeBot g
] : map Prod.fst (f ×ˢ g) = f
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `Filter.map_snd_prod`：map_snd_prod (f : Filter α) (g : Filter β) [NeBot f
] : map Prod.snd (f ×ˢ g) = g
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_le_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
    f₁ ×ˢ g₁ ≤ f₂ ×ˢ g₂ ↔ f₁ ≤ f₂ ∧ g₁ ≤ g₂ :=
  ⟨fun h =>
    ⟨map_fst_prod f₁ g₁ ▸ tendsto_fst.mono_left h, map_snd_prod f₁ g₁ ▸ tendsto_snd.mono_left h⟩,
    fun h => prod_mono h.1 h.2⟩

@[simp]
/-
**Filter.prod_inj** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_inj {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] : f₁ 
×ˢ g₁ = f₂ ×ˢ g₂ ↔ f₁ = f₂ ∧ g₁ = g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.prod_le_prod`：prod_le_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} 
[NeBot f₁] [NeBot g₁] : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂ ↔ f₁ <= f₂ ∧ g₁ <= g₂
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.neBot_of_le`：neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f 
<= g) : NeBot g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem prod_inj {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
    f₁ ×ˢ g₁ = f₂ ×ˢ g₂ ↔ f₁ = f₂ ∧ g₁ = g₂ := by
  refine ⟨fun h => ?_, fun h => h.1 ▸ h.2 ▸ rfl⟩
  have hle : f₁ ≤ f₂ ∧ g₁ ≤ g₂ := prod_le_prod.1 h.le
  have := neBot_of_le hle.1; have := neBot_of_le hle.2
  exact ⟨hle.1.antisymm <| (prod_le_prod.1 h.ge).1, hle.2.antisymm <| (prod_le_prod.1 h.ge).2⟩
/-
**Filter.eventually_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_swap_iff {p : α × β -> Prop} : (forallᶠ x : α × β in f ×ˢ g, p 
x) ↔ forallᶠ y : β × α in g ×ˢ f, p y.swap
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_comm`：prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_swap_iff {p : α × β → Prop} :
    (∀ᶠ x : α × β in f ×ˢ g, p x) ↔ ∀ᶠ y : β × α in g ×ˢ f, p y.swap := by
  rw [prod_comm]; rfl

/-- A technical lemma which is a generalization of `Filter.Eventually.trans_prod`. -/
/-
**Filter.Eventually.eventually_prod_of_eventually_swap** 是 Mathlib 中的一个定理，位于命名空间
 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Filter 
β} {h : Filter γ} [g.NeBot] {p : α → β → Prop}   {q : β → γ → Prop} {r : α → γ →
 Prop},   (∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p x y) →     (∀ᶠ (z : γ) in h, ∀ᶠ (
y : β) in g, q y z) →       (∀ (x : α) (y : β) (z : γ), p x y → q y z → r x z) →
 ∀ᶠ (xz : α × γ) in f ×ˢ h, r xz.1 xz.2
参数：∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p x y；∀ᶠ (z : γ) in h, ∀ᶠ (y : β) in g, q y
 z；∀ (x : α) (y : β) (z : γ), p x y → q y z → r x z；xz : α × γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x

--- 原说明 ---
A technical lemma which is a generalization of `Filter.Eventually.trans_prod`.
-/
lemma Eventually.eventually_prod_of_eventually_swap {h : Filter γ}
    [NeBot g] {p : α → β → Prop} {q : β → γ → Prop} {r : α → γ → Prop}
    (hp : ∀ᶠ x in f, ∀ᶠ y in g, p x y) (hq : ∀ᶠ z in h, ∀ᶠ y in g, q y z)
    (hpqr : ∀ x y z, p x y → q y z → r x z) :
    ∀ᶠ xz in f ×ˢ h, r xz.1 xz.2 := by
  refine eventually_prod_iff.mpr ⟨_, hp, _, hq, fun {x} hx {z} hz ↦ ?_⟩
  rcases (hx.and hz).exists with ⟨y, hpy, hqy⟩
  exact hpqr x y z hpy hqy
/-
**Filter.Eventually.trans_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Filter 
β} {h : Filter γ} [g.NeBot] {p : α → β → Prop}   {q : β → γ → Prop} {r : α → γ →
 Prop},   (∀ᶠ (xy : α × β) in f ×ˢ g, p xy.1 xy.2) →     (∀ᶠ (yz : β × γ) in g ×
ˢ h, q yz.1 yz.2) →       (∀ (x : α) (y : β) (z : γ), p x y → q y z → r x z) → ∀
ᶠ (xz : α × γ) in f ×ˢ h, r xz.1 xz.2
参数：∀ᶠ (xy : α × β) in f ×ˢ g, p xy.1 xy.2；∀ᶠ (yz : β × γ) in g ×ˢ h, q yz.1 yz.2
；∀ (x : α) (y : β) (z : γ), p x y → q y z → r x z；xz : α × γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.eventually_prod_of_eventually_swap`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} {f : Filter α} {g : Filter β} {h : Filter γ} [g.NeB
ot] {p : α → β → Prop}   {q : β → γ → Prop…
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_swap_iff`：eventually_swap_iff {p : α × β -> Prop} : (f
orallᶠ x : α × β in f ×ˢ g, p x) ↔ forallᶠ y : β × α in g ×ˢ f, p y.swap
-/
lemma Eventually.trans_prod {h : Filter γ}
    [NeBot g] {p : α → β → Prop} {q : β → γ → Prop} {r : α → γ → Prop}
    (hp : ∀ᶠ xy in f ×ˢ g, p xy.1 xy.2) (hq : ∀ᶠ yz in g ×ˢ h, q yz.1 yz.2)
    (hpqr : ∀ x y z, p x y → q y z → r x z) :
    ∀ᶠ xz in f ×ˢ h, r xz.1 xz.2 :=
  hp.curry.eventually_prod_of_eventually_swap (eventually_swap_iff.mp hq |>.curry) hpqr
/-
**Filter.prod_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_assoc (f : Filter α) (g : Filter β) (h : Filter γ) : map (Equiv.prodA
ssoc α β γ) ((f ×ˢ g) ×ˢ h) = f ×ˢ (g ×ˢ h)
参数：f : Filter α；g : Filter β；h : Filter γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.prodAssoc_symm_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u
_11) (p : α × β × γ), (Equiv.prodAssoc α β γ).symm p = ((p.1, p.2.1), p.2.2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_assoc (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equiv.prodAssoc α β γ) ((f ×ˢ g) ×ˢ h) = f ×ˢ (g ×ˢ h) := by
  simp_rw [← comap_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_symm_apply]
/-
**Filter.prod_assoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_assoc_symm (f : Filter α) (g : Filter β) (h : Filter γ) : map (Equiv.
prodAssoc α β γ).symm (f ×ˢ (g ×ˢ h)) = (f ×ˢ g) ×ˢ h
参数：f : Filter α；g : Filter β；h : Filter γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_equiv_symm`：map_equiv_symm (e : α ≃ β) (f : Filter β) : map e
.symm f = comap e f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.prodAssoc_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u_11) 
(p : (α × β) × γ), (Equiv.prodAssoc α β γ) p = (p.1.1, p.1.2, p.2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_assoc_symm (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equiv.prodAssoc α β γ).symm (f ×ˢ (g ×ˢ h)) = (f ×ˢ g) ×ˢ h := by
  simp_rw [map_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_apply]
/-
**Filter.tendsto_prodAssoc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_prodAssoc {h : Filter γ} : Tendsto (Equiv.prodAssoc α β γ) ((f ×ˢ 
g) ×ˢ h) (f ×ˢ (g ×ˢ h))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.prod_assoc`：prod_assoc (f : Filter α) (g : Filter β) (h : Filter 
γ) : map (Equiv.prodAssoc α β γ) ((f ×ˢ g) ×ˢ h) = f ×ˢ (g ×ˢ h)
-/
theorem tendsto_prodAssoc {h : Filter γ} :
    Tendsto (Equiv.prodAssoc α β γ) ((f ×ˢ g) ×ˢ h) (f ×ˢ (g ×ˢ h)) :=
  (prod_assoc f g h).le
/-
**Filter.tendsto_prodAssoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_prodAssoc_symm {h : Filter γ} : Tendsto (Equiv.prodAssoc α β γ).sy
mm (f ×ˢ (g ×ˢ h)) ((f ×ˢ g) ×ˢ h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Filter.prod_assoc_symm`：prod_assoc_symm (f : Filter α) (g : Filter β) (h
 : Filter γ) : map (Equiv.prodAssoc α β γ).symm (f ×ˢ (g ×ˢ h)) = (f ×ˢ g) ×ˢ h
-/
theorem tendsto_prodAssoc_symm {h : Filter γ} :
    Tendsto (Equiv.prodAssoc α β γ).symm (f ×ˢ (g ×ˢ h)) ((f ×ˢ g) ×ˢ h) :=
  (prod_assoc_symm f g h).le

/-- A useful lemma when dealing with uniformities. -/
/-
**Filter.map_swap4_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_swap4_prod {h : Filter γ} {k : Filter δ} : map (fun p : (α × β) × γ × 
δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h ×ˢ k)) = (f ×ˢ h) ×ˢ (g ×
ˢ k)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_swap4_eq_comap`：map_swap4_eq_comap {f : Filter ((α × β) × γ ×
 δ)} : map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f = com
ap (fun p : (α …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instIdempotentOpMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], S
td.IdempotentOp fun x1 x2 => x1 ⊓ x2

--- 原说明 ---
A useful lemma when dealing with uniformities.
-/
theorem map_swap4_prod {h : Filter γ} {k : Filter δ} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h ×ˢ k)) =
      (f ×ˢ h) ×ˢ (g ×ˢ k) := by
  simp_rw [map_swap4_eq_comap, prod_eq_inf, comap_inf, comap_comap]; ac_rfl
/-
**Filter.tendsto_swap4_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_swap4_prod {h : Filter γ} {k : Filter δ} : Tendsto (fun p : (α × β
) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h ×ˢ k)) ((f ×ˢ h) 
×ˢ (g ×ˢ k))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.map_swap4_prod`：map_swap4_prod {h : Filter γ} {k : Filter δ} : ma
p (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h 
×ˢ k)) = (f…
-/
theorem tendsto_swap4_prod {h : Filter γ} {k : Filter δ} :
    Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h ×ˢ k))
      ((f ×ˢ h) ×ˢ (g ×ˢ k)) :=
  map_swap4_prod.le
/-
**Filter.prod_map_map_eq.** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
    map m₁ f₁ ×ˢ map m₂ f₂ = map (fun p : α₁ × α₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ˢ f₂) :=
  le_antisymm
    (fun s hs =>
      let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs
      mem_of_superset (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) <|
        by rwa [prod_image_image_eq, image_subset_iff])
    ((tendsto_map.comp tendsto_fst).prodMk (tendsto_map.comp tendsto_snd))
/-
**Filter.prod_map_map_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (f : 
α₁ -> α₂) (g : β₁ -> β₂) (F : Filter α₁) (G : Filter β₁) : map f F ×ˢ map g G = 
map (Prod.map f g) (F ×ˢ G)
参数：f : α₁ -> α₂；g : β₁ -> β₂；F : Filter α₁；G : Filter β₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
-/
theorem prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (f : α₁ → α₂)
    (g : β₁ → β₂) (F : Filter α₁) (G : Filter β₁) :
    map f F ×ˢ map g G = map (Prod.map f g) (F ×ˢ G) :=
  prod_map_map_eq
/-
**Filter.prod_map_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_map_left (f : α -> β) (F : Filter α) (G : Filter γ) : map f F ×ˢ G = 
map (Prod.map f id) (F ×ˢ G)
参数：f : α -> β；F : Filter α；G : Filter γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_map_map_eq'`：prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ 
: Type*} {β₂ : Type*} (f : α₁ -> α₂) (g : β₁ -> β₂) (F : Filter α₁) (G : Filter 
β₁) : map f F…
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
-/
theorem prod_map_left (f : α → β) (F : Filter α) (G : Filter γ) :
    map f F ×ˢ G = map (Prod.map f id) (F ×ˢ G) := by
  rw [← prod_map_map_eq', map_id]
/-
**Filter.prod_map_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_map_right (f : β -> γ) (F : Filter α) (G : Filter β) : F ×ˢ map f G =
 map (Prod.map id f) (F ×ˢ G)
参数：f : β -> γ；F : Filter α；G : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_map_map_eq'`：prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ 
: Type*} {β₂ : Type*} (f : α₁ -> α₂) (g : β₁ -> β₂) (F : Filter α₁) (G : Filter 
β₁) : map f F…
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
-/
theorem prod_map_right (f : β → γ) (F : Filter α) (G : Filter β) :
    F ×ˢ map f G = map (Prod.map id f) (F ×ˢ G) := by
  rw [← prod_map_map_eq', map_id]
/-
**Filter.le_prod_map_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_prod_map_fst_snd {f : Filter (α × β)} : f <= map Prod.fst f ×ˢ map Prod
.snd f
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Filter.le_comap_map`：le_comap_map : f <= comap m (map m f)
-/
theorem le_prod_map_fst_snd {f : Filter (α × β)} : f ≤ map Prod.fst f ×ˢ map Prod.snd f :=
  le_inf le_comap_map le_comap_map
/-
**Filter.Tendsto.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_6} {f : α → γ} 
{g : β → δ} {a : Filter α} {b : Filter β}   {c : Filter γ} {d : Filter δ},   Fil
ter.Tendsto f a c → Filter.Tendsto g b d → Filter.Tendsto (Prod.map f g) (a ×ˢ b
) (c ×ˢ d)
参数：Prod.map f g；a ×ˢ b；c ×ˢ d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Prod.map_def`：map_def {f : α -> γ} {g : β -> δ} : Prod.map f g = fun p :
 α × β => (f p.1, g p.2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
-/
theorem Tendsto.prodMap {δ : Type*} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}
    {c : Filter γ} {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) :
    Tendsto (Prod.map f g) (a ×ˢ b) (c ×ˢ d) := by
  rw [Tendsto, Prod.map_def, ← prod_map_map_eq]
  exact Filter.prod_mono hf hg
/-
**Filter.map_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (m : α × β → γ) (f : Filter
 α) (g : Filter β),   Filter.map m (f ×ˢ g) = (Filter.map (fun a b => m (a, b)) 
f).seq g
参数：m : α × β → γ；f : Filter α；g : Filter β；f ×ˢ g；Filter.map (fun a b => m (a, b
)) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem map_prod (m : α × β → γ) (f : Filter α) (g : Filter β) :
    map m (f ×ˢ g) = (f.map fun a b => m (a, b)).seq g := by
  simp only [Filter.ext_iff, mem_map, mem_prod_iff, mem_map_seq_iff, exists_and_left]
  intro s
  constructor
  · exact fun ⟨t, ht, s, hs, h⟩ => ⟨s, hs, t, ht, fun x hx y hy => @h ⟨x, y⟩ ⟨hx, hy⟩⟩
  · exact fun ⟨s, hs, t, ht, h⟩ => ⟨t, ht, s, hs, fun ⟨x, y⟩ ⟨hx, hy⟩ => h x hx y hy⟩
/-
**Filter.prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_eq : f ×ˢ g = (f.map Prod.mk).seq g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (m : α ×
 β → γ) (f : Filter α) (g : Filter β),   Filter.map m (f ×ˢ g) = (Filter.map (fu
n a b…
-/
theorem prod_eq : f ×ˢ g = (f.map Prod.mk).seq g := f.map_prod id g
/-
**Filter.prod_inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} : (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ 
g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_left_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓
 (b ⊓ c) = b ⊓ (a ⊓ c)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} :
    (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂) := by
  simp only [prod_eq_inf, comap_inf, inf_comm, inf_assoc, inf_left_comm]
/-
**Filter.inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_prod {f₁ f₂ : Filter α} : (f₁ ⊓ f₂) ×ˢ g = (f₁ ×ˢ g) ⊓ (f₂ ×ˢ g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_inf_prod`：prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β
} : (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂)
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
theorem inf_prod {f₁ f₂ : Filter α} : (f₁ ⊓ f₂) ×ˢ g = (f₁ ×ˢ g) ⊓ (f₂ ×ˢ g) := by
  rw [prod_inf_prod, inf_idem]
/-
**Filter.prod_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_inf {g₁ g₂ : Filter β} : f ×ˢ (g₁ ⊓ g₂) = (f ×ˢ g₁) ⊓ (f ×ˢ g₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_inf_prod`：prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β
} : (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂)
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
theorem prod_inf {g₁ g₂ : Filter β} : f ×ˢ (g₁ ⊓ g₂) = (f ×ˢ g₁) ⊓ (f ×ˢ g₂) := by
  rw [prod_inf_prod, inf_idem]

@[simp]
/-
**Filter.prod_principal_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_principal_principal {s : Set α} {t : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
-/
theorem prod_principal_principal {s : Set α} {t : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t) := by
  simp only [prod_eq_inf, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal]; rfl

@[simp]
/-
**Filter.pure_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (Prod.mk a) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_eq`：prod_eq : f ×ˢ g = (f.map Prod.mk).seq g
· 使用定理 `Filter.map_pure`：map_pure (f : α -> β) (a : α) : map f (pure a) = pure (
f a)
· 使用定理 `Filter.pure_seq_eq_map`：pure_seq_eq_map (g : α -> β) (f : Filter α) : se
q (pure g) f = f.map g
-/
theorem pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (Prod.mk a) f := by
  rw [prod_eq, map_pure, pure_seq_eq_map]
/-
**Filter.map_pure_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_pure_prod (f : α -> β -> γ) (a : α) (B : Filter β) : map (Function.unc
urry f) (pure a ×ˢ B) = map (f a) B
参数：f : α -> β -> γ；a : α；B : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.pure_prod`：pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (
Prod.mk a) f
-/
theorem map_pure_prod (f : α → β → γ) (a : α) (B : Filter β) :
    map (Function.uncurry f) (pure a ×ˢ B) = map (f a) B := by
  rw [Filter.pure_prod]; rfl

@[simp]
/-
**Filter.prod_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_eq`：prod_eq : f ×ˢ g = (f.map Prod.mk).seq g
· 使用定理 `Filter.seq_pure`：seq_pure (f : Filter (α -> β)) (a : α) : seq f (pure a)
 = map (fun g : α -> β => g a) f
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
-/
theorem prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)) f := by
  rw [prod_eq, seq_pure, map_map]; rfl
/-
**Filter.prod_pure_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_pure_pure {a : α} {b : β} : (pure a : Filter α) ×ˢ (pure b : Filter β
) = pure (a, b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_pure_pure {a : α} {b : β} :
    (pure a : Filter α) ×ˢ (pure b : Filter β) = pure (a, b) := by simp

@[simp]
/-
**Filter.prod_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_eq_bot : f ×ˢ g = ⊥ ↔ f = ⊥ ∨ g = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_bot : f ×ˢ g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := by
  simp_rw [← empty_mem_iff_bot, mem_prod_iff, subset_empty_iff, prod_eq_empty_iff, ← exists_prop,
    Subtype.exists', exists_or, exists_const, Subtype.exists, exists_prop, exists_eq_right]
/-
**Filter.prod_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f ×ˢ ⊥ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.prod_eq_bot`：prod_eq_bot : f ×ˢ g = ⊥ ↔ f = ⊥ ∨ g = ⊥
-/
@[simp] theorem prod_bot : f ×ˢ (⊥ : Filter β) = ⊥ := prod_eq_bot.2 <| Or.inr rfl
/-
**Filter.bot_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {g : Filter β}, ⊥ ×ˢ g = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.prod_eq_bot`：prod_eq_bot : f ×ˢ g = ⊥ ↔ f = ⊥ ∨ g = ⊥
-/
@[simp] theorem bot_prod : (⊥ : Filter α) ×ˢ g = ⊥ := prod_eq_bot.2 <| Or.inl rfl
/-
**Filter.prod_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_neBot : NeBot (f ×ˢ g) ↔ NeBot f ∧ NeBot g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_neBot : NeBot (f ×ˢ g) ↔ NeBot f ∧ NeBot g := by
  simp only [neBot_iff, Ne, prod_eq_bot, not_or]
/-
**Filter.NeBot.prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : Filter β}, f.NeBot → g
.NeBot → (f ×ˢ g).NeBot
参数：f ×ˢ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.prod_neBot`：prod_neBot : NeBot (f ×ˢ g) ↔ NeBot f ∧ NeBot g
-/
protected theorem NeBot.prod (hf : NeBot f) (hg : NeBot g) : NeBot (f ×ˢ g) := prod_neBot.2 ⟨hf, hg⟩
/-
**Filter.prod.instNeBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : Filter β} [hf : f.NeBo
t] [hg : g.NeBot], (f ×ˢ g).NeBot
参数：f ×ˢ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.prod`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : F
ilter β}, f.NeBot → g.NeBot → (f ×ˢ g).NeBot
-/
instance prod.instNeBot [hf : NeBot f] [hg : NeBot g] : NeBot (f ×ˢ g) := hf.prod hg

@[simp]
/-
**Filter.disjoint_prod** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：disjoint_prod {f' : Filter α} {g' : Filter β} : Disjoint (f ×ˢ g) (f' ×ˢ g
') ↔ Disjoint f f' ∨ Disjoint g g'
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
· 使用定理 `Filter.prod_inf_prod`：prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β
} : (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma disjoint_prod {f' : Filter α} {g' : Filter β} :
    Disjoint (f ×ˢ g) (f' ×ˢ g') ↔ Disjoint f f' ∨ Disjoint g g' := by
  simp only [disjoint_iff, prod_inf_prod, prod_eq_bot]

/-- `p ∧ q` occurs frequently along the product of two filters
iff both `p` and `q` occur frequently along the corresponding filters. -/
/-
**Filter.frequently_prod_and** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_prod_and {p : α -> Prop} {q : β -> Prop} : (existsᶠ x in f ×ˢ g
, p x.1 ∧ q x.2) ↔ (existsᶠ a in f, p a) ∧ existsᶠ b in g, q b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`p ∧ q` occurs frequently along the product of two filters
iff both `p` and `q` occur frequently along the corresponding filters.
-/
theorem frequently_prod_and {p : α → Prop} {q : β → Prop} :
    (∃ᶠ x in f ×ˢ g, p x.1 ∧ q x.2) ↔ (∃ᶠ a in f, p a) ∧ ∃ᶠ b in g, q b := by
  simp only [frequently_iff_neBot, ← prod_neBot, ← prod_inf_prod, prod_principal_principal]
  rfl
/-
**Filter.tendsto_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_prod_iff {f : α × β -> γ} {x : Filter α} {y : Filter β} {z : Filte
r γ} : Tendsto f (x ×ˢ y) z ↔ forall W in z, exists U in x, exists V in y, foral
l x y, x in U -> y in V -> f (x, y) in W
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_prod_iff {f : α × β → γ} {x : Filter α} {y : Filter β} {z : Filter γ} :
    Tendsto f (x ×ˢ y) z ↔ ∀ W ∈ z, ∃ U ∈ x, ∃ V ∈ y, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W := by
  simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff]
/-
**Filter.tendsto_prod_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_prod_iff' {g' : Filter γ} {s : α -> β × γ} : Tendsto s f (g ×ˢ g')
 ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n => (s n).2) f g'
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_prod_iff' {g' : Filter γ} {s : α → β × γ} :
    Tendsto s f (g ×ˢ g') ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n => (s n).2) f g' := by
  simp only [prod_eq_inf, tendsto_inf, tendsto_comap_iff, Function.comp_def]
/-
**Filter.le_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_prod {f : Filter (α × β)} {g : Filter α} {g' : Filter β} : (f <= g ×ˢ g
') ↔ Tendsto Prod.fst f g ∧ Tendsto Prod.snd f g'
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_prod_iff'`：tendsto_prod_iff' {g' : Filter γ} {s : α -> β 
× γ} : Tendsto s f (g ×ˢ g') ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n =
> (s n).2) f g…
-/
theorem le_prod {f : Filter (α × β)} {g : Filter α} {g' : Filter β} :
    (f ≤ g ×ˢ g') ↔ Tendsto Prod.fst f g ∧ Tendsto Prod.snd f g' :=
  tendsto_prod_iff'

end Prod

/-! ### Coproducts of filters -/

section Coprod

variable {f : Filter α} {g : Filter β}

/-
**Filter.coprod_eq_prod_top_sup_top_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：coprod_eq_prod_top_sup_top_prod (f : Filter α) (g : Filter β) : Filter.cop
rod f g = f ×ˢ ⊤ ⊔ ⊤ ×ˢ g
参数：f : Filter α；g : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_top`：prod_top : f ×ˢ (⊤ : Filter β) = f.comap Prod.fst
· 使用定理 `Filter.top_prod`：top_prod : (⊤ : Filter α) ×ˢ g = g.comap Prod.snd
-/
theorem coprod_eq_prod_top_sup_top_prod (f : Filter α) (g : Filter β) :
    Filter.coprod f g = f ×ˢ ⊤ ⊔ ⊤ ×ˢ g := by
  rw [prod_top, top_prod]
  rfl
/-
**Filter.mem_coprod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_coprod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} : s in f.co
prod g ↔ (exists t₁ in f, Prod.fst ⁻¹' t₁ subseteq s) ∧ exists t₂ in g, Prod.snd
 ⁻¹' t₂ subseteq s
参数：α × β。
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
theorem mem_coprod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f.coprod g ↔ (∃ t₁ ∈ f, Prod.fst ⁻¹' t₁ ⊆ s) ∧ ∃ t₂ ∈ g, Prod.snd ⁻¹' t₂ ⊆ s := by
  simp [Filter.coprod]

@[simp]
/-
**Filter.bot_coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bot_coprod (l : Filter β) : (⊥ : Filter α).coprod l = comap Prod.snd l
参数：l : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_bot`：comap_bot : comap m ⊥ = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bot_coprod (l : Filter β) : (⊥ : Filter α).coprod l = comap Prod.snd l := by
  simp [Filter.coprod]

@[simp]
/-
**Filter.coprod_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：coprod_bot (l : Filter α) : l.coprod (⊥ : Filter β) = comap Prod.fst l
参数：l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_bot`：comap_bot : comap m ⊥ = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod_bot (l : Filter α) : l.coprod (⊥ : Filter β) = comap Prod.fst l := by
  simp [Filter.coprod]
/-
**Filter.bot_coprod_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bot_coprod_bot : (⊥ : Filter α).coprod (⊥ : Filter β) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.coprod_bot`：coprod_bot (l : Filter α) : l.coprod (⊥ : Filter β) =
 comap Prod.fst l
· 使用定理 `Filter.comap_bot`：comap_bot : comap m ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bot_coprod_bot : (⊥ : Filter α).coprod (⊥ : Filter β) = ⊥ := by simp
/-
**Filter.compl_mem_coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_mem_coprod {s : Set (α × β)} {la : Filter α} {lb : Filter β} : sᶜ in
 la.coprod lb ↔ (Prod.fst '' s)ᶜ in la ∧ (Prod.snd '' s)ᶜ in lb
参数：α × β。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_mem_coprod {s : Set (α × β)} {la : Filter α} {lb : Filter β} :
    sᶜ ∈ la.coprod lb ↔ (Prod.fst '' s)ᶜ ∈ la ∧ (Prod.snd '' s)ᶜ ∈ lb := by
  simp only [Filter.coprod, mem_sup, compl_mem_comap]

@[gcongr, mono]
/-
**Filter.coprod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：coprod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ <= f₂) (hg : g₁
 <= g₂) : f₁.coprod g₁ <= f₂.coprod g₂
参数：hf : f₁ <= f₂；hg : g₁ <= g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
-/
theorem coprod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁.coprod g₁ ≤ f₂.coprod g₂ :=
  sup_le_sup (comap_mono hf) (comap_mono hg)
/-
**Filter.coprod_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：coprod_neBot_iff : (f.coprod g).NeBot ↔ f.NeBot ∧ Nonempty β ∨ Nonempty α 
∧ g.NeBot
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coprod_neBot_iff : (f.coprod g).NeBot ↔ f.NeBot ∧ Nonempty β ∨ Nonempty α ∧ g.NeBot := by
  simp [Filter.coprod]

@[instance]
/-
**Filter.coprod_neBot_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：coprod_neBot_left [NeBot f] [Nonempty β] : (f.coprod g).NeBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.coprod_neBot_iff`：coprod_neBot_iff : (f.coprod g).NeBot ↔ f.NeBot
 ∧ Nonempty β ∨ Nonempty α ∧ g.NeBot
-/
theorem coprod_neBot_left [NeBot f] [Nonempty β] : (f.coprod g).NeBot :=
  coprod_neBot_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

@[instance]
/-
**Filter.coprod_neBot_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：coprod_neBot_right [NeBot g] [Nonempty α] : (f.coprod g).NeBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.coprod_neBot_iff`：coprod_neBot_iff : (f.coprod g).NeBot ↔ f.NeBot
 ∧ Nonempty β ∨ Nonempty α ∧ g.NeBot
-/
theorem coprod_neBot_right [NeBot g] [Nonempty α] : (f.coprod g).NeBot :=
  coprod_neBot_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**Filter.coprod_inf_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：coprod_inf_prod_le (f₁ f₂ : Filter α) (g₁ g₂ : Filter β) : f₁.coprod g₁ ⊓ 
f₂ ×ˢ g₂ <= f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁
参数：f₁ f₂ : Filter α；g₁ g₂ : Filter β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.coprod_eq_prod_top_sup_top_prod`：coprod_eq_prod_top_sup_top_prod 
(f : Filter α) (g : Filter β) : Filter.coprod f g = f ×ˢ ⊤ ⊔ ⊤ ×ˢ g
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.prod_inf_prod`：prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β
} : (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂)
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coprod_inf_prod_le (f₁ f₂ : Filter α) (g₁ g₂ : Filter β) :
    f₁.coprod g₁ ⊓ f₂ ×ˢ g₂ ≤ f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁ := calc
  f₁.coprod g₁ ⊓ f₂ ×ˢ g₂
  _ = (f₁ ×ˢ ⊤ ⊔ ⊤ ×ˢ g₁) ⊓ f₂ ×ˢ g₂            := by rw [coprod_eq_prod_top_sup_top_prod]
  _ = f₁ ×ˢ ⊤ ⊓ f₂ ×ˢ g₂ ⊔ ⊤ ×ˢ g₁ ⊓ f₂ ×ˢ g₂   := inf_sup_right _ _ _
  _ = (f₁ ⊓ f₂) ×ˢ g₂ ⊔ f₂ ×ˢ (g₁ ⊓ g₂)         := by simp [prod_inf_prod]
  _ ≤ f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁                       :=
    sup_le_sup (prod_mono inf_le_left le_rfl) (prod_mono le_rfl inf_le_left)
/-
**Filter.principal_coprod_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：principal_coprod_principal (s : Set α) (t : Set β) : (𝓟 s).coprod (𝓟 t) = 
𝓟 (sᶜ ×ˢ tᶜ)ᶜ
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.coprod.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : Filter α) (g : 
Filter β),   f.coprod g = Filter.comap Prod.fst f ⊔ Filter.comap Prod.snd g
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.sup_principal`：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s uni
on t)
· 使用定理 `Set.prod_eq`：prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s i
nter Prod.snd ⁻¹' t
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem principal_coprod_principal (s : Set α) (t : Set β) :
    (𝓟 s).coprod (𝓟 t) = 𝓟 (sᶜ ×ˢ tᶜ)ᶜ := by
  rw [Filter.coprod, comap_principal, comap_principal, sup_principal, Set.prod_eq, compl_inter,
    preimage_compl, preimage_compl, compl_compl, compl_compl]

-- this inequality can be strict; see `map_const_principal_coprod_map_id_principal` and
-- `map_prodMap_const_id_principal_coprod_principal` below.
/-
**Filter.map_prodMap_coprod_le.** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_prodMap_coprod_le.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
    map (Prod.map m₁ m₂) (f₁.coprod f₂) ≤ (map m₁ f₁).coprod (map m₂ f₂) := by
  intro s
  simp only [mem_map, mem_coprod_iff]
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩
  refine ⟨⟨m₁ ⁻¹' u₁, hu₁, fun _ hx => h₁ ?_⟩, ⟨m₂ ⁻¹' u₂, hu₂, fun _ hx => h₂ ?_⟩⟩ <;> convert!
    hx

/-- Characterization of the coproduct of the `Filter.map`s of two principal filters `𝓟 {a}` and
`𝓟 {i}`, the first under the constant function `fun a => b` and the second under the identity
function. Together with the next lemma, `map_prodMap_const_id_principal_coprod_principal`, this
provides an example showing that the inequality in the lemma `map_prodMap_coprod_le` can be strict.
-/
/-
**Filter.map_const_principal_coprod_map_id_principal** 是 Mathlib 中的一个定理，位于命名空间 `
Filter`。
形式化陈述：map_const_principal_coprod_map_id_principal {α β ι : Type*} (a : α) (b : β
) (i : ι) : (map (fun _ => b) (𝓟 {a})).coprod (map id (𝓟 {i})) = 𝓟 ((({b} : Set 
β) ×ˢ univ) union (univ ×ˢ ({i} : Set ι)))
参数：a : α；b : β；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Filter.sup_principal`：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s uni
on t)
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Characterization of the coproduct of the `Filter.map`s of two principal filters 
`𝓟 {a}` and
`𝓟 {i}`, the first under the constant function `fun a => b` and the second under
 the identity
function. Together with the next lemma, `map_prodMap_const_id_principal_coprod_p
rincipal`, this
provides an example showing that the inequality in the lemma `map_prodMap_coprod
_le` can be strict.
-/
theorem map_const_principal_coprod_map_id_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
    (map (fun _ => b) (𝓟 {a})).coprod (map id (𝓟 {i})) =
      𝓟 ((({b} : Set β) ×ˢ univ) ∪ (univ ×ˢ ({i} : Set ι))) := by
  simp only [map_principal, Filter.coprod, comap_principal, sup_principal, image_singleton,
    prod_univ, univ_prod, id]

/-- Characterization of the `Filter.map` of the coproduct of two principal filters `𝓟 {a}` and
`𝓟 {i}`, under the `Prod.map` of two functions, respectively the constant function `fun a => b` and
the identity function.  Together with the previous lemma,
`map_const_principal_coprod_map_id_principal`, this provides an example showing that the inequality
in the lemma `map_prodMap_coprod_le` can be strict. -/
/-
**Filter.map_prodMap_const_id_principal_coprod_principal** 是 Mathlib 中的一个定理，位于命名
空间 `Filter`。
形式化陈述：map_prodMap_const_id_principal_coprod_principal {α β ι : Type*} (a : α) (b
 : β) (i : ι) : map (Prod.map (fun _ : α => b) id) ((𝓟 {a}).coprod (𝓟 {i})) = 𝓟 
(({b} : Set β) ×ˢ (univ : Set ι))
参数：a : α；b : β；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_coprod_principal`：principal_coprod_principal (s : Set α
) (t : Set β) : (𝓟 s).coprod (𝓟 t) = 𝓟 (sᶜ ×ˢ tᶜ)ᶜ
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
Characterization of the `Filter.map` of the coproduct of two principal filters `
𝓟 {a}` and
`𝓟 {i}`, under the `Prod.map` of two functions, respectively the constant functi
on `fun a => b` and
the identity function.  Together with the previous lemma,
`map_const_principal_coprod_map_id_principal`, this provides an example showing 
that the inequality
in the lemma `map_prodMap_coprod_le` can be strict.
-/
theorem map_prodMap_const_id_principal_coprod_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
    map (Prod.map (fun _ : α => b) id) ((𝓟 {a}).coprod (𝓟 {i})) =
      𝓟 (({b} : Set β) ×ˢ (univ : Set ι)) := by
  rw [principal_coprod_principal, map_principal]
  congr
  ext ⟨b', i'⟩
  constructor
  · rintro ⟨⟨a'', i''⟩, _, h₂, h₃⟩
    simp
  · rintro ⟨h₁, _⟩
    use (a, i')
    simpa using h₁.symm
/-
**Filter.Tendsto.prodMap_coprod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_6} {f : α → γ} 
{g : β → δ} {a : Filter α} {b : Filter β}   {c : Filter γ} {d : Filter δ},   Fil
ter.Tendsto f a c → Filter.Tendsto g b d → Filter.Tendsto (Prod.map f g) (a.copr
od b) (c.coprod d)
参数：Prod.map f g；a.coprod b；c.coprod d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.map_prodMap_coprod_le`：map_prodMap_coprod_le.{u, v, w, x} {α₁ : T
ype u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α
₂} {m₁ : α₁ -> β₁}…
· 使用定理 `Filter.coprod_mono`：coprod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (h
f : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.coprod g₁ <= f₂.coprod g₂
-/
theorem Tendsto.prodMap_coprod {δ : Type*} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}
    {c : Filter γ} {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) :
    Tendsto (Prod.map f g) (a.coprod b) (c.coprod d) :=
  map_prodMap_coprod_le.trans (coprod_mono hf hg)
/-
**Filter.Tendsto.coprod_of_prod_top_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tend
sto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α × β → γ} {la : Filte
r α} {lb : Filter β} {lc : Filter γ},   (∀ s ∈ la, Filter.Tendsto f (Filter.prin
cipal sᶜ ×ˢ lb) lc) →     Filter.Tendsto f (la ×ˢ ⊤) lc → Filter.Tendsto f (la.c
oprod lb) lc
参数：∀ s ∈ la, Filter.Tendsto f (Filter.principal sᶜ ×ˢ lb) lc；la ×ˢ ⊤；la.coprod l
b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.coprod_eq_prod_top_sup_top_prod`：coprod_eq_prod_top_sup_top_prod 
(f : Filter α) (g : Filter β) : Filter.coprod f g = f ×ˢ ⊤ ⊔ ⊤ ×ˢ g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma Tendsto.coprod_of_prod_top_right {f : α × β → γ} {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (h₁ : ∀ s : Set α, s ∈ la → Tendsto f (𝓟 sᶜ ×ˢ lb) lc)
    (h₂ : Tendsto f (la ×ˢ ⊤) lc) :
    Tendsto f (la.coprod lb) lc := by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind
/-
**Filter.Tendsto.coprod_of_prod_top_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tends
to`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α × β → γ} {la : Filte
r α} {lb : Filter β} {lc : Filter γ},   (∀ s ∈ lb, Filter.Tendsto f (la ×ˢ Filte
r.principal sᶜ) lc) →     Filter.Tendsto f (⊤ ×ˢ lb) lc → Filter.Tendsto f (la.c
oprod lb) lc
参数：∀ s ∈ lb, Filter.Tendsto f (la ×ˢ Filter.principal sᶜ) lc；⊤ ×ˢ lb；la.coprod l
b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.coprod_eq_prod_top_sup_top_prod`：coprod_eq_prod_top_sup_top_prod 
(f : Filter α) (g : Filter β) : Filter.coprod f g = f ×ˢ ⊤ ⊔ ⊤ ×ˢ g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma Tendsto.coprod_of_prod_top_left {f : α × β → γ} {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (h₁ : ∀ s : Set β, s ∈ lb → Tendsto f (la ×ˢ 𝓟 sᶜ) lc)
    (h₂ : Tendsto f (⊤ ×ˢ lb) lc) :
    Tendsto f (la.coprod lb) lc := by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

end Coprod

end Filter

