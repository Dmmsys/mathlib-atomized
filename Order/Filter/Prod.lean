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
s ∈ F ↔ ∃ n, [n..∞] × univ ⊆ s
s ∈ G ↔ ∀ i:ℕ, ∃ n, [n..∞] × {i} ⊆ s
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

/--
theorem `prod_mem_prod` / 定理 `prod_mem_prod`

English:
theorem prod_mem_prod
  given: (hs : s in f) (ht : t in g)
  statement: s ×ˢ t in f ×ˢ g
  proof: inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)

中文:
定理 prod_mem_prod
  条件: (hs : s in f) (ht : t in g)
  结论: s ×ˢ t in f ×ˢ g
  证明: inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)

Depends on / 依赖: inter_mem_inf, preimage_mem_comap
-/
theorem prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t in f ×ˢ g :=
  inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)

/--
theorem `mem_prod_iff` / 定理 `mem_prod_iff`

English:
theorem mem_prod_iff
  given: {s : Set (α × β)} {f : Filter α} {g : Filter β}
  proof: by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h

@[simp]

中文:
定理 mem_prod_iff
  条件: {s : Set (α × β)} {f : Filter α} {g : Filter β}
  证明: by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h

@[simp]

Depends on / 依赖: mem_inf_of_inter, preimage_mem_comap
-/
theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s := by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h

@[simp]
/--
theorem `compl_diagonal_mem_prod` / 定理 `compl_diagonal_mem_prod`

English:
theorem compl_diagonal_mem_prod
  given: {l₁ l₂ : Filter α}
  statement: (diagonal α)ᶜ in l₁ ×ˢ l₂ ↔ Disjoint l₁ l₂
  proof: by
  simp only [mem_prod_iff, Filter.disjoint_iff, prod_subset_compl_diagonal_iff_disjoint]

@[simp]

中文:
定理 compl_diagonal_mem_prod
  条件: {l₁ l₂ : Filter α}
  结论: (diagonal α)ᶜ in l₁ ×ˢ l₂ ↔ Disjoint l₁ l₂
  证明: by
  simp only [mem_prod_iff, Filter.disjoint_iff, prod_subset_compl_diagonal_iff_disjoint]

@[simp]

Depends on / 依赖: Filter, Filter.disjoint_iff, disjoint_iff, mem_prod_iff, prod_subset_compl_diagonal_iff_disjoint
-/
theorem compl_diagonal_mem_prod {l₁ l₂ : Filter α} : (diagonal α)ᶜ in l₁ ×ˢ l₂ ↔ Disjoint l₁ l₂ := by
  simp only [mem_prod_iff, Filter.disjoint_iff, prod_subset_compl_diagonal_iff_disjoint]

@[simp]
/--
theorem `prod_mem_prod_iff` / 定理 `prod_mem_prod_iff`

English:
theorem prod_mem_prod_iff
  given: [f.NeBot] [g.NeBot]
  statement: s ×ˢ t in f ×ˢ g ↔ s in f ∧ t in g
  proof: ⟨fun h =>
    let ⟨_s', hs', _t', ht', H⟩ := mem_prod_iff.1 h
    (prod_subset_prod_iff.1 H).elim
      (fun ⟨hs's, ht't⟩ => ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩) fun h =>
      h.elim (fun hs'e => absurd hs'e (nonempty_of_mem hs').ne_empty) fun ht'e =>
        absurd ht'e (nonempty_

中文:
定理 prod_mem_prod_iff
  条件: [f.NeBot] [g.NeBot]
  结论: s ×ˢ t in f ×ˢ g ↔ s in f ∧ t in g
  证明: ⟨fun h =>
    let ⟨_s', hs', _t', ht', H⟩ := mem_prod_iff.1 h
    (prod_subset_prod_iff.1 H).elim
      (fun ⟨hs's, ht't⟩ => ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩) fun h =>
      h.elim (fun hs'e => absurd hs'e (nonempty_of_mem hs').ne_empty) fun ht'e =>
        absurd ht'e (nonempty_

Depends on / 依赖: absurd, h.elim, mem_of_superset, mem_prod_iff, ne_empty, nonempty_of_mem, prod_mem_prod, prod_subset_prod_iff
-/
theorem prod_mem_prod_iff [f.NeBot] [g.NeBot] : s ×ˢ t in f ×ˢ g ↔ s in f ∧ t in g :=
  ⟨fun h =>
    let ⟨_s', hs', _t', ht', H⟩ := mem_prod_iff.1 h
    (prod_subset_prod_iff.1 H).elim
      (fun ⟨hs's, ht't⟩ => ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩) fun h =>
      h.elim (fun hs'e => absurd hs'e (nonempty_of_mem hs').ne_empty) fun ht'e =>
        absurd ht'e (nonempty_of_mem ht').ne_empty,
    fun h => prod_mem_prod h.1 h.2⟩

/--
theorem `mem_prod_principal` / 定理 `mem_prod_principal`

English:
theorem mem_prod_principal
  given: {s : Set (α × β)}
  proof: by
  rw [← @exists_mem_subset_iff _ f]; rw [mem_prod_iff]
  refine exists_congr fun u => Iff.rfl.and ⟨?_, fun h => ⟨t, mem_principal_self t, ?_⟩⟩
  · rintro ⟨v, v_in, hv⟩ a a_in b b_in
    exact hv (mk_mem_prod a_in <| v_in b_in)
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h hx y hy

中文:
定理 mem_prod_principal
  条件: {s : Set (α × β)}
  证明: by
  rw [← @exists_mem_subset_iff _ f]; rw [mem_prod_iff]
  refine exists_congr fun u => Iff.rfl.and ⟨?_, fun h => ⟨t, mem_principal_self t, ?_⟩⟩
  · rintro ⟨v, v_in, hv⟩ a a_in b b_in
    exact hv (mk_mem_prod a_in <| v_in b_in)
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h hx y hy

Depends on / 依赖: Iff.rfl.and, a_in, b_in, exists_congr, exists_mem_subset_iff, mem_principal_self, mem_prod_iff, mk_mem_prod, v_in
-/
theorem mem_prod_principal {s : Set (α × β)} :
    s in f ×ˢ 𝓟 t ↔ { a | forall b in t, (a, b) in s } in f := by
  rw [← @exists_mem_subset_iff _ f]; rw [mem_prod_iff]
  refine exists_congr fun u => Iff.rfl.and ⟨?_, fun h => ⟨t, mem_principal_self t, ?_⟩⟩
  · rintro ⟨v, v_in, hv⟩ a a_in b b_in
    exact hv (mk_mem_prod a_in <| v_in b_in)
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h hx y hy

/--
theorem `mem_prod_top` / 定理 `mem_prod_top`

English:
theorem mem_prod_top
  given: {s : Set (α × β)}
  proof: by
  rw [← principal_univ]; rw [mem_prod_principal]
  simp only [mem_univ, forall_true_left]

中文:
定理 mem_prod_top
  条件: {s : Set (α × β)}
  证明: by
  rw [← principal_univ]; rw [mem_prod_principal]
  simp only [mem_univ, forall_true_left]

Depends on / 依赖: forall_true_left, mem_prod_principal, mem_univ, principal_univ
-/
theorem mem_prod_top {s : Set (α × β)} :
    s in f ×ˢ (⊤ : Filter β) ↔ { a | forall b, (a, b) in s } in f := by
  rw [← principal_univ]; rw [mem_prod_principal]
  simp only [mem_univ, forall_true_left]

/--
theorem `eventually_prod_principal_iff` / 定理 `eventually_prod_principal_iff`

English:
theorem eventually_prod_principal_iff
  given: {p : α × β -> Prop} {s : Set β}
  proof: by
  rw [eventually_iff]; rw [eventually_iff]; rw [mem_prod_principal]
  simp only [mem_ofPred_eq]

中文:
定理 eventually_prod_principal_iff
  条件: {p : α × β -> 命题} {s : Set β}
  证明: by
  rw [eventually_iff]; rw [eventually_iff]; rw [mem_prod_principal]
  simp only [mem_ofPred_eq]

Depends on / 依赖: eventually_iff, mem_ofPred_eq, mem_prod_principal
-/
theorem eventually_prod_principal_iff {p : α × β -> Prop} {s : Set β} :
    (forallᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ forallᶠ x : α in f, forall y : β, y in s -> p (x, y) := by
  rw [eventually_iff]; rw [eventually_iff]; rw [mem_prod_principal]
  simp only [mem_ofPred_eq]

/--
theorem `comap_prod` / 定理 `comap_prod`

English:
theorem comap_prod
  given: (f : α -> β × γ) (b : Filter β) (c : Filter γ)
  proof: by
  rw [prod_eq_inf]; rw [comap_inf]; rw [Filter.comap_comap]; rw [Filter.comap_comap]

中文:
定理 comap_prod
  条件: (f : α -> β × γ) (b : Filter β) (c : Filter γ)
  证明: by
  rw [prod_eq_inf]; rw [comap_inf]; rw [Filter.comap_comap]; rw [Filter.comap_comap]

Depends on / 依赖: Filter, Filter.comap_comap, comap_comap, comap_inf, prod_eq_inf
-/
theorem comap_prod (f : α -> β × γ) (b : Filter β) (c : Filter γ) :
    comap f (b ×ˢ c) = comap (Prod.fst ∘ f) b ⊓ comap (Prod.snd ∘ f) c := by
  rw [prod_eq_inf]; rw [comap_inf]; rw [Filter.comap_comap]; rw [Filter.comap_comap]

/--
theorem `comap_prodMap_prod` / 定理 `comap_prodMap_prod`

English:
theorem comap_prodMap_prod
  given: (f : α -> β) (g : γ -> δ) (lb : Filter β) (ld : Filter δ)
  proof: by
  simp [prod_eq_inf, comap_comap, Function.comp_def]

中文:
定理 comap_prodMap_prod
  条件: (f : α -> β) (g : γ -> δ) (lb : Filter β) (ld : Filter δ)
  证明: by
  simp [prod_eq_inf, comap_comap, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comp_def, prod_eq_inf
-/
theorem comap_prodMap_prod (f : α -> β) (g : γ -> δ) (lb : Filter β) (ld : Filter δ) :
    comap (Prod.map f g) (lb ×ˢ ld) = comap f lb ×ˢ comap g ld := by
  simp [prod_eq_inf, comap_comap, Function.comp_def]

/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  statement: f ×ˢ (⊤ : Filter β) = f.comap Prod.fst
  proof: by
  rw [prod_eq_inf]; rw [comap_top]; rw [inf_top_eq]

中文:
定理 prod_top
  结论: f ×ˢ (⊤ : Filter β) = f.comap Prod.fst
  证明: by
  rw [prod_eq_inf]; rw [comap_top]; rw [inf_top_eq]

Depends on / 依赖: comap_top, inf_top_eq, prod_eq_inf
-/
theorem prod_top : f ×ˢ (⊤ : Filter β) = f.comap Prod.fst := by
  rw [prod_eq_inf]; rw [comap_top]; rw [inf_top_eq]

/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  statement: (⊤ : Filter α) ×ˢ g = g.comap Prod.snd
  proof: by
  rw [prod_eq_inf]; rw [comap_top]; rw [top_inf_eq]

中文:
定理 top_prod
  结论: (⊤ : Filter α) ×ˢ g = g.comap Prod.snd
  证明: by
  rw [prod_eq_inf]; rw [comap_top]; rw [top_inf_eq]

Depends on / 依赖: comap_top, prod_eq_inf, top_inf_eq
-/
theorem top_prod : (⊤ : Filter α) ×ˢ g = g.comap Prod.snd := by
  rw [prod_eq_inf]; rw [comap_top]; rw [top_inf_eq]

/--
theorem `sup_prod` / 定理 `sup_prod`

English:
theorem sup_prod
  given: (f₁ f₂ : Filter α) (g : Filter β)
  statement: (f₁ ⊔ f₂) ×ˢ g = (f₁ ×ˢ g) ⊔ (f₂ ×ˢ g)
  proof: by
  simp only [prod_eq_inf, comap_sup, inf_sup_right]

中文:
定理 sup_prod
  条件: (f₁ f₂ : Filter α) (g : Filter β)
  结论: (f₁ ⊔ f₂) ×ˢ g = (f₁ ×ˢ g) ⊔ (f₂ ×ˢ g)
  证明: by
  simp only [prod_eq_inf, comap_sup, inf_sup_right]

Depends on / 依赖: comap_sup, inf_sup_right, prod_eq_inf
-/
theorem sup_prod (f₁ f₂ : Filter α) (g : Filter β) : (f₁ ⊔ f₂) ×ˢ g = (f₁ ×ˢ g) ⊔ (f₂ ×ˢ g) := by
  simp only [prod_eq_inf, comap_sup, inf_sup_right]

/--
theorem `prod_sup` / 定理 `prod_sup`

English:
theorem prod_sup
  given: (f : Filter α) (g₁ g₂ : Filter β)
  statement: f ×ˢ (g₁ ⊔ g₂) = (f ×ˢ g₁) ⊔ (f ×ˢ g₂)
  proof: by
  simp only [prod_eq_inf, comap_sup, inf_sup_left]

中文:
定理 prod_sup
  条件: (f : Filter α) (g₁ g₂ : Filter β)
  结论: f ×ˢ (g₁ ⊔ g₂) = (f ×ˢ g₁) ⊔ (f ×ˢ g₂)
  证明: by
  simp only [prod_eq_inf, comap_sup, inf_sup_left]

Depends on / 依赖: comap_sup, inf_sup_left, prod_eq_inf
-/
theorem prod_sup (f : Filter α) (g₁ g₂ : Filter β) : f ×ˢ (g₁ ⊔ g₂) = (f ×ˢ g₁) ⊔ (f ×ˢ g₂) := by
  simp only [prod_eq_inf, comap_sup, inf_sup_left]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eventually_prod_iff` / 定理 `eventually_prod_iff`

English:
theorem eventually_prod_iff
  given: {p : α × β -> Prop}
  proof: by
  simpa only [Set.prod_subset_iff] using! @mem_prod_iff α β p f g

中文:
定理 eventually_prod_iff
  条件: {p : α × β -> 命题}
  证明: by
  simpa only [Set.prod_subset_iff] using! @mem_prod_iff α β p f g

Depends on / 依赖: Set.prod_subset_iff, mem_prod_iff, prod_subset_iff
-/
theorem eventually_prod_iff {p : α × β -> Prop} :
    (forallᶠ x in f ×ˢ g, p x) ↔
      exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exists pb : β -> Prop, (forallᶠ y in g, pb y) ∧
        forall {x}, pa x -> forall {y}, pb y -> p (x, y) := by
  simpa only [Set.prod_subset_iff] using! @mem_prod_iff α β p f g

/--
theorem `tendsto_fst` / 定理 `tendsto_fst`

English:
theorem tendsto_fst
  statement: Tendsto Prod.fst (f ×ˢ g) f
  proof: tendsto_inf_left tendsto_comap

中文:
定理 tendsto_fst
  结论: Tendsto Prod.fst (f ×ˢ g) f
  证明: tendsto_inf_left tendsto_comap

Depends on / 依赖: tendsto_comap, tendsto_inf_left
-/
theorem tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f :=
  tendsto_inf_left tendsto_comap

/--
theorem `tendsto_snd` / 定理 `tendsto_snd`

English:
theorem tendsto_snd
  statement: Tendsto Prod.snd (f ×ˢ g) g
  proof: tendsto_inf_right tendsto_comap

中文:
定理 tendsto_snd
  结论: Tendsto Prod.snd (f ×ˢ g) g
  证明: tendsto_inf_right tendsto_comap

Depends on / 依赖: tendsto_comap, tendsto_inf_right
-/
theorem tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g :=
  tendsto_inf_right tendsto_comap

/--
theorem `Tendsto.fst` / 定理 `Tendsto.fst`

English:
theorem Tendsto.fst
  given: {h : Filter γ} {m : α -> β × γ} (H : Tendsto m f (g ×ˢ h))
  proof: tendsto_fst.comp H

中文:
定理 Tendsto.fst
  条件: {h : Filter γ} {m : α -> β × γ} (H : Tendsto m f (g ×ˢ h))
  证明: tendsto_fst.comp H

Depends on / 依赖: tendsto_fst, tendsto_fst.comp
-/
theorem Tendsto.fst {h : Filter γ} {m : α -> β × γ} (H : Tendsto m f (g ×ˢ h)) :
    Tendsto (fun a => (m a).1) f g :=
  tendsto_fst.comp H

/--
theorem `Tendsto.snd` / 定理 `Tendsto.snd`

English:
theorem Tendsto.snd
  given: {h : Filter γ} {m : α -> β × γ} (H : Tendsto m f (g ×ˢ h))
  proof: tendsto_snd.comp H

中文:
定理 Tendsto.snd
  条件: {h : Filter γ} {m : α -> β × γ} (H : Tendsto m f (g ×ˢ h))
  证明: tendsto_snd.comp H

Depends on / 依赖: tendsto_snd, tendsto_snd.comp
-/
theorem Tendsto.snd {h : Filter γ} {m : α -> β × γ} (H : Tendsto m f (g ×ˢ h)) :
    Tendsto (fun a => (m a).2) f h :=
  tendsto_snd.comp H

/--
theorem `Tendsto.prodMk` / 定理 `Tendsto.prodMk`

English:
theorem Tendsto.prodMk
  statement: {h : Filter γ} {m₁ : α -> β} {m₂ : α -> γ}
  proof: tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

中文:
定理 Tendsto.prodMk
  结论: {h : Filter γ} {m₁ : α -> β} {m₂ : α -> γ}
  证明: tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

Depends on / 依赖: tendsto_comap_iff, tendsto_inf
-/
theorem Tendsto.prodMk {h : Filter γ} {m₁ : α -> β} {m₂ : α -> γ}
    (h₁ : Tendsto m₁ f g) (h₂ : Tendsto m₂ f h) : Tendsto (fun x => (m₁ x, m₂ x)) f (g ×ˢ h) :=
  tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

/--
theorem `tendsto_prod_swap` / 定理 `tendsto_prod_swap`

English:
theorem tendsto_prod_swap
  statement: Tendsto (Prod.swap : α × β -> β × α) (f ×ˢ g) (g ×ˢ f)
  proof: tendsto_snd.prodMk tendsto_fst

中文:
定理 tendsto_prod_swap
  结论: Tendsto (Prod.swap : α × β -> β × α) (f ×ˢ g) (g ×ˢ f)
  证明: tendsto_snd.prodMk tendsto_fst

Depends on / 依赖: prodMk, tendsto_fst, tendsto_snd, tendsto_snd.prodMk
-/
theorem tendsto_prod_swap : Tendsto (Prod.swap : α × β -> β × α) (f ×ˢ g) (g ×ˢ f) :=
  tendsto_snd.prodMk tendsto_fst

/--
theorem `Eventually.prod_inl` / 定理 `Eventually.prod_inl`

English:
theorem Eventually.prod_inl
  given: {la : Filter α} {p : α -> Prop} (h : forallᶠ x in la, p x) (lb : Filter β)
  proof: tendsto_fst.eventually h

中文:
定理 Eventually.prod_inl
  条件: {la : Filter α} {p : α -> 命题} (h : 对任意ᶠ x in la, p x) (lb : Filter β)
  证明: tendsto_fst.eventually h

Depends on / 依赖: eventually, tendsto_fst, tendsto_fst.eventually
-/
theorem Eventually.prod_inl {la : Filter α} {p : α -> Prop} (h : forallᶠ x in la, p x) (lb : Filter β) :
    forallᶠ x in la ×ˢ lb, p (x : α × β).1 :=
  tendsto_fst.eventually h

/--
theorem `Eventually.prod_inr` / 定理 `Eventually.prod_inr`

English:
theorem Eventually.prod_inr
  given: {lb : Filter β} {p : β -> Prop} (h : forallᶠ x in lb, p x) (la : Filter α)
  proof: tendsto_snd.eventually h

中文:
定理 Eventually.prod_inr
  条件: {lb : Filter β} {p : β -> 命题} (h : 对任意ᶠ x in lb, p x) (la : Filter α)
  证明: tendsto_snd.eventually h

Depends on / 依赖: eventually, tendsto_snd, tendsto_snd.eventually
-/
theorem Eventually.prod_inr {lb : Filter β} {p : β -> Prop} (h : forallᶠ x in lb, p x) (la : Filter α) :
    forallᶠ x in la ×ˢ lb, p (x : α × β).2 :=
  tendsto_snd.eventually h

/--
theorem `Eventually.prod_mk` / 定理 `Eventually.prod_mk`

English:
theorem Eventually.prod_mk
  statement: {la : Filter α} {pa : α -> Prop} (ha : forallᶠ x in la, pa x) {lb : Filter β}
  proof: (ha.prod_inl lb).and (hb.prod_inr la)

中文:
定理 Eventually.prod_mk
  结论: {la : Filter α} {pa : α -> 命题} (ha : 对任意ᶠ x in la, pa x) {lb : Filter β}
  证明: (ha.prod_inl lb).and (hb.prod_inr la)

Depends on / 依赖: ha.prod_inl, hb.prod_inr, prod_inl, prod_inr
-/
theorem Eventually.prod_mk {la : Filter α} {pa : α -> Prop} (ha : forallᶠ x in la, pa x) {lb : Filter β}
    {pb : β -> Prop} (hb : forallᶠ y in lb, pb y) : forallᶠ p in la ×ˢ lb, pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl lb).and (hb.prod_inr la)

/--
theorem `EventuallyEq.prodMap` / 定理 `EventuallyEq.prodMap`

English:
theorem EventuallyEq.prodMap
  statement: {δ} {la : Filter α} {fa ga : α -> γ} (ha : fa =ᶠ[la] ga)
  proof: (Eventually.prod_mk ha hb).mono fun _ h => Prod.ext h.1 h.2

中文:
定理 EventuallyEq.prodMap
  结论: {δ} {la : Filter α} {fa ga : α -> γ} (ha : fa =ᶠ[la] ga)
  证明: (Eventually.prod_mk ha hb).mono fun _ h => Prod.ext h.1 h.2

Depends on / 依赖: Eventually, Eventually.prod_mk, Prod.ext, prod_mk
-/
theorem EventuallyEq.prodMap {δ} {la : Filter α} {fa ga : α -> γ} (ha : fa =ᶠ[la] ga)
    {lb : Filter β} {fb gb : β -> δ} (hb : fb =ᶠ[lb] gb) :
    Prod.map fa fb =ᶠ[la ×ˢ lb] Prod.map ga gb :=
  (Eventually.prod_mk ha hb).mono fun _ h => Prod.ext h.1 h.2

/--
theorem `EventuallyLE.prodMap` / 定理 `EventuallyLE.prodMap`

English:
theorem EventuallyLE.prodMap
  statement: {δ} [LE γ] [LE δ] {la : Filter α} {fa ga : α -> γ} (ha : fa <=ᶠ[la] ga)
  proof: Eventually.prod_mk ha hb

中文:
定理 EventuallyLE.prodMap
  结论: {δ} [LE γ] [LE δ] {la : Filter α} {fa ga : α -> γ} (ha : fa <=ᶠ[la] ga)
  证明: Eventually.prod_mk ha hb

Depends on / 依赖: Eventually, Eventually.prod_mk, prod_mk
-/
theorem EventuallyLE.prodMap {δ} [LE γ] [LE δ] {la : Filter α} {fa ga : α -> γ} (ha : fa <=ᶠ[la] ga)
    {lb : Filter β} {fb gb : β -> δ} (hb : fb <=ᶠ[lb] gb) :
    Prod.map fa fb <=ᶠ[la ×ˢ lb] Prod.map ga gb :=
  Eventually.prod_mk ha hb

/--
theorem `Eventually.curry` / 定理 `Eventually.curry`

English:
theorem Eventually.curry
  statement: {la : Filter α} {lb : Filter β} {p : α × β -> Prop}
  proof: by
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩
  exact ha.mono fun a ha => hb.mono fun b hb => h ha hb

中文:
定理 Eventually.curry
  结论: {la : Filter α} {lb : Filter β} {p : α × β -> 命题}
  证明: by
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩
  exact ha.mono fun a ha => hb.mono fun b hb => h ha hb

Depends on / 依赖: eventually_prod_iff, ha.mono, hb.mono
-/
theorem Eventually.curry {la : Filter α} {lb : Filter β} {p : α × β -> Prop}
    (h : forallᶠ x in la ×ˢ lb, p x) : forallᶠ x in la, forallᶠ y in lb, p (x, y) := by
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩
  exact ha.mono fun a ha => hb.mono fun b hb => h ha hb

/--
lemma `Frequently.uncurry` / 引理 `Frequently.uncurry`

English:
lemma Frequently.uncurry
  statement: {la : Filter α} {lb : Filter β} {p : α -> β -> Prop}
  proof: by
  contrapose! h
  exact h.curry

中文:
引理 Frequently.uncurry
  结论: {la : Filter α} {lb : Filter β} {p : α -> β -> 命题}
  证明: by
  contrapose! h
  exact h.curry
-/
protected lemma Frequently.uncurry {la : Filter α} {lb : Filter β} {p : α -> β -> Prop}
    (h : existsᶠ x in la, existsᶠ y in lb, p x y) : existsᶠ xy in la ×ˢ lb, p xy.1 xy.2 := by
  contrapose! h
  exact h.curry

/--
lemma `Frequently.of_curry` / 引理 `Frequently.of_curry`

English:
lemma Frequently.of_curry
  statement: {la : Filter α} {lb : Filter β} {p : α × β -> Prop}
  proof: h.uncurry

中文:
引理 Frequently.of_curry
  结论: {la : Filter α} {lb : Filter β} {p : α × β -> 命题}
  证明: h.uncurry

Depends on / 依赖: h.uncurry, uncurry
-/
lemma Frequently.of_curry {la : Filter α} {lb : Filter β} {p : α × β -> Prop}
    (h : existsᶠ x in la, existsᶠ y in lb, p (x, y)) : existsᶠ xy in la ×ˢ lb, p xy :=
  h.uncurry

/--
theorem `Eventually.image_of_prod` / 定理 `Eventually.image_of_prod`

English:
theorem Eventually.image_of_prod
  statement: {y : α -> β} {r : α -> β -> Prop}
  proof: by
  obtain ⟨p, hp, q, hq, hr⟩ := eventually_prod_iff.mp hr
  filter_upwards [hp, hy.eventually hq] with _ hp hq using hr hp hq

中文:
定理 Eventually.image_of_prod
  结论: {y : α -> β} {r : α -> β -> 命题}
  证明: by
  obtain ⟨p, hp, q, hq, hr⟩ := eventually_prod_iff.mp hr
  filter_upwards [hp, hy.eventually hq] with _ hp hq using hr hp hq

Depends on / 依赖: eventually, eventually_prod_iff, eventually_prod_iff.mp, filter_upwards, hy.eventually
-/
theorem Eventually.image_of_prod {y : α -> β} {r : α -> β -> Prop}
    (hy : Tendsto y f g) (hr : forallᶠ p in f ×ˢ g, r p.1 p.2) : forallᶠ x in f, r x (y x) := by
  obtain ⟨p, hp, q, hq, hr⟩ := eventually_prod_iff.mp hr
  filter_upwards [hp, hy.eventually hq] with _ hp hq using hr hp hq

/--
theorem `Eventually.diag_of_prod` / 定理 `Eventually.diag_of_prod`

English:
theorem Eventually.diag_of_prod
  given: {p : α × α -> Prop} (h : forallᶠ i in f ×ˢ f, p i)
  proof: h.image_of_prod (r := p.curry) tendsto_id

中文:
定理 Eventually.diag_of_prod
  条件: {p : α × α -> 命题} (h : 对任意ᶠ i in f ×ˢ f, p i)
  证明: h.image_of_prod (r := p.curry) tendsto_id

Depends on / 依赖: h.image_of_prod, image_of_prod, p.curry, tendsto_id
-/
theorem Eventually.diag_of_prod {p : α × α -> Prop} (h : forallᶠ i in f ×ˢ f, p i) :
    forallᶠ i in f, p (i, i) :=
  h.image_of_prod (r := p.curry) tendsto_id

/--
theorem `Eventually.diag_of_prod_left` / 定理 `Eventually.diag_of_prod_left`

English:
theorem Eventually.diag_of_prod_left
  given: {f : Filter α} {g : Filter γ} {p : (α × α) × γ -> Prop}
  proof: by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.diag_of_prod.prod_mk hs).mono fun x hx => by simp only [hst hx.1 hx.2]

中文:
定理 Eventually.diag_of_prod_left
  条件: {f : Filter α} {g : Filter γ} {p : (α × α) × γ -> 命题}
  证明: by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.diag_of_prod.prod_mk hs).mono fun x hx => by simp only [hst hx.1 hx.2]

Depends on / 依赖: diag_of_prod, eventually_prod_iff, ht.diag_of_prod.prod_mk, prod_mk
-/
theorem Eventually.diag_of_prod_left {f : Filter α} {g : Filter γ} {p : (α × α) × γ -> Prop} :
    (forallᶠ x in (f ×ˢ f) ×ˢ g, p x) -> forallᶠ x : α × γ in f ×ˢ g, p ((x.1, x.1), x.2) := by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.diag_of_prod.prod_mk hs).mono fun x hx => by simp only [hst hx.1 hx.2]

/--
theorem `Eventually.diag_of_prod_right` / 定理 `Eventually.diag_of_prod_right`

English:
theorem Eventually.diag_of_prod_right
  given: {f : Filter α} {g : Filter γ} {p : α × γ × γ -> Prop}
  proof: by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.prod_mk hs.diag_of_prod).mono fun x hx => by simp only [hst hx.1 hx.2]

中文:
定理 Eventually.diag_of_prod_right
  条件: {f : Filter α} {g : Filter γ} {p : α × γ × γ -> 命题}
  证明: by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.prod_mk hs.diag_of_prod).mono fun x hx => by simp only [hst hx.1 hx.2]

Depends on / 依赖: diag_of_prod, eventually_prod_iff, hs.diag_of_prod, ht.prod_mk, prod_mk
-/
theorem Eventually.diag_of_prod_right {f : Filter α} {g : Filter γ} {p : α × γ × γ -> Prop} :
    (forallᶠ x in f ×ˢ (g ×ˢ g), p x) -> forallᶠ x : α × γ in f ×ˢ g, p (x.1, x.2, x.2) := by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.prod_mk hs.diag_of_prod).mono fun x hx => by simp only [hst hx.1 hx.2]

/--
theorem `tendsto_diag` / 定理 `tendsto_diag`

English:
theorem tendsto_diag
  statement: Tendsto Function.diag f (f ×ˢ f)
  proof: tendsto_iff_eventually.mpr fun _ hpr => hpr.diag_of_prod

中文:
定理 tendsto_diag
  结论: Tendsto Function.diag f (f ×ˢ f)
  证明: tendsto_iff_eventually.mpr fun _ hpr => hpr.diag_of_prod

Depends on / 依赖: diag_of_prod, hpr.diag_of_prod, tendsto_iff_eventually, tendsto_iff_eventually.mpr
-/
theorem tendsto_diag : Tendsto Function.diag f (f ×ˢ f) :=
  tendsto_iff_eventually.mpr fun _ hpr => hpr.diag_of_prod

/--
theorem `prod_iInf_left` / 定理 `prod_iInf_left`

English:
theorem prod_iInf_left
  given: [Nonempty ι] {f : ι -> Filter α} {g : Filter β}
  proof: by
  simp only [prod_eq_inf, comap_iInf, iInf_inf]

中文:
定理 prod_iInf_left
  条件: [Nonempty ι] {f : ι -> Filter α} {g : Filter β}
  证明: by
  simp only [prod_eq_inf, comap_iInf, iInf_inf]

Depends on / 依赖: comap_iInf, iInf_inf, prod_eq_inf
-/
theorem prod_iInf_left [Nonempty ι] {f : ι -> Filter α} {g : Filter β} :
    (⨅ i, f i) ×ˢ g = ⨅ i, f i ×ˢ g := by
  simp only [prod_eq_inf, comap_iInf, iInf_inf]

/--
theorem `prod_iInf_right` / 定理 `prod_iInf_right`

English:
theorem prod_iInf_right
  given: [Nonempty ι] {f : Filter α} {g : ι -> Filter β}
  proof: by
  simp only [prod_eq_inf, comap_iInf, inf_iInf]

@[mono, gcongr]

中文:
定理 prod_iInf_right
  条件: [Nonempty ι] {f : Filter α} {g : ι -> Filter β}
  证明: by
  simp only [prod_eq_inf, comap_iInf, inf_iInf]

@[mono, gcongr]

Depends on / 依赖: comap_iInf, inf_iInf, prod_eq_inf
-/
theorem prod_iInf_right [Nonempty ι] {f : Filter α} {g : ι -> Filter β} :
    (f ×ˢ ⨅ i, g i) = ⨅ i, f ×ˢ g i := by
  simp only [prod_eq_inf, comap_iInf, inf_iInf]

@[mono, gcongr]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  proof: inf_le_inf (comap_mono hf) (comap_mono hg)

中文:
定理 prod_mono
  条件: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  证明: inf_le_inf (comap_mono hf) (comap_mono hg)

Depends on / 依赖: comap_mono, inf_le_inf
-/
theorem prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ <= f₂) (hg : g₁ <= g₂) :
    f₁ ×ˢ g₁ <= f₂ ×ˢ g₂ :=
  inf_le_inf (comap_mono hf) (comap_mono hg)

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  given: (g : Filter β) {f₁ f₂ : Filter α} (hf : f₁ <= f₂)
  statement: f₁ ×ˢ g <= f₂ ×ˢ g
  proof: Filter.prod_mono hf rfl.le

中文:
定理 prod_mono_left
  条件: (g : Filter β) {f₁ f₂ : Filter α} (hf : f₁ <= f₂)
  结论: f₁ ×ˢ g <= f₂ ×ˢ g
  证明: Filter.prod_mono hf rfl.le

Depends on / 依赖: Filter, Filter.prod_mono, prod_mono, rfl.le
-/
theorem prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} (hf : f₁ <= f₂) : f₁ ×ˢ g <= f₂ ×ˢ g :=
  Filter.prod_mono hf rfl.le

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  given: (f : Filter α) {g₁ g₂ : Filter β} (hf : g₁ <= g₂)
  statement: f ×ˢ g₁ <= f ×ˢ g₂
  proof: Filter.prod_mono rfl.le hf

中文:
定理 prod_mono_right
  条件: (f : Filter α) {g₁ g₂ : Filter β} (hf : g₁ <= g₂)
  结论: f ×ˢ g₁ <= f ×ˢ g₂
  证明: Filter.prod_mono rfl.le hf

Depends on / 依赖: Filter, Filter.prod_mono, prod_mono, rfl.le
-/
theorem prod_mono_right (f : Filter α) {g₁ g₂ : Filter β} (hf : g₁ <= g₂) : f ×ˢ g₁ <= f ×ˢ g₂ :=
  Filter.prod_mono rfl.le hf

/--
theorem `prod_comap_comap_eq.` / 定理 `prod_comap_comap_eq.`

English:
theorem prod_comap_comap_eq.{u,
  given: v, w, x} {α₁
  statement: Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  proof: by
  simp only [prod_eq_inf, comap_comap, comap_inf, Function.comp_def]

中文:
定理 prod_comap_comap_eq.{u,
  条件: v, w, x} {α₁
  结论: 类型u} {α₂ : 类型v} {β₁ : Type w} {β₂ : Type x}
  证明: by
  simp only [prod_eq_inf, comap_comap, comap_inf, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comap_inf, comp_def, prod_eq_inf
-/
theorem prod_comap_comap_eq.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : β₁ -> α₁} {m₂ : β₂ -> α₂} :
    comap m₁ f₁ ×ˢ comap m₂ f₂ = comap (fun p : β₁ × β₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ˢ f₂) := by
  simp only [prod_eq_inf, comap_comap, comap_inf, Function.comp_def]

/--
theorem `prod_comm'` / 定理 `prod_comm'`

English:
theorem prod_comm'
  statement: f ×ˢ g = comap Prod.swap (g ×ˢ f)
  proof: by
  simp only [prod_eq_inf, comap_comap, Function.comp_def, inf_comm, Prod.swap, comap_inf]

中文:
定理 prod_comm'
  结论: f ×ˢ g = comap Prod.swap (g ×ˢ f)
  证明: by
  simp only [prod_eq_inf, comap_comap, Function.comp_def, inf_comm, Prod.swap, comap_inf]

Depends on / 依赖: Function, Function.comp_def, Prod.swap, comap_comap, comap_inf, comp_def, inf_comm, prod_eq_inf
-/
theorem prod_comm' : f ×ˢ g = comap Prod.swap (g ×ˢ f) := by
  simp only [prod_eq_inf, comap_comap, Function.comp_def, inf_comm, Prod.swap, comap_inf]

/--
theorem `prod_comm` / 定理 `prod_comm`

English:
theorem prod_comm
  statement: f ×ˢ g = map Prod.swap (g ×ˢ f)
  proof: by
  rw [prod_comm']; rw [← map_swap_eq_comap_swap]

中文:
定理 prod_comm
  结论: f ×ˢ g = map Prod.swap (g ×ˢ f)
  证明: by
  rw [prod_comm']; rw [← map_swap_eq_comap_swap]

Depends on / 依赖: map_swap_eq_comap_swap, prod_comm
-/
theorem prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f) := by
  rw [prod_comm']; rw [← map_swap_eq_comap_swap]

/--
theorem `mem_prod_iff_left` / 定理 `mem_prod_iff_left`

English:
theorem mem_prod_iff_left
  given: {s : Set (α × β)}
  proof: by
  simp only [mem_prod_iff, prod_subset_iff]
refine exists_congr fun _ => Iff.rfl.and Iff.trans ?_ exists_mem_subset_iff
  exact exists_congr fun _ => Iff.rfl.and forall₂_comm

中文:
定理 mem_prod_iff_left
  条件: {s : Set (α × β)}
  证明: by
  simp only [mem_prod_iff, prod_subset_iff]
refine exists_congr fun _ => Iff.rfl.and Iff.trans ?_ exists_mem_subset_iff
  exact exists_congr fun _ => Iff.rfl.and forall₂_comm

Depends on / 依赖: Iff.rfl.and, Iff.trans, exists_congr, exists_mem_subset_iff, mem_prod_iff, prod_subset_iff
-/
theorem mem_prod_iff_left {s : Set (α × β)} :
    s in f ×ˢ g ↔ exists t in f, forallᶠ y in g, forall x in t, (x, y) in s := by
  simp only [mem_prod_iff, prod_subset_iff]
refine exists_congr fun _ => Iff.rfl.and Iff.trans ?_ exists_mem_subset_iff
  exact exists_congr fun _ => Iff.rfl.and forall₂_comm

/--
theorem `mem_prod_iff_right` / 定理 `mem_prod_iff_right`

English:
theorem mem_prod_iff_right
  given: {s : Set (α × β)}
  proof: by
  rw [prod_comm]; rw [mem_map]; rw [mem_prod_iff_left]; rfl

@[simp]

中文:
定理 mem_prod_iff_right
  条件: {s : Set (α × β)}
  证明: by
  rw [prod_comm]; rw [mem_map]; rw [mem_prod_iff_left]; rfl

@[simp]

Depends on / 依赖: mem_map, mem_prod_iff_left, prod_comm
-/
theorem mem_prod_iff_right {s : Set (α × β)} :
    s in f ×ˢ g ↔ exists t in g, forallᶠ x in f, forall y in t, (x, y) in s := by
  rw [prod_comm]; rw [mem_map]; rw [mem_prod_iff_left]; rfl

@[simp]
/--
theorem `map_fst_prod` / 定理 `map_fst_prod`

English:
theorem map_fst_prod
  given: (f : Filter α) (g : Filter β) [NeBot g]
  statement: map Prod.fst (f ×ˢ g) = f
  proof: by
  ext s
  simp only [mem_map, mem_prod_iff_left, mem_preimage, eventually_const, ← subset_def,
    exists_mem_subset_iff]

@[simp]

中文:
定理 map_fst_prod
  条件: (f : Filter α) (g : Filter β) [NeBot g]
  结论: map Prod.fst (f ×ˢ g) = f
  证明: by
  ext s
  simp only [mem_map, mem_prod_iff_left, mem_preimage, eventually_const, ← subset_def,
    exists_mem_subset_iff]

@[simp]

Depends on / 依赖: eventually_const, exists_mem_subset_iff, mem_map, mem_preimage, mem_prod_iff_left, subset_def
-/
theorem map_fst_prod (f : Filter α) (g : Filter β) [NeBot g] : map Prod.fst (f ×ˢ g) = f := by
  ext s
  simp only [mem_map, mem_prod_iff_left, mem_preimage, eventually_const, ← subset_def,
    exists_mem_subset_iff]

@[simp]
/--
theorem `map_snd_prod` / 定理 `map_snd_prod`

English:
theorem map_snd_prod
  given: (f : Filter α) (g : Filter β) [NeBot f]
  statement: map Prod.snd (f ×ˢ g) = g
  proof: by
  rw [prod_comm]; rw [map_map]; apply map_fst_prod

@[simp]

中文:
定理 map_snd_prod
  条件: (f : Filter α) (g : Filter β) [NeBot f]
  结论: map Prod.snd (f ×ˢ g) = g
  证明: by
  rw [prod_comm]; rw [map_map]; apply map_fst_prod

@[simp]

Depends on / 依赖: map_fst_prod, map_map, prod_comm
-/
theorem map_snd_prod (f : Filter α) (g : Filter β) [NeBot f] : map Prod.snd (f ×ˢ g) = g := by
  rw [prod_comm]; rw [map_map]; apply map_fst_prod

@[simp]
/--
theorem `prod_le_prod` / 定理 `prod_le_prod`

English:
theorem prod_le_prod
  given: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁]
  proof: ⟨fun h =>
    ⟨map_fst_prod f₁ g₁ ▸ tendsto_fst.mono_left h, map_snd_prod f₁ g₁ ▸ tendsto_snd.mono_left h⟩,
    fun h => prod_mono h.1 h.2⟩

@[simp]

中文:
定理 prod_le_prod
  条件: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁]
  证明: ⟨fun h =>
    ⟨map_fst_prod f₁ g₁ ▸ tendsto_fst.mono_left h, map_snd_prod f₁ g₁ ▸ tendsto_snd.mono_left h⟩,
    fun h => prod_mono h.1 h.2⟩

@[simp]

Depends on / 依赖: map_fst_prod, map_snd_prod, mono_left, prod_mono, tendsto_fst, tendsto_fst.mono_left, tendsto_snd, tendsto_snd.mono_left
-/
theorem prod_le_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
    f₁ ×ˢ g₁ <= f₂ ×ˢ g₂ ↔ f₁ <= f₂ ∧ g₁ <= g₂ :=
  ⟨fun h =>
    ⟨map_fst_prod f₁ g₁ ▸ tendsto_fst.mono_left h, map_snd_prod f₁ g₁ ▸ tendsto_snd.mono_left h⟩,
    fun h => prod_mono h.1 h.2⟩

@[simp]
/--
theorem `prod_inj` / 定理 `prod_inj`

English:
theorem prod_inj
  given: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁]
  proof: by
  refine ⟨fun h => ?_, fun h => h.1 ▸ h.2 ▸ rfl⟩
  have hle : f₁ <= f₂ ∧ g₁ <= g₂ := prod_le_prod.1 h.le
  have := neBot_of_le hle.1; have := neBot_of_le hle.2
exact ⟨hle.1.antisymm (prod_le_prod.1 h.ge).1, hle.2.antisymm (prod_le_prod.1 h.ge).2⟩

中文:
定理 prod_inj
  条件: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁]
  证明: by
  refine ⟨fun h => ?_, fun h => h.1 ▸ h.2 ▸ rfl⟩
  have hle : f₁ <= f₂ ∧ g₁ <= g₂ := prod_le_prod.1 h.le
  have := neBot_of_le hle.1; have := neBot_of_le hle.2
exact ⟨hle.1.antisymm (prod_le_prod.1 h.ge).1, hle.2.antisymm (prod_le_prod.1 h.ge).2⟩

Depends on / 依赖: antisymm, h.ge, h.le, neBot_of_le, prod_le_prod
-/
theorem prod_inj {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
    f₁ ×ˢ g₁ = f₂ ×ˢ g₂ ↔ f₁ = f₂ ∧ g₁ = g₂ := by
  refine ⟨fun h => ?_, fun h => h.1 ▸ h.2 ▸ rfl⟩
  have hle : f₁ <= f₂ ∧ g₁ <= g₂ := prod_le_prod.1 h.le
  have := neBot_of_le hle.1; have := neBot_of_le hle.2
exact ⟨hle.1.antisymm (prod_le_prod.1 h.ge).1, hle.2.antisymm (prod_le_prod.1 h.ge).2⟩

/--
theorem `eventually_swap_iff` / 定理 `eventually_swap_iff`

English:
theorem eventually_swap_iff
  given: {p : α × β -> Prop}
  proof: by
  rw [prod_comm]; rfl

中文:
定理 eventually_swap_iff
  条件: {p : α × β -> 命题}
  证明: by
  rw [prod_comm]; rfl

Depends on / 依赖: prod_comm
-/
theorem eventually_swap_iff {p : α × β -> Prop} :
    (forallᶠ x : α × β in f ×ˢ g, p x) ↔ forallᶠ y : β × α in g ×ˢ f, p y.swap := by
  rw [prod_comm]; rfl

/--
lemma `Eventually.eventually_prod_of_eventually_swap` / 引理 `Eventually.eventually_prod_of_eventually_swap`

English:
lemma Eventually.eventually_prod_of_eventually_swap
  statement: {h : Filter γ}
  proof: by
  refine eventually_prod_iff.mpr ⟨_, hp, _, hq, fun {x} hx {z} hz => ?_⟩
  rcases (hx.and hz).exists with ⟨y, hpy, hqy⟩
  exact hpqr x y z hpy hqy

中文:
引理 Eventually.eventually_prod_of_eventually_swap
  结论: {h : Filter γ}
  证明: by
  refine eventually_prod_iff.mpr ⟨_, hp, _, hq, fun {x} hx {z} hz => ?_⟩
  rcases (hx.and hz).exists with ⟨y, hpy, hqy⟩
  exact hpqr x y z hpy hqy

Depends on / 依赖: eventually_prod_iff, eventually_prod_iff.mpr, hx.and
-/
lemma Eventually.eventually_prod_of_eventually_swap {h : Filter γ}
    [NeBot g] {p : α -> β -> Prop} {q : β -> γ -> Prop} {r : α -> γ -> Prop}
    (hp : forallᶠ x in f, forallᶠ y in g, p x y) (hq : forallᶠ z in h, forallᶠ y in g, q y z)
    (hpqr : forall x y z, p x y -> q y z -> r x z) :
    forallᶠ xz in f ×ˢ h, r xz.1 xz.2 := by
  refine eventually_prod_iff.mpr ⟨_, hp, _, hq, fun {x} hx {z} hz => ?_⟩
  rcases (hx.and hz).exists with ⟨y, hpy, hqy⟩
  exact hpqr x y z hpy hqy

/--
lemma `Eventually.trans_prod` / 引理 `Eventually.trans_prod`

English:
lemma Eventually.trans_prod
  statement: {h : Filter γ}
  proof: hp.curry.eventually_prod_of_eventually_swap (eventually_swap_iff.mp hq |>.curry) hpqr

中文:
引理 Eventually.trans_prod
  结论: {h : Filter γ}
  证明: hp.curry.eventually_prod_of_eventually_swap (eventually_swap_iff.mp hq |>.curry) hpqr

Depends on / 依赖: eventually_prod_of_eventually_swap, eventually_swap_iff, eventually_swap_iff.mp, hp.curry.eventually_prod_of_eventually_swap
-/
lemma Eventually.trans_prod {h : Filter γ}
    [NeBot g] {p : α -> β -> Prop} {q : β -> γ -> Prop} {r : α -> γ -> Prop}
    (hp : forallᶠ xy in f ×ˢ g, p xy.1 xy.2) (hq : forallᶠ yz in g ×ˢ h, q yz.1 yz.2)
    (hpqr : forall x y z, p x y -> q y z -> r x z) :
    forallᶠ xz in f ×ˢ h, r xz.1 xz.2 :=
  hp.curry.eventually_prod_of_eventually_swap (eventually_swap_iff.mp hq |>.curry) hpqr

/--
theorem `prod_assoc` / 定理 `prod_assoc`

English:
theorem prod_assoc
  given: (f : Filter α) (g : Filter β) (h : Filter γ)
  proof: by
  simp_rw [← comap_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_symm_apply]

中文:
定理 prod_assoc
  条件: (f : Filter α) (g : Filter β) (h : Filter γ)
  证明: by
  simp_rw [← comap_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_symm_apply]

Depends on / 依赖: Equiv.prodAssoc_symm_apply, Function, Function.comp_def, comap_comap, comap_equiv_symm, comap_inf, comp_def, inf_assoc, prodAssoc_symm_apply, prod_eq_inf, simp_rw
-/
theorem prod_assoc (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equiv.prodAssoc α β γ) ((f ×ˢ g) ×ˢ h) = f ×ˢ (g ×ˢ h) := by
  simp_rw [← comap_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_symm_apply]

/--
theorem `prod_assoc_symm` / 定理 `prod_assoc_symm`

English:
theorem prod_assoc_symm
  given: (f : Filter α) (g : Filter β) (h : Filter γ)
  proof: by
  simp_rw [map_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_apply]

中文:
定理 prod_assoc_symm
  条件: (f : Filter α) (g : Filter β) (h : Filter γ)
  证明: by
  simp_rw [map_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_apply]

Depends on / 依赖: Equiv.prodAssoc_apply, Function, Function.comp_def, comap_comap, comap_inf, comp_def, inf_assoc, map_equiv_symm, prodAssoc_apply, prod_eq_inf, simp_rw
-/
theorem prod_assoc_symm (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equiv.prodAssoc α β γ).symm (f ×ˢ (g ×ˢ h)) = (f ×ˢ g) ×ˢ h := by
  simp_rw [map_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_apply]

/--
theorem `tendsto_prodAssoc` / 定理 `tendsto_prodAssoc`

English:
theorem tendsto_prodAssoc
  given: {h : Filter γ}
  proof: (prod_assoc f g h).le

中文:
定理 tendsto_prodAssoc
  条件: {h : Filter γ}
  证明: (prod_assoc f g h).le

Depends on / 依赖: prod_assoc
-/
theorem tendsto_prodAssoc {h : Filter γ} :
    Tendsto (Equiv.prodAssoc α β γ) ((f ×ˢ g) ×ˢ h) (f ×ˢ (g ×ˢ h)) :=
  (prod_assoc f g h).le

/--
theorem `tendsto_prodAssoc_symm` / 定理 `tendsto_prodAssoc_symm`

English:
theorem tendsto_prodAssoc_symm
  given: {h : Filter γ}
  proof: (prod_assoc_symm f g h).le

中文:
定理 tendsto_prodAssoc_symm
  条件: {h : Filter γ}
  证明: (prod_assoc_symm f g h).le

Depends on / 依赖: prod_assoc_symm
-/
theorem tendsto_prodAssoc_symm {h : Filter γ} :
    Tendsto (Equiv.prodAssoc α β γ).symm (f ×ˢ (g ×ˢ h)) ((f ×ˢ g) ×ˢ h) :=
  (prod_assoc_symm f g h).le

/--
theorem `map_swap4_prod` / 定理 `map_swap4_prod`

English:
theorem map_swap4_prod
  given: {h : Filter γ} {k : Filter δ}
  proof: by
  simp_rw [map_swap4_eq_comap, prod_eq_inf, comap_inf, comap_comap]; ac_rfl

中文:
定理 map_swap4_prod
  条件: {h : Filter γ} {k : Filter δ}
  证明: by
  simp_rw [map_swap4_eq_comap, prod_eq_inf, comap_inf, comap_comap]; ac_rfl

Depends on / 依赖: comap_comap, comap_inf, map_swap4_eq_comap, prod_eq_inf, simp_rw
-/
theorem map_swap4_prod {h : Filter γ} {k : Filter δ} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h ×ˢ k)) =
      (f ×ˢ h) ×ˢ (g ×ˢ k) := by
  simp_rw [map_swap4_eq_comap, prod_eq_inf, comap_inf, comap_comap]; ac_rfl

/--
theorem `tendsto_swap4_prod` / 定理 `tendsto_swap4_prod`

English:
theorem tendsto_swap4_prod
  given: {h : Filter γ} {k : Filter δ}
  proof: map_swap4_prod.le

中文:
定理 tendsto_swap4_prod
  条件: {h : Filter γ} {k : Filter δ}
  证明: map_swap4_prod.le

Depends on / 依赖: map_swap4_prod, map_swap4_prod.le
-/
theorem tendsto_swap4_prod {h : Filter γ} {k : Filter δ} :
    Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h ×ˢ k))
      ((f ×ˢ h) ×ˢ (g ×ˢ k)) :=
  map_swap4_prod.le

/--
theorem `prod_map_map_eq.` / 定理 `prod_map_map_eq.`

English:
theorem prod_map_map_eq.{u,
  given: v, w, x} {α₁
  statement: Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  proof: le_antisymm
    (fun s hs =>
      let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs
mem_of_superset (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂))
        by rwa [prod_image_image_eq, image_subset_iff])
    ((tendsto_map.comp tendsto_fst).prodMk (tendsto_map.comp tendsto_snd))

中文:
定理 prod_map_map_eq.{u,
  条件: v, w, x} {α₁
  结论: 类型u} {α₂ : 类型v} {β₁ : Type w} {β₂ : Type x}
  证明: le_antisymm
    (fun s hs =>
      let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs
mem_of_superset (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂))
        by rwa [prod_image_image_eq, image_subset_iff])
    ((tendsto_map.comp tendsto_fst).prodMk (tendsto_map.comp tendsto_snd))

Depends on / 依赖: image_mem_map, image_subset_iff, le_antisymm, mem_of_superset, mem_prod_iff, mem_prod_iff.mp, prodMk, prod_image_image_eq, prod_mem_prod, tendsto_fst, tendsto_map, tendsto_map.comp, tendsto_snd
-/
theorem prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ -> β₁} {m₂ : α₂ -> β₂} :
    map m₁ f₁ ×ˢ map m₂ f₂ = map (fun p : α₁ × α₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ˢ f₂) :=
  le_antisymm
    (fun s hs =>
      let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs
mem_of_superset (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂))
        by rwa [prod_image_image_eq, image_subset_iff])
    ((tendsto_map.comp tendsto_fst).prodMk (tendsto_map.comp tendsto_snd))

/--
theorem `prod_map_map_eq'` / 定理 `prod_map_map_eq'`

English:
theorem prod_map_map_eq'
  statement: {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (f : α₁ -> α₂)
  proof: prod_map_map_eq

中文:
定理 prod_map_map_eq'
  结论: {α₁ : 类型} {α₂ : 类型} {β₁ : 类型} {β₂ : 类型} (f : α₁ -> α₂)
  证明: prod_map_map_eq

Depends on / 依赖: prod_map_map_eq
-/
theorem prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (f : α₁ -> α₂)
    (g : β₁ -> β₂) (F : Filter α₁) (G : Filter β₁) :
    map f F ×ˢ map g G = map (Prod.map f g) (F ×ˢ G) :=
  prod_map_map_eq

/--
theorem `prod_map_left` / 定理 `prod_map_left`

English:
theorem prod_map_left
  given: (f : α -> β) (F : Filter α) (G : Filter γ)
  proof: by
  rw [← prod_map_map_eq']; rw [map_id]

中文:
定理 prod_map_left
  条件: (f : α -> β) (F : Filter α) (G : Filter γ)
  证明: by
  rw [← prod_map_map_eq']; rw [map_id]

Depends on / 依赖: map_id, prod_map_map_eq
-/
theorem prod_map_left (f : α -> β) (F : Filter α) (G : Filter γ) :
    map f F ×ˢ G = map (Prod.map f id) (F ×ˢ G) := by
  rw [← prod_map_map_eq']; rw [map_id]

/--
theorem `prod_map_right` / 定理 `prod_map_right`

English:
theorem prod_map_right
  given: (f : β -> γ) (F : Filter α) (G : Filter β)
  proof: by
  rw [← prod_map_map_eq']; rw [map_id]

中文:
定理 prod_map_right
  条件: (f : β -> γ) (F : Filter α) (G : Filter β)
  证明: by
  rw [← prod_map_map_eq']; rw [map_id]

Depends on / 依赖: map_id, prod_map_map_eq
-/
theorem prod_map_right (f : β -> γ) (F : Filter α) (G : Filter β) :
    F ×ˢ map f G = map (Prod.map id f) (F ×ˢ G) := by
  rw [← prod_map_map_eq']; rw [map_id]

/--
theorem `le_prod_map_fst_snd` / 定理 `le_prod_map_fst_snd`

English:
theorem le_prod_map_fst_snd
  given: {f : Filter (α × β)}
  statement: f <= map Prod.fst f ×ˢ map Prod.snd f
  proof: le_inf le_comap_map le_comap_map

中文:
定理 le_prod_map_fst_snd
  条件: {f : Filter (α × β)}
  结论: f <= map Prod.fst f ×ˢ map Prod.snd f
  证明: le_inf le_comap_map le_comap_map

Depends on / 依赖: le_comap_map, le_inf
-/
theorem le_prod_map_fst_snd {f : Filter (α × β)} : f <= map Prod.fst f ×ˢ map Prod.snd f :=
  le_inf le_comap_map le_comap_map

/--
theorem `Tendsto.prodMap` / 定理 `Tendsto.prodMap`

English:
theorem Tendsto.prodMap
  statement: {δ : Type*} {f : α -> γ} {g : β -> δ} {a : Filter α} {b : Filter β}
  proof: by
  rw [Tendsto]; rw [Prod.map_def]; rw [← prod_map_map_eq]
  exact Filter.prod_mono hf hg

中文:
定理 Tendsto.prodMap
  结论: {δ : 类型} {f : α -> γ} {g : β -> δ} {a : Filter α} {b : Filter β}
  证明: by
  rw [Tendsto]; rw [Prod.map_def]; rw [← prod_map_map_eq]
  exact Filter.prod_mono hf hg

Depends on / 依赖: Filter, Filter.prod_mono, Prod.map_def, Tendsto, map_def, prod_map_map_eq, prod_mono
-/
theorem Tendsto.prodMap {δ : Type*} {f : α -> γ} {g : β -> δ} {a : Filter α} {b : Filter β}
    {c : Filter γ} {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) :
    Tendsto (Prod.map f g) (a ×ˢ b) (c ×ˢ d) := by
  rw [Tendsto]; rw [Prod.map_def]; rw [← prod_map_map_eq]
  exact Filter.prod_mono hf hg

/--
theorem `map_prod` / 定理 `map_prod`

English:
theorem map_prod
  given: (m : α × β -> γ) (f : Filter α) (g : Filter β)
  proof: by
  simp only [Filter.ext_iff, mem_map, mem_prod_iff, mem_map_seq_iff, exists_and_left]
  intro s
  constructor
  · exact fun ⟨t, ht, s, hs, h⟩ => ⟨s, hs, t, ht, fun x hx y hy => @h ⟨x, y⟩ ⟨hx, hy⟩⟩
  · exact fun ⟨s, hs, t, ht, h⟩ => ⟨t, ht, s, hs, fun ⟨x, y⟩ ⟨hx, hy⟩ => h x hx y hy⟩

中文:
定理 map_prod
  条件: (m : α × β -> γ) (f : Filter α) (g : Filter β)
  证明: by
  simp only [Filter.ext_iff, mem_map, mem_prod_iff, mem_map_seq_iff, exists_and_left]
  intro s
  constructor
  · exact fun ⟨t, ht, s, hs, h⟩ => ⟨s, hs, t, ht, fun x hx y hy => @h ⟨x, y⟩ ⟨hx, hy⟩⟩
  · exact fun ⟨s, hs, t, ht, h⟩ => ⟨t, ht, s, hs, fun ⟨x, y⟩ ⟨hx, hy⟩ => h x hx y hy⟩
-/
protected theorem map_prod (m : α × β -> γ) (f : Filter α) (g : Filter β) :
    map m (f ×ˢ g) = (f.map fun a b => m (a, b)).seq g := by
  simp only [Filter.ext_iff, mem_map, mem_prod_iff, mem_map_seq_iff, exists_and_left]
  intro s
  constructor
  · exact fun ⟨t, ht, s, hs, h⟩ => ⟨s, hs, t, ht, fun x hx y hy => @h ⟨x, y⟩ ⟨hx, hy⟩⟩
  · exact fun ⟨s, hs, t, ht, h⟩ => ⟨t, ht, s, hs, fun ⟨x, y⟩ ⟨hx, hy⟩ => h x hx y hy⟩

/--
theorem `prod_eq` / 定理 `prod_eq`

English:
theorem prod_eq
  statement: f ×ˢ g = (f.map Prod.mk).seq g
  proof: f.map_prod id g

中文:
定理 prod_eq
  结论: f ×ˢ g = (f.map Prod.mk).seq g
  证明: f.map_prod id g

Depends on / 依赖: f.map_prod, map_prod
-/
theorem prod_eq : f ×ˢ g = (f.map Prod.mk).seq g := f.map_prod id g

/--
theorem `prod_inf_prod` / 定理 `prod_inf_prod`

English:
theorem prod_inf_prod
  given: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β}
  proof: by
  simp only [prod_eq_inf, comap_inf, inf_comm, inf_assoc, inf_left_comm]

中文:
定理 prod_inf_prod
  条件: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β}
  证明: by
  simp only [prod_eq_inf, comap_inf, inf_comm, inf_assoc, inf_left_comm]

Depends on / 依赖: comap_inf, inf_assoc, inf_comm, inf_left_comm, prod_eq_inf
-/
theorem prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} :
    (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂) := by
  simp only [prod_eq_inf, comap_inf, inf_comm, inf_assoc, inf_left_comm]

/--
theorem `inf_prod` / 定理 `inf_prod`

English:
theorem inf_prod
  given: {f₁ f₂ : Filter α}
  statement: (f₁ ⊓ f₂) ×ˢ g = (f₁ ×ˢ g) ⊓ (f₂ ×ˢ g)
  proof: by
  rw [prod_inf_prod]; rw [inf_idem]

中文:
定理 inf_prod
  条件: {f₁ f₂ : Filter α}
  结论: (f₁ ⊓ f₂) ×ˢ g = (f₁ ×ˢ g) ⊓ (f₂ ×ˢ g)
  证明: by
  rw [prod_inf_prod]; rw [inf_idem]

Depends on / 依赖: inf_idem, prod_inf_prod
-/
theorem inf_prod {f₁ f₂ : Filter α} : (f₁ ⊓ f₂) ×ˢ g = (f₁ ×ˢ g) ⊓ (f₂ ×ˢ g) := by
  rw [prod_inf_prod]; rw [inf_idem]

/--
theorem `prod_inf` / 定理 `prod_inf`

English:
theorem prod_inf
  given: {g₁ g₂ : Filter β}
  statement: f ×ˢ (g₁ ⊓ g₂) = (f ×ˢ g₁) ⊓ (f ×ˢ g₂)
  proof: by
  rw [prod_inf_prod]; rw [inf_idem]

@[simp]

中文:
定理 prod_inf
  条件: {g₁ g₂ : Filter β}
  结论: f ×ˢ (g₁ ⊓ g₂) = (f ×ˢ g₁) ⊓ (f ×ˢ g₂)
  证明: by
  rw [prod_inf_prod]; rw [inf_idem]

@[simp]

Depends on / 依赖: inf_idem, prod_inf_prod
-/
theorem prod_inf {g₁ g₂ : Filter β} : f ×ˢ (g₁ ⊓ g₂) = (f ×ˢ g₁) ⊓ (f ×ˢ g₂) := by
  rw [prod_inf_prod]; rw [inf_idem]

@[simp]
/--
theorem `prod_principal_principal` / 定理 `prod_principal_principal`

English:
theorem prod_principal_principal
  given: {s : Set α} {t : Set β}
  statement: 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
  proof: by
  simp only [prod_eq_inf, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal]; rfl

@[simp]

中文:
定理 prod_principal_principal
  条件: {s : Set α} {t : Set β}
  结论: 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
  证明: by
  simp only [prod_eq_inf, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal]; rfl

@[simp]

Depends on / 依赖: comap_principal, inf_principal, principal_eq_iff_eq, prod_eq_inf
-/
theorem prod_principal_principal {s : Set α} {t : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t) := by
  simp only [prod_eq_inf, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal]; rfl

@[simp]
/--
theorem `pure_prod` / 定理 `pure_prod`

English:
theorem pure_prod
  given: {a : α} {f : Filter β}
  statement: pure a ×ˢ f = map (Prod.mk a) f
  proof: by
  rw [prod_eq]; rw [map_pure]; rw [pure_seq_eq_map]

中文:
定理 pure_prod
  条件: {a : α} {f : Filter β}
  结论: pure a ×ˢ f = map (Prod.mk a) f
  证明: by
  rw [prod_eq]; rw [map_pure]; rw [pure_seq_eq_map]

Depends on / 依赖: map_pure, prod_eq, pure_seq_eq_map
-/
theorem pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (Prod.mk a) f := by
  rw [prod_eq]; rw [map_pure]; rw [pure_seq_eq_map]

/--
theorem `map_pure_prod` / 定理 `map_pure_prod`

English:
theorem map_pure_prod
  given: (f : α -> β -> γ) (a : α) (B : Filter β)
  proof: by
  rw [Filter.pure_prod]; rfl

@[simp]

中文:
定理 map_pure_prod
  条件: (f : α -> β -> γ) (a : α) (B : Filter β)
  证明: by
  rw [Filter.pure_prod]; rfl

@[simp]

Depends on / 依赖: Filter, Filter.pure_prod, pure_prod
-/
theorem map_pure_prod (f : α -> β -> γ) (a : α) (B : Filter β) :
    map (Function.uncurry f) (pure a ×ˢ B) = map (f a) B := by
  rw [Filter.pure_prod]; rfl

@[simp]
/--
theorem `prod_pure` / 定理 `prod_pure`

English:
theorem prod_pure
  given: {b : β}
  statement: f ×ˢ pure b = map (fun a => (a, b)) f
  proof: by
  rw [prod_eq]; rw [seq_pure]; rw [map_map]; rfl

中文:
定理 prod_pure
  条件: {b : β}
  结论: f ×ˢ pure b = map (fun a => (a, b)) f
  证明: by
  rw [prod_eq]; rw [seq_pure]; rw [map_map]; rfl

Depends on / 依赖: map_map, prod_eq, seq_pure
-/
theorem prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)) f := by
  rw [prod_eq]; rw [seq_pure]; rw [map_map]; rfl

/--
theorem `prod_pure_pure` / 定理 `prod_pure_pure`

English:
theorem prod_pure_pure
  given: {a : α} {b : β}
  proof: by simp

@[simp]

中文:
定理 prod_pure_pure
  条件: {a : α} {b : β}
  证明: by simp

@[simp]
-/
theorem prod_pure_pure {a : α} {b : β} :
    (pure a : Filter α) ×ˢ (pure b : Filter β) = pure (a, b) := by simp

@[simp]
/--
theorem `prod_eq_bot` / 定理 `prod_eq_bot`

English:
theorem prod_eq_bot
  statement: f ×ˢ g = ⊥ ↔ f = ⊥ ∨ g = ⊥
  proof: by
  simp_rw [← empty_mem_iff_bot, mem_prod_iff, subset_empty_iff, prod_eq_empty_iff, ← exists_prop,
    Subtype.exists', exists_or, exists_const, Subtype.exists, exists_prop, exists_eq_right]

中文:
定理 prod_eq_bot
  结论: f ×ˢ g = ⊥ ↔ f = ⊥ ∨ g = ⊥
  证明: by
  simp_rw [← empty_mem_iff_bot, mem_prod_iff, subset_empty_iff, prod_eq_empty_iff, ← exists_prop,
    Subtype.exists', exists_or, exists_const, Subtype.exists, exists_prop, exists_eq_right]

Depends on / 依赖: Subtype, Subtype.exists, empty_mem_iff_bot, exists_const, exists_eq_right, exists_or, exists_prop, mem_prod_iff, prod_eq_empty_iff, simp_rw, subset_empty_iff
-/
theorem prod_eq_bot : f ×ˢ g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := by
  simp_rw [← empty_mem_iff_bot, mem_prod_iff, subset_empty_iff, prod_eq_empty_iff, ← exists_prop,
    Subtype.exists', exists_or, exists_const, Subtype.exists, exists_prop, exists_eq_right]

/--
theorem `prod_bot` / 定理 `prod_bot`

English:
theorem prod_bot
  statement: f ×ˢ (⊥ : Filter β) = ⊥
  proof: prod_eq_bot.2 Or.inr rfl

中文:
定理 prod_bot
  结论: f ×ˢ (⊥ : Filter β) = ⊥
  证明: prod_eq_bot.2 Or.inr rfl
-/
@[simp] theorem prod_bot : f ×ˢ (⊥ : Filter β) = ⊥ := prod_eq_bot.2 Or.inr rfl

/--
theorem `bot_prod` / 定理 `bot_prod`

English:
theorem bot_prod
  statement: (⊥ : Filter α) ×ˢ g = ⊥
  proof: prod_eq_bot.2 Or.inl rfl

中文:
定理 bot_prod
  结论: (⊥ : Filter α) ×ˢ g = ⊥
  证明: prod_eq_bot.2 Or.inl rfl
-/
@[simp] theorem bot_prod : (⊥ : Filter α) ×ˢ g = ⊥ := prod_eq_bot.2 Or.inl rfl

/--
theorem `prod_neBot` / 定理 `prod_neBot`

English:
theorem prod_neBot
  statement: NeBot (f ×ˢ g) ↔ NeBot f ∧ NeBot g
  proof: by
  simp only [neBot_iff, Ne, prod_eq_bot, not_or]

中文:
定理 prod_neBot
  结论: NeBot (f ×ˢ g) ↔ NeBot f ∧ NeBot g
  证明: by
  simp only [neBot_iff, Ne, prod_eq_bot, not_or]

Depends on / 依赖: neBot_iff, not_or, prod_eq_bot
-/
theorem prod_neBot : NeBot (f ×ˢ g) ↔ NeBot f ∧ NeBot g := by
  simp only [neBot_iff, Ne, prod_eq_bot, not_or]

/--
theorem `NeBot.prod` / 定理 `NeBot.prod`

English:
theorem NeBot.prod
  given: (hf : NeBot f) (hg : NeBot g)
  statement: NeBot (f ×ˢ g)
  proof: prod_neBot.2 ⟨hf, hg⟩

中文:
定理 NeBot.prod
  条件: (hf : NeBot f) (hg : NeBot g)
  结论: NeBot (f ×ˢ g)
  证明: prod_neBot.2 ⟨hf, hg⟩
-/
protected theorem NeBot.prod (hf : NeBot f) (hg : NeBot g) : NeBot (f ×ˢ g) := prod_neBot.2 ⟨hf, hg⟩

/--
Instance `prod.instNeBot` / 实例 `prod.instNeBot`

English:
instance prod.instNeBot
  signature: [hf : NeBot f] [hg : NeBot g]
  body: hf.prod hg

@[simp]

中文:
实例 prod.instNeBot
  签名: [hf : NeBot f] [hg : NeBot g]
  定义体: hf.prod hg

@[simp]

Depends on / 依赖: hf.prod
-/
instance prod.instNeBot [hf : NeBot f] [hg : NeBot g] : NeBot (f ×ˢ g) := hf.prod hg

@[simp]
/--
lemma `disjoint_prod` / 引理 `disjoint_prod`

English:
lemma disjoint_prod
  given: {f' : Filter α} {g' : Filter β}
  proof: by
  simp only [disjoint_iff, prod_inf_prod, prod_eq_bot]

中文:
引理 disjoint_prod
  条件: {f' : Filter α} {g' : Filter β}
  证明: by
  simp only [disjoint_iff, prod_inf_prod, prod_eq_bot]

Depends on / 依赖: disjoint_iff, prod_eq_bot, prod_inf_prod
-/
lemma disjoint_prod {f' : Filter α} {g' : Filter β} :
    Disjoint (f ×ˢ g) (f' ×ˢ g') ↔ Disjoint f f' ∨ Disjoint g g' := by
  simp only [disjoint_iff, prod_inf_prod, prod_eq_bot]

/--
theorem `frequently_prod_and` / 定理 `frequently_prod_and`

English:
theorem frequently_prod_and
  given: {p : α -> Prop} {q : β -> Prop}
  proof: by
  simp only [frequently_iff_neBot, ← prod_neBot, ← prod_inf_prod, prod_principal_principal]
  rfl

中文:
定理 frequently_prod_and
  条件: {p : α -> 命题} {q : β -> 命题}
  证明: by
  simp only [frequently_iff_neBot, ← prod_neBot, ← prod_inf_prod, prod_principal_principal]
  rfl

Depends on / 依赖: frequently_iff_neBot, prod_inf_prod, prod_neBot, prod_principal_principal
-/
theorem frequently_prod_and {p : α -> Prop} {q : β -> Prop} :
    (existsᶠ x in f ×ˢ g, p x.1 ∧ q x.2) ↔ (existsᶠ a in f, p a) ∧ existsᶠ b in g, q b := by
  simp only [frequently_iff_neBot, ← prod_neBot, ← prod_inf_prod, prod_principal_principal]
  rfl

/--
theorem `tendsto_prod_iff` / 定理 `tendsto_prod_iff`

English:
theorem tendsto_prod_iff
  given: {f : α × β -> γ} {x : Filter α} {y : Filter β} {z : Filter γ}
  proof: by
  simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff]

中文:
定理 tendsto_prod_iff
  条件: {f : α × β -> γ} {x : Filter α} {y : Filter β} {z : Filter γ}
  证明: by
  simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff]

Depends on / 依赖: mem_prod_iff, prod_sub_preimage_iff, tendsto_def
-/
theorem tendsto_prod_iff {f : α × β -> γ} {x : Filter α} {y : Filter β} {z : Filter γ} :
    Tendsto f (x ×ˢ y) z ↔ forall W in z, exists U in x, exists V in y, forall x y, x in U -> y in V -> f (x, y) in W := by
  simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff]

/--
theorem `tendsto_prod_iff'` / 定理 `tendsto_prod_iff'`

English:
theorem tendsto_prod_iff'
  given: {g' : Filter γ} {s : α -> β × γ}
  proof: by
  simp only [prod_eq_inf, tendsto_inf, tendsto_comap_iff, Function.comp_def]

中文:
定理 tendsto_prod_iff'
  条件: {g' : Filter γ} {s : α -> β × γ}
  证明: by
  simp only [prod_eq_inf, tendsto_inf, tendsto_comap_iff, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, prod_eq_inf, tendsto_comap_iff, tendsto_inf
-/
theorem tendsto_prod_iff' {g' : Filter γ} {s : α -> β × γ} :
    Tendsto s f (g ×ˢ g') ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n => (s n).2) f g' := by
  simp only [prod_eq_inf, tendsto_inf, tendsto_comap_iff, Function.comp_def]

/--
theorem `le_prod` / 定理 `le_prod`

English:
theorem le_prod
  given: {f : Filter (α × β)} {g : Filter α} {g' : Filter β}
  proof: tendsto_prod_iff'

中文:
定理 le_prod
  条件: {f : Filter (α × β)} {g : Filter α} {g' : Filter β}
  证明: tendsto_prod_iff'

Depends on / 依赖: tendsto_prod_iff
-/
theorem le_prod {f : Filter (α × β)} {g : Filter α} {g' : Filter β} :
    (f <= g ×ˢ g') ↔ Tendsto Prod.fst f g ∧ Tendsto Prod.snd f g' :=
  tendsto_prod_iff'

end Prod

/-! ### Coproducts of filters -/

section Coprod

variable {f : Filter α} {g : Filter β}

/--
theorem `coprod_eq_prod_top_sup_top_prod` / 定理 `coprod_eq_prod_top_sup_top_prod`

English:
theorem coprod_eq_prod_top_sup_top_prod
  given: (f : Filter α) (g : Filter β)
  proof: by
  rw [prod_top]; rw [top_prod]
  rfl

中文:
定理 coprod_eq_prod_top_sup_top_prod
  条件: (f : Filter α) (g : Filter β)
  证明: by
  rw [prod_top]; rw [top_prod]
  rfl

Depends on / 依赖: prod_top, top_prod
-/
theorem coprod_eq_prod_top_sup_top_prod (f : Filter α) (g : Filter β) :
    Filter.coprod f g = f ×ˢ ⊤ ⊔ ⊤ ×ˢ g := by
  rw [prod_top]; rw [top_prod]
  rfl

/--
theorem `mem_coprod_iff` / 定理 `mem_coprod_iff`

English:
theorem mem_coprod_iff
  given: {s : Set (α × β)} {f : Filter α} {g : Filter β}
  proof: by
  simp [Filter.coprod]

@[simp]

中文:
定理 mem_coprod_iff
  条件: {s : Set (α × β)} {f : Filter α} {g : Filter β}
  证明: by
  simp [Filter.coprod]

@[simp]

Depends on / 依赖: Filter, Filter.coprod, coprod
-/
theorem mem_coprod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s in f.coprod g ↔ (exists t₁ in f, Prod.fst ⁻¹' t₁ subseteq s) ∧ exists t₂ in g, Prod.snd ⁻¹' t₂ subseteq s := by
  simp [Filter.coprod]

@[simp]
/--
theorem `bot_coprod` / 定理 `bot_coprod`

English:
theorem bot_coprod
  given: (l : Filter β)
  statement: (⊥ : Filter α).coprod l = comap Prod.snd l
  proof: by
  simp [Filter.coprod]

@[simp]

中文:
定理 bot_coprod
  条件: (l : Filter β)
  结论: (⊥ : Filter α).coprod l = comap Prod.snd l
  证明: by
  simp [Filter.coprod]

@[simp]

Depends on / 依赖: Filter, Filter.coprod, coprod
-/
theorem bot_coprod (l : Filter β) : (⊥ : Filter α).coprod l = comap Prod.snd l := by
  simp [Filter.coprod]

@[simp]
/--
theorem `coprod_bot` / 定理 `coprod_bot`

English:
theorem coprod_bot
  given: (l : Filter α)
  statement: l.coprod (⊥ : Filter β) = comap Prod.fst l
  proof: by
  simp [Filter.coprod]

中文:
定理 coprod_bot
  条件: (l : Filter α)
  结论: l.coprod (⊥ : Filter β) = comap Prod.fst l
  证明: by
  simp [Filter.coprod]

Depends on / 依赖: Filter, Filter.coprod, coprod
-/
theorem coprod_bot (l : Filter α) : l.coprod (⊥ : Filter β) = comap Prod.fst l := by
  simp [Filter.coprod]

/--
theorem `bot_coprod_bot` / 定理 `bot_coprod_bot`

English:
theorem bot_coprod_bot
  statement: (⊥ : Filter α).coprod (⊥ : Filter β) = ⊥
  proof: by simp

中文:
定理 bot_coprod_bot
  结论: (⊥ : Filter α).coprod (⊥ : Filter β) = ⊥
  证明: by simp

Depends on / 依赖: e.symm
-/
theorem bot_coprod_bot : (⊥ : Filter α).coprod (⊥ : Filter β) = ⊥ := by simp

/--
theorem `compl_mem_coprod` / 定理 `compl_mem_coprod`

English:
theorem compl_mem_coprod
  given: {s : Set (α × β)} {la : Filter α} {lb : Filter β}
  proof: by
  simp only [Filter.coprod, mem_sup, compl_mem_comap]

@[gcongr, mono]

中文:
定理 compl_mem_coprod
  条件: {s : Set (α × β)} {la : Filter α} {lb : Filter β}
  证明: by
  simp only [Filter.coprod, mem_sup, compl_mem_comap]

@[gcongr, mono]

Depends on / 依赖: Filter, Filter.coprod, compl_mem_comap, coprod, mem_sup
-/
theorem compl_mem_coprod {s : Set (α × β)} {la : Filter α} {lb : Filter β} :
    sᶜ in la.coprod lb ↔ (Prod.fst '' s)ᶜ in la ∧ (Prod.snd '' s)ᶜ in lb := by
  simp only [Filter.coprod, mem_sup, compl_mem_comap]

@[gcongr, mono]
/--
theorem `coprod_mono` / 定理 `coprod_mono`

English:
theorem coprod_mono
  given: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  proof: sup_le_sup (comap_mono hf) (comap_mono hg)

中文:
定理 coprod_mono
  条件: {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  证明: sup_le_sup (comap_mono hf) (comap_mono hg)

Depends on / 依赖: comap_mono, sup_le_sup
-/
theorem coprod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ <= f₂) (hg : g₁ <= g₂) :
    f₁.coprod g₁ <= f₂.coprod g₂ :=
  sup_le_sup (comap_mono hf) (comap_mono hg)

/--
theorem `coprod_neBot_iff` / 定理 `coprod_neBot_iff`

English:
theorem coprod_neBot_iff
  statement: (f.coprod g).NeBot ↔ f.NeBot ∧ Nonempty β ∨ Nonempty α ∧ g.NeBot
  proof: by
  simp [Filter.coprod]

@[instance]

中文:
定理 coprod_neBot_iff
  结论: (f.coprod g).NeBot ↔ f.NeBot ∧ Nonempty β ∨ Nonempty α ∧ g.NeBot
  证明: by
  simp [Filter.coprod]

@[instance]

Depends on / 依赖: Filter, Filter.coprod, coprod
-/
theorem coprod_neBot_iff : (f.coprod g).NeBot ↔ f.NeBot ∧ Nonempty β ∨ Nonempty α ∧ g.NeBot := by
  simp [Filter.coprod]

@[instance]
/--
theorem `coprod_neBot_left` / 定理 `coprod_neBot_left`

English:
theorem coprod_neBot_left
  given: [NeBot f] [Nonempty β]
  statement: (f.coprod g).NeBot
  proof: coprod_neBot_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

@[instance]

中文:
定理 coprod_neBot_left
  条件: [NeBot f] [Nonempty β]
  结论: (f.coprod g).NeBot
  证明: coprod_neBot_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

@[instance]

Depends on / 依赖: Or.inl, coprod_neBot_iff
-/
theorem coprod_neBot_left [NeBot f] [Nonempty β] : (f.coprod g).NeBot :=
  coprod_neBot_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

@[instance]
/--
theorem `coprod_neBot_right` / 定理 `coprod_neBot_right`

English:
theorem coprod_neBot_right
  given: [NeBot g] [Nonempty α]
  statement: (f.coprod g).NeBot
  proof: coprod_neBot_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

中文:
定理 coprod_neBot_right
  条件: [NeBot g] [Nonempty α]
  结论: (f.coprod g).NeBot
  证明: coprod_neBot_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

Depends on / 依赖: Or.inr, coprod_neBot_iff
-/
theorem coprod_neBot_right [NeBot g] [Nonempty α] : (f.coprod g).NeBot :=
  coprod_neBot_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `coprod_inf_prod_le` / 定理 `coprod_inf_prod_le`

English:
theorem coprod_inf_prod_le
  given: (f₁ f₂ : Filter α) (g₁ g₂ : Filter β)
  proof: calc
  f₁.coprod g₁ ⊓ f₂ ×ˢ g₂
  _ = (f₁ ×ˢ ⊤ ⊔ ⊤ ×ˢ g₁) ⊓ f₂ ×ˢ g₂ := by rw [coprod_eq_prod_top_sup_top_prod]
  _ = f₁ ×ˢ ⊤ ⊓ f₂ ×ˢ g₂ ⊔ ⊤ ×ˢ g₁ ⊓ f₂ ×ˢ g₂ := inf_sup_right _ _ _
  _ = (f₁ ⊓ f₂) ×ˢ g₂ ⊔ f₂ ×ˢ (g₁ ⊓ g₂) := by simp [prod_inf_prod]
  _ <= f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁ :=
    sup_le_sup (prod_mo

中文:
定理 coprod_inf_prod_le
  条件: (f₁ f₂ : Filter α) (g₁ g₂ : Filter β)
  证明: calc
  f₁.coprod g₁ ⊓ f₂ ×ˢ g₂
  _ = (f₁ ×ˢ ⊤ ⊔ ⊤ ×ˢ g₁) ⊓ f₂ ×ˢ g₂ := by rw [coprod_eq_prod_top_sup_top_prod]
  _ = f₁ ×ˢ ⊤ ⊓ f₂ ×ˢ g₂ ⊔ ⊤ ×ˢ g₁ ⊓ f₂ ×ˢ g₂ := inf_sup_right _ _ _
  _ = (f₁ ⊓ f₂) ×ˢ g₂ ⊔ f₂ ×ˢ (g₁ ⊓ g₂) := by simp [prod_inf_prod]
  _ <= f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁ :=
    sup_le_sup (prod_mo
-/
theorem coprod_inf_prod_le (f₁ f₂ : Filter α) (g₁ g₂ : Filter β) :
    f₁.coprod g₁ ⊓ f₂ ×ˢ g₂ <= f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁ := calc
  f₁.coprod g₁ ⊓ f₂ ×ˢ g₂
  _ = (f₁ ×ˢ ⊤ ⊔ ⊤ ×ˢ g₁) ⊓ f₂ ×ˢ g₂ := by rw [coprod_eq_prod_top_sup_top_prod]
  _ = f₁ ×ˢ ⊤ ⊓ f₂ ×ˢ g₂ ⊔ ⊤ ×ˢ g₁ ⊓ f₂ ×ˢ g₂ := inf_sup_right _ _ _
  _ = (f₁ ⊓ f₂) ×ˢ g₂ ⊔ f₂ ×ˢ (g₁ ⊓ g₂) := by simp [prod_inf_prod]
  _ <= f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁ :=
    sup_le_sup (prod_mono inf_le_left le_rfl) (prod_mono le_rfl inf_le_left)

/--
theorem `principal_coprod_principal` / 定理 `principal_coprod_principal`

English:
theorem principal_coprod_principal
  given: (s : Set α) (t : Set β)
  proof: by
  rw [Filter.coprod]; rw [comap_principal]; rw [comap_principal]; rw [sup_principal]; rw [Set.prod_eq]; rw [compl_inter]; rw [preimage_compl]; rw [preimage_compl]; rw [compl_compl]; rw [compl_compl]

中文:
定理 principal_coprod_principal
  条件: (s : Set α) (t : Set β)
  证明: by
  rw [Filter.coprod]; rw [comap_principal]; rw [comap_principal]; rw [sup_principal]; rw [Set.prod_eq]; rw [compl_inter]; rw [preimage_compl]; rw [preimage_compl]; rw [compl_compl]; rw [compl_compl]

Depends on / 依赖: Filter, Filter.coprod, Set.prod_eq, comap_principal, compl_compl, compl_inter, coprod, preimage_compl, prod_eq, sup_principal
-/
theorem principal_coprod_principal (s : Set α) (t : Set β) :
    (𝓟 s).coprod (𝓟 t) = 𝓟 (sᶜ ×ˢ tᶜ)ᶜ := by
  rw [Filter.coprod]; rw [comap_principal]; rw [comap_principal]; rw [sup_principal]; rw [Set.prod_eq]; rw [compl_inter]; rw [preimage_compl]; rw [preimage_compl]; rw [compl_compl]; rw [compl_compl]

-- this inequality can be strict; see `map_const_principal_coprod_map_id_principal` and
-- `map_prodMap_const_id_principal_coprod_principal` below.
/--
theorem `map_prodMap_coprod_le.` / 定理 `map_prodMap_coprod_le.`

English:
theorem map_prodMap_coprod_le.{u,
  given: v, w, x} {α₁
  statement: Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  proof: by
  intro s
  simp only [mem_map, mem_coprod_iff]
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩
  refine ⟨⟨m₁ ⁻¹' u₁, hu₁, fun _ hx => h₁ ?_⟩, ⟨m₂ ⁻¹' u₂, hu₂, fun _ hx => h₂ ?_⟩⟩ <;> convert!
    hx

中文:
定理 map_prodMap_coprod_le.{u,
  条件: v, w, x} {α₁
  结论: 类型u} {α₂ : 类型v} {β₁ : Type w} {β₂ : Type x}
  证明: by
  intro s
  simp only [mem_map, mem_coprod_iff]
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩
  refine ⟨⟨m₁ ⁻¹' u₁, hu₁, fun _ hx => h₁ ?_⟩, ⟨m₂ ⁻¹' u₂, hu₂, fun _ hx => h₂ ?_⟩⟩ <;> convert!
    hx

Depends on / 依赖: convert, mem_coprod_iff, mem_map
-/
theorem map_prodMap_coprod_le.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ -> β₁} {m₂ : α₂ -> β₂} :
    map (Prod.map m₁ m₂) (f₁.coprod f₂) <= (map m₁ f₁).coprod (map m₂ f₂) := by
  intro s
  simp only [mem_map, mem_coprod_iff]
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩
  refine ⟨⟨m₁ ⁻¹' u₁, hu₁, fun _ hx => h₁ ?_⟩, ⟨m₂ ⁻¹' u₂, hu₂, fun _ hx => h₂ ?_⟩⟩ <;> convert!
    hx

/--
theorem `map_const_principal_coprod_map_id_principal` / 定理 `map_const_principal_coprod_map_id_principal`

English:
theorem map_const_principal_coprod_map_id_principal
  given: {α β ι : Type*} (a : α) (b : β) (i : ι)
  proof: by
  simp only [map_principal, Filter.coprod, comap_principal, sup_principal, image_singleton,
    prod_univ, univ_prod, id]

中文:
定理 map_const_principal_coprod_map_id_principal
  条件: {α β ι : 类型} (a : α) (b : β) (i : ι)
  证明: by
  simp only [map_principal, Filter.coprod, comap_principal, sup_principal, image_singleton,
    prod_univ, univ_prod, id]

Depends on / 依赖: Filter, Filter.coprod, comap_principal, coprod, image_singleton, map_principal, prod_univ, sup_principal, univ_prod
-/
theorem map_const_principal_coprod_map_id_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
    (map (fun _ => b) (𝓟 {a})).coprod (map id (𝓟 {i})) =
      𝓟 ((({b} : Set β) ×ˢ univ) union (univ ×ˢ ({i} : Set ι))) := by
  simp only [map_principal, Filter.coprod, comap_principal, sup_principal, image_singleton,
    prod_univ, univ_prod, id]

/--
theorem `map_prodMap_const_id_principal_coprod_principal` / 定理 `map_prodMap_const_id_principal_coprod_principal`

English:
theorem map_prodMap_const_id_principal_coprod_principal
  given: {α β ι : Type*} (a : α) (b : β) (i : ι)
  proof: by
  rw [principal_coprod_principal]; rw [map_principal]
  congr
  ext ⟨b', i'⟩
  constructor
  · rintro ⟨⟨a'', i''⟩, _, h₂, h₃⟩
    simp
  · rintro ⟨h₁, _⟩
    use (a, i')
    simpa using h₁.symm

中文:
定理 map_prodMap_const_id_principal_coprod_principal
  条件: {α β ι : 类型} (a : α) (b : β) (i : ι)
  证明: by
  rw [principal_coprod_principal]; rw [map_principal]
  congr
  ext ⟨b', i'⟩
  constructor
  · rintro ⟨⟨a'', i''⟩, _, h₂, h₃⟩
    simp
  · rintro ⟨h₁, _⟩
    use (a, i')
    simpa using h₁.symm

Depends on / 依赖: map_principal, principal_coprod_principal
-/
theorem map_prodMap_const_id_principal_coprod_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
    map (Prod.map (fun _ : α => b) id) ((𝓟 {a}).coprod (𝓟 {i})) =
      𝓟 (({b} : Set β) ×ˢ (univ : Set ι)) := by
  rw [principal_coprod_principal]; rw [map_principal]
  congr
  ext ⟨b', i'⟩
  constructor
  · rintro ⟨⟨a'', i''⟩, _, h₂, h₃⟩
    simp
  · rintro ⟨h₁, _⟩
    use (a, i')
    simpa using h₁.symm

/--
theorem `Tendsto.prodMap_coprod` / 定理 `Tendsto.prodMap_coprod`

English:
theorem Tendsto.prodMap_coprod
  statement: {δ : Type*} {f : α -> γ} {g : β -> δ} {a : Filter α} {b : Filter β}
  proof: map_prodMap_coprod_le.trans (coprod_mono hf hg)

中文:
定理 Tendsto.prodMap_coprod
  结论: {δ : 类型} {f : α -> γ} {g : β -> δ} {a : Filter α} {b : Filter β}
  证明: map_prodMap_coprod_le.trans (coprod_mono hf hg)

Depends on / 依赖: coprod_mono, map_prodMap_coprod_le, map_prodMap_coprod_le.trans
-/
theorem Tendsto.prodMap_coprod {δ : Type*} {f : α -> γ} {g : β -> δ} {a : Filter α} {b : Filter β}
    {c : Filter γ} {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) :
    Tendsto (Prod.map f g) (a.coprod b) (c.coprod d) :=
  map_prodMap_coprod_le.trans (coprod_mono hf hg)

/--
lemma `Tendsto.coprod_of_prod_top_right` / 引理 `Tendsto.coprod_of_prod_top_right`

English:
lemma Tendsto.coprod_of_prod_top_right
  statement: {f : α × β -> γ} {la : Filter α} {lb : Filter β}
  proof: by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

中文:
引理 Tendsto.coprod_of_prod_top_right
  结论: {f : α × β -> γ} {la : Filter α} {lb : Filter β}
  证明: by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

Depends on / 依赖: coprod_eq_prod_top_sup_top_prod, tendsto_prod_iff
-/
lemma Tendsto.coprod_of_prod_top_right {f : α × β -> γ} {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (h₁ : forall s : Set α, s in la -> Tendsto f (𝓟 sᶜ ×ˢ lb) lc)
    (h₂ : Tendsto f (la ×ˢ ⊤) lc) :
    Tendsto f (la.coprod lb) lc := by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

/--
lemma `Tendsto.coprod_of_prod_top_left` / 引理 `Tendsto.coprod_of_prod_top_left`

English:
lemma Tendsto.coprod_of_prod_top_left
  statement: {f : α × β -> γ} {la : Filter α} {lb : Filter β}
  proof: by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

中文:
引理 Tendsto.coprod_of_prod_top_left
  结论: {f : α × β -> γ} {la : Filter α} {lb : Filter β}
  证明: by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

Depends on / 依赖: coprod_eq_prod_top_sup_top_prod, tendsto_prod_iff
-/
lemma Tendsto.coprod_of_prod_top_left {f : α × β -> γ} {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (h₁ : forall s : Set β, s in lb -> Tendsto f (la ×ˢ 𝓟 sᶜ) lc)
    (h₂ : Tendsto f (⊤ ×ˢ lb) lc) :
    Tendsto f (la.coprod lb) lc := by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

end Coprod

end Filter
