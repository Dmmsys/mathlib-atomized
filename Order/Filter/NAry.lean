/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Filter.Bases.Basic
public import Mathlib.Order.Filter.Prod

/-!
# N-ary maps of filter

This file defines the binary and ternary maps of filters. This is mostly useful to define pointwise
operations on filters.

## Main declarations

* `Filter.map₂`: Binary map of filters.

## Notes

This file is very similar to `Mathlib/Data/Set/NAry.lean`, `Mathlib/Data/Finset/NAry.lean` and
`Mathlib/Data/Option/NAry.lean`. Please keep them in sync.
-/

@[expose] public section


open Function Set

open Filter

namespace Filter

variable {α α' β β' γ γ' δ δ' ε ε' : Type*} {m : α -> β -> γ} {f f₁ f₂ : Filter α}
  {g g₁ g₂ : Filter β} {h : Filter γ} {s : Set α} {t : Set β} {u : Set γ}
  {a : α} {b : β}

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (m : α -> β -> γ) (f : Filter α) (g : Filter β)
  body: ((f ×ˢ g).map (uncurry m)).copy { s | exists u in f, exists v in g, image2 m u v subseteq s } fun _ => by
    simp only [mem_map, mem_prod_iff, image2_subset_iff, prod_subset_iff]; rfl

@[simp 900]

中文:
定义 map₂
  签名: (m : α -> β -> γ) (f : 滤子 α) (g : 滤子 β)
  定义体: ((f ×ˢ g).map (uncurry m)).copy { s | exists u in f, exists v in g, image2 m u v subseteq s } fun _ => by
    simp only [mem_map, mem_prod_iff, image2_subset_iff, prod_subset_iff]; rfl

@[simp 900]

Depends on / 依赖: image2, image2_subset_iff, mem_map, mem_prod_iff, prod_subset_iff, subseteq, uncurry
-/
def map₂ (m : α -> β -> γ) (f : Filter α) (g : Filter β) : Filter γ :=
  ((f ×ˢ g).map (uncurry m)).copy { s | exists u in f, exists v in g, image2 m u v subseteq s } fun _ => by
    simp only [mem_map, mem_prod_iff, image2_subset_iff, prod_subset_iff]; rfl

@[simp 900]
/--
theorem `mem_map₂_iff` / 定理 `mem_map₂_iff`

English:
theorem mem_map₂_iff
  statement: u in map₂ m f g ↔ exists s in f, exists t in g, image2 m s t subseteq u
  proof: Iff.rfl

中文:
定理 mem_map₂_iff
  结论: u in map₂ m f g ↔ 存在 s in f, 存在 t in g, image2 m s t subseteq u
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_map₂_iff : u in map₂ m f g ↔ exists s in f, exists t in g, image2 m s t subseteq u :=
  Iff.rfl

/--
theorem `image2_mem_map₂` / 定理 `image2_mem_map₂`

English:
theorem image2_mem_map₂
  given: (hs : s in f) (ht : t in g)
  statement: image2 m s t in map₂ m f g
  proof: ⟨_, hs, _, ht, Subset.rfl⟩

中文:
定理 image2_mem_map₂
  条件: (hs : s in f) (ht : t in g)
  结论: image2 m s t in map₂ m f g
  证明: ⟨_, hs, _, ht, Subset.rfl⟩

Depends on / 依赖: Subset, Subset.rfl
-/
theorem image2_mem_map₂ (hs : s in f) (ht : t in g) : image2 m s t in map₂ m f g :=
  ⟨_, hs, _, ht, Subset.rfl⟩

/--
theorem `map_prod_eq_map₂` / 定理 `map_prod_eq_map₂`

English:
theorem map_prod_eq_map₂
  given: (m : α -> β -> γ) (f : Filter α) (g : Filter β)
  proof: by
  rw [map₂]; rw [copy_eq]; rw [uncurry_def]

中文:
定理 map_prod_eq_map₂
  条件: (m : α -> β -> γ) (f : 滤子 α) (g : 滤子 β)
  证明: by
  rw [map₂]; rw [copy_eq]; rw [uncurry_def]

Depends on / 依赖: copy_eq, uncurry_def
-/
theorem map_prod_eq_map₂ (m : α -> β -> γ) (f : Filter α) (g : Filter β) :
    Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f g := by
  rw [map₂]; rw [copy_eq]; rw [uncurry_def]

/--
theorem `map_prod_eq_map₂'` / 定理 `map_prod_eq_map₂'`

English:
theorem map_prod_eq_map₂'
  given: (m : α × β -> γ) (f : Filter α) (g : Filter β)
  proof: map_prod_eq_map₂ m.curry f g

@[simp]

中文:
定理 map_prod_eq_map₂'
  条件: (m : α × β -> γ) (f : 滤子 α) (g : 滤子 β)
  证明: map_prod_eq_map₂ m.curry f g

@[simp]

Depends on / 依赖: m.curry
-/
theorem map_prod_eq_map₂' (m : α × β -> γ) (f : Filter α) (g : Filter β) :
    Filter.map m (f ×ˢ g) = map₂ (fun a b => m (a, b)) f g :=
  map_prod_eq_map₂ m.curry f g

@[simp]
/--
theorem `map₂_mk_eq_prod` / 定理 `map₂_mk_eq_prod`

English:
theorem map₂_mk_eq_prod
  given: (f : Filter α) (g : Filter β)
  statement: map₂ Prod.mk f g = f ×ˢ g
  proof: by
  simp only [← map_prod_eq_map₂, map_id']

中文:
定理 map₂_mk_eq_prod
  条件: (f : 滤子 α) (g : 滤子 β)
  结论: map₂ 积类型.mk f g = f ×ˢ g
  证明: by
  simp only [← map_prod_eq_map₂, map_id']

Depends on / 依赖: map_id
-/
theorem map₂_mk_eq_prod (f : Filter α) (g : Filter β) : map₂ Prod.mk f g = f ×ˢ g := by
  simp only [← map_prod_eq_map₂, map_id']

/--
lemma `HasBasis.map₂` / 引理 `HasBasis.map₂`

English:
lemma HasBasis.map₂
  statement: {ι ι' : Type*} {p : ι -> Prop} {q : ι' -> Prop} {s t}
  proof: by
  simpa only [← map_prod_eq_map₂, ← image_prod] using (hf.prod hg).map _

中文:
引理 有基.map₂
  结论: {ι ι' : 类型} {p : ι -> 命题} {q : ι' -> 命题} {s t}
  证明: by
  simpa only [← map_prod_eq_map₂, ← image_prod] using (hf.prod hg).map _
-/
protected lemma HasBasis.map₂ {ι ι' : Type*} {p : ι -> Prop} {q : ι' -> Prop} {s t}
    (m : α -> β -> γ) (hf : f.HasBasis p s) (hg : g.HasBasis q t) :
    (map₂ m f g).HasBasis (fun i : ι × ι' => p i.1 ∧ q i.2) fun i => image2 m (s i.1) (t i.2) := by
  simpa only [← map_prod_eq_map₂, ← image_prod] using (hf.prod hg).map _

-- lemma image2_mem_map₂_iff (hm : injective2 m) : image2 m s t ∈ map₂ m f g ↔ s ∈ f ∧ t ∈ g :=
-- ⟨by { rintro ⟨u, v, hu, hv, h⟩, rw image2_subset_image2_iff hm at h,
-- exact ⟨mem_of_superset hu h.1, mem_of_superset hv h.2⟩ }, fun h ↦ image2_mem_map₂ h.1 h.2⟩
@[gcongr]
/--
theorem `map₂_mono` / 定理 `map₂_mono`

English:
theorem map₂_mono
  given: (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  statement: map₂ m f₁ g₁ <= map₂ m f₂ g₂
  proof: fun _ ⟨s, hs, t, ht, hst⟩ => ⟨s, hf hs, t, hg ht, hst⟩

中文:
定理 map₂_mono
  条件: (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  结论: map₂ m f₁ g₁ <= map₂ m f₂ g₂
  证明: fun _ ⟨s, hs, t, ht, hst⟩ => ⟨s, hf hs, t, hg ht, hst⟩
-/
theorem map₂_mono (hf : f₁ <= f₂) (hg : g₁ <= g₂) : map₂ m f₁ g₁ <= map₂ m f₂ g₂ :=
  fun _ ⟨s, hs, t, ht, hst⟩ => ⟨s, hf hs, t, hg ht, hst⟩

/--
theorem `map₂_mono_left` / 定理 `map₂_mono_left`

English:
theorem map₂_mono_left
  given: (h : g₁ <= g₂)
  statement: map₂ m f g₁ <= map₂ m f g₂
  proof: map₂_mono Subset.rfl h

中文:
定理 map₂_mono_left
  条件: (h : g₁ <= g₂)
  结论: map₂ m f g₁ <= map₂ m f g₂
  证明: map₂_mono Subset.rfl h

Depends on / 依赖: Subset, Subset.rfl
-/
theorem map₂_mono_left (h : g₁ <= g₂) : map₂ m f g₁ <= map₂ m f g₂ :=
  map₂_mono Subset.rfl h

/--
theorem `map₂_mono_right` / 定理 `map₂_mono_right`

English:
theorem map₂_mono_right
  given: (h : f₁ <= f₂)
  statement: map₂ m f₁ g <= map₂ m f₂ g
  proof: map₂_mono h Subset.rfl

@[simp]

中文:
定理 map₂_mono_right
  条件: (h : f₁ <= f₂)
  结论: map₂ m f₁ g <= map₂ m f₂ g
  证明: map₂_mono h Subset.rfl

@[simp]

Depends on / 依赖: Subset, Subset.rfl
-/
theorem map₂_mono_right (h : f₁ <= f₂) : map₂ m f₁ g <= map₂ m f₂ g :=
  map₂_mono h Subset.rfl

@[simp]
/--
theorem `le_map₂_iff` / 定理 `le_map₂_iff`

English:
theorem le_map₂_iff
  given: {h : Filter γ}
  proof: ⟨fun H _ hs _ ht => H image2_mem_map₂ hs ht, fun H _ ⟨_, hs, _, ht, hu⟩ =>
    mem_of_superset (H hs ht) hu⟩

@[simp]

中文:
定理 le_map₂_iff
  条件: {h : 滤子 γ}
  证明: ⟨fun H _ hs _ ht => H image2_mem_map₂ hs ht, fun H _ ⟨_, hs, _, ht, hu⟩ =>
    mem_of_superset (H hs ht) hu⟩

@[simp]

Depends on / 依赖: mem_of_superset
-/
theorem le_map₂_iff {h : Filter γ} :
    h <= map₂ m f g ↔ forall ⦃s⦄, s in f -> forall ⦃t⦄, t in g -> image2 m s t in h :=
⟨fun H _ hs _ ht => H image2_mem_map₂ hs ht, fun H _ ⟨_, hs, _, ht, hu⟩ =>
    mem_of_superset (H hs ht) hu⟩

@[simp]
/--
theorem `map₂_eq_bot_iff` / 定理 `map₂_eq_bot_iff`

English:
theorem map₂_eq_bot_iff
  statement: map₂ m f g = ⊥ ↔ f = ⊥ ∨ g = ⊥
  proof: by simp [← map_prod_eq_map₂]

@[simp]

中文:
定理 map₂_eq_bot_iff
  结论: map₂ m f g = ⊥ ↔ f = ⊥ ∨ g = ⊥
  证明: by simp [← map_prod_eq_map₂]

@[simp]
-/
theorem map₂_eq_bot_iff : map₂ m f g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := by simp [← map_prod_eq_map₂]

@[simp]
/--
theorem `map₂_bot_left` / 定理 `map₂_bot_left`

English:
theorem map₂_bot_left
  statement: map₂ m ⊥ g = ⊥
  proof: map₂_eq_bot_iff.2 .inl rfl

@[simp]

中文:
定理 map₂_bot_left
  结论: map₂ m ⊥ g = ⊥
  证明: map₂_eq_bot_iff.2 .inl rfl

@[simp]
-/
theorem map₂_bot_left : map₂ m ⊥ g = ⊥ := map₂_eq_bot_iff.2 .inl rfl

@[simp]
/--
theorem `map₂_bot_right` / 定理 `map₂_bot_right`

English:
theorem map₂_bot_right
  statement: map₂ m f ⊥ = ⊥
  proof: map₂_eq_bot_iff.2 .inr rfl

@[simp]

中文:
定理 map₂_bot_right
  结论: map₂ m f ⊥ = ⊥
  证明: map₂_eq_bot_iff.2 .inr rfl

@[simp]
-/
theorem map₂_bot_right : map₂ m f ⊥ = ⊥ := map₂_eq_bot_iff.2 .inr rfl

@[simp]
/--
theorem `map₂_neBot_iff` / 定理 `map₂_neBot_iff`

English:
theorem map₂_neBot_iff
  statement: (map₂ m f g).NeBot ↔ f.NeBot ∧ g.NeBot
  proof: by simp [neBot_iff, not_or]

中文:
定理 map₂_neBot_iff
  结论: (map₂ m f g).NeBot ↔ f.NeBot ∧ g.NeBot
  证明: by simp [neBot_iff, not_or]

Depends on / 依赖: neBot_iff, not_or
-/
theorem map₂_neBot_iff : (map₂ m f g).NeBot ↔ f.NeBot ∧ g.NeBot := by simp [neBot_iff, not_or]

/--
theorem `NeBot.map₂` / 定理 `NeBot.map₂`

English:
theorem NeBot.map₂
  given: (hf : f.NeBot) (hg : g.NeBot)
  statement: (map₂ m f g).NeBot
  proof: map₂_neBot_iff.2 ⟨hf, hg⟩

中文:
定理 NeBot.map₂
  条件: (hf : f.NeBot) (hg : g.NeBot)
  结论: (map₂ m f g).NeBot
  证明: map₂_neBot_iff.2 ⟨hf, hg⟩
-/
protected theorem NeBot.map₂ (hf : f.NeBot) (hg : g.NeBot) : (map₂ m f g).NeBot :=
  map₂_neBot_iff.2 ⟨hf, hg⟩

/--
Instance `map₂.neBot` / 实例 `map₂.neBot`

English:
instance map₂.neBot
  signature: [NeBot f] [NeBot g]
  body: .map₂ ‹_› ‹_›

中文:
实例 map₂.neBot
  签名: [NeBot f] [NeBot g]
  定义体: .map₂ ‹_› ‹_›
-/
instance map₂.neBot [NeBot f] [NeBot g] : NeBot (map₂ m f g) := .map₂ ‹_› ‹_›

/--
theorem `NeBot.of_map₂_left` / 定理 `NeBot.of_map₂_left`

English:
theorem NeBot.of_map₂_left
  given: (h : (map₂ m f g).NeBot)
  statement: f.NeBot
  proof: (map₂_neBot_iff.1 h).1

中文:
定理 NeBot.of_map₂_left
  条件: (h : (map₂ m f g).NeBot)
  结论: f.NeBot
  证明: (map₂_neBot_iff.1 h).1
-/
theorem NeBot.of_map₂_left (h : (map₂ m f g).NeBot) : f.NeBot :=
  (map₂_neBot_iff.1 h).1

/--
theorem `NeBot.of_map₂_right` / 定理 `NeBot.of_map₂_right`

English:
theorem NeBot.of_map₂_right
  given: (h : (map₂ m f g).NeBot)
  statement: g.NeBot
  proof: (map₂_neBot_iff.1 h).2

中文:
定理 NeBot.of_map₂_right
  条件: (h : (map₂ m f g).NeBot)
  结论: g.NeBot
  证明: (map₂_neBot_iff.1 h).2
-/
theorem NeBot.of_map₂_right (h : (map₂ m f g).NeBot) : g.NeBot :=
  (map₂_neBot_iff.1 h).2

/--
theorem `map₂_sup_left` / 定理 `map₂_sup_left`

English:
theorem map₂_sup_left
  statement: map₂ m (f₁ ⊔ f₂) g = map₂ m f₁ g ⊔ map₂ m f₂ g
  proof: by
  simp_rw [← map_prod_eq_map₂, sup_prod, map_sup]

中文:
定理 map₂_sup_left
  结论: map₂ m (f₁ ⊔ f₂) g = map₂ m f₁ g ⊔ map₂ m f₂ g
  证明: by
  simp_rw [← map_prod_eq_map₂, sup_prod, map_sup]

Depends on / 依赖: map_sup, simp_rw, sup_prod
-/
theorem map₂_sup_left : map₂ m (f₁ ⊔ f₂) g = map₂ m f₁ g ⊔ map₂ m f₂ g := by
  simp_rw [← map_prod_eq_map₂, sup_prod, map_sup]

/--
theorem `map₂_sup_right` / 定理 `map₂_sup_right`

English:
theorem map₂_sup_right
  statement: map₂ m f (g₁ ⊔ g₂) = map₂ m f g₁ ⊔ map₂ m f g₂
  proof: by
  simp_rw [← map_prod_eq_map₂, prod_sup, map_sup]

中文:
定理 map₂_sup_right
  结论: map₂ m f (g₁ ⊔ g₂) = map₂ m f g₁ ⊔ map₂ m f g₂
  证明: by
  simp_rw [← map_prod_eq_map₂, prod_sup, map_sup]

Depends on / 依赖: map_sup, prod_sup, simp_rw
-/
theorem map₂_sup_right : map₂ m f (g₁ ⊔ g₂) = map₂ m f g₁ ⊔ map₂ m f g₂ := by
  simp_rw [← map_prod_eq_map₂, prod_sup, map_sup]

/--
theorem `map₂_inf_subset_left` / 定理 `map₂_inf_subset_left`

English:
theorem map₂_inf_subset_left
  statement: map₂ m (f₁ ⊓ f₂) g <= map₂ m f₁ g ⊓ map₂ m f₂ g
  proof: Monotone.map_inf_le (fun _ _ => map₂_mono_right) f₁ f₂

中文:
定理 map₂_inf_subset_left
  结论: map₂ m (f₁ ⊓ f₂) g <= map₂ m f₁ g ⊓ map₂ m f₂ g
  证明: Monotone.map_inf_le (fun _ _ => map₂_mono_right) f₁ f₂

Depends on / 依赖: Monotone, Monotone.map_inf_le, map_inf_le
-/
theorem map₂_inf_subset_left : map₂ m (f₁ ⊓ f₂) g <= map₂ m f₁ g ⊓ map₂ m f₂ g :=
  Monotone.map_inf_le (fun _ _ => map₂_mono_right) f₁ f₂

/--
theorem `map₂_inf_subset_right` / 定理 `map₂_inf_subset_right`

English:
theorem map₂_inf_subset_right
  statement: map₂ m f (g₁ ⊓ g₂) <= map₂ m f g₁ ⊓ map₂ m f g₂
  proof: Monotone.map_inf_le (fun _ _ => map₂_mono_left) g₁ g₂

@[simp]

中文:
定理 map₂_inf_subset_right
  结论: map₂ m f (g₁ ⊓ g₂) <= map₂ m f g₁ ⊓ map₂ m f g₂
  证明: Monotone.map_inf_le (fun _ _ => map₂_mono_left) g₁ g₂

@[simp]

Depends on / 依赖: Monotone, Monotone.map_inf_le, map_inf_le
-/
theorem map₂_inf_subset_right : map₂ m f (g₁ ⊓ g₂) <= map₂ m f g₁ ⊓ map₂ m f g₂ :=
  Monotone.map_inf_le (fun _ _ => map₂_mono_left) g₁ g₂

@[simp]
/--
theorem `map₂_pure_left` / 定理 `map₂_pure_left`

English:
theorem map₂_pure_left
  statement: map₂ m (pure a) g = g.map (m a)
  proof: by
  rw [← map_prod_eq_map₂]; rw [pure_prod]; rw [map_map]; rfl

@[simp]

中文:
定理 map₂_pure_left
  结论: map₂ m (pure a) g = g.map (m a)
  证明: by
  rw [← map_prod_eq_map₂]; rw [pure_prod]; rw [map_map]; rfl

@[simp]

Depends on / 依赖: map_map, pure_prod
-/
theorem map₂_pure_left : map₂ m (pure a) g = g.map (m a) := by
  rw [← map_prod_eq_map₂]; rw [pure_prod]; rw [map_map]; rfl

@[simp]
/--
theorem `map₂_pure_right` / 定理 `map₂_pure_right`

English:
theorem map₂_pure_right
  statement: map₂ m f (pure b) = f.map (m · b)
  proof: by
  rw [← map_prod_eq_map₂]; rw [prod_pure]; rw [map_map]; rfl

中文:
定理 map₂_pure_right
  结论: map₂ m f (pure b) = f.map (m · b)
  证明: by
  rw [← map_prod_eq_map₂]; rw [prod_pure]; rw [map_map]; rfl

Depends on / 依赖: map_map, prod_pure
-/
theorem map₂_pure_right : map₂ m f (pure b) = f.map (m · b) := by
  rw [← map_prod_eq_map₂]; rw [prod_pure]; rw [map_map]; rfl

/--
theorem `map₂_pure` / 定理 `map₂_pure`

English:
theorem map₂_pure
  statement: map₂ m (pure a) (pure b) = pure (m a b)
  proof: by rw [map₂_pure_right, map_pure]

中文:
定理 map₂_pure
  结论: map₂ m (pure a) (pure b) = pure (m a b)
  证明: by rw [map₂_pure_right, map_pure]

Depends on / 依赖: map_pure
-/
theorem map₂_pure : map₂ m (pure a) (pure b) = pure (m a b) := by rw [map₂_pure_right, map_pure]

/--
theorem `map₂_swap` / 定理 `map₂_swap`

English:
theorem map₂_swap
  given: (m : α -> β -> γ) (f : Filter α) (g : Filter β)
  proof: by
  rw [← map_prod_eq_map₂]; rw [prod_comm]; rw [map_map]; rw [← map_prod_eq_map₂]; rw [Function.comp_def]
  simp

@[simp]

中文:
定理 map₂_swap
  条件: (m : α -> β -> γ) (f : 滤子 α) (g : 滤子 β)
  证明: by
  rw [← map_prod_eq_map₂]; rw [prod_comm]; rw [map_map]; rw [← map_prod_eq_map₂]; rw [Function.comp_def]
  simp

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_def, map_map, prod_comm
-/
theorem map₂_swap (m : α -> β -> γ) (f : Filter α) (g : Filter β) :
    map₂ m f g = map₂ (fun a b => m b a) g f := by
  rw [← map_prod_eq_map₂]; rw [prod_comm]; rw [map_map]; rw [← map_prod_eq_map₂]; rw [Function.comp_def]
  simp

@[simp]
/--
theorem `map₂_left` / 定理 `map₂_left`

English:
theorem map₂_left
  given: [NeBot g]
  statement: map₂ (fun x _ => x) f g = f
  proof: by
  rw [← map_prod_eq_map₂]; rw [map_fst_prod]

@[simp]

中文:
定理 map₂_left
  条件: [NeBot g]
  结论: map₂ (fun x _ => x) f g = f
  证明: by
  rw [← map_prod_eq_map₂]; rw [map_fst_prod]

@[simp]

Depends on / 依赖: map_fst_prod
-/
theorem map₂_left [NeBot g] : map₂ (fun x _ => x) f g = f := by
  rw [← map_prod_eq_map₂]; rw [map_fst_prod]

@[simp]
/--
theorem `map₂_right` / 定理 `map₂_right`

English:
theorem map₂_right
  given: [NeBot f]
  statement: map₂ (fun _ y => y) f g = g
  proof: by rw [map₂_swap, map₂_left]

中文:
定理 map₂_right
  条件: [NeBot f]
  结论: map₂ (fun _ y => y) f g = g
  证明: by rw [map₂_swap, map₂_left]
-/
theorem map₂_right [NeBot f] : map₂ (fun _ y => y) f g = g := by rw [map₂_swap, map₂_left]

/--
theorem `map_map₂` / 定理 `map_map₂`

English:
theorem map_map₂
  given: (m : α -> β -> γ) (n : γ -> δ)
  proof: by
  rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [map_map]; rfl

中文:
定理 map_map₂
  条件: (m : α -> β -> γ) (n : γ -> δ)
  证明: by
  rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [map_map]; rfl

Depends on / 依赖: map_map
-/
theorem map_map₂ (m : α -> β -> γ) (n : γ -> δ) :
    (map₂ m f g).map n = map₂ (fun a b => n (m a b)) f g := by
  rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [map_map]; rfl

/--
theorem `map₂_map_left` / 定理 `map₂_map_left`

English:
theorem map₂_map_left
  given: (m : γ -> β -> δ) (n : α -> γ)
  proof: by
  rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [← @map_id _ g]; rw [prod_map_map_eq]; rw [map_map]; rw [map_id]; rfl

中文:
定理 map₂_map_left
  条件: (m : γ -> β -> δ) (n : α -> γ)
  证明: by
  rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [← @map_id _ g]; rw [prod_map_map_eq]; rw [map_map]; rw [map_id]; rfl

Depends on / 依赖: map_id, map_map, prod_map_map_eq
-/
theorem map₂_map_left (m : γ -> β -> δ) (n : α -> γ) :
    map₂ m (f.map n) g = map₂ (fun a b => m (n a) b) f g := by
  rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [← @map_id _ g]; rw [prod_map_map_eq]; rw [map_map]; rw [map_id]; rfl

/--
theorem `map₂_map_right` / 定理 `map₂_map_right`

English:
theorem map₂_map_right
  given: (m : α -> γ -> δ) (n : β -> γ)
  proof: by
  rw [map₂_swap]; rw [map₂_map_left]; rw [map₂_swap]

@[simp]

中文:
定理 map₂_map_right
  条件: (m : α -> γ -> δ) (n : β -> γ)
  证明: by
  rw [map₂_swap]; rw [map₂_map_left]; rw [map₂_swap]

@[simp]

Depends on / 依赖: BialgHomClass, toBialgHomClass
-/
theorem map₂_map_right (m : α -> γ -> δ) (n : β -> γ) :
    map₂ m f (g.map n) = map₂ (fun a b => m a (n b)) f g := by
  rw [map₂_swap]; rw [map₂_map_left]; rw [map₂_swap]

@[simp]
/--
theorem `map₂_curry` / 定理 `map₂_curry`

English:
theorem map₂_curry
  given: (m : α × β -> γ) (f : Filter α) (g : Filter β)
  proof: (map_prod_eq_map₂' _ _ _).symm

@[simp]

中文:
定理 map₂_curry
  条件: (m : α × β -> γ) (f : 滤子 α) (g : 滤子 β)
  证明: (map_prod_eq_map₂' _ _ _).symm

@[simp]
-/
theorem map₂_curry (m : α × β -> γ) (f : Filter α) (g : Filter β) :
    map₂ m.curry f g = (f ×ˢ g).map m :=
  (map_prod_eq_map₂' _ _ _).symm

@[simp]
/--
theorem `map_uncurry_prod` / 定理 `map_uncurry_prod`

English:
theorem map_uncurry_prod
  given: (m : α -> β -> γ) (f : Filter α) (g : Filter β)
  proof: (map₂_curry (uncurry m) f g).symm

中文:
定理 map_uncurry_prod
  条件: (m : α -> β -> γ) (f : 滤子 α) (g : 滤子 β)
  证明: (map₂_curry (uncurry m) f g).symm

Depends on / 依赖: uncurry
-/
theorem map_uncurry_prod (m : α -> β -> γ) (f : Filter α) (g : Filter β) :
    (f ×ˢ g).map (uncurry m) = map₂ m f g :=
  (map₂_curry (uncurry m) f g).symm


/--
theorem `map₂_assoc` / 定理 `map₂_assoc`

English:
theorem map₂_assoc
  statement: {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> ε' -> ε} {n' : β -> γ -> ε'}
  proof: by
  rw [← map_prod_eq_map₂ n]; rw [← map_prod_eq_map₂ n']; rw [map₂_map_left]; rw [map₂_map_right]; rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [← prod_assoc]; rw [map_map]
  simp only [h_assoc, Function.comp_def, Equiv.prodAssoc_apply]

中文:
定理 map₂_assoc
  结论: {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> ε' -> ε} {n' : β -> γ -> ε'}
  证明: by
  rw [← map_prod_eq_map₂ n]; rw [← map_prod_eq_map₂ n']; rw [map₂_map_left]; rw [map₂_map_right]; rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [← prod_assoc]; rw [map_map]
  simp only [h_assoc, Function.comp_def, Equiv.prodAssoc_apply]

Depends on / 依赖: AlgEquivClass, Equiv.prodAssoc_apply, Function, Function.comp_def, comp_def, h_assoc, map_map, prodAssoc_apply, prod_assoc, toAlgEquivClass
-/
theorem map₂_assoc {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> ε' -> ε} {n' : β -> γ -> ε'}
    {h : Filter γ} (h_assoc : forall a b c, m (n a b) c = m' a (n' b c)) :
    map₂ m (map₂ n f g) h = map₂ m' f (map₂ n' g h) := by
  rw [← map_prod_eq_map₂ n]; rw [← map_prod_eq_map₂ n']; rw [map₂_map_left]; rw [map₂_map_right]; rw [← map_prod_eq_map₂]; rw [← map_prod_eq_map₂]; rw [← prod_assoc]; rw [map_map]
  simp only [h_assoc, Function.comp_def, Equiv.prodAssoc_apply]

/--
theorem `map₂_comm` / 定理 `map₂_comm`

English:
theorem map₂_comm
  given: {n : β -> α -> γ} (h_comm : forall a b, m a b = n b a)
  statement: map₂ m f g = map₂ n g f
  proof: (map₂_swap _ _ _).trans by simp_rw [h_comm]

中文:
定理 map₂_comm
  条件: {n : β -> α -> γ} (h_comm : 对任意 a b, m a b = n b a)
  结论: map₂ m f g = map₂ n g f
  证明: (map₂_swap _ _ _).trans by simp_rw [h_comm]

Depends on / 依赖: h_comm, simp_rw
-/
theorem map₂_comm {n : β -> α -> γ} (h_comm : forall a b, m a b = n b a) : map₂ m f g = map₂ n g f :=
(map₂_swap _ _ _).trans by simp_rw [h_comm]

/--
theorem `map₂_left_comm` / 定理 `map₂_left_comm`

English:
theorem map₂_left_comm
  statement: {m : α -> δ -> ε} {n : β -> γ -> δ} {m' : α -> γ -> δ'} {n' : β -> δ' -> ε}
  proof: by
  rw [map₂_swap m']; rw [map₂_swap m]
  exact map₂_assoc fun _ _ _ => h_left_comm _ _ _

中文:
定理 map₂_left_comm
  结论: {m : α -> δ -> ε} {n : β -> γ -> δ} {m' : α -> γ -> δ'} {n' : β -> δ' -> ε}
  证明: by
  rw [map₂_swap m']; rw [map₂_swap m]
  exact map₂_assoc fun _ _ _ => h_left_comm _ _ _

Depends on / 依赖: h_left_comm
-/
theorem map₂_left_comm {m : α -> δ -> ε} {n : β -> γ -> δ} {m' : α -> γ -> δ'} {n' : β -> δ' -> ε}
    (h_left_comm : forall a b c, m a (n b c) = n' b (m' a c)) :
    map₂ m f (map₂ n g h) = map₂ n' g (map₂ m' f h) := by
  rw [map₂_swap m']; rw [map₂_swap m]
  exact map₂_assoc fun _ _ _ => h_left_comm _ _ _

/--
theorem `map₂_right_comm` / 定理 `map₂_right_comm`

English:
theorem map₂_right_comm
  statement: {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> γ -> δ'} {n' : δ' -> β -> ε}
  proof: by
  rw [map₂_swap n]; rw [map₂_swap n']
  exact map₂_assoc fun _ _ _ => h_right_comm _ _ _

中文:
定理 map₂_right_comm
  结论: {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> γ -> δ'} {n' : δ' -> β -> ε}
  证明: by
  rw [map₂_swap n]; rw [map₂_swap n']
  exact map₂_assoc fun _ _ _ => h_right_comm _ _ _

Depends on / 依赖: h_right_comm
-/
theorem map₂_right_comm {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> γ -> δ'} {n' : δ' -> β -> ε}
    (h_right_comm : forall a b c, m (n a b) c = n' (m' a c) b) :
    map₂ m (map₂ n f g) h = map₂ n' (map₂ m' f h) g := by
  rw [map₂_swap n]; rw [map₂_swap n']
  exact map₂_assoc fun _ _ _ => h_right_comm _ _ _

/--
theorem `map_map₂_distrib` / 定理 `map_map₂_distrib`

English:
theorem map_map₂_distrib
  statement: {n : γ -> δ} {m' : α' -> β' -> δ} {n₁ : α -> α'} {n₂ : β -> β'}
  proof: by
  simp_rw [map_map₂, map₂_map_left, map₂_map_right, h_distrib]

中文:
定理 map_map₂_distrib
  结论: {n : γ -> δ} {m' : α' -> β' -> δ} {n₁ : α -> α'} {n₂ : β -> β'}
  证明: by
  simp_rw [map_map₂, map₂_map_left, map₂_map_right, h_distrib]

Depends on / 依赖: h_distrib, simp_rw
-/
theorem map_map₂_distrib {n : γ -> δ} {m' : α' -> β' -> δ} {n₁ : α -> α'} {n₂ : β -> β'}
    (h_distrib : forall a b, n (m a b) = m' (n₁ a) (n₂ b)) :
    (map₂ m f g).map n = map₂ m' (f.map n₁) (g.map n₂) := by
  simp_rw [map_map₂, map₂_map_left, map₂_map_right, h_distrib]

/--
theorem `map_map₂_distrib_left` / 定理 `map_map₂_distrib_left`

English:
theorem map_map₂_distrib_left
  statement: {n : γ -> δ} {m' : α' -> β -> δ} {n' : α -> α'}
  proof: map_map₂_distrib h_distrib

中文:
定理 map_map₂_distrib_left
  结论: {n : γ -> δ} {m' : α' -> β -> δ} {n' : α -> α'}
  证明: map_map₂_distrib h_distrib

Depends on / 依赖: h_distrib
-/
theorem map_map₂_distrib_left {n : γ -> δ} {m' : α' -> β -> δ} {n' : α -> α'}
    (h_distrib : forall a b, n (m a b) = m' (n' a) b) : (map₂ m f g).map n = map₂ m' (f.map n') g :=
  map_map₂_distrib h_distrib

/--
theorem `map_map₂_distrib_right` / 定理 `map_map₂_distrib_right`

English:
theorem map_map₂_distrib_right
  statement: {n : γ -> δ} {m' : α -> β' -> δ} {n' : β -> β'}
  proof: map_map₂_distrib h_distrib

中文:
定理 map_map₂_distrib_right
  结论: {n : γ -> δ} {m' : α -> β' -> δ} {n' : β -> β'}
  证明: map_map₂_distrib h_distrib

Depends on / 依赖: h_distrib
-/
theorem map_map₂_distrib_right {n : γ -> δ} {m' : α -> β' -> δ} {n' : β -> β'}
    (h_distrib : forall a b, n (m a b) = m' a (n' b)) : (map₂ m f g).map n = map₂ m' f (g.map n') :=
  map_map₂_distrib h_distrib

/--
theorem `map₂_map_left_comm` / 定理 `map₂_map_left_comm`

English:
theorem map₂_map_left_comm
  statement: {m : α' -> β -> γ} {n : α -> α'} {m' : α -> β -> δ} {n' : δ -> γ}
  proof: (map_map₂_distrib_left fun a b => (h_left_comm a b).symm).symm

中文:
定理 map₂_map_left_comm
  结论: {m : α' -> β -> γ} {n : α -> α'} {m' : α -> β -> δ} {n' : δ -> γ}
  证明: (map_map₂_distrib_left fun a b => (h_left_comm a b).symm).symm

Depends on / 依赖: h_left_comm
-/
theorem map₂_map_left_comm {m : α' -> β -> γ} {n : α -> α'} {m' : α -> β -> δ} {n' : δ -> γ}
    (h_left_comm : forall a b, m (n a) b = n' (m' a b)) : map₂ m (f.map n) g = (map₂ m' f g).map n' :=
  (map_map₂_distrib_left fun a b => (h_left_comm a b).symm).symm

/--
theorem `map_map₂_right_comm` / 定理 `map_map₂_right_comm`

English:
theorem map_map₂_right_comm
  statement: {m : α -> β' -> γ} {n : β -> β'} {m' : α -> β -> δ} {n' : δ -> γ}
  proof: (map_map₂_distrib_right fun a b => (h_right_comm a b).symm).symm

中文:
定理 map_map₂_right_comm
  结论: {m : α -> β' -> γ} {n : β -> β'} {m' : α -> β -> δ} {n' : δ -> γ}
  证明: (map_map₂_distrib_right fun a b => (h_right_comm a b).symm).symm

Depends on / 依赖: h_right_comm
-/
theorem map_map₂_right_comm {m : α -> β' -> γ} {n : β -> β'} {m' : α -> β -> δ} {n' : δ -> γ}
    (h_right_comm : forall a b, m a (n b) = n' (m' a b)) : map₂ m f (g.map n) = (map₂ m' f g).map n' :=
  (map_map₂_distrib_right fun a b => (h_right_comm a b).symm).symm

/--
theorem `map₂_distrib_le_left` / 定理 `map₂_distrib_le_left`

English:
theorem map₂_distrib_le_left
  statement: {m : α -> δ -> ε} {n : β -> γ -> δ} {m₁ : α -> β -> β'} {m₂ : α -> γ -> γ'}
  proof: by
  rintro s ⟨t₁, ⟨u₁, hu₁, v, hv, ht₁⟩, t₂, ⟨u₂, hu₂, w, hw, ht₂⟩, hs⟩
  refine ⟨u₁ inter u₂, inter_mem hu₁ hu₂, _, image2_mem_map₂ hv hw, ?_⟩
  refine (image2_distrib_subset_left h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_right inter_subset_left).trans ht₁
  · exac

中文:
定理 map₂_distrib_le_left
  结论: {m : α -> δ -> ε} {n : β -> γ -> δ} {m₁ : α -> β -> β'} {m₂ : α -> γ -> γ'}
  证明: by
  rintro s ⟨t₁, ⟨u₁, hu₁, v, hv, ht₁⟩, t₂, ⟨u₂, hu₂, w, hw, ht₂⟩, hs⟩
  refine ⟨u₁ inter u₂, inter_mem hu₁ hu₂, _, image2_mem_map₂ hv hw, ?_⟩
  refine (image2_distrib_subset_left h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_right inter_subset_left).trans ht₁
  · exac

Depends on / 依赖: h_distrib, image2_distrib_subset_left, image2_subset, image2_subset_right, inter_mem, inter_subset_left, inter_subset_right
-/
theorem map₂_distrib_le_left {m : α -> δ -> ε} {n : β -> γ -> δ} {m₁ : α -> β -> β'} {m₂ : α -> γ -> γ'}
    {n' : β' -> γ' -> ε} (h_distrib : forall a b c, m a (n b c) = n' (m₁ a b) (m₂ a c)) :
    map₂ m f (map₂ n g h) <= map₂ n' (map₂ m₁ f g) (map₂ m₂ f h) := by
  rintro s ⟨t₁, ⟨u₁, hu₁, v, hv, ht₁⟩, t₂, ⟨u₂, hu₂, w, hw, ht₂⟩, hs⟩
  refine ⟨u₁ inter u₂, inter_mem hu₁ hu₂, _, image2_mem_map₂ hv hw, ?_⟩
  refine (image2_distrib_subset_left h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_right inter_subset_left).trans ht₁
  · exact (image2_subset_right inter_subset_right).trans ht₂

/--
theorem `map₂_distrib_le_right` / 定理 `map₂_distrib_le_right`

English:
theorem map₂_distrib_le_right
  statement: {m : δ -> γ -> ε} {n : α -> β -> δ} {m₁ : α -> γ -> α'} {m₂ : β -> γ -> β'}
  proof: by
  rintro s ⟨t₁, ⟨u, hu, w₁, hw₁, ht₁⟩, t₂, ⟨v, hv, w₂, hw₂, ht₂⟩, hs⟩
  refine ⟨_, image2_mem_map₂ hu hv, w₁ inter w₂, inter_mem hw₁ hw₂, ?_⟩
  refine (image2_distrib_subset_right h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_left inter_subset_left).trans ht₁
  · exac

中文:
定理 map₂_distrib_le_right
  结论: {m : δ -> γ -> ε} {n : α -> β -> δ} {m₁ : α -> γ -> α'} {m₂ : β -> γ -> β'}
  证明: by
  rintro s ⟨t₁, ⟨u, hu, w₁, hw₁, ht₁⟩, t₂, ⟨v, hv, w₂, hw₂, ht₂⟩, hs⟩
  refine ⟨_, image2_mem_map₂ hu hv, w₁ inter w₂, inter_mem hw₁ hw₂, ?_⟩
  refine (image2_distrib_subset_right h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_left inter_subset_left).trans ht₁
  · exac

Depends on / 依赖: h_distrib, image2_distrib_subset_right, image2_subset, image2_subset_left, inter_mem, inter_subset_left, inter_subset_right
-/
theorem map₂_distrib_le_right {m : δ -> γ -> ε} {n : α -> β -> δ} {m₁ : α -> γ -> α'} {m₂ : β -> γ -> β'}
    {n' : α' -> β' -> ε} (h_distrib : forall a b c, m (n a b) c = n' (m₁ a c) (m₂ b c)) :
    map₂ m (map₂ n f g) h <= map₂ n' (map₂ m₁ f h) (map₂ m₂ g h) := by
  rintro s ⟨t₁, ⟨u, hu, w₁, hw₁, ht₁⟩, t₂, ⟨v, hv, w₂, hw₂, ht₂⟩, hs⟩
  refine ⟨_, image2_mem_map₂ hu hv, w₁ inter w₂, inter_mem hw₁ hw₂, ?_⟩
  refine (image2_distrib_subset_right h_distrib).trans ((image2_subset ?_ ?_).trans hs)
  · exact (image2_subset_left inter_subset_left).trans ht₁
  · exact (image2_subset_left inter_subset_right).trans ht₂

/--
theorem `map_map₂_antidistrib` / 定理 `map_map₂_antidistrib`

English:
theorem map_map₂_antidistrib
  statement: {n : γ -> δ} {m' : β' -> α' -> δ} {n₁ : β -> β'} {n₂ : α -> α'}
  proof: by
  rw [map₂_swap m]
  exact map_map₂_distrib fun _ _ => h_antidistrib _ _

中文:
定理 map_map₂_antidistrib
  结论: {n : γ -> δ} {m' : β' -> α' -> δ} {n₁ : β -> β'} {n₂ : α -> α'}
  证明: by
  rw [map₂_swap m]
  exact map_map₂_distrib fun _ _ => h_antidistrib _ _

Depends on / 依赖: h_antidistrib
-/
theorem map_map₂_antidistrib {n : γ -> δ} {m' : β' -> α' -> δ} {n₁ : β -> β'} {n₂ : α -> α'}
    (h_antidistrib : forall a b, n (m a b) = m' (n₁ b) (n₂ a)) :
    (map₂ m f g).map n = map₂ m' (g.map n₁) (f.map n₂) := by
  rw [map₂_swap m]
  exact map_map₂_distrib fun _ _ => h_antidistrib _ _

/--
theorem `map_map₂_antidistrib_left` / 定理 `map_map₂_antidistrib_left`

English:
theorem map_map₂_antidistrib_left
  statement: {n : γ -> δ} {m' : β' -> α -> δ} {n' : β -> β'}
  proof: map_map₂_antidistrib h_antidistrib

中文:
定理 map_map₂_antidistrib_left
  结论: {n : γ -> δ} {m' : β' -> α -> δ} {n' : β -> β'}
  证明: map_map₂_antidistrib h_antidistrib

Depends on / 依赖: h_antidistrib
-/
theorem map_map₂_antidistrib_left {n : γ -> δ} {m' : β' -> α -> δ} {n' : β -> β'}
    (h_antidistrib : forall a b, n (m a b) = m' (n' b) a) : (map₂ m f g).map n = map₂ m' (g.map n') f :=
  map_map₂_antidistrib h_antidistrib

/--
theorem `map_map₂_antidistrib_right` / 定理 `map_map₂_antidistrib_right`

English:
theorem map_map₂_antidistrib_right
  statement: {n : γ -> δ} {m' : β -> α' -> δ} {n' : α -> α'}
  proof: map_map₂_antidistrib h_antidistrib

中文:
定理 map_map₂_antidistrib_right
  结论: {n : γ -> δ} {m' : β -> α' -> δ} {n' : α -> α'}
  证明: map_map₂_antidistrib h_antidistrib

Depends on / 依赖: h_antidistrib
-/
theorem map_map₂_antidistrib_right {n : γ -> δ} {m' : β -> α' -> δ} {n' : α -> α'}
    (h_antidistrib : forall a b, n (m a b) = m' b (n' a)) : (map₂ m f g).map n = map₂ m' g (f.map n') :=
  map_map₂_antidistrib h_antidistrib

/--
theorem `map₂_map_left_anticomm` / 定理 `map₂_map_left_anticomm`

English:
theorem map₂_map_left_anticomm
  statement: {m : α' -> β -> γ} {n : α -> α'} {m' : β -> α -> δ} {n' : δ -> γ}
  proof: (map_map₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

中文:
定理 map₂_map_left_anticomm
  结论: {m : α' -> β -> γ} {n : α -> α'} {m' : β -> α -> δ} {n' : δ -> γ}
  证明: (map_map₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

Depends on / 依赖: h_left_anticomm
-/
theorem map₂_map_left_anticomm {m : α' -> β -> γ} {n : α -> α'} {m' : β -> α -> δ} {n' : δ -> γ}
    (h_left_anticomm : forall a b, m (n a) b = n' (m' b a)) :
    map₂ m (f.map n) g = (map₂ m' g f).map n' :=
  (map_map₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/--
theorem `map_map₂_right_anticomm` / 定理 `map_map₂_right_anticomm`

English:
theorem map_map₂_right_anticomm
  statement: {m : α -> β' -> γ} {n : β -> β'} {m' : β -> α -> δ} {n' : δ -> γ}
  proof: (map_map₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

中文:
定理 map_map₂_right_anticomm
  结论: {m : α -> β' -> γ} {n : β -> β'} {m' : β -> α -> δ} {n' : δ -> γ}
  证明: (map_map₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

Depends on / 依赖: h_right_anticomm
-/
theorem map_map₂_right_anticomm {m : α -> β' -> γ} {n : β -> β'} {m' : β -> α -> δ} {n' : δ -> γ}
    (h_right_anticomm : forall a b, m a (n b) = n' (m' b a)) :
    map₂ m f (g.map n) = (map₂ m' g f).map n' :=
  (map_map₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

/--
theorem `map₂_left_identity` / 定理 `map₂_left_identity`

English:
theorem map₂_left_identity
  given: {f : α -> β -> β} {a : α} (h : forall b, f a b = b) (l : Filter β)
  proof: by rw [map₂_pure_left, show f a = id from funext h, map_id]

中文:
定理 map₂_left_identity
  条件: {f : α -> β -> β} {a : α} (h : 对任意 b, f a b = b) (l : 滤子 β)
  证明: by rw [map₂_pure_left, show f a = id from funext h, map_id]

Depends on / 依赖: map_id
-/
theorem map₂_left_identity {f : α -> β -> β} {a : α} (h : forall b, f a b = b) (l : Filter β) :
    map₂ f (pure a) l = l := by rw [map₂_pure_left, show f a = id from funext h, map_id]

/--
theorem `map₂_right_identity` / 定理 `map₂_right_identity`

English:
theorem map₂_right_identity
  given: {f : α -> β -> α} {b : β} (h : forall a, f a b = a) (l : Filter α)
  proof: by rw [map₂_pure_right, funext h, map_id']

中文:
定理 map₂_right_identity
  条件: {f : α -> β -> α} {b : β} (h : 对任意 a, f a b = a) (l : 滤子 α)
  证明: by rw [map₂_pure_right, funext h, map_id']

Depends on / 依赖: map_id
-/
theorem map₂_right_identity {f : α -> β -> α} {b : β} (h : forall a, f a b = a) (l : Filter α) :
    map₂ f l (pure b) = l := by rw [map₂_pure_right, funext h, map_id']

end Filter
