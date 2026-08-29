/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Control.Basic
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Filter.Basic

/-!
# Theorems about map and comap on filters.
-/

@[expose] public section

assert_not_exists IsOrderedRing Fintype

open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α β γ δ : Type*} {ι : Sort*} {F : Filter α} {G : Filter β}

/-! ### Push-forwards, pull-backs, and the monad structure -/

section Map

@[simp]
/--
theorem `map_principal` / 定理 `map_principal`

English:
theorem map_principal
  given: {s : Set α} {f : α -> β}
  statement: map f (𝓟 s) = 𝓟 (Set.image f s)
  proof: Filter.ext fun _ => image_subset_iff.symm

中文:
定理 map_principal
  条件: {s : 集合 α} {f : α -> β}
  结论: map f (𝓟 s) = 𝓟 (集合.像 f s)
  证明: Filter.ext fun _ => image_subset_iff.symm

Depends on / 依赖: Filter, Filter.ext, image_subset_iff, image_subset_iff.symm
-/
theorem map_principal {s : Set α} {f : α -> β} : map f (𝓟 s) = 𝓟 (Set.image f s) :=
  Filter.ext fun _ => image_subset_iff.symm

variable {f : Filter α} {m : α -> β} {m' : β -> γ} {s : Set α} {t : Set β}

@[simp]
/--
theorem `eventually_map` / 定理 `eventually_map`

English:
theorem eventually_map
  given: {P : β -> Prop}
  statement: (forallᶠ b in map m f, P b) ↔ forallᶠ a in f, P (m a)
  proof: Iff.rfl

@[simp]

中文:
定理 eventually_map
  条件: {P : β -> 命题}
  结论: (对任意ᶠ b in map m f, P b) ↔ 对任意ᶠ a in f, P (m a)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem eventually_map {P : β -> Prop} : (forallᶠ b in map m f, P b) ↔ forallᶠ a in f, P (m a) :=
  Iff.rfl

@[simp]
/--
theorem `frequently_map` / 定理 `frequently_map`

English:
theorem frequently_map
  given: {P : β -> Prop}
  statement: (existsᶠ b in map m f, P b) ↔ existsᶠ a in f, P (m a)
  proof: Iff.rfl

@[simp]

中文:
定理 frequently_map
  条件: {P : β -> 命题}
  结论: (存在ᶠ b in map m f, P b) ↔ 存在ᶠ a in f, P (m a)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem frequently_map {P : β -> Prop} : (existsᶠ b in map m f, P b) ↔ existsᶠ a in f, P (m a) :=
  Iff.rfl

@[simp]
/--
theorem `eventuallyEq_map` / 定理 `eventuallyEq_map`

English:
theorem eventuallyEq_map
  given: {f₁ f₂ : β -> γ}
  statement: f₁ =ᶠ[map m f] f₂ ↔ f₁ ∘ m =ᶠ[f] f₂ ∘ m
  proof: .rfl

@[simp]

中文:
定理 eventuallyEq_map
  条件: {f₁ f₂ : β -> γ}
  结论: f₁ =ᶠ[map m f] f₂ ↔ f₁ ∘ m =ᶠ[f] f₂ ∘ m
  证明: .rfl

@[simp]
-/
theorem eventuallyEq_map {f₁ f₂ : β -> γ} : f₁ =ᶠ[map m f] f₂ ↔ f₁ ∘ m =ᶠ[f] f₂ ∘ m := .rfl

@[simp]
/--
theorem `eventuallyLE_map` / 定理 `eventuallyLE_map`

English:
theorem eventuallyLE_map
  given: [LE γ] {f₁ f₂ : β -> γ}
  statement: f₁ <=ᶠ[map m f] f₂ ↔ f₁ ∘ m <=ᶠ[f] f₂ ∘ m
  proof: .rfl

@[simp]

中文:
定理 eventuallyLE_map
  条件: [LE γ] {f₁ f₂ : β -> γ}
  结论: f₁ <=ᶠ[map m f] f₂ ↔ f₁ ∘ m <=ᶠ[f] f₂ ∘ m
  证明: .rfl

@[simp]
-/
theorem eventuallyLE_map [LE γ] {f₁ f₂ : β -> γ} : f₁ <=ᶠ[map m f] f₂ ↔ f₁ ∘ m <=ᶠ[f] f₂ ∘ m := .rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  statement: t in map m f ↔ m ⁻¹' t in f
  proof: Iff.rfl

中文:
定理 mem_map
  结论: t in map m f ↔ m ⁻¹' t in f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_map : t in map m f ↔ m ⁻¹' t in f :=
  Iff.rfl

/--
theorem `mem_map'` / 定理 `mem_map'`

English:
theorem mem_map'
  statement: t in map m f ↔ { x | m x in t } in f
  proof: Iff.rfl

中文:
定理 mem_map'
  结论: t in map m f ↔ { x | m x in t } in f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_map' : t in map m f ↔ { x | m x in t } in f :=
  Iff.rfl

/--
theorem `image_mem_map` / 定理 `image_mem_map`

English:
theorem image_mem_map
  given: (hs : s in f)
  statement: m '' s in map m f
  proof: f.sets_of_superset hs subset_preimage_image m s

@[simp 1100]

中文:
定理 image_mem_map
  条件: (hs : s in f)
  结论: m '' s in map m f
  证明: f.sets_of_superset hs subset_preimage_image m s

@[simp 1100]

Depends on / 依赖: f.sets_of_superset, sets_of_superset, subset_preimage_image
-/
theorem image_mem_map (hs : s in f) : m '' s in map m f :=
f.sets_of_superset hs subset_preimage_image m s

@[simp 1100]
/--
theorem `image_mem_map_iff` / 定理 `image_mem_map_iff`

English:
theorem image_mem_map_iff
  given: (hf : Injective m)
  statement: m '' s in map m f ↔ s in f
  proof: ⟨fun h => by rwa [← preimage_image_eq s hf], image_mem_map⟩

中文:
定理 image_mem_map_iff
  条件: (hf : 单射 m)
  结论: m '' s in map m f ↔ s in f
  证明: ⟨fun h => by rwa [← preimage_image_eq s hf], image_mem_map⟩

Depends on / 依赖: image_mem_map, preimage_image_eq
-/
theorem image_mem_map_iff (hf : Injective m) : m '' s in map m f ↔ s in f :=
  ⟨fun h => by rwa [← preimage_image_eq s hf], image_mem_map⟩

/--
theorem `range_mem_map` / 定理 `range_mem_map`

English:
theorem range_mem_map
  statement: range m in map m f
  proof: by
  rw [← image_univ]
  exact image_mem_map univ_mem

中文:
定理 range_mem_map
  结论: range m in map m f
  证明: by
  rw [← image_univ]
  exact image_mem_map univ_mem

Depends on / 依赖: image_mem_map, image_univ, univ_mem
-/
theorem range_mem_map : range m in map m f := by
  rw [← image_univ]
  exact image_mem_map univ_mem

/--
theorem `mem_map_iff_exists_image` / 定理 `mem_map_iff_exists_image`

English:
theorem mem_map_iff_exists_image
  statement: t in map m f ↔ exists s in f, m '' s subseteq t
  proof: ⟨fun ht => ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩, fun ⟨_, hs, ht⟩ =>
    mem_of_superset (image_mem_map hs) ht⟩

@[simp]

中文:
定理 mem_map_iff_存在_image
  结论: t in map m f ↔ 存在 s in f, m '' s subseteq t
  证明: ⟨fun ht => ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩, fun ⟨_, hs, ht⟩ =>
    mem_of_superset (image_mem_map hs) ht⟩

@[simp]

Depends on / 依赖: image_mem_map, image_preimage_subset, mem_of_superset
-/
theorem mem_map_iff_exists_image : t in map m f ↔ exists s in f, m '' s subseteq t :=
  ⟨fun ht => ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩, fun ⟨_, hs, ht⟩ =>
    mem_of_superset (image_mem_map hs) ht⟩

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: Filter.map id f = f
  proof: filter_eq rfl

@[simp]

中文:
定理 map_id
  结论: 滤子.map id f = f
  证明: filter_eq rfl

@[simp]

Depends on / 依赖: filter_eq
-/
theorem map_id : Filter.map id f = f :=
filter_eq rfl

@[simp]
/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  statement: Filter.map (fun x => x) f = f
  proof: map_id

@[simp]

中文:
定理 map_id'
  结论: 滤子.map (fun x => x) f = f
  证明: map_id

@[simp]

Depends on / 依赖: map_id
-/
theorem map_id' : Filter.map (fun x => x) f = f :=
  map_id

@[simp]
/--
theorem `map_compose` / 定理 `map_compose`

English:
theorem map_compose
  statement: Filter.map m' ∘ Filter.map m = Filter.map (m' ∘ m)
  proof: funext fun _ => filter_eq rfl

@[simp]

中文:
定理 map_compose
  结论: 滤子.map m' ∘ 滤子.map m = 滤子.map (m' ∘ m)
  证明: funext fun _ => filter_eq rfl

@[simp]

Depends on / 依赖: filter_eq
-/
theorem map_compose : Filter.map m' ∘ Filter.map m = Filter.map (m' ∘ m) :=
funext fun _ => filter_eq rfl

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f
  proof: congr_fun Filter.map_compose f

中文:
定理 map_map
  结论: 滤子.map m' (滤子.map m f) = 滤子.map (m' ∘ m) f
  证明: congr_fun Filter.map_compose f

Depends on / 依赖: Filter, Filter.map_compose, congr_fun, map_compose
-/
theorem map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f :=
  congr_fun Filter.map_compose f

/--
theorem `map_congr` / 定理 `map_congr`

English:
theorem map_congr
  given: {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f] m₂)
  statement: map m₁ f = map m₂ f
  proof: Filter.ext' fun _ => eventually_congr (h.mono fun _ hx => hx ▸ Iff.rfl)

中文:
定理 map_congr
  条件: {m₁ m₂ : α -> β} {f : 滤子 α} (h : m₁ =ᶠ[f] m₂)
  结论: map m₁ f = map m₂ f
  证明: Filter.ext' fun _ => eventually_congr (h.mono fun _ hx => hx ▸ Iff.rfl)

Depends on / 依赖: Filter, Filter.ext, Iff.rfl, eventually_congr, h.mono
-/
theorem map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f] m₂) : map m₁ f = map m₂ f :=
  Filter.ext' fun _ => eventually_congr (h.mono fun _ hx => hx ▸ Iff.rfl)

end Map

section Comap

variable {f : α -> β} {l : Filter β} {p : α -> Prop} {s : Set α}

/--
theorem `mem_comap'` / 定理 `mem_comap'`

English:
theorem mem_comap'
  statement: s in comap f l ↔ { y | forall ⦃x⦄, f x = y -> x in s } in l
  proof: ⟨fun ⟨t, ht, hts⟩ => mem_of_superset ht fun y hy x hx => hts mem_preimage.2 by rwa [hx],
    fun h => ⟨_, h, fun _ hx => hx rfl⟩⟩

中文:
定理 mem_comap'
  结论: s in comap f l ↔ { y | 对任意 ⦃x⦄, f x = y -> x in s } in l
  证明: ⟨fun ⟨t, ht, hts⟩ => mem_of_superset ht fun y hy x hx => hts mem_preimage.2 by rwa [hx],
    fun h => ⟨_, h, fun _ hx => hx rfl⟩⟩

Depends on / 依赖: mem_of_superset, mem_preimage
-/
theorem mem_comap' : s in comap f l ↔ { y | forall ⦃x⦄, f x = y -> x in s } in l :=
⟨fun ⟨t, ht, hts⟩ => mem_of_superset ht fun y hy x hx => hts mem_preimage.2 by rwa [hx],
    fun h => ⟨_, h, fun _ hx => hx rfl⟩⟩

-- TODO: it would be nice to use `kernImage` much more to take advantage of common name and API,
-- and then this would become `mem_comap'`
/--
theorem `mem_comap''` / 定理 `mem_comap''`

English:
theorem mem_comap''
  statement: s in comap f l ↔ kernImage f s in l
  proof: mem_comap'

中文:
定理 mem_comap''
  结论: s in comap f l ↔ kernImage f s in l
  证明: mem_comap'

Depends on / 依赖: mem_comap
-/
theorem mem_comap'' : s in comap f l ↔ kernImage f s in l :=
  mem_comap'

/--
lemma `mem_comap_prodMk` / 引理 `mem_comap_prodMk`

English:
lemma mem_comap_prodMk
  given: {x : α} {s : Set β} {F : Filter (α × β)}
  proof: by
  simp_rw [mem_comap', Prod.ext_iff, and_imp, @forall_comm β (_ = _), forall_eq, eq_comm]

@[simp]

中文:
引理 mem_comap_prodMk
  条件: {x : α} {s : 集合 β} {F : 滤子 (α × β)}
  证明: by
  simp_rw [mem_comap', Prod.ext_iff, and_imp, @forall_comm β (_ = _), forall_eq, eq_comm]

@[simp]

Depends on / 依赖: Prod.ext_iff, and_imp, eq_comm, ext_iff, forall_comm, forall_eq, mem_comap, simp_rw
-/
lemma mem_comap_prodMk {x : α} {s : Set β} {F : Filter (α × β)} :
    s in comap (Prod.mk x) F ↔ {p : α × β | p.fst = x -> p.snd in s} in F := by
  simp_rw [mem_comap', Prod.ext_iff, and_imp, @forall_comm β (_ = _), forall_eq, eq_comm]

@[simp]
/--
theorem `eventually_comap` / 定理 `eventually_comap`

English:
theorem eventually_comap
  statement: (forallᶠ a in comap f l, p a) ↔ forallᶠ b in l, forall a, f a = b -> p a
  proof: mem_comap'

@[simp]

中文:
定理 eventually_comap
  结论: (对任意ᶠ a in comap f l, p a) ↔ 对任意ᶠ b in l, 对任意 a, f a = b -> p a
  证明: mem_comap'

@[simp]

Depends on / 依赖: mem_comap
-/
theorem eventually_comap : (forallᶠ a in comap f l, p a) ↔ forallᶠ b in l, forall a, f a = b -> p a :=
  mem_comap'

@[simp]
/--
theorem `frequently_comap` / 定理 `frequently_comap`

English:
theorem frequently_comap
  statement: (existsᶠ a in comap f l, p a) ↔ existsᶠ b in l, exists a, f a = b ∧ p a
  proof: by
  simp only [Filter.Frequently, eventually_comap, not_exists, _root_.not_and]

中文:
定理 frequently_comap
  结论: (存在ᶠ a in comap f l, p a) ↔ 存在ᶠ b in l, 存在 a, f a = b ∧ p a
  证明: by
  simp only [Filter.Frequently, eventually_comap, not_exists, _root_.not_and]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, _root_, _root_.not_and, eventually_comap, not_and, not_exists
-/
theorem frequently_comap : (existsᶠ a in comap f l, p a) ↔ existsᶠ b in l, exists a, f a = b ∧ p a := by
  simp only [Filter.Frequently, eventually_comap, not_exists, _root_.not_and]

/--
theorem `mem_comap_iff_compl` / 定理 `mem_comap_iff_compl`

English:
theorem mem_comap_iff_compl
  statement: s in comap f l ↔ (f '' sᶜ)ᶜ in l
  proof: by
  simp only [mem_comap'', kernImage_eq_compl]

中文:
定理 mem_comap_iff_compl
  结论: s in comap f l ↔ (f '' sᶜ)ᶜ in l
  证明: by
  simp only [mem_comap'', kernImage_eq_compl]

Depends on / 依赖: kernImage_eq_compl, mem_comap
-/
theorem mem_comap_iff_compl : s in comap f l ↔ (f '' sᶜ)ᶜ in l := by
  simp only [mem_comap'', kernImage_eq_compl]

/--
theorem `compl_mem_comap` / 定理 `compl_mem_comap`

English:
theorem compl_mem_comap
  statement: sᶜ in comap f l ↔ (f '' s)ᶜ in l
  proof: by rw [mem_comap_iff_compl, compl_compl]

中文:
定理 compl_mem_comap
  结论: sᶜ in comap f l ↔ (f '' s)ᶜ in l
  证明: by rw [mem_comap_iff_compl, compl_compl]

Depends on / 依赖: compl_compl, mem_comap_iff_compl
-/
theorem compl_mem_comap : sᶜ in comap f l ↔ (f '' s)ᶜ in l := by rw [mem_comap_iff_compl, compl_compl]

end Comap


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor (Filter : Type u -> Type u)
  body: map_id
  comp_map _ _ _ := map_map.symm
  map_const := rfl

中文:
实例 :
  签名: Lawful函子 (滤子 : 类型u -> 类型u)
  定义体: map_id
  comp_map _ _ _ := map_map.symm
  map_const := rfl

Depends on / 依赖: map_id
-/
instance : LawfulFunctor (Filter : Type u -> Type u) where
  id_map _ := map_id
  comp_map _ _ _ := map_map.symm
  map_const := rfl

/--
theorem `pure_sets` / 定理 `pure_sets`

English:
theorem pure_sets
  given: (a : α)
  statement: (pure a : Filter α).sets = { s | a in s }
  proof: rfl

@[simp]

中文:
定理 pure_sets
  条件: (a : α)
  结论: (pure a : 滤子 α).sets = { s | a in s }
  证明: rfl

@[simp]
-/
theorem pure_sets (a : α) : (pure a : Filter α).sets = { s | a in s } :=
  rfl

@[simp]
/--
theorem `eventually_pure` / 定理 `eventually_pure`

English:
theorem eventually_pure
  given: {a : α} {p : α -> Prop}
  statement: (forallᶠ x in pure a, p x) ↔ p a
  proof: Iff.rfl

@[simp]

中文:
定理 eventually_pure
  条件: {a : α} {p : α -> 命题}
  结论: (对任意ᶠ x in pure a, p x) ↔ p a
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem eventually_pure {a : α} {p : α -> Prop} : (forallᶠ x in pure a, p x) ↔ p a :=
  Iff.rfl

@[simp]
/--
theorem `frequently_pure` / 定理 `frequently_pure`

English:
theorem frequently_pure
  given: {a : α} {p : α -> Prop}
  statement: (existsᶠ x in pure a, p x) ↔ p a
  proof: by
  simp [Filter.Frequently]

@[simp]

中文:
定理 frequently_pure
  条件: {a : α} {p : α -> 命题}
  结论: (存在ᶠ x in pure a, p x) ↔ p a
  证明: by
  simp [Filter.Frequently]

@[simp]

Depends on / 依赖: Filter, Filter.Frequently, Frequently
-/
theorem frequently_pure {a : α} {p : α -> Prop} : (existsᶠ x in pure a, p x) ↔ p a := by
  simp [Filter.Frequently]

@[simp]
/--
theorem `principal_singleton` / 定理 `principal_singleton`

English:
theorem principal_singleton
  given: (a : α)
  statement: 𝓟 {a} = pure a
  proof: Filter.ext fun s => by simp only [mem_pure, mem_principal, singleton_subset_iff]

@[simp]

中文:
定理 principal_singleton
  条件: (a : α)
  结论: 𝓟 {a} = pure a
  证明: Filter.ext fun s => by simp only [mem_pure, mem_principal, singleton_subset_iff]

@[simp]

Depends on / 依赖: Filter, Filter.ext, mem_principal, mem_pure, singleton_subset_iff
-/
theorem principal_singleton (a : α) : 𝓟 {a} = pure a :=
  Filter.ext fun s => by simp only [mem_pure, mem_principal, singleton_subset_iff]

@[simp]
/--
theorem `biSup_pure_eq_principal` / 定理 `biSup_pure_eq_principal`

English:
theorem biSup_pure_eq_principal
  given: (s : Set α)
  statement: ⨆ a in s, pure a = 𝓟 s
  proof: Filter.ext fun s => by simp [Set.subset_def]

@[simp]

中文:
定理 biSup_pure_eq_principal
  条件: (s : 集合 α)
  结论: ⨆ a in s, pure a = 𝓟 s
  证明: Filter.ext fun s => by simp [Set.subset_def]

@[simp]

Depends on / 依赖: Filter, Filter.ext, Set.subset_def, subset_def
-/
theorem biSup_pure_eq_principal (s : Set α) : ⨆ a in s, pure a = 𝓟 s :=
  Filter.ext fun s => by simp [Set.subset_def]

@[simp]
/--
theorem `iSup_pure_eq_top` / 定理 `iSup_pure_eq_top`

English:
theorem iSup_pure_eq_top
  statement: ⨆ a, pure a = (⊤ : Filter α)
  proof: by
  rw [← principal_univ]; rw [← biSup_pure_eq_principal]; rw [iSup_univ]

@[simp]

中文:
定理 iSup_pure_eq_top
  结论: ⨆ a, pure a = (⊤ : 滤子 α)
  证明: by
  rw [← principal_univ]; rw [← biSup_pure_eq_principal]; rw [iSup_univ]

@[simp]

Depends on / 依赖: biSup_pure_eq_principal, iSup_univ, principal_univ
-/
theorem iSup_pure_eq_top : ⨆ a, pure a = (⊤ : Filter α) := by
  rw [← principal_univ]; rw [← biSup_pure_eq_principal]; rw [iSup_univ]

@[simp]
/--
theorem `map_pure` / 定理 `map_pure`

English:
theorem map_pure
  given: (f : α -> β) (a : α)
  statement: map f (pure a) = pure (f a)
  proof: rfl

中文:
定理 map_pure
  条件: (f : α -> β) (a : α)
  结论: map f (pure a) = pure (f a)
  证明: rfl
-/
theorem map_pure (f : α -> β) (a : α) : map f (pure a) = pure (f a) :=
  rfl

/--
theorem `pure_le_principal` / 定理 `pure_le_principal`

English:
theorem pure_le_principal
  given: {s : Set α} (a : α)
  statement: pure a <= 𝓟 s ↔ a in s
  proof: by
  simp

中文:
定理 pure_le_principal
  条件: {s : 集合 α} (a : α)
  结论: pure a <= 𝓟 s ↔ a in s
  证明: by
  simp
-/
theorem pure_le_principal {s : Set α} (a : α) : pure a <= 𝓟 s ↔ a in s := by
  simp

/--
theorem `join_pure` / 定理 `join_pure`

English:
theorem join_pure
  given: (f : Filter α)
  statement: join (pure f) = f
  proof: rfl

@[simp]

中文:
定理 join_pure
  条件: (f : 滤子 α)
  结论: join (pure f) = f
  证明: rfl

@[simp]
-/
@[simp] theorem join_pure (f : Filter α) : join (pure f) = f := rfl

@[simp]
/--
theorem `pure_bind` / 定理 `pure_bind`

English:
theorem pure_bind
  given: (a : α) (m : α -> Filter β)
  statement: bind (pure a) m = m a
  proof: by
  simp only [bind, map_pure, join_pure]

中文:
定理 pure_bind
  条件: (a : α) (m : α -> 滤子 β)
  结论: bind (pure a) m = m a
  证明: by
  simp only [bind, map_pure, join_pure]

Depends on / 依赖: join_pure, map_pure
-/
theorem pure_bind (a : α) (m : α -> Filter β) : bind (pure a) m = m a := by
  simp only [bind, map_pure, join_pure]

/--
theorem `map_bind` / 定理 `map_bind`

English:
theorem map_bind
  given: {α β} (m : β -> γ) (f : Filter α) (g : α -> Filter β)
  proof: rfl

中文:
定理 map_bind
  条件: {α β} (m : β -> γ) (f : 滤子 α) (g : α -> 滤子 β)
  证明: rfl
-/
theorem map_bind {α β} (m : β -> γ) (f : Filter α) (g : α -> Filter β) :
    map m (bind f g) = bind f (map m ∘ g) :=
  rfl

/--
theorem `bind_map` / 定理 `bind_map`

English:
theorem bind_map
  given: {α β} (m : α -> β) (f : Filter α) (g : β -> Filter γ)
  proof: rfl

中文:
定理 bind_map
  条件: {α β} (m : α -> β) (f : 滤子 α) (g : β -> 滤子 γ)
  证明: rfl
-/
theorem bind_map {α β} (m : α -> β) (f : Filter α) (g : β -> Filter γ) :
    (bind (map m f) g) = bind f (g ∘ m) :=
  rfl

/-!
### `Filter` as a `Monad`

In this section we define `Filter.monad`, a `Monad` structure on `Filter`s. This definition is not
an instance because its `Seq` projection is not equal to the `Filter.seq` function we use in the
`Applicative` instance on `Filter`.
-/

section

/-- The monad structure on filters. -/
@[instance_reducible]
/--
Definition of `monad` / `monad` 的定义

English:
definition monad
  signature: : Monad Filter where map
  body: @Filter.map

中文:
定义 monad
  签名: : 单子 滤子 where map
  定义体: @Filter.map
-/
protected def monad : Monad Filter where map := @Filter.map

attribute [local instance] Filter.monad

/--
theorem `lawfulMonad` / 定理 `lawfulMonad`

English:
theorem lawfulMonad
  statement: LawfulMonad Filter where
  proof: rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

中文:
定理 lawfulMonad
  结论: 合法单子 滤子 where
  证明: rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl
-/
protected theorem lawfulMonad : LawfulMonad Filter where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Alternative Filter
  body: fun x y => x.seq (y ())
  failure := ⊥
  orElse x y := x ⊔ y ()

@[simp]

中文:
实例 :
  签名: Alternative 滤子
  定义体: fun x y => x.seq (y ())
  failure := ⊥
  orElse x y := x ⊔ y ()

@[simp]

Depends on / 依赖: x.seq
-/
instance : Alternative Filter where
  seq := fun x y => x.seq (y ())
  failure := ⊥
  orElse x y := x ⊔ y ()

@[simp]
/--
theorem `map_def` / 定理 `map_def`

English:
theorem map_def
  given: {α β} (m : α -> β) (f : Filter α)
  statement: m < > f = map m f
  proof: rfl

@[simp]

中文:
定理 map_def
  条件: {α β} (m : α -> β) (f : 滤子 α)
  结论: m < > f = map m f
  证明: rfl

@[simp]
-/
theorem map_def {α β} (m : α -> β) (f : Filter α) : m < > f = map m f :=
  rfl

@[simp]
/--
theorem `bind_def` / 定理 `bind_def`

English:
theorem bind_def
  given: {α β} (f : Filter α) (m : α -> Filter β)
  statement: f >>= m = bind f m
  proof: rfl

中文:
定理 bind_def
  条件: {α β} (f : 滤子 α) (m : α -> 滤子 β)
  结论: f >>= m = bind f m
  证明: rfl
-/
theorem bind_def {α β} (f : Filter α) (m : α -> Filter β) : f >>= m = bind f m :=
  rfl

/-! #### `map` and `comap` equations -/

section Map

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Filter β} {m : α -> β} {m' : β -> γ} {s : Set α} {t : Set β}

/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  statement: s in comap m g ↔ exists t in g, m ⁻¹' t subseteq s
  proof: Iff.rfl

中文:
定理 mem_comap
  结论: s in comap m g ↔ 存在 t in g, m ⁻¹' t subseteq s
  证明: Iff.rfl
-/
@[simp] theorem mem_comap : s in comap m g ↔ exists t in g, m ⁻¹' t subseteq s := Iff.rfl

/--
theorem `preimage_mem_comap` / 定理 `preimage_mem_comap`

English:
theorem preimage_mem_comap
  given: (ht : t in g)
  statement: m ⁻¹' t in comap m g
  proof: ⟨t, ht, Subset.rfl⟩

中文:
定理 preimage_mem_comap
  条件: (ht : t in g)
  结论: m ⁻¹' t in comap m g
  证明: ⟨t, ht, Subset.rfl⟩

Depends on / 依赖: Subset, Subset.rfl
-/
theorem preimage_mem_comap (ht : t in g) : m ⁻¹' t in comap m g :=
  ⟨t, ht, Subset.rfl⟩

/--
theorem `Eventually.comap` / 定理 `Eventually.comap`

English:
theorem Eventually.comap
  given: {p : β -> Prop} (hf : forallᶠ b in g, p b) (f : α -> β)
  proof: preimage_mem_comap hf

@[simp]

中文:
定理 Eventually.comap
  条件: {p : β -> 命题} (hf : 对任意ᶠ b in g, p b) (f : α -> β)
  证明: preimage_mem_comap hf

@[simp]

Depends on / 依赖: preimage_mem_comap
-/
theorem Eventually.comap {p : β -> Prop} (hf : forallᶠ b in g, p b) (f : α -> β) :
    forallᶠ a in comap f g, p (f a) :=
  preimage_mem_comap hf

@[simp]
/--
lemma `EventuallyEq.comp_comap` / 引理 `EventuallyEq.comp_comap`

English:
lemma EventuallyEq.comp_comap
  statement: {F : Filter β} {f g : β -> γ} (h : α -> β)
  proof: hfg.comap _

中文:
引理 EventuallyEq.comp_comap
  结论: {F : 滤子 β} {f g : β -> γ} (h : α -> β)
  证明: hfg.comap _

Depends on / 依赖: hfg.comap
-/
lemma EventuallyEq.comp_comap {F : Filter β} {f g : β -> γ} (h : α -> β)
    (hfg : f =ᶠ[F] g) : f.comp h =ᶠ[comap h F] g.comp h :=
  hfg.comap _

/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: comap id f = f
  proof: le_antisymm (fun _ => preimage_mem_comap) fun _ ⟨_, ht, hst⟩ => mem_of_superset ht hst

中文:
定理 comap_id
  结论: comap id f = f
  证明: le_antisymm (fun _ => preimage_mem_comap) fun _ ⟨_, ht, hst⟩ => mem_of_superset ht hst

Depends on / 依赖: le_antisymm, mem_of_superset, preimage_mem_comap
-/
theorem comap_id : comap id f = f :=
  le_antisymm (fun _ => preimage_mem_comap) fun _ ⟨_, ht, hst⟩ => mem_of_superset ht hst

/--
theorem `comap_id'` / 定理 `comap_id'`

English:
theorem comap_id'
  statement: comap (fun x => x) f = f
  proof: comap_id

中文:
定理 comap_id'
  结论: comap (fun x => x) f = f
  证明: comap_id

Depends on / 依赖: comap_id
-/
theorem comap_id' : comap (fun x => x) f = f := comap_id

/--
theorem `comap_const_of_notMem` / 定理 `comap_const_of_notMem`

English:
theorem comap_const_of_notMem
  given: {x : β} (ht : t in g) (hx : x ∉ t)
  statement: comap (fun _ : α => x) g = ⊥
  proof: empty_mem_iff_bot.1 mem_comap'.2 mem_of_superset ht fun _ hx' _ h => hx h.symm ▸ hx'

中文:
定理 comap_const_of_notMem
  条件: {x : β} (ht : t in g) (hx : x ∉ t)
  结论: comap (fun _ : α => x) g = ⊥
  证明: empty_mem_iff_bot.1 mem_comap'.2 mem_of_superset ht fun _ hx' _ h => hx h.symm ▸ hx'

Depends on / 依赖: empty_mem_iff_bot, h.symm, mem_comap, mem_of_superset
-/
theorem comap_const_of_notMem {x : β} (ht : t in g) (hx : x ∉ t) : comap (fun _ : α => x) g = ⊥ :=
empty_mem_iff_bot.1 mem_comap'.2 mem_of_superset ht fun _ hx' _ h => hx h.symm ▸ hx'

/--
theorem `comap_const_of_mem` / 定理 `comap_const_of_mem`

English:
theorem comap_const_of_mem
  given: {x : β} (h : forall t in g, x in t)
  statement: comap (fun _ : α => x) g = ⊤
  proof: top_unique fun _ hs => univ_mem' fun _ => h _ (mem_comap'.1 hs) rfl

中文:
定理 comap_const_of_mem
  条件: {x : β} (h : 对任意 t in g, x in t)
  结论: comap (fun _ : α => x) g = ⊤
  证明: top_unique fun _ hs => univ_mem' fun _ => h _ (mem_comap'.1 hs) rfl

Depends on / 依赖: mem_comap, top_unique, univ_mem
-/
theorem comap_const_of_mem {x : β} (h : forall t in g, x in t) : comap (fun _ : α => x) g = ⊤ :=
  top_unique fun _ hs => univ_mem' fun _ => h _ (mem_comap'.1 hs) rfl

/--
theorem `map_const` / 定理 `map_const`

English:
theorem map_const
  given: [NeBot f] {c : β}
  statement: (f.map fun _ => c) = pure c
  proof: by
  ext s
  by_cases h : c in s <;> simp [h]

中文:
定理 map_const
  条件: [NeBot f] {c : β}
  结论: (f.map fun _ => c) = pure c
  证明: by
  ext s
  by_cases h : c in s <;> simp [h]
-/
theorem map_const [NeBot f] {c : β} : (f.map fun _ => c) = pure c := by
  ext s
  by_cases h : c in s <;> simp [h]

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: {m : γ -> β} {n : β -> α}
  statement: comap m (comap n f) = comap (n ∘ m) f
  proof: Filter.coext fun s => by simp only [compl_mem_comap, image_image, (· ∘ ·)]

中文:
定理 comap_comap
  条件: {m : γ -> β} {n : β -> α}
  结论: comap m (comap n f) = comap (n ∘ m) f
  证明: Filter.coext fun s => by simp only [compl_mem_comap, image_image, (· ∘ ·)]

Depends on / 依赖: Filter, Filter.coext, compl_mem_comap, image_image
-/
theorem comap_comap {m : γ -> β} {n : β -> α} : comap m (comap n f) = comap (n ∘ m) f :=
  Filter.coext fun s => by simp only [compl_mem_comap, image_image, (· ∘ ·)]

section comm

/-!
The variables in the following lemmas are used as in this diagram:
```
    φ
  α → β
θ ↓ ↓ ψ
  γ → δ
    ρ
```
-/


variable {φ : α -> β} {θ : α -> γ} {ψ : β -> δ} {ρ : γ -> δ}

/--
theorem `map_comm` / 定理 `map_comm`

English:
theorem map_comm
  given: (H : ψ ∘ φ = ρ ∘ θ) (F : Filter α)
  proof: by
  rw [Filter.map_map]; rw [H]; rw [← Filter.map_map]

中文:
定理 map_comm
  条件: (H : ψ ∘ φ = ρ ∘ θ) (F : 滤子 α)
  证明: by
  rw [Filter.map_map]; rw [H]; rw [← Filter.map_map]

Depends on / 依赖: Filter, Filter.map_map, map_map
-/
theorem map_comm (H : ψ ∘ φ = ρ ∘ θ) (F : Filter α) :
    map ψ (map φ F) = map ρ (map θ F) := by
  rw [Filter.map_map]; rw [H]; rw [← Filter.map_map]

/--
theorem `comap_comm` / 定理 `comap_comm`

English:
theorem comap_comm
  given: (H : ψ ∘ φ = ρ ∘ θ) (G : Filter δ)
  proof: by
  rw [Filter.comap_comap]; rw [H]; rw [← Filter.comap_comap]

中文:
定理 comap_comm
  条件: (H : ψ ∘ φ = ρ ∘ θ) (G : 滤子 δ)
  证明: by
  rw [Filter.comap_comap]; rw [H]; rw [← Filter.comap_comap]

Depends on / 依赖: Filter, Filter.comap_comap, comap_comap
-/
theorem comap_comm (H : ψ ∘ φ = ρ ∘ θ) (G : Filter δ) :
    comap φ (comap ψ G) = comap θ (comap ρ G) := by
  rw [Filter.comap_comap]; rw [H]; rw [← Filter.comap_comap]

end comm

/--
theorem `_root_.Function.Semiconj.filter_map` / 定理 `_root_.Function.Semiconj.filter_map`

English:
theorem _root_.Function.Semiconj.filter_map
  statement: {f : α -> β} {ga : α -> α} {gb : β -> β}
  proof: map_comm h.comp_eq

中文:
定理 _root_.函数.Semiconj.filter_map
  结论: {f : α -> β} {ga : α -> α} {gb : β -> β}
  证明: map_comm h.comp_eq

Depends on / 依赖: comp_eq, h.comp_eq, map_comm
-/
theorem _root_.Function.Semiconj.filter_map {f : α -> β} {ga : α -> α} {gb : β -> β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) :=
  map_comm h.comp_eq

/--
theorem `_root_.Function.Commute.filter_map` / 定理 `_root_.Function.Commute.filter_map`

English:
theorem _root_.Function.Commute.filter_map
  given: {f g : α -> α} (h : Function.Commute f g)
  proof: h.semiconj.filter_map

中文:
定理 _root_.函数.Commute.filter_map
  条件: {f g : α -> α} (h : 函数.Commute f g)
  证明: h.semiconj.filter_map

Depends on / 依赖: filter_map, h.semiconj.filter_map, semiconj
-/
theorem _root_.Function.Commute.filter_map {f g : α -> α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  h.semiconj.filter_map

/--
theorem `_root_.Function.Semiconj.filter_comap` / 定理 `_root_.Function.Semiconj.filter_comap`

English:
theorem _root_.Function.Semiconj.filter_comap
  statement: {f : α -> β} {ga : α -> α} {gb : β -> β}
  proof: comap_comm h.comp_eq.symm

中文:
定理 _root_.函数.Semiconj.filter_comap
  结论: {f : α -> β} {ga : α -> α} {gb : β -> β}
  证明: comap_comm h.comp_eq.symm

Depends on / 依赖: comap_comm, comp_eq, h.comp_eq.symm
-/
theorem _root_.Function.Semiconj.filter_comap {f : α -> β} {ga : α -> α} {gb : β -> β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (comap f) (comap gb) (comap ga) :=
  comap_comm h.comp_eq.symm

/--
theorem `_root_.Function.Commute.filter_comap` / 定理 `_root_.Function.Commute.filter_comap`

English:
theorem _root_.Function.Commute.filter_comap
  given: {f g : α -> α} (h : Function.Commute f g)
  proof: h.semiconj.filter_comap

中文:
定理 _root_.函数.Commute.filter_comap
  条件: {f g : α -> α} (h : 函数.Commute f g)
  证明: h.semiconj.filter_comap

Depends on / 依赖: filter_comap, h.semiconj.filter_comap, semiconj
-/
theorem _root_.Function.Commute.filter_comap {f g : α -> α} (h : Function.Commute f g) :
    Function.Commute (comap f) (comap g) :=
  h.semiconj.filter_comap

section

open Filter

/--
theorem `_root_.Function.LeftInverse.filter_map` / 定理 `_root_.Function.LeftInverse.filter_map`

English:
theorem _root_.Function.LeftInverse.filter_map
  given: {f : α -> β} {g : β -> α} (hfg : LeftInverse g f)
  proof: fun F => by
  rw [map_map]; rw [hfg.comp_eq_id]; rw [map_id]

中文:
定理 _root_.函数.左逆.filter_map
  条件: {f : α -> β} {g : β -> α} (hfg : 左逆 g f)
  证明: fun F => by
  rw [map_map]; rw [hfg.comp_eq_id]; rw [map_id]

Depends on / 依赖: comp_eq_id, hfg.comp_eq_id, map_id, map_map
-/
theorem _root_.Function.LeftInverse.filter_map {f : α -> β} {g : β -> α} (hfg : LeftInverse g f) :
    LeftInverse (map g) (map f) := fun F => by
  rw [map_map]; rw [hfg.comp_eq_id]; rw [map_id]

/--
theorem `_root_.Function.LeftInverse.filter_comap` / 定理 `_root_.Function.LeftInverse.filter_comap`

English:
theorem _root_.Function.LeftInverse.filter_comap
  given: {f : α -> β} {g : β -> α} (hfg : LeftInverse g f)
  proof: fun F => by
  rw [comap_comap]; rw [hfg.comp_eq_id]; rw [comap_id]

nonrec theorem _root_.Function.RightInverse.filter_map {f : α -> β} {g : β -> α}
    (hfg : RightInverse g f) : RightInverse (map g) (map f) :=
  hfg.filter_map

nonrec theorem _root_.Function.RightInverse.filter_comap {f : α -> β} {g : β -> α}
    (hfg : RightInverse g f) : LeftInverse (comap g) (comap f) :=
  hfg.filter_comap

中文:
定理 _root_.函数.左逆.filter_comap
  条件: {f : α -> β} {g : β -> α} (hfg : 左逆 g f)
  证明: fun F => by
  rw [comap_comap]; rw [hfg.comp_eq_id]; rw [comap_id]

nonrec theorem _root_.Function.RightInverse.filter_map {f : α -> β} {g : β -> α}
    (hfg : RightInverse g f) : RightInverse (map g) (map f) :=
  hfg.filter_map

nonrec theorem _root_.Function.RightInverse.filter_comap {f : α -> β} {g : β -> α}
    (hfg : RightInverse g f) : LeftInverse (comap g) (comap f) :=
  hfg.filter_comap

Depends on / 依赖: comap_comap, comap_id, comp_eq_id, hfg.comp_eq_id
-/
theorem _root_.Function.LeftInverse.filter_comap {f : α -> β} {g : β -> α} (hfg : LeftInverse g f) :
    RightInverse (comap g) (comap f) := fun F => by
  rw [comap_comap]; rw [hfg.comp_eq_id]; rw [comap_id]

nonrec theorem _root_.Function.RightInverse.filter_map {f : α -> β} {g : β -> α}
    (hfg : RightInverse g f) : RightInverse (map g) (map f) :=
  hfg.filter_map

nonrec theorem _root_.Function.RightInverse.filter_comap {f : α -> β} {g : β -> α}
    (hfg : RightInverse g f) : LeftInverse (comap g) (comap f) :=
  hfg.filter_comap

/--
theorem `_root_.Set.LeftInvOn.filter_map_Iic` / 定理 `_root_.Set.LeftInvOn.filter_map_Iic`

English:
theorem _root_.Set.LeftInvOn.filter_map_Iic
  given: {f : α -> β} {g : β -> α} (hfg : LeftInvOn g f s)
  proof: fun F (hF : F <= 𝓟 s) => by
  have : (g ∘ f) =ᶠ[𝓟 s] id := by simpa only [eventuallyEq_principal] using! hfg
  rw [map_map]; rw [map_congr (this.filter_mono hF)]; rw [map_id]

nonrec theorem _root_.Set.RightInvOn.filter_map_Iic {f : α -> β} {g : β -> α}
    (hfg : RightInvOn g f t) : RightInvOn (map g) (map f) (Iic <| 𝓟 t) :=
  hfg.filter_map_Iic

中文:
定理 _root_.集合.LeftInvOn.filter_map_Iic
  条件: {f : α -> β} {g : β -> α} (hfg : LeftInvOn g f s)
  证明: fun F (hF : F <= 𝓟 s) => by
  have : (g ∘ f) =ᶠ[𝓟 s] id := by simpa only [eventuallyEq_principal] using! hfg
  rw [map_map]; rw [map_congr (this.filter_mono hF)]; rw [map_id]

nonrec theorem _root_.Set.RightInvOn.filter_map_Iic {f : α -> β} {g : β -> α}
    (hfg : RightInvOn g f t) : RightInvOn (map g) (map f) (Iic <| 𝓟 t) :=
  hfg.filter_map_Iic

Depends on / 依赖: eventuallyEq_principal, filter_mono, map_congr, map_id, map_map, this.filter_mono
-/
theorem _root_.Set.LeftInvOn.filter_map_Iic {f : α -> β} {g : β -> α} (hfg : LeftInvOn g f s) :
    LeftInvOn (map g) (map f) (Iic <| 𝓟 s) := fun F (hF : F <= 𝓟 s) => by
  have : (g ∘ f) =ᶠ[𝓟 s] id := by simpa only [eventuallyEq_principal] using! hfg
  rw [map_map]; rw [map_congr (this.filter_mono hF)]; rw [map_id]

nonrec theorem _root_.Set.RightInvOn.filter_map_Iic {f : α -> β} {g : β -> α}
    (hfg : RightInvOn g f t) : RightInvOn (map g) (map f) (Iic <| 𝓟 t) :=
  hfg.filter_map_Iic

end

section KernMap

/--
Definition of `kernMap` / `kernMap` 的定义

English:
definition kernMap
  signature: (m : α -> β) (f : Filter α)
  body: (kernImage m) '' f.sets
  univ_sets := ⟨univ, f.univ_sets, by simp [kernImage_eq_compl]⟩
  sets_of_superset := by
    rintro _ t ⟨s, hs, rfl⟩ hst
    refine ⟨s union m ⁻¹' t, mem_of_superset hs subset_union_left, ?_⟩
    rw [kernImage_union_preimage]; rw [union_eq_right.mpr hst]
  inter_sets := by
    rintro _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩
    exact ⟨s₁ inter s₂, f.inter_sets h₁ h₂, Set.preimage_kernImage.u_inf⟩

中文:
定义 kernMap
  签名: (m : α -> β) (f : 滤子 α)
  定义体: (kernImage m) '' f.sets
  univ_sets := ⟨univ, f.univ_sets, by simp [kernImage_eq_compl]⟩
  sets_of_superset := by
    rintro _ t ⟨s, hs, rfl⟩ hst
    refine ⟨s union m ⁻¹' t, mem_of_superset hs subset_union_left, ?_⟩
    rw [kernImage_union_preimage]; rw [union_eq_right.mpr hst]
  inter_sets := by
    rintro _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩
    exact ⟨s₁ inter s₂, f.inter_sets h₁ h₂, Set.preimage_kernImage.u_inf⟩

Depends on / 依赖: f.sets, kernImage
-/
def kernMap (m : α -> β) (f : Filter α) : Filter β where
  sets := (kernImage m) '' f.sets
  univ_sets := ⟨univ, f.univ_sets, by simp [kernImage_eq_compl]⟩
  sets_of_superset := by
    rintro _ t ⟨s, hs, rfl⟩ hst
    refine ⟨s union m ⁻¹' t, mem_of_superset hs subset_union_left, ?_⟩
    rw [kernImage_union_preimage]; rw [union_eq_right.mpr hst]
  inter_sets := by
    rintro _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩
    exact ⟨s₁ inter s₂, f.inter_sets h₁ h₂, Set.preimage_kernImage.u_inf⟩

variable {m : α -> β} {f : Filter α}

/--
theorem `mem_kernMap` / 定理 `mem_kernMap`

English:
theorem mem_kernMap
  given: {s : Set β}
  statement: s in kernMap m f ↔ exists t in f, kernImage m t = s
  proof: Iff.rfl

中文:
定理 mem_kernMap
  条件: {s : 集合 β}
  结论: s in kernMap m f ↔ 存在 t in f, kernImage m t = s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_kernMap {s : Set β} : s in kernMap m f ↔ exists t in f, kernImage m t = s :=
  Iff.rfl

/--
theorem `mem_kernMap_iff_compl` / 定理 `mem_kernMap_iff_compl`

English:
theorem mem_kernMap_iff_compl
  given: {s : Set β}
  statement: s in kernMap m f ↔ exists t, tᶜ in f ∧ m '' t = sᶜ
  proof: by
  rw [mem_kernMap]; rw [compl_surjective.exists]
  refine exists_congr (fun x => and_congr_right fun _ => ?_)
  rw [kernImage_compl]; rw [compl_eq_comm]; rw [eq_comm]

中文:
定理 mem_kernMap_iff_compl
  条件: {s : 集合 β}
  结论: s in kernMap m f ↔ 存在 t, tᶜ in f ∧ m '' t = sᶜ
  证明: by
  rw [mem_kernMap]; rw [compl_surjective.exists]
  refine exists_congr (fun x => and_congr_right fun _ => ?_)
  rw [kernImage_compl]; rw [compl_eq_comm]; rw [eq_comm]

Depends on / 依赖: and_congr_right, compl_eq_comm, compl_surjective, compl_surjective.exists, eq_comm, exists_congr, kernImage_compl, mem_kernMap
-/
theorem mem_kernMap_iff_compl {s : Set β} : s in kernMap m f ↔ exists t, tᶜ in f ∧ m '' t = sᶜ := by
  rw [mem_kernMap]; rw [compl_surjective.exists]
  refine exists_congr (fun x => and_congr_right fun _ => ?_)
  rw [kernImage_compl]; rw [compl_eq_comm]; rw [eq_comm]

/--
theorem `compl_mem_kernMap` / 定理 `compl_mem_kernMap`

English:
theorem compl_mem_kernMap
  given: {s : Set β}
  statement: sᶜ in kernMap m f ↔ exists t, tᶜ in f ∧ m '' t = s
  proof: by
  simp_rw [mem_kernMap_iff_compl, compl_compl]

中文:
定理 compl_mem_kernMap
  条件: {s : 集合 β}
  结论: sᶜ in kernMap m f ↔ 存在 t, tᶜ in f ∧ m '' t = s
  证明: by
  simp_rw [mem_kernMap_iff_compl, compl_compl]

Depends on / 依赖: compl_compl, mem_kernMap_iff_compl, simp_rw
-/
theorem compl_mem_kernMap {s : Set β} : sᶜ in kernMap m f ↔ exists t, tᶜ in f ∧ m '' t = s := by
  simp_rw [mem_kernMap_iff_compl, compl_compl]

/--
theorem `comap_le_iff_le_kernMap` / 定理 `comap_le_iff_le_kernMap`

English:
theorem comap_le_iff_le_kernMap
  statement: comap m g <= f ↔ g <= kernMap m f
  proof: by
  simp [Filter.le_def, mem_comap'', mem_kernMap, -mem_comap]

中文:
定理 comap_le_iff_le_kernMap
  结论: comap m g <= f ↔ g <= kernMap m f
  证明: by
  simp [Filter.le_def, mem_comap'', mem_kernMap, -mem_comap]

Depends on / 依赖: Filter, Filter.le_def, le_def, mem_comap, mem_kernMap
-/
theorem comap_le_iff_le_kernMap : comap m g <= f ↔ g <= kernMap m f := by
  simp [Filter.le_def, mem_comap'', mem_kernMap, -mem_comap]

/--
theorem `gc_comap_kernMap` / 定理 `gc_comap_kernMap`

English:
theorem gc_comap_kernMap
  given: (m : α -> β)
  statement: GaloisConnection (comap m) (kernMap m)
  proof: fun _ _ => comap_le_iff_le_kernMap

中文:
定理 gc_comap_kernMap
  条件: (m : α -> β)
  结论: GaloisConnection (comap m) (kernMap m)
  证明: fun _ _ => comap_le_iff_le_kernMap

Depends on / 依赖: comap_le_iff_le_kernMap
-/
theorem gc_comap_kernMap (m : α -> β) : GaloisConnection (comap m) (kernMap m) :=
  fun _ _ => comap_le_iff_le_kernMap

/--
theorem `kernMap_principal` / 定理 `kernMap_principal`

English:
theorem kernMap_principal
  given: {s : Set α}
  statement: kernMap m (𝓟 s) = 𝓟 (kernImage m s)
  proof: by
  refine eq_of_forall_le_iff (fun g => ?_)
  rw [← comap_le_iff_le_kernMap]; rw [le_principal_iff]; rw [le_principal_iff]; rw [mem_comap'']

中文:
定理 kernMap_principal
  条件: {s : 集合 α}
  结论: kernMap m (𝓟 s) = 𝓟 (kernImage m s)
  证明: by
  refine eq_of_forall_le_iff (fun g => ?_)
  rw [← comap_le_iff_le_kernMap]; rw [le_principal_iff]; rw [le_principal_iff]; rw [mem_comap'']

Depends on / 依赖: comap_le_iff_le_kernMap, eq_of_forall_le_iff, le_principal_iff, mem_comap
-/
theorem kernMap_principal {s : Set α} : kernMap m (𝓟 s) = 𝓟 (kernImage m s) := by
  refine eq_of_forall_le_iff (fun g => ?_)
  rw [← comap_le_iff_le_kernMap]; rw [le_principal_iff]; rw [le_principal_iff]; rw [mem_comap'']

end KernMap

@[simp]
/--
theorem `comap_principal` / 定理 `comap_principal`

English:
theorem comap_principal
  given: {t : Set β}
  statement: comap m (𝓟 t) = 𝓟 (m ⁻¹' t)
  proof: Filter.ext fun _ => ⟨fun ⟨_u, hu, b⟩ => (preimage_mono hu).trans b,
    fun h => ⟨t, Subset.rfl, h⟩⟩

中文:
定理 comap_principal
  条件: {t : 集合 β}
  结论: comap m (𝓟 t) = 𝓟 (m ⁻¹' t)
  证明: Filter.ext fun _ => ⟨fun ⟨_u, hu, b⟩ => (preimage_mono hu).trans b,
    fun h => ⟨t, Subset.rfl, h⟩⟩

Depends on / 依赖: Filter, Filter.ext, Subset, Subset.rfl, preimage_mono
-/
theorem comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 (m ⁻¹' t) :=
  Filter.ext fun _ => ⟨fun ⟨_u, hu, b⟩ => (preimage_mono hu).trans b,
    fun h => ⟨t, Subset.rfl, h⟩⟩

/--
theorem `principal_subtype` / 定理 `principal_subtype`

English:
theorem principal_subtype
  given: {α : Type*} (s : Set α) (t : Set s)
  proof: by
  rw [comap_principal]; rw [preimage_image_eq _ Subtype.coe_injective]

@[simp]

中文:
定理 principal_subtype
  条件: {α : 类型} (s : 集合 α) (t : 集合 s)
  证明: by
  rw [comap_principal]; rw [preimage_image_eq _ Subtype.coe_injective]

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, comap_principal, preimage_image_eq
-/
theorem principal_subtype {α : Type*} (s : Set α) (t : Set s) :
    𝓟 t = comap (↑) (𝓟 (((↑) : s -> α) '' t)) := by
  rw [comap_principal]; rw [preimage_image_eq _ Subtype.coe_injective]

@[simp]
/--
theorem `comap_pure` / 定理 `comap_pure`

English:
theorem comap_pure
  given: {b : β}
  statement: comap m (pure b) = 𝓟 (m ⁻¹' {b})
  proof: by
  rw [← principal_singleton]; rw [comap_principal]

中文:
定理 comap_pure
  条件: {b : β}
  结论: comap m (pure b) = 𝓟 (m ⁻¹' {b})
  证明: by
  rw [← principal_singleton]; rw [comap_principal]

Depends on / 依赖: comap_principal, principal_singleton
-/
theorem comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b}) := by
  rw [← principal_singleton]; rw [comap_principal]

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  statement: map m f <= g ↔ f <= comap m g
  proof: ⟨fun h _ ⟨_, ht, hts⟩ => mem_of_superset (h ht) hts, fun h _ ht => h ⟨_, ht, Subset.rfl⟩⟩

中文:
定理 map_le_iff_le_comap
  结论: map m f <= g ↔ f <= comap m g
  证明: ⟨fun h _ ⟨_, ht, hts⟩ => mem_of_superset (h ht) hts, fun h _ ht => h ⟨_, ht, Subset.rfl⟩⟩

Depends on / 依赖: Subset, Subset.rfl, mem_of_superset
-/
theorem map_le_iff_le_comap : map m f <= g ↔ f <= comap m g :=
  ⟨fun h _ ⟨_, ht, hts⟩ => mem_of_superset (h ht) hts, fun h _ ht => h ⟨_, ht, Subset.rfl⟩⟩

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (m : α -> β)
  statement: GaloisConnection (map m) (comap m)
  proof: fun _ _ => map_le_iff_le_comap

@[gcongr, mono]

中文:
定理 gc_map_comap
  条件: (m : α -> β)
  结论: GaloisConnection (map m) (comap m)
  证明: fun _ _ => map_le_iff_le_comap

@[gcongr, mono]

Depends on / 依赖: map_le_iff_le_comap
-/
theorem gc_map_comap (m : α -> β) : GaloisConnection (map m) (comap m) :=
  fun _ _ => map_le_iff_le_comap

@[gcongr, mono]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  statement: Monotone (map m)
  proof: (gc_map_comap m).monotone_l

@[gcongr, mono]

中文:
定理 map_mono
  结论: 递增 (map m)
  证明: (gc_map_comap m).monotone_l

@[gcongr, mono]

Depends on / 依赖: gc_map_comap, monotone_l
-/
theorem map_mono : Monotone (map m) :=
  (gc_map_comap m).monotone_l

@[gcongr, mono]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  statement: Monotone (comap m)
  proof: (gc_map_comap m).monotone_u

中文:
定理 comap_mono
  结论: 递增 (comap m)
  证明: (gc_map_comap m).monotone_u

Depends on / 依赖: gc_map_comap, monotone_u
-/
theorem comap_mono : Monotone (comap m) :=
  (gc_map_comap m).monotone_u

/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  statement: map m ⊥ = ⊥
  proof: (gc_map_comap m).l_bot

中文:
定理 map_bot
  结论: map m ⊥ = ⊥
  证明: (gc_map_comap m).l_bot
-/
@[simp] theorem map_bot : map m ⊥ = ⊥ := (gc_map_comap m).l_bot

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  statement: map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂
  proof: (gc_map_comap m).l_sup

@[simp]

中文:
定理 map_sup
  结论: map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂
  证明: (gc_map_comap m).l_sup

@[simp]
-/
@[simp] theorem map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_comap m).l_sup

@[simp]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {f : ι -> Filter α}
  statement: map m (⨆ i, f i) = ⨆ i, map m (f i)
  proof: (gc_map_comap m).l_iSup

@[simp]

中文:
定理 map_iSup
  条件: {f : ι -> 滤子 α}
  结论: map m (⨆ i, f i) = ⨆ i, map m (f i)
  证明: (gc_map_comap m).l_iSup

@[simp]

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {f : ι -> Filter α} : map m (⨆ i, f i) = ⨆ i, map m (f i) :=
  (gc_map_comap m).l_iSup

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  given: (f : α -> β)
  statement: map f ⊤ = 𝓟 (range f)
  proof: by
  rw [← principal_univ]; rw [map_principal]; rw [image_univ]

中文:
定理 map_top
  条件: (f : α -> β)
  结论: map f ⊤ = 𝓟 (range f)
  证明: by
  rw [← principal_univ]; rw [map_principal]; rw [image_univ]

Depends on / 依赖: image_univ, map_principal, principal_univ
-/
theorem map_top (f : α -> β) : map f ⊤ = 𝓟 (range f) := by
  rw [← principal_univ]; rw [map_principal]; rw [image_univ]

/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  statement: comap m ⊤ = ⊤
  proof: (gc_map_comap m).u_top

中文:
定理 comap_top
  结论: comap m ⊤ = ⊤
  证明: (gc_map_comap m).u_top
-/
@[simp] theorem comap_top : comap m ⊤ = ⊤ := (gc_map_comap m).u_top

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  statement: comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂
  proof: (gc_map_comap m).u_inf

@[simp]

中文:
定理 comap_inf
  结论: comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂
  证明: (gc_map_comap m).u_inf

@[simp]
-/
@[simp] theorem comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ := (gc_map_comap m).u_inf

@[simp]
/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {f : ι -> Filter β}
  statement: comap m (⨅ i, f i) = ⨅ i, comap m (f i)
  proof: (gc_map_comap m).u_iInf

中文:
定理 comap_iInf
  条件: {f : ι -> 滤子 β}
  结论: comap m (⨅ i, f i) = ⨅ i, comap m (f i)
  证明: (gc_map_comap m).u_iInf

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) = ⨅ i, comap m (f i) :=
  (gc_map_comap m).u_iInf

/--
theorem `le_comap_top` / 定理 `le_comap_top`

English:
theorem le_comap_top
  given: (f : α -> β) (l : Filter α)
  statement: l <= comap f ⊤
  proof: by
  rw [comap_top]
  exact le_top

中文:
定理 le_comap_top
  条件: (f : α -> β) (l : 滤子 α)
  结论: l <= comap f ⊤
  证明: by
  rw [comap_top]
  exact le_top

Depends on / 依赖: comap_top, le_top
-/
theorem le_comap_top (f : α -> β) (l : Filter α) : l <= comap f ⊤ := by
  rw [comap_top]
  exact le_top

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  statement: map m (comap m g) <= g
  proof: (gc_map_comap m).l_u_le _

中文:
定理 map_comap_le
  结论: map m (comap m g) <= g
  证明: (gc_map_comap m).l_u_le _

Depends on / 依赖: gc_map_comap, l_u_le
-/
theorem map_comap_le : map m (comap m g) <= g :=
  (gc_map_comap m).l_u_le _

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  statement: f <= comap m (map m f)
  proof: (gc_map_comap m).le_u_l _

@[simp]

中文:
定理 le_comap_map
  结论: f <= comap m (map m f)
  证明: (gc_map_comap m).le_u_l _

@[simp]

Depends on / 依赖: gc_map_comap, le_u_l
-/
theorem le_comap_map : f <= comap m (map m f) :=
  (gc_map_comap m).le_u_l _

@[simp]
/--
theorem `comap_bot` / 定理 `comap_bot`

English:
theorem comap_bot
  statement: comap m ⊥ = ⊥
  proof: bot_unique fun s _ => ⟨∅, mem_bot, by simp only [empty_subset, preimage_empty]⟩

中文:
定理 comap_bot
  结论: comap m ⊥ = ⊥
  证明: bot_unique fun s _ => ⟨∅, mem_bot, by simp only [empty_subset, preimage_empty]⟩

Depends on / 依赖: bot_unique, empty_subset, mem_bot, preimage_empty
-/
theorem comap_bot : comap m ⊥ = ⊥ :=
  bot_unique fun s _ => ⟨∅, mem_bot, by simp only [empty_subset, preimage_empty]⟩

/--
theorem `neBot_of_comap` / 定理 `neBot_of_comap`

English:
theorem neBot_of_comap
  given: (h : (comap m g).NeBot)
  statement: g.NeBot
  proof: by
  rw [neBot_iff] at *
  contrapose h
  rw [h]
  exact comap_bot

中文:
定理 neBot_of_comap
  条件: (h : (comap m g).NeBot)
  结论: g.NeBot
  证明: by
  rw [neBot_iff] at *
  contrapose h
  rw [h]
  exact comap_bot

Depends on / 依赖: comap_bot, contrapose, neBot_iff
-/
theorem neBot_of_comap (h : (comap m g).NeBot) : g.NeBot := by
  rw [neBot_iff] at *
  contrapose h
  rw [h]
  exact comap_bot

/--
theorem `comap_inf_principal_range` / 定理 `comap_inf_principal_range`

English:
theorem comap_inf_principal_range
  statement: comap m (g ⊓ 𝓟 (range m)) = comap m g
  proof: by
  simp

中文:
定理 comap_inf_principal_range
  结论: comap m (g ⊓ 𝓟 (range m)) = comap m g
  证明: by
  simp
-/
theorem comap_inf_principal_range : comap m (g ⊓ 𝓟 (range m)) = comap m g := by
  simp

/--
theorem `disjoint_comap` / 定理 `disjoint_comap`

English:
theorem disjoint_comap
  given: (h : Disjoint g₁ g₂)
  statement: Disjoint (comap m g₁) (comap m g₂)
  proof: by
  simp only [disjoint_iff, ← comap_inf, h.eq_bot, comap_bot]

中文:
定理 disjoint_comap
  条件: (h : Disjoint g₁ g₂)
  结论: Disjoint (comap m g₁) (comap m g₂)
  证明: by
  simp only [disjoint_iff, ← comap_inf, h.eq_bot, comap_bot]

Depends on / 依赖: comap_bot, comap_inf, disjoint_iff, eq_bot, h.eq_bot
-/
theorem disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (comap m g₁) (comap m g₂) := by
  simp only [disjoint_iff, ← comap_inf, h.eq_bot, comap_bot]

/--
theorem `comap_iSup` / 定理 `comap_iSup`

English:
theorem comap_iSup
  given: {ι} {f : ι -> Filter β} {m : α -> β}
  statement: comap m (iSup f) = ⨆ i, comap m (f i)
  proof: (gc_comap_kernMap m).l_iSup

中文:
定理 comap_iSup
  条件: {ι} {f : ι -> 滤子 β} {m : α -> β}
  结论: comap m (iSup f) = ⨆ i, comap m (f i)
  证明: (gc_comap_kernMap m).l_iSup

Depends on / 依赖: gc_comap_kernMap, l_iSup
-/
theorem comap_iSup {ι} {f : ι -> Filter β} {m : α -> β} : comap m (iSup f) = ⨆ i, comap m (f i) :=
  (gc_comap_kernMap m).l_iSup

/--
theorem `comap_sSup` / 定理 `comap_sSup`

English:
theorem comap_sSup
  given: {s : Set (Filter β)} {m : α -> β}
  statement: comap m (sSup s) = ⨆ f in s, comap m f
  proof: by
  simp only [sSup_eq_iSup, comap_iSup]

中文:
定理 comap_sSup
  条件: {s : 集合 (滤子 β)} {m : α -> β}
  结论: comap m (sSup s) = ⨆ f in s, comap m f
  证明: by
  simp only [sSup_eq_iSup, comap_iSup]

Depends on / 依赖: comap_iSup, sSup_eq_iSup
-/
theorem comap_sSup {s : Set (Filter β)} {m : α -> β} : comap m (sSup s) = ⨆ f in s, comap m f := by
  simp only [sSup_eq_iSup, comap_iSup]

/--
theorem `comap_sup` / 定理 `comap_sup`

English:
theorem comap_sup
  statement: comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂
  proof: by
  rw [sup_eq_iSup]; rw [comap_iSup]; rw [iSup_bool_eq]; rw [Bool.cond_true]; rw [Bool.cond_false]

中文:
定理 comap_sup
  结论: comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂
  证明: by
  rw [sup_eq_iSup]; rw [comap_iSup]; rw [iSup_bool_eq]; rw [Bool.cond_true]; rw [Bool.cond_false]

Depends on / 依赖: Bool.cond_false, Bool.cond_true, comap_iSup, cond_false, cond_true, iSup_bool_eq, sup_eq_iSup
-/
theorem comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ := by
  rw [sup_eq_iSup]; rw [comap_iSup]; rw [iSup_bool_eq]; rw [Bool.cond_true]; rw [Bool.cond_false]

/--
theorem `map_comap` / 定理 `map_comap`

English:
theorem map_comap
  given: (f : Filter β) (m : α -> β)
  statement: (f.comap m).map m = f ⊓ 𝓟 (range m)
  proof: by
  refine le_antisymm (le_inf map_comap_le <| le_principal_iff.2 range_mem_map) ?_
  rintro t' ⟨t, ht, sub⟩
  refine mem_inf_principal.2 (mem_of_superset ht ?_)
  rintro _ hxt ⟨x, rfl⟩
  exact sub hxt

中文:
定理 map_comap
  条件: (f : 滤子 β) (m : α -> β)
  结论: (f.comap m).map m = f ⊓ 𝓟 (range m)
  证明: by
  refine le_antisymm (le_inf map_comap_le <| le_principal_iff.2 range_mem_map) ?_
  rintro t' ⟨t, ht, sub⟩
  refine mem_inf_principal.2 (mem_of_superset ht ?_)
  rintro _ hxt ⟨x, rfl⟩
  exact sub hxt

Depends on / 依赖: le_antisymm, le_inf, le_principal_iff, map_comap_le, mem_inf_principal, mem_of_superset, range_mem_map
-/
theorem map_comap (f : Filter β) (m : α -> β) : (f.comap m).map m = f ⊓ 𝓟 (range m) := by
  refine le_antisymm (le_inf map_comap_le <| le_principal_iff.2 range_mem_map) ?_
  rintro t' ⟨t, ht, sub⟩
  refine mem_inf_principal.2 (mem_of_superset ht ?_)
  rintro _ hxt ⟨x, rfl⟩
  exact sub hxt

/--
theorem `map_comap_setCoe_val` / 定理 `map_comap_setCoe_val`

English:
theorem map_comap_setCoe_val
  given: (f : Filter β) (s : Set β)
  proof: by
  rw [map_comap]; rw [Subtype.range_val]

中文:
定理 map_comap_setCoe_val
  条件: (f : 滤子 β) (s : 集合 β)
  证明: by
  rw [map_comap]; rw [Subtype.range_val]

Depends on / 依赖: Subtype, Subtype.range_val, map_comap, range_val
-/
theorem map_comap_setCoe_val (f : Filter β) (s : Set β) :
    (f.comap ((↑) : s -> β)).map (↑) = f ⊓ 𝓟 s := by
  rw [map_comap]; rw [Subtype.range_val]

/--
theorem `map_comap_of_mem` / 定理 `map_comap_of_mem`

English:
theorem map_comap_of_mem
  given: {f : Filter β} {m : α -> β} (hf : range m in f)
  statement: (f.comap m).map m = f
  proof: by
  rw [map_comap]; rw [inf_eq_left.2 (le_principal_iff.2 hf)]

中文:
定理 map_comap_of_mem
  条件: {f : 滤子 β} {m : α -> β} (hf : range m in f)
  结论: (f.comap m).map m = f
  证明: by
  rw [map_comap]; rw [inf_eq_left.2 (le_principal_iff.2 hf)]

Depends on / 依赖: inf_eq_left, le_principal_iff, map_comap
-/
theorem map_comap_of_mem {f : Filter β} {m : α -> β} (hf : range m in f) : (f.comap m).map m = f := by
  rw [map_comap]; rw [inf_eq_left.2 (le_principal_iff.2 hf)]

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: (c) (p) [CanLift α β c p]
  body: ⟨comap c f, map_comap_of_mem hf.mono CanLift.prf⟩

中文:
实例 canLift
  签名: (c) (p) [CanLift α β c p]
  定义体: ⟨comap c f, map_comap_of_mem hf.mono CanLift.prf⟩

Depends on / 依赖: CanLift, CanLift.prf, hf.mono, map_comap_of_mem
-/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Filter α) (Filter β) (map c) fun f => forallᶠ x : α in f, p x where
prf f hf := ⟨comap c f, map_comap_of_mem hf.mono CanLift.prf⟩

/--
theorem `comap_le_comap_iff` / 定理 `comap_le_comap_iff`

English:
theorem comap_le_comap_iff
  given: {f g : Filter β} {m : α -> β} (hf : range m in f)
  proof: ⟨fun h => map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, fun h => comap_mono h⟩

中文:
定理 comap_le_comap_iff
  条件: {f g : 滤子 β} {m : α -> β} (hf : range m in f)
  证明: ⟨fun h => map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, fun h => comap_mono h⟩

Depends on / 依赖: comap_mono, map_comap_le, map_comap_of_mem, map_mono
-/
theorem comap_le_comap_iff {f g : Filter β} {m : α -> β} (hf : range m in f) :
    comap m f <= comap m g ↔ f <= g :=
  ⟨fun h => map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, fun h => comap_mono h⟩

/--
theorem `map_comap_of_surjective` / 定理 `map_comap_of_surjective`

English:
theorem map_comap_of_surjective
  given: {f : α -> β} (hf : Surjective f) (l : Filter β)
  proof: map_comap_of_mem by simp only [hf.range_eq, univ_mem]

中文:
定理 map_comap_of_surjective
  条件: {f : α -> β} (hf : 满射 f) (l : 滤子 β)
  证明: map_comap_of_mem by simp only [hf.range_eq, univ_mem]

Depends on / 依赖: hf.range_eq, map_comap_of_mem, range_eq, univ_mem
-/
theorem map_comap_of_surjective {f : α -> β} (hf : Surjective f) (l : Filter β) :
    map f (comap f l) = l :=
map_comap_of_mem by simp only [hf.range_eq, univ_mem]

/--
theorem `comap_injective` / 定理 `comap_injective`

English:
theorem comap_injective
  given: {f : α -> β} (hf : Surjective f)
  statement: Injective (comap f)
  proof: LeftInverse.injective map_comap_of_surjective hf

中文:
定理 comap_injective
  条件: {f : α -> β} (hf : 满射 f)
  结论: 单射 (comap f)
  证明: LeftInverse.injective map_comap_of_surjective hf

Depends on / 依赖: LeftInverse, LeftInverse.injective, injective, map_comap_of_surjective
-/
theorem comap_injective {f : α -> β} (hf : Surjective f) : Injective (comap f) :=
LeftInverse.injective map_comap_of_surjective hf

/--
theorem `_root_.Function.Surjective.filter_map_top` / 定理 `_root_.Function.Surjective.filter_map_top`

English:
theorem _root_.Function.Surjective.filter_map_top
  given: {f : α -> β} (hf : Surjective f)
  statement: map f ⊤ = ⊤
  proof: (congr_arg _ comap_top).symm.trans map_comap_of_surjective hf ⊤

中文:
定理 _root_.函数.满射.filter_map_top
  条件: {f : α -> β} (hf : 满射 f)
  结论: map f ⊤ = ⊤
  证明: (congr_arg _ comap_top).symm.trans map_comap_of_surjective hf ⊤

Depends on / 依赖: comap_top, congr_arg, map_comap_of_surjective, symm.trans
-/
theorem _root_.Function.Surjective.filter_map_top {f : α -> β} (hf : Surjective f) : map f ⊤ = ⊤ :=
(congr_arg _ comap_top).symm.trans map_comap_of_surjective hf ⊤

/--
theorem `subtype_coe_map_comap` / 定理 `subtype_coe_map_comap`

English:
theorem subtype_coe_map_comap
  given: (s : Set α) (f : Filter α)
  proof: by rw [map_comap, Subtype.range_coe]

中文:
定理 subtype_coe_map_comap
  条件: (s : 集合 α) (f : 滤子 α)
  证明: by rw [map_comap, Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.range_coe, map_comap, range_coe
-/
theorem subtype_coe_map_comap (s : Set α) (f : Filter α) :
    map ((↑) : s -> α) (comap ((↑) : s -> α) f) = f ⊓ 𝓟 s := by rw [map_comap, Subtype.range_coe]

/--
theorem `image_mem_of_mem_comap` / 定理 `image_mem_of_mem_comap`

English:
theorem image_mem_of_mem_comap
  statement: {f : Filter α} {c : β -> α} (h : range c in f) {W : Set β}
  proof: by
  rw [← map_comap_of_mem h]
  exact image_mem_map W_in

中文:
定理 image_mem_of_mem_comap
  结论: {f : 滤子 α} {c : β -> α} (h : range c in f) {W : 集合 β}
  证明: by
  rw [← map_comap_of_mem h]
  exact image_mem_map W_in

Depends on / 依赖: W_in, image_mem_map, map_comap_of_mem
-/
theorem image_mem_of_mem_comap {f : Filter α} {c : β -> α} (h : range c in f) {W : Set β}
    (W_in : W in comap c f) : c '' W in f := by
  rw [← map_comap_of_mem h]
  exact image_mem_map W_in

/--
theorem `image_coe_mem_of_mem_comap` / 定理 `image_coe_mem_of_mem_comap`

English:
theorem image_coe_mem_of_mem_comap
  statement: {f : Filter α} {U : Set α} (h : U in f) {W : Set U}
  proof: image_mem_of_mem_comap (by simp [h]) W_in

中文:
定理 image_coe_mem_of_mem_comap
  结论: {f : 滤子 α} {U : 集合 α} (h : U in f) {W : 集合 U}
  证明: image_mem_of_mem_comap (by simp [h]) W_in

Depends on / 依赖: W_in, image_mem_of_mem_comap
-/
theorem image_coe_mem_of_mem_comap {f : Filter α} {U : Set α} (h : U in f) {W : Set U}
    (W_in : W in comap ((↑) : U -> α) f) : (↑) '' W in f :=
  image_mem_of_mem_comap (by simp [h]) W_in

/--
theorem `comap_map` / 定理 `comap_map`

English:
theorem comap_map
  given: {f : Filter α} {m : α -> β} (h : Injective m)
  statement: comap m (map m f) = f
  proof: le_antisymm
    (fun s hs =>
mem_of_superset (preimage_mem_comap <| image_mem_map hs) by
        simp only [preimage_image_eq s h, Subset.rfl])
    le_comap_map

中文:
定理 comap_map
  条件: {f : 滤子 α} {m : α -> β} (h : 单射 m)
  结论: comap m (map m f) = f
  证明: le_antisymm
    (fun s hs =>
mem_of_superset (preimage_mem_comap <| image_mem_map hs) by
        simp only [preimage_image_eq s h, Subset.rfl])
    le_comap_map

Depends on / 依赖: Subset, Subset.rfl, image_mem_map, le_antisymm, le_comap_map, mem_of_superset, preimage_image_eq, preimage_mem_comap
-/
theorem comap_map {f : Filter α} {m : α -> β} (h : Injective m) : comap m (map m f) = f :=
  le_antisymm
    (fun s hs =>
mem_of_superset (preimage_mem_comap <| image_mem_map hs) by
        simp only [preimage_image_eq s h, Subset.rfl])
    le_comap_map

/--
theorem `mem_comap_iff` / 定理 `mem_comap_iff`

English:
theorem mem_comap_iff
  statement: {f : Filter β} {m : α -> β} (inj : Injective m) (large : Set.range m in f)
  proof: by
  rw [← image_mem_map_iff inj]; rw [map_comap_of_mem large]

中文:
定理 mem_comap_iff
  结论: {f : 滤子 β} {m : α -> β} (inj : 单射 m) (large : 集合.range m in f)
  证明: by
  rw [← image_mem_map_iff inj]; rw [map_comap_of_mem large]

Depends on / 依赖: image_mem_map_iff, map_comap_of_mem
-/
theorem mem_comap_iff {f : Filter β} {m : α -> β} (inj : Injective m) (large : Set.range m in f)
    {S : Set α} : S in comap m f ↔ m '' S in f := by
  rw [← image_mem_map_iff inj]; rw [map_comap_of_mem large]

/--
theorem `map_le_map_iff_of_injOn` / 定理 `map_le_map_iff_of_injOn`

English:
theorem map_le_map_iff_of_injOn
  statement: {l₁ l₂ : Filter α} {f : α -> β} {s : Set α} (h₁ : s in l₁)
  proof: ⟨fun h _t ht =>
mp_mem h₁
      mem_of_superset (h <| image_mem_map (inter_mem h₂ ht)) fun _y ⟨_x, ⟨hxs, hxt⟩, hxy⟩ hys =>
        hinj hxs hys hxy ▸ hxt,
    fun h => map_mono h⟩

中文:
定理 map_le_map_iff_of_injOn
  结论: {l₁ l₂ : 滤子 α} {f : α -> β} {s : 集合 α} (h₁ : s in l₁)
  证明: ⟨fun h _t ht =>
mp_mem h₁
      mem_of_superset (h <| image_mem_map (inter_mem h₂ ht)) fun _y ⟨_x, ⟨hxs, hxt⟩, hxy⟩ hys =>
        hinj hxs hys hxy ▸ hxt,
    fun h => map_mono h⟩

Depends on / 依赖: image_mem_map, inter_mem, map_mono, mem_of_superset, mp_mem
-/
theorem map_le_map_iff_of_injOn {l₁ l₂ : Filter α} {f : α -> β} {s : Set α} (h₁ : s in l₁)
    (h₂ : s in l₂) (hinj : InjOn f s) : map f l₁ <= map f l₂ ↔ l₁ <= l₂ :=
  ⟨fun h _t ht =>
mp_mem h₁
      mem_of_superset (h <| image_mem_map (inter_mem h₂ ht)) fun _y ⟨_x, ⟨hxs, hxt⟩, hxy⟩ hys =>
        hinj hxs hys hxy ▸ hxt,
    fun h => map_mono h⟩

/--
theorem `map_le_map_iff` / 定理 `map_le_map_iff`

English:
theorem map_le_map_iff
  given: {f g : Filter α} {m : α -> β} (hm : Injective m)
  proof: by rw [map_le_iff_le_comap, comap_map hm]

中文:
定理 map_le_map_iff
  条件: {f g : 滤子 α} {m : α -> β} (hm : 单射 m)
  证明: by rw [map_le_iff_le_comap, comap_map hm]

Depends on / 依赖: comap_map, map_le_iff_le_comap
-/
theorem map_le_map_iff {f g : Filter α} {m : α -> β} (hm : Injective m) :
    map m f <= map m g ↔ f <= g := by rw [map_le_iff_le_comap, comap_map hm]

/--
theorem `map_eq_map_iff_of_injOn` / 定理 `map_eq_map_iff_of_injOn`

English:
theorem map_eq_map_iff_of_injOn
  statement: {f g : Filter α} {m : α -> β} {s : Set α} (hsf : s in f) (hsg : s in g)
  proof: by
  simp only [le_antisymm_iff, map_le_map_iff_of_injOn hsf hsg hm,
    map_le_map_iff_of_injOn hsg hsf hm]

中文:
定理 map_eq_map_iff_of_injOn
  结论: {f g : 滤子 α} {m : α -> β} {s : 集合 α} (hsf : s in f) (hsg : s in g)
  证明: by
  simp only [le_antisymm_iff, map_le_map_iff_of_injOn hsf hsg hm,
    map_le_map_iff_of_injOn hsg hsf hm]

Depends on / 依赖: le_antisymm_iff, map_le_map_iff_of_injOn
-/
theorem map_eq_map_iff_of_injOn {f g : Filter α} {m : α -> β} {s : Set α} (hsf : s in f) (hsg : s in g)
    (hm : InjOn m s) : map m f = map m g ↔ f = g := by
  simp only [le_antisymm_iff, map_le_map_iff_of_injOn hsf hsg hm,
    map_le_map_iff_of_injOn hsg hsf hm]

/--
theorem `map_inj` / 定理 `map_inj`

English:
theorem map_inj
  given: {f g : Filter α} {m : α -> β} (hm : Injective m)
  statement: map m f = map m g ↔ f = g
  proof: map_eq_map_iff_of_injOn univ_mem univ_mem hm.injOn

中文:
定理 map_inj
  条件: {f g : 滤子 α} {m : α -> β} (hm : 单射 m)
  结论: map m f = map m g ↔ f = g
  证明: map_eq_map_iff_of_injOn univ_mem univ_mem hm.injOn

Depends on / 依赖: hm.injOn, map_eq_map_iff_of_injOn, univ_mem
-/
theorem map_inj {f g : Filter α} {m : α -> β} (hm : Injective m) : map m f = map m g ↔ f = g :=
  map_eq_map_iff_of_injOn univ_mem univ_mem hm.injOn

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {m : α -> β} (hm : Injective m)
  statement: Injective (map m)
  proof: fun _ _ =>
  (map_inj hm).1

中文:
定理 map_injective
  条件: {m : α -> β} (hm : 单射 m)
  结论: 单射 (map m)
  证明: fun _ _ =>
  (map_inj hm).1
-/
theorem map_injective {m : α -> β} (hm : Injective m) : Injective (map m) := fun _ _ =>
  (map_inj hm).1

/--
theorem `comap_neBot_iff` / 定理 `comap_neBot_iff`

English:
theorem comap_neBot_iff
  given: {f : Filter β} {m : α -> β}
  statement: NeBot (comap m f) ↔ forall t in f, exists a, m a in t
  proof: by
  simp only [← forall_mem_nonempty_iff_neBot, mem_comap, forall_exists_index, and_imp]
  exact ⟨fun h t t_in => h (m ⁻¹' t) t t_in Subset.rfl, fun h s t ht hst => (h t ht).imp hst⟩

中文:
定理 comap_neBot_iff
  条件: {f : 滤子 β} {m : α -> β}
  结论: NeBot (comap m f) ↔ 对任意 t in f, 存在 a, m a in t
  证明: by
  simp only [← forall_mem_nonempty_iff_neBot, mem_comap, forall_exists_index, and_imp]
  exact ⟨fun h t t_in => h (m ⁻¹' t) t t_in Subset.rfl, fun h s t ht hst => (h t ht).imp hst⟩

Depends on / 依赖: Subset, Subset.rfl, and_imp, forall_exists_index, forall_mem_nonempty_iff_neBot, mem_comap, t_in
-/
theorem comap_neBot_iff {f : Filter β} {m : α -> β} : NeBot (comap m f) ↔ forall t in f, exists a, m a in t := by
  simp only [← forall_mem_nonempty_iff_neBot, mem_comap, forall_exists_index, and_imp]
  exact ⟨fun h t t_in => h (m ⁻¹' t) t t_in Subset.rfl, fun h s t ht hst => (h t ht).imp hst⟩

/--
theorem `comap_neBot` / 定理 `comap_neBot`

English:
theorem comap_neBot
  given: {f : Filter β} {m : α -> β} (hm : forall t in f, exists a, m a in t)
  statement: NeBot (comap m f)
  proof: comap_neBot_iff.mpr hm

中文:
定理 comap_neBot
  条件: {f : 滤子 β} {m : α -> β} (hm : 对任意 t in f, 存在 a, m a in t)
  结论: NeBot (comap m f)
  证明: comap_neBot_iff.mpr hm

Depends on / 依赖: comap_neBot_iff, comap_neBot_iff.mpr
-/
theorem comap_neBot {f : Filter β} {m : α -> β} (hm : forall t in f, exists a, m a in t) : NeBot (comap m f) :=
  comap_neBot_iff.mpr hm

/--
theorem `comap_neBot_iff_frequently` / 定理 `comap_neBot_iff_frequently`

English:
theorem comap_neBot_iff_frequently
  given: {f : Filter β} {m : α -> β}
  proof: by
  simp only [comap_neBot_iff, frequently_iff, mem_range, @and_comm (_ in _), exists_exists_eq_and]

中文:
定理 comap_neBot_iff_frequently
  条件: {f : 滤子 β} {m : α -> β}
  证明: by
  simp only [comap_neBot_iff, frequently_iff, mem_range, @and_comm (_ in _), exists_exists_eq_and]

Depends on / 依赖: and_comm, comap_neBot_iff, exists_exists_eq_and, frequently_iff, mem_range
-/
theorem comap_neBot_iff_frequently {f : Filter β} {m : α -> β} :
    NeBot (comap m f) ↔ existsᶠ y in f, y in range m := by
  simp only [comap_neBot_iff, frequently_iff, mem_range, @and_comm (_ in _), exists_exists_eq_and]

/--
theorem `comap_neBot_iff_compl_range` / 定理 `comap_neBot_iff_compl_range`

English:
theorem comap_neBot_iff_compl_range
  given: {f : Filter β} {m : α -> β}
  proof: comap_neBot_iff_frequently

中文:
定理 comap_neBot_iff_compl_range
  条件: {f : 滤子 β} {m : α -> β}
  证明: comap_neBot_iff_frequently

Depends on / 依赖: comap_neBot_iff_frequently
-/
theorem comap_neBot_iff_compl_range {f : Filter β} {m : α -> β} :
    NeBot (comap m f) ↔ (range m)ᶜ ∉ f :=
  comap_neBot_iff_frequently

/--
theorem `comap_eq_bot_iff_compl_range` / 定理 `comap_eq_bot_iff_compl_range`

English:
theorem comap_eq_bot_iff_compl_range
  given: {f : Filter β} {m : α -> β}
  statement: comap m f = ⊥ ↔ (range m)ᶜ in f
  proof: not_iff_not.mp neBot_iff.symm.trans comap_neBot_iff_compl_range

中文:
定理 comap_eq_bot_iff_compl_range
  条件: {f : 滤子 β} {m : α -> β}
  结论: comap m f = ⊥ ↔ (range m)ᶜ in f
  证明: not_iff_not.mp neBot_iff.symm.trans comap_neBot_iff_compl_range

Depends on / 依赖: comap_neBot_iff_compl_range, neBot_iff, neBot_iff.symm.trans, not_iff_not, not_iff_not.mp
-/
theorem comap_eq_bot_iff_compl_range {f : Filter β} {m : α -> β} : comap m f = ⊥ ↔ (range m)ᶜ in f :=
not_iff_not.mp neBot_iff.symm.trans comap_neBot_iff_compl_range

/--
theorem `comap_surjective_eq_bot` / 定理 `comap_surjective_eq_bot`

English:
theorem comap_surjective_eq_bot
  given: {f : Filter β} {m : α -> β} (hm : Surjective m)
  proof: by
  rw [comap_eq_bot_iff_compl_range]; rw [hm.range_eq]; rw [compl_univ]; rw [empty_mem_iff_bot]

中文:
定理 comap_surjective_eq_bot
  条件: {f : 滤子 β} {m : α -> β} (hm : 满射 m)
  证明: by
  rw [comap_eq_bot_iff_compl_range]; rw [hm.range_eq]; rw [compl_univ]; rw [empty_mem_iff_bot]

Depends on / 依赖: comap_eq_bot_iff_compl_range, compl_univ, empty_mem_iff_bot, hm.range_eq, range_eq
-/
theorem comap_surjective_eq_bot {f : Filter β} {m : α -> β} (hm : Surjective m) :
    comap m f = ⊥ ↔ f = ⊥ := by
  rw [comap_eq_bot_iff_compl_range]; rw [hm.range_eq]; rw [compl_univ]; rw [empty_mem_iff_bot]

/--
theorem `disjoint_comap_iff` / 定理 `disjoint_comap_iff`

English:
theorem disjoint_comap_iff
  given: (h : Surjective m)
  proof: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← comap_inf]; rw [comap_surjective_eq_bot h]

中文:
定理 disjoint_comap_iff
  条件: (h : 满射 m)
  证明: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← comap_inf]; rw [comap_surjective_eq_bot h]

Depends on / 依赖: comap_inf, comap_surjective_eq_bot, disjoint_iff
-/
theorem disjoint_comap_iff (h : Surjective m) :
    Disjoint (comap m g₁) (comap m g₂) ↔ Disjoint g₁ g₂ := by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← comap_inf]; rw [comap_surjective_eq_bot h]

/--
theorem `NeBot.comap_of_range_mem` / 定理 `NeBot.comap_of_range_mem`

English:
theorem NeBot.comap_of_range_mem
  given: {f : Filter β} {m : α -> β} (_ : NeBot f) (hm : range m in f)
  proof: comap_neBot_iff_frequently.2 Eventually.frequently hm

中文:
定理 NeBot.comap_of_range_mem
  条件: {f : 滤子 β} {m : α -> β} (_ : NeBot f) (hm : range m in f)
  证明: comap_neBot_iff_frequently.2 Eventually.frequently hm

Depends on / 依赖: Eventually, Eventually.frequently, comap_neBot_iff_frequently, frequently
-/
theorem NeBot.comap_of_range_mem {f : Filter β} {m : α -> β} (_ : NeBot f) (hm : range m in f) :
    NeBot (comap m f) :=
comap_neBot_iff_frequently.2 Eventually.frequently hm

section Sum
open Sum

@[simp]
/--
theorem `comap_inl_map_inr` / 定理 `comap_inl_map_inr`

English:
theorem comap_inl_map_inr
  statement: comap inl (map (@inr α β) g) = ⊥
  proof: by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]

中文:
定理 comap_inl_map_inr
  结论: comap inl (map (@inr α β) g) = ⊥
  证明: by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]

Depends on / 依赖: mem_comap_iff_compl
-/
theorem comap_inl_map_inr : comap inl (map (@inr α β) g) = ⊥ := by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]
/--
theorem `comap_inr_map_inl` / 定理 `comap_inr_map_inl`

English:
theorem comap_inr_map_inl
  statement: comap inr (map (@inl α β) f) = ⊥
  proof: by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]

中文:
定理 comap_inr_map_inl
  结论: comap inr (map (@inl α β) f) = ⊥
  证明: by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]

Depends on / 依赖: mem_comap_iff_compl
-/
theorem comap_inr_map_inl : comap inr (map (@inl α β) f) = ⊥ := by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]
/--
theorem `map_inl_inf_map_inr` / 定理 `map_inl_inf_map_inr`

English:
theorem map_inl_inf_map_inr
  statement: map inl f ⊓ map inr g = ⊥
  proof: by
  apply le_bot_iff.mp
  trans map inl ⊤ ⊓ map inr ⊤
  · apply inf_le_inf <;> simp
  · simp

@[simp]

中文:
定理 map_inl_inf_map_inr
  结论: map inl f ⊓ map inr g = ⊥
  证明: by
  apply le_bot_iff.mp
  trans map inl ⊤ ⊓ map inr ⊤
  · apply inf_le_inf <;> simp
  · simp

@[simp]

Depends on / 依赖: inf_le_inf, le_bot_iff, le_bot_iff.mp
-/
theorem map_inl_inf_map_inr : map inl f ⊓ map inr g = ⊥ := by
  apply le_bot_iff.mp
  trans map inl ⊤ ⊓ map inr ⊤
  · apply inf_le_inf <;> simp
  · simp

@[simp]
/--
theorem `map_inr_inf_map_inl` / 定理 `map_inr_inf_map_inl`

English:
theorem map_inr_inf_map_inl
  statement: map inr f ⊓ map inl g = ⊥
  proof: by
  rw [inf_comm]; rw [map_inl_inf_map_inr]

中文:
定理 map_inr_inf_map_inl
  结论: map inr f ⊓ map inl g = ⊥
  证明: by
  rw [inf_comm]; rw [map_inl_inf_map_inr]

Depends on / 依赖: inf_comm, map_inl_inf_map_inr
-/
theorem map_inr_inf_map_inl : map inr f ⊓ map inl g = ⊥ := by
  rw [inf_comm]; rw [map_inl_inf_map_inr]

/--
theorem `comap_sumElim_eq` / 定理 `comap_sumElim_eq`

English:
theorem comap_sumElim_eq
  given: (l : Filter γ) (m₁ : α -> γ) (m₂ : β -> γ)
  proof: by
  ext s
  simp_rw [mem_sup, mem_map, mem_comap_iff_compl]
  simp [image_sumElim]

中文:
定理 comap_sumElim_eq
  条件: (l : 滤子 γ) (m₁ : α -> γ) (m₂ : β -> γ)
  证明: by
  ext s
  simp_rw [mem_sup, mem_map, mem_comap_iff_compl]
  simp [image_sumElim]

Depends on / 依赖: image_sumElim, mem_comap_iff_compl, mem_map, mem_sup, simp_rw
-/
theorem comap_sumElim_eq (l : Filter γ) (m₁ : α -> γ) (m₂ : β -> γ) :
    comap (Sum.elim m₁ m₂) l = map inl (comap m₁ l) ⊔ map inr (comap m₂ l) := by
  ext s
  simp_rw [mem_sup, mem_map, mem_comap_iff_compl]
  simp [image_sumElim]

/--
theorem `map_comap_inl_sup_map_comap_inr` / 定理 `map_comap_inl_sup_map_comap_inr`

English:
theorem map_comap_inl_sup_map_comap_inr
  given: (l : Filter (α oplus β))
  proof: by
  rw [← comap_sumElim_eq]; rw [Sum.elim_inl_inr]; rw [comap_id]

中文:
定理 map_comap_inl_sup_map_comap_inr
  条件: (l : 滤子 (α oplus β))
  证明: by
  rw [← comap_sumElim_eq]; rw [Sum.elim_inl_inr]; rw [comap_id]

Depends on / 依赖: Sum.elim_inl_inr, comap_id, comap_sumElim_eq, elim_inl_inr
-/
theorem map_comap_inl_sup_map_comap_inr (l : Filter (α oplus β)) :
    map inl (comap inl l) ⊔ map inr (comap inr l) = l := by
  rw [← comap_sumElim_eq]; rw [Sum.elim_inl_inr]; rw [comap_id]

/--
theorem `map_sumElim_eq` / 定理 `map_sumElim_eq`

English:
theorem map_sumElim_eq
  given: (l : Filter (α oplus β)) (m₁ : α -> γ) (m₂ : β -> γ)
  proof: by
  rw [← map_comap_inl_sup_map_comap_inr l]
  simp [map_sup, map_map, comap_sup, (gc_map_comap _).u_l_u_eq_u]

中文:
定理 map_sumElim_eq
  条件: (l : 滤子 (α oplus β)) (m₁ : α -> γ) (m₂ : β -> γ)
  证明: by
  rw [← map_comap_inl_sup_map_comap_inr l]
  simp [map_sup, map_map, comap_sup, (gc_map_comap _).u_l_u_eq_u]

Depends on / 依赖: comap_sup, gc_map_comap, map_comap_inl_sup_map_comap_inr, map_map, map_sup, u_l_u_eq_u
-/
theorem map_sumElim_eq (l : Filter (α oplus β)) (m₁ : α -> γ) (m₂ : β -> γ) :
    map (Sum.elim m₁ m₂) l = map m₁ (comap inl l) ⊔ map m₂ (comap inr l) := by
  rw [← map_comap_inl_sup_map_comap_inr l]
  simp [map_sup, map_map, comap_sup, (gc_map_comap _).u_l_u_eq_u]

end Sum

@[simp]
/--
theorem `comap_fst_neBot_iff` / 定理 `comap_fst_neBot_iff`

English:
theorem comap_fst_neBot_iff
  given: {f : Filter α}
  proof: by
  cases isEmpty_or_nonempty β
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp [*]
  · simp [comap_neBot_iff_frequently, *]

@[instance]

中文:
定理 comap_fst_neBot_iff
  条件: {f : 滤子 α}
  证明: by
  cases isEmpty_or_nonempty β
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp [*]
  · simp [comap_neBot_iff_frequently, *]

@[instance]

Depends on / 依赖: comap_neBot_iff_frequently, f.comap, filter_eq_bot_of_isEmpty, isEmpty_or_nonempty, not_iff_not
-/
theorem comap_fst_neBot_iff {f : Filter α} :
    (f.comap (Prod.fst : α × β -> α)).NeBot ↔ f.NeBot ∧ Nonempty β := by
  cases isEmpty_or_nonempty β
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp [*]
  · simp [comap_neBot_iff_frequently, *]

@[instance]
/--
theorem `comap_fst_neBot` / 定理 `comap_fst_neBot`

English:
theorem comap_fst_neBot
  given: [Nonempty β] {f : Filter α} [NeBot f]
  proof: comap_fst_neBot_iff.2 ⟨‹_›, ‹_›⟩

@[simp]

中文:
定理 comap_fst_neBot
  条件: [非空 β] {f : 滤子 α} [NeBot f]
  证明: comap_fst_neBot_iff.2 ⟨‹_›, ‹_›⟩

@[simp]

Depends on / 依赖: comap_fst_neBot_iff
-/
theorem comap_fst_neBot [Nonempty β] {f : Filter α} [NeBot f] :
    (f.comap (Prod.fst : α × β -> α)).NeBot :=
  comap_fst_neBot_iff.2 ⟨‹_›, ‹_›⟩

@[simp]
/--
theorem `comap_snd_neBot_iff` / 定理 `comap_snd_neBot_iff`

English:
theorem comap_snd_neBot_iff
  given: {f : Filter β}
  proof: by
  rcases isEmpty_or_nonempty α with hα | hα
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp
  · simp [comap_neBot_iff_frequently, hα]

@[instance]

中文:
定理 comap_snd_neBot_iff
  条件: {f : 滤子 β}
  证明: by
  rcases isEmpty_or_nonempty α with hα | hα
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp
  · simp [comap_neBot_iff_frequently, hα]

@[instance]

Depends on / 依赖: comap_neBot_iff_frequently, f.comap, filter_eq_bot_of_isEmpty, isEmpty_or_nonempty, not_iff_not
-/
theorem comap_snd_neBot_iff {f : Filter β} :
    (f.comap (Prod.snd : α × β -> β)).NeBot ↔ Nonempty α ∧ f.NeBot := by
  rcases isEmpty_or_nonempty α with hα | hα
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp
  · simp [comap_neBot_iff_frequently, hα]

@[instance]
/--
theorem `comap_snd_neBot` / 定理 `comap_snd_neBot`

English:
theorem comap_snd_neBot
  given: [Nonempty α] {f : Filter β} [NeBot f]
  proof: comap_snd_neBot_iff.2 ⟨‹_›, ‹_›⟩

中文:
定理 comap_snd_neBot
  条件: [非空 α] {f : 滤子 β} [NeBot f]
  证明: comap_snd_neBot_iff.2 ⟨‹_›, ‹_›⟩

Depends on / 依赖: comap_snd_neBot_iff
-/
theorem comap_snd_neBot [Nonempty α] {f : Filter β} [NeBot f] :
    (f.comap (Prod.snd : α × β -> β)).NeBot :=
  comap_snd_neBot_iff.2 ⟨‹_›, ‹_›⟩

/--
theorem `comap_eval_neBot_iff'` / 定理 `comap_eval_neBot_iff'`

English:
theorem comap_eval_neBot_iff'
  given: {ι : Type*} {α : ι -> Type*} {i : ι} {f : Filter (α i)}
  proof: by
  rcases isEmpty_or_nonempty (forall j, α j) with H | H
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]
    simp [← Classical.nonempty_pi]
  · have : forall j, Nonempty (α j) := Classical.nonempty_pi.1 H
    simp [comap_neBot_iff_frequently, *]

@[simp]

中文:
定理 comap_eval_neBot_iff'
  条件: {ι : 类型} {α : ι -> 类型} {i : ι} {f : 滤子 (α i)}
  证明: by
  rcases isEmpty_or_nonempty (forall j, α j) with H | H
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]
    simp [← Classical.nonempty_pi]
  · have : forall j, Nonempty (α j) := Classical.nonempty_pi.1 H
    simp [comap_neBot_iff_frequently, *]

@[simp]

Depends on / 依赖: Classical, Classical.nonempty_pi, Nonempty, comap_neBot_iff_frequently, f.comap, filter_eq_bot_of_isEmpty, isEmpty_or_nonempty, nonempty_pi, not_iff_not
-/
theorem comap_eval_neBot_iff' {ι : Type*} {α : ι -> Type*} {i : ι} {f : Filter (α i)} :
    (comap (eval i) f).NeBot ↔ (forall j, Nonempty (α j)) ∧ NeBot f := by
  rcases isEmpty_or_nonempty (forall j, α j) with H | H
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]
    simp [← Classical.nonempty_pi]
  · have : forall j, Nonempty (α j) := Classical.nonempty_pi.1 H
    simp [comap_neBot_iff_frequently, *]

@[simp]
/--
theorem `comap_eval_neBot_iff` / 定理 `comap_eval_neBot_iff`

English:
theorem comap_eval_neBot_iff
  statement: {ι : Type*} {α : ι -> Type*} [forall j, Nonempty (α j)] {i : ι}
  proof: by simp [comap_eval_neBot_iff', *]

@[instance]

中文:
定理 comap_eval_neBot_iff
  结论: {ι : 类型} {α : ι -> 类型} [对任意 j, 非空 (α j)] {i : ι}
  证明: by simp [comap_eval_neBot_iff', *]

@[instance]

Depends on / 依赖: comap_eval_neBot_iff
-/
theorem comap_eval_neBot_iff {ι : Type*} {α : ι -> Type*} [forall j, Nonempty (α j)] {i : ι}
    {f : Filter (α i)} : (comap (eval i) f).NeBot ↔ NeBot f := by simp [comap_eval_neBot_iff', *]

@[instance]
/--
theorem `comap_eval_neBot` / 定理 `comap_eval_neBot`

English:
theorem comap_eval_neBot
  statement: {ι : Type*} {α : ι -> Type*} [forall j, Nonempty (α j)] (i : ι)
  proof: comap_eval_neBot_iff.2 ‹_›

中文:
定理 comap_eval_neBot
  结论: {ι : 类型} {α : ι -> 类型} [对任意 j, 非空 (α j)] (i : ι)
  证明: comap_eval_neBot_iff.2 ‹_›

Depends on / 依赖: comap_eval_neBot_iff
-/
theorem comap_eval_neBot {ι : Type*} {α : ι -> Type*} [forall j, Nonempty (α j)] (i : ι)
    (f : Filter (α i)) [NeBot f] : (comap (eval i) f).NeBot :=
  comap_eval_neBot_iff.2 ‹_›

/--
theorem `comap_coe_neBot_of_le_principal` / 定理 `comap_coe_neBot_of_le_principal`

English:
theorem comap_coe_neBot_of_le_principal
  given: {s : Set γ} {l : Filter γ} [h : NeBot l] (h' : l <= 𝓟 s)
  proof: h.comap_of_range_mem (@Subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)

中文:
定理 comap_coe_neBot_of_le_principal
  条件: {s : 集合 γ} {l : 滤子 γ} [h : NeBot l] (h' : l <= 𝓟 s)
  证明: h.comap_of_range_mem (@Subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)

Depends on / 依赖: Subtype, Subtype.range_coe, comap_of_range_mem, h.comap_of_range_mem, mem_principal_self, range_coe
-/
theorem comap_coe_neBot_of_le_principal {s : Set γ} {l : Filter γ} [h : NeBot l] (h' : l <= 𝓟 s) :
    NeBot (comap ((↑) : s -> γ) l) :=
h.comap_of_range_mem (@Subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)

/--
theorem `NeBot.comap_of_surj` / 定理 `NeBot.comap_of_surj`

English:
theorem NeBot.comap_of_surj
  given: {f : Filter β} {m : α -> β} (hf : NeBot f) (hm : Surjective m)
  proof: hf.comap_of_range_mem univ_mem' hm

中文:
定理 NeBot.comap_of_surj
  条件: {f : 滤子 β} {m : α -> β} (hf : NeBot f) (hm : 满射 m)
  证明: hf.comap_of_range_mem univ_mem' hm

Depends on / 依赖: comap_of_range_mem, hf.comap_of_range_mem, univ_mem
-/
theorem NeBot.comap_of_surj {f : Filter β} {m : α -> β} (hf : NeBot f) (hm : Surjective m) :
    NeBot (comap m f) :=
hf.comap_of_range_mem univ_mem' hm

/--
theorem `NeBot.comap_of_image_mem` / 定理 `NeBot.comap_of_image_mem`

English:
theorem NeBot.comap_of_image_mem
  statement: {f : Filter β} {m : α -> β} (hf : NeBot f) {s : Set α}
  proof: hf.comap_of_range_mem mem_of_superset hs (image_subset_range _ _)

@[simp]

中文:
定理 NeBot.comap_of_image_mem
  结论: {f : 滤子 β} {m : α -> β} (hf : NeBot f) {s : 集合 α}
  证明: hf.comap_of_range_mem mem_of_superset hs (image_subset_range _ _)

@[simp]

Depends on / 依赖: comap_of_range_mem, hf.comap_of_range_mem, image_subset_range, mem_of_superset
-/
theorem NeBot.comap_of_image_mem {f : Filter β} {m : α -> β} (hf : NeBot f) {s : Set α}
    (hs : m '' s in f) : NeBot (comap m f) :=
hf.comap_of_range_mem mem_of_superset hs (image_subset_range _ _)

@[simp]
/--
theorem `map_eq_bot_iff` / 定理 `map_eq_bot_iff`

English:
theorem map_eq_bot_iff
  statement: map m f = ⊥ ↔ f = ⊥
  proof: ⟨by
    rw [← empty_mem_iff_bot]; rw [← empty_mem_iff_bot]
    exact id, fun h => by simp only [h, map_bot]⟩

@[simp]

中文:
定理 map_eq_bot_iff
  结论: map m f = ⊥ ↔ f = ⊥
  证明: ⟨by
    rw [← empty_mem_iff_bot]; rw [← empty_mem_iff_bot]
    exact id, fun h => by simp only [h, map_bot]⟩

@[simp]

Depends on / 依赖: empty_mem_iff_bot, map_bot
-/
theorem map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
  ⟨by
    rw [← empty_mem_iff_bot]; rw [← empty_mem_iff_bot]
    exact id, fun h => by simp only [h, map_bot]⟩

@[simp]
/--
theorem `bot_eq_map_iff` / 定理 `bot_eq_map_iff`

English:
theorem bot_eq_map_iff
  statement: ⊥ = map m f ↔ f = ⊥
  proof: by rw [eq_comm, map_eq_bot_iff]

中文:
定理 bot_eq_map_iff
  结论: ⊥ = map m f ↔ f = ⊥
  证明: by rw [eq_comm, map_eq_bot_iff]

Depends on / 依赖: eq_comm, map_eq_bot_iff
-/
theorem bot_eq_map_iff : ⊥ = map m f ↔ f = ⊥ := by rw [eq_comm, map_eq_bot_iff]

/--
theorem `map_neBot_iff` / 定理 `map_neBot_iff`

English:
theorem map_neBot_iff
  given: (f : α -> β) {F : Filter α}
  statement: NeBot (map f F) ↔ NeBot F
  proof: by
  simp only [neBot_iff, Ne, map_eq_bot_iff]

中文:
定理 map_neBot_iff
  条件: (f : α -> β) {F : 滤子 α}
  结论: NeBot (map f F) ↔ NeBot F
  证明: by
  simp only [neBot_iff, Ne, map_eq_bot_iff]

Depends on / 依赖: map_eq_bot_iff, neBot_iff
-/
theorem map_neBot_iff (f : α -> β) {F : Filter α} : NeBot (map f F) ↔ NeBot F := by
  simp only [neBot_iff, Ne, map_eq_bot_iff]

/--
theorem `NeBot.map` / 定理 `NeBot.map`

English:
theorem NeBot.map
  given: (hf : NeBot f) (m : α -> β)
  statement: NeBot (map m f)
  proof: (map_neBot_iff m).2 hf

中文:
定理 NeBot.map
  条件: (hf : NeBot f) (m : α -> β)
  结论: NeBot (map m f)
  证明: (map_neBot_iff m).2 hf

Depends on / 依赖: map_neBot_iff
-/
theorem NeBot.map (hf : NeBot f) (m : α -> β) : NeBot (map m f) :=
  (map_neBot_iff m).2 hf

/--
theorem `NeBot.of_map` / 定理 `NeBot.of_map`

English:
theorem NeBot.of_map
  statement: NeBot (f.map m) -> NeBot f
  proof: (map_neBot_iff m).1

中文:
定理 NeBot.of_map
  结论: NeBot (f.map m) -> NeBot f
  证明: (map_neBot_iff m).1

Depends on / 依赖: map_neBot_iff
-/
theorem NeBot.of_map : NeBot (f.map m) -> NeBot f :=
  (map_neBot_iff m).1

/--
Instance `map_neBot` / 实例 `map_neBot`

English:
instance map_neBot
  signature: [hf : NeBot f]
  body: hf.map m

中文:
实例 map_neBot
  签名: [hf : NeBot f]
  定义体: hf.map m

Depends on / 依赖: hf.map
-/
instance map_neBot [hf : NeBot f] : NeBot (f.map m) :=
  hf.map m

/--
theorem `sInter_comap_sets` / 定理 `sInter_comap_sets`

English:
theorem sInter_comap_sets
  given: (f : α -> β) (F : Filter β)
  statement: ⋂₀ (comap f F).sets = ⋂ U in F, f ⁻¹' U
  proof: by
  ext x
  suffices (forall (A : Set α) (B : Set β), B in F -> f ⁻¹' B subseteq A -> x in A) ↔
      forall B : Set β, B in F -> f x in B by
    simp only [mem_sInter, mem_iInter, Filter.mem_sets, mem_comap, this, and_imp,
      mem_preimage, exists_imp]
  constructor
  · intro h U U_in
    simpa only [Subset.rfl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in
  · intro h V U U_in f_U_V
    exact f_U_V (h U U_in)

中文:
定理 s整数er_comap_sets
  条件: (f : α -> β) (F : 滤子 β)
  结论: ⋂₀ (comap f F).sets = ⋂ U in F, f ⁻¹' U
  证明: by
  ext x
  suffices (forall (A : Set α) (B : Set β), B in F -> f ⁻¹' B subseteq A -> x in A) ↔
      forall B : Set β, B in F -> f x in B by
    simp only [mem_sInter, mem_iInter, Filter.mem_sets, mem_comap, this, and_imp,
      mem_preimage, exists_imp]
  constructor
  · intro h U U_in
    simpa only [Subset.rfl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in
  · intro h V U U_in f_U_V
    exact f_U_V (h U U_in)

Depends on / 依赖: Filter, Filter.mem_sets, Subset, Subset.rfl, U_in, and_imp, exists_imp, f_U_V, forall_prop_of_true, mem_comap, mem_iInter, mem_preimage, mem_sInter, mem_sets, subseteq
-/
theorem sInter_comap_sets (f : α -> β) (F : Filter β) : ⋂₀ (comap f F).sets = ⋂ U in F, f ⁻¹' U := by
  ext x
  suffices (forall (A : Set α) (B : Set β), B in F -> f ⁻¹' B subseteq A -> x in A) ↔
      forall B : Set β, B in F -> f x in B by
    simp only [mem_sInter, mem_iInter, Filter.mem_sets, mem_comap, this, and_imp,
      mem_preimage, exists_imp]
  constructor
  · intro h U U_in
    simpa only [Subset.rfl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in
  · intro h V U U_in f_U_V
    exact f_U_V (h U U_in)

end Map

-- this is a generic rule for monotone functions:
/--
theorem `map_iInf_le` / 定理 `map_iInf_le`

English:
theorem map_iInf_le
  given: {f : ι -> Filter α} {m : α -> β}
  statement: map m (iInf f) <= ⨅ i, map m (f i)
  proof: le_iInf fun _ => map_mono iInf_le _ _

中文:
定理 map_iInf_le
  条件: {f : ι -> 滤子 α} {m : α -> β}
  结论: map m (iInf f) <= ⨅ i, map m (f i)
  证明: le_iInf fun _ => map_mono iInf_le _ _

Depends on / 依赖: iInf_le, le_iInf, map_mono
-/
theorem map_iInf_le {f : ι -> Filter α} {m : α -> β} : map m (iInf f) <= ⨅ i, map m (f i) :=
le_iInf fun _ => map_mono iInf_le _ _

/--
theorem `map_iInf_eq` / 定理 `map_iInf_eq`

English:
theorem map_iInf_eq
  given: {f : ι -> Filter α} {m : α -> β} (hf : Directed (· >= ·) f) [Nonempty ι]
  proof: map_iInf_le.antisymm fun s (hs : m ⁻¹' s in iInf f) =>
    let ⟨i, hi⟩ := (mem_iInf_of_directed hf _).1 hs
    have : ⨅ i, map m (f i) <= 𝓟 s :=
iInf_le_of_le i by simpa only [le_principal_iff, mem_map]
    Filter.le_principal_iff.1 this

中文:
定理 map_iInf_eq
  条件: {f : ι -> 滤子 α} {m : α -> β} (hf : Directed (· >= ·) f) [非空 ι]
  证明: map_iInf_le.antisymm fun s (hs : m ⁻¹' s in iInf f) =>
    let ⟨i, hi⟩ := (mem_iInf_of_directed hf _).1 hs
    have : ⨅ i, map m (f i) <= 𝓟 s :=
iInf_le_of_le i by simpa only [le_principal_iff, mem_map]
    Filter.le_principal_iff.1 this

Depends on / 依赖: Filter, Filter.le_principal_iff, antisymm, iInf_le_of_le, isArtinian_of_tower, le_principal_iff, map_iInf_le, map_iInf_le.antisymm, mem_iInf_of_directed, mem_map
-/
theorem map_iInf_eq {f : ι -> Filter α} {m : α -> β} (hf : Directed (· >= ·) f) [Nonempty ι] :
    map m (iInf f) = ⨅ i, map m (f i) :=
  map_iInf_le.antisymm fun s (hs : m ⁻¹' s in iInf f) =>
    let ⟨i, hi⟩ := (mem_iInf_of_directed hf _).1 hs
    have : ⨅ i, map m (f i) <= 𝓟 s :=
iInf_le_of_le i by simpa only [le_principal_iff, mem_map]
    Filter.le_principal_iff.1 this

/--
theorem `map_biInf_eq` / 定理 `map_biInf_eq`

English:
theorem map_biInf_eq
  statement: {ι : Type w} {f : ι -> Filter α} {m : α -> β} {p : ι -> Prop}
  proof: by
  have := nonempty_subtype.2 ne
  simp only [iInf_subtype']
  exact map_iInf_eq h.directed_val

中文:
定理 map_biInf_eq
  结论: {ι : 类型 w} {f : ι -> 滤子 α} {m : α -> β} {p : ι -> 命题}
  证明: by
  have := nonempty_subtype.2 ne
  simp only [iInf_subtype']
  exact map_iInf_eq h.directed_val

Depends on / 依赖: IsArtinianRing, IsDedekindFiniteMonoid, Semiring, directed_val, h.directed_val, iInf_subtype, map_iInf_eq, nonempty_subtype
-/
theorem map_biInf_eq {ι : Type w} {f : ι -> Filter α} {m : α -> β} {p : ι -> Prop}
    (h : DirectedOn (f ⁻¹'o (· >= ·)) { x | p x }) (ne : exists i, p i) :
    map m (⨅ (i) (_ : p i), f i) = ⨅ (i) (_ : p i), map m (f i) := by
  have := nonempty_subtype.2 ne
  simp only [iInf_subtype']
  exact map_iInf_eq h.directed_val

/--
theorem `map_inf_le` / 定理 `map_inf_le`

English:
theorem map_inf_le
  given: {f g : Filter α} {m : α -> β}
  statement: map m (f ⊓ g) <= map m f ⊓ map m g
  proof: (@map_mono _ _ m).map_inf_le f g

中文:
定理 map_inf_le
  条件: {f g : 滤子 α} {m : α -> β}
  结论: map m (f ⊓ g) <= map m f ⊓ map m g
  证明: (@map_mono _ _ m).map_inf_le f g

Depends on / 依赖: map_inf_le, map_mono
-/
theorem map_inf_le {f g : Filter α} {m : α -> β} : map m (f ⊓ g) <= map m f ⊓ map m g :=
  (@map_mono _ _ m).map_inf_le f g

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: {f g : Filter α} {m : α -> β} (h : Injective m)
  proof: by
  refine map_inf_le.antisymm ?_
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ inter s₂⟩
  refine mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) ?_
  rw [← image_inter h]; rw [image_subset_iff]; rw [ht]

中文:
定理 map_inf
  条件: {f g : 滤子 α} {m : α -> β} (h : 单射 m)
  证明: by
  refine map_inf_le.antisymm ?_
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ inter s₂⟩
  refine mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) ?_
  rw [← image_inter h]; rw [image_subset_iff]; rw [ht]

Depends on / 依赖: antisymm, image_inter, image_mem_map, image_subset_iff, map_inf_le, map_inf_le.antisymm, mem_inf_of_inter
-/
theorem map_inf {f g : Filter α} {m : α -> β} (h : Injective m) :
    map m (f ⊓ g) = map m f ⊓ map m g := by
  refine map_inf_le.antisymm ?_
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ inter s₂⟩
  refine mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) ?_
  rw [← image_inter h]; rw [image_subset_iff]; rw [ht]

/--
theorem `map_inf'` / 定理 `map_inf'`

English:
theorem map_inf'
  statement: {f g : Filter α} {m : α -> β} {t : Set α} (htf : t in f) (htg : t in g)
  proof: by
  lift f to Filter t using htf; lift g to Filter t using htg
  replace h : Injective (m ∘ ((↑) : t -> α)) := h.injective
  simp only [map_map, ← map_inf Subtype.coe_injective, map_inf h]

中文:
定理 map_inf'
  结论: {f g : 滤子 α} {m : α -> β} {t : 集合 α} (htf : t in f) (htg : t in g)
  证明: by
  lift f to Filter t using htf; lift g to Filter t using htg
  replace h : Injective (m ∘ ((↑) : t -> α)) := h.injective
  simp only [map_map, ← map_inf Subtype.coe_injective, map_inf h]

Depends on / 依赖: Filter, Injective, Subtype, Subtype.coe_injective, coe_injective, h.injective, injective, map_inf, map_map, replace
-/
theorem map_inf' {f g : Filter α} {m : α -> β} {t : Set α} (htf : t in f) (htg : t in g)
    (h : InjOn m t) : map m (f ⊓ g) = map m f ⊓ map m g := by
  lift f to Filter t using htf; lift g to Filter t using htg
  replace h : Injective (m ∘ ((↑) : t -> α)) := h.injective
  simp only [map_map, ← map_inf Subtype.coe_injective, map_inf h]

/--
lemma `disjoint_of_map` / 引理 `disjoint_of_map`

English:
lemma disjoint_of_map
  statement: {α β : Type*} {F G : Filter α} {f : α -> β}
  proof: disjoint_iff.mpr map_eq_bot_iff.mp le_bot_iff.mp trans map_inf_le (disjoint_iff.mp h)

中文:
引理 disjoint_of_map
  结论: {α β : 类型} {F G : 滤子 α} {f : α -> β}
  证明: disjoint_iff.mpr map_eq_bot_iff.mp le_bot_iff.mp trans map_inf_le (disjoint_iff.mp h)

Depends on / 依赖: disjoint_iff, disjoint_iff.mp, disjoint_iff.mpr, le_bot_iff, le_bot_iff.mp, map_eq_bot_iff, map_eq_bot_iff.mp, map_inf_le, of_finite
-/
lemma disjoint_of_map {α β : Type*} {F G : Filter α} {f : α -> β}
    (h : Disjoint (map f F) (map f G)) : Disjoint F G :=
disjoint_iff.mpr map_eq_bot_iff.mp le_bot_iff.mp trans map_inf_le (disjoint_iff.mp h)

/--
theorem `disjoint_map` / 定理 `disjoint_map`

English:
theorem disjoint_map
  given: {m : α -> β} (hm : Injective m) {f₁ f₂ : Filter α}
  proof: by
  simp only [disjoint_iff, ← map_inf hm, map_eq_bot_iff]

中文:
定理 disjoint_map
  条件: {m : α -> β} (hm : 单射 m) {f₁ f₂ : 滤子 α}
  证明: by
  simp only [disjoint_iff, ← map_inf hm, map_eq_bot_iff]

Depends on / 依赖: disjoint_iff, map_eq_bot_iff, map_inf, of_finite
-/
theorem disjoint_map {m : α -> β} (hm : Injective m) {f₁ f₂ : Filter α} :
    Disjoint (map m f₁) (map m f₂) ↔ Disjoint f₁ f₂ := by
  simp only [disjoint_iff, ← map_inf hm, map_eq_bot_iff]

/--
theorem `map_equiv_symm` / 定理 `map_equiv_symm`

English:
theorem map_equiv_symm
  given: (e : α ≃ β) (f : Filter β)
  statement: map e.symm f = comap e f
  proof: map_injective e.injective by
    rw [map_map]; rw [e.self_comp_symm]; rw [map_id]; rw [map_comap_of_surjective e.surjective]

中文:
定理 map_equiv_symm
  条件: (e : α ≃ β) (f : 滤子 β)
  结论: map e.symm f = comap e f
  证明: map_injective e.injective by
    rw [map_map]; rw [e.self_comp_symm]; rw [map_id]; rw [map_comap_of_surjective e.surjective]

Depends on / 依赖: e.injective, e.self_comp_symm, e.surjective, injective, map_comap_of_surjective, map_id, map_injective, map_map, self_comp_symm, surjective
-/
theorem map_equiv_symm (e : α ≃ β) (f : Filter β) : map e.symm f = comap e f :=
map_injective e.injective by
    rw [map_map]; rw [e.self_comp_symm]; rw [map_id]; rw [map_comap_of_surjective e.surjective]

/--
theorem `map_eq_comap_of_inverse` / 定理 `map_eq_comap_of_inverse`

English:
theorem map_eq_comap_of_inverse
  statement: {f : Filter α} {m : α -> β} {n : β -> α} (h₁ : m ∘ n = id)
  proof: map_equiv_symm ⟨n, m, congr_fun h₁, congr_fun h₂⟩ f

中文:
定理 map_eq_comap_of_inverse
  结论: {f : 滤子 α} {m : α -> β} {n : β -> α} (h₁ : m ∘ n = id)
  证明: map_equiv_symm ⟨n, m, congr_fun h₁, congr_fun h₂⟩ f

Depends on / 依赖: congr_fun, map_equiv_symm
-/
theorem map_eq_comap_of_inverse {f : Filter α} {m : α -> β} {n : β -> α} (h₁ : m ∘ n = id)
    (h₂ : n ∘ m = id) : map m f = comap n f :=
  map_equiv_symm ⟨n, m, congr_fun h₁, congr_fun h₂⟩ f

/--
theorem `comap_equiv_symm` / 定理 `comap_equiv_symm`

English:
theorem comap_equiv_symm
  given: (e : α ≃ β) (f : Filter α)
  statement: comap e.symm f = map e f
  proof: (map_eq_comap_of_inverse e.self_comp_symm e.symm_comp_self).symm

中文:
定理 comap_equiv_symm
  条件: (e : α ≃ β) (f : 滤子 α)
  结论: comap e.symm f = map e f
  证明: (map_eq_comap_of_inverse e.self_comp_symm e.symm_comp_self).symm

Depends on / 依赖: e.self_comp_symm, e.symm_comp_self, map_eq_comap_of_inverse, self_comp_symm, symm_comp_self
-/
theorem comap_equiv_symm (e : α ≃ β) (f : Filter α) : comap e.symm f = map e f :=
  (map_eq_comap_of_inverse e.self_comp_symm e.symm_comp_self).symm

/--
theorem `map_swap_eq_comap_swap` / 定理 `map_swap_eq_comap_swap`

English:
theorem map_swap_eq_comap_swap
  given: {f : Filter (α × β)}
  statement: map Prod.swap f = comap Prod.swap f
  proof: map_eq_comap_of_inverse Prod.swap_swap_eq Prod.swap_swap_eq

中文:
定理 map_swap_eq_comap_swap
  条件: {f : 滤子 (α × β)}
  结论: map 积类型.swap f = comap 积类型.swap f
  证明: map_eq_comap_of_inverse Prod.swap_swap_eq Prod.swap_swap_eq

Depends on / 依赖: Prod.swap_swap_eq, map_eq_comap_of_inverse, swap_swap_eq
-/
theorem map_swap_eq_comap_swap {f : Filter (α × β)} : map Prod.swap f = comap Prod.swap f :=
  map_eq_comap_of_inverse Prod.swap_swap_eq Prod.swap_swap_eq

/--
theorem `map_swap4_eq_comap` / 定理 `map_swap4_eq_comap`

English:
theorem map_swap4_eq_comap
  given: {f : Filter ((α × β) × γ × δ)}
  proof: map_eq_comap_of_inverse (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl) (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)

中文:
定理 map_swap4_eq_comap
  条件: {f : 滤子 ((α × β) × γ × δ)}
  证明: map_eq_comap_of_inverse (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl) (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)

Depends on / 依赖: map_eq_comap_of_inverse
-/
theorem map_swap4_eq_comap {f : Filter ((α × β) × γ × δ)} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f =
      comap (fun p : (α × γ) × β × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f :=
  map_eq_comap_of_inverse (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl) (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)

/--
theorem `le_map` / 定理 `le_map`

English:
theorem le_map
  given: {f : Filter α} {m : α -> β} {g : Filter β} (h : forall s in f, m '' s in g)
  statement: g <= f.map m
  proof: fun _ hs => mem_of_superset (h _ hs) image_preimage_subset _ _

中文:
定理 le_map
  条件: {f : 滤子 α} {m : α -> β} {g : 滤子 β} (h : 对任意 s in f, m '' s in g)
  结论: g <= f.map m
  证明: fun _ hs => mem_of_superset (h _ hs) image_preimage_subset _ _

Depends on / 依赖: Ideal.idealProdEquiv.toOrderEmbedding.wellFoundedLT, idealProdEquiv, image_preimage_subset, mem_of_superset, toOrderEmbedding, wellFoundedLT
-/
theorem le_map {f : Filter α} {m : α -> β} {g : Filter β} (h : forall s in f, m '' s in g) : g <= f.map m :=
fun _ hs => mem_of_superset (h _ hs) image_preimage_subset _ _

/--
theorem `le_map_iff` / 定理 `le_map_iff`

English:
theorem le_map_iff
  given: {f : Filter α} {m : α -> β} {g : Filter β}
  statement: g <= f.map m ↔ forall s in f, m '' s in g
  proof: ⟨fun h _ hs => h (image_mem_map hs), le_map⟩

中文:
定理 le_map_iff
  条件: {f : 滤子 α} {m : α -> β} {g : 滤子 β}
  结论: g <= f.map m ↔ 对任意 s in f, m '' s in g
  证明: ⟨fun h _ hs => h (image_mem_map hs), le_map⟩

Depends on / 依赖: Finite, Finite.induction_empty_option, RingEquiv, RingEquiv.isArtinianRing, image_mem_map, induction_empty_option, infer_instance, isArtinianRing, le_map, piCongrLeft, piOptionEquivProd
-/
theorem le_map_iff {f : Filter α} {m : α -> β} {g : Filter β} : g <= f.map m ↔ forall s in f, m '' s in g :=
  ⟨fun h _ hs => h (image_mem_map hs), le_map⟩

/--
theorem `push_pull` / 定理 `push_pull`

English:
theorem push_pull
  given: (f : α -> β) (F : Filter α) (G : Filter β)
  proof: by
  apply le_antisymm
  · calc
      map f (F ⊓ comap f G) <= map f F ⊓ (map f <| comap f G) := map_inf_le
      _ <= map f F ⊓ G := inf_le_inf_left (map f F) map_comap_le
  · rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩
    apply mem_inf_of_inter (image_mem_map V_in) Z_in
    calc
      f '' V inter Z = f '' (V inter f ⁻¹' Z) := by rw [image_inter_preimage]
      _ subseteq f '' (V inter W) := by gcongr
      _ = f '' f ⁻¹' U := by rw [h]
      _ subseteq U := image_preimage_subset f U

中文:
定理 push_pull
  条件: (f : α -> β) (F : 滤子 α) (G : 滤子 β)
  证明: by
  apply le_antisymm
  · calc
      map f (F ⊓ comap f G) <= map f F ⊓ (map f <| comap f G) := map_inf_le
      _ <= map f F ⊓ G := inf_le_inf_left (map f F) map_comap_le
  · rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩
    apply mem_inf_of_inter (image_mem_map V_in) Z_in
    calc
      f '' V inter Z = f '' (V inter f ⁻¹' Z) := by rw [image_inter_preimage]
      _ subseteq f '' (V inter W) := by gcongr
      _ = f '' f ⁻¹' U := by rw [h]
      _ subseteq U := image_preimage_subset f U
-/
protected theorem push_pull (f : α -> β) (F : Filter α) (G : Filter β) :
    map f (F ⊓ comap f G) = map f F ⊓ G := by
  apply le_antisymm
  · calc
      map f (F ⊓ comap f G) <= map f F ⊓ (map f <| comap f G) := map_inf_le
      _ <= map f F ⊓ G := inf_le_inf_left (map f F) map_comap_le
  · rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩
    apply mem_inf_of_inter (image_mem_map V_in) Z_in
    calc
      f '' V inter Z = f '' (V inter f ⁻¹' Z) := by rw [image_inter_preimage]
      _ subseteq f '' (V inter W) := by gcongr
      _ = f '' f ⁻¹' U := by rw [h]
      _ subseteq U := image_preimage_subset f U

/--
theorem `push_pull'` / 定理 `push_pull'`

English:
theorem push_pull'
  given: (f : α -> β) (F : Filter α) (G : Filter β)
  proof: by simp only [Filter.push_pull, inf_comm]

中文:
定理 push_pull'
  条件: (f : α -> β) (F : 滤子 α) (G : 滤子 β)
  证明: by simp only [Filter.push_pull, inf_comm]
-/
protected theorem push_pull' (f : α -> β) (F : Filter α) (G : Filter β) :
    map f (comap f G ⊓ F) = G ⊓ map f F := by simp only [Filter.push_pull, inf_comm]

/--
theorem `disjoint_comap_iff_map` / 定理 `disjoint_comap_iff_map`

English:
theorem disjoint_comap_iff_map
  given: {f : α -> β} {F : Filter α} {G : Filter β}
  proof: by
  simp only [disjoint_iff, ← Filter.push_pull, map_eq_bot_iff]

中文:
定理 disjoint_comap_iff_map
  条件: {f : α -> β} {F : 滤子 α} {G : 滤子 β}
  证明: by
  simp only [disjoint_iff, ← Filter.push_pull, map_eq_bot_iff]

Depends on / 依赖: Filter, Filter.push_pull, disjoint_iff, map_eq_bot_iff, push_pull
-/
theorem disjoint_comap_iff_map {f : α -> β} {F : Filter α} {G : Filter β} :
    Disjoint F (comap f G) ↔ Disjoint (map f F) G := by
  simp only [disjoint_iff, ← Filter.push_pull, map_eq_bot_iff]

/--
theorem `disjoint_comap_iff_map'` / 定理 `disjoint_comap_iff_map'`

English:
theorem disjoint_comap_iff_map'
  given: {f : α -> β} {F : Filter α} {G : Filter β}
  proof: by
  simp only [disjoint_iff, ← Filter.push_pull', map_eq_bot_iff]

中文:
定理 disjoint_comap_iff_map'
  条件: {f : α -> β} {F : 滤子 α} {G : 滤子 β}
  证明: by
  simp only [disjoint_iff, ← Filter.push_pull', map_eq_bot_iff]

Depends on / 依赖: Filter, Filter.push_pull, disjoint_iff, map_eq_bot_iff, push_pull
-/
theorem disjoint_comap_iff_map' {f : α -> β} {F : Filter α} {G : Filter β} :
    Disjoint (comap f G) F ↔ Disjoint G (map f F) := by
  simp only [disjoint_iff, ← Filter.push_pull', map_eq_bot_iff]

/--
theorem `neBot_inf_comap_iff_map` / 定理 `neBot_inf_comap_iff_map`

English:
theorem neBot_inf_comap_iff_map
  given: {f : α -> β} {F : Filter α} {G : Filter β}
  proof: by
  rw [← map_neBot_iff]; rw [Filter.push_pull]

中文:
定理 neBot_inf_comap_iff_map
  条件: {f : α -> β} {F : 滤子 α} {G : 滤子 β}
  证明: by
  rw [← map_neBot_iff]; rw [Filter.push_pull]

Depends on / 依赖: Filter, Filter.push_pull, map_neBot_iff, push_pull
-/
theorem neBot_inf_comap_iff_map {f : α -> β} {F : Filter α} {G : Filter β} :
    NeBot (F ⊓ comap f G) ↔ NeBot (map f F ⊓ G) := by
  rw [← map_neBot_iff]; rw [Filter.push_pull]

/--
theorem `neBot_inf_comap_iff_map'` / 定理 `neBot_inf_comap_iff_map'`

English:
theorem neBot_inf_comap_iff_map'
  given: {f : α -> β} {F : Filter α} {G : Filter β}
  proof: by
  rw [← map_neBot_iff]; rw [Filter.push_pull']

中文:
定理 neBot_inf_comap_iff_map'
  条件: {f : α -> β} {F : 滤子 α} {G : 滤子 β}
  证明: by
  rw [← map_neBot_iff]; rw [Filter.push_pull']

Depends on / 依赖: Filter, Filter.push_pull, map_neBot_iff, push_pull
-/
theorem neBot_inf_comap_iff_map' {f : α -> β} {F : Filter α} {G : Filter β} :
    NeBot (comap f G ⊓ F) ↔ NeBot (G ⊓ map f F) := by
  rw [← map_neBot_iff]; rw [Filter.push_pull']

/--
theorem `comap_inf_principal_neBot_of_image_mem` / 定理 `comap_inf_principal_neBot_of_image_mem`

English:
theorem comap_inf_principal_neBot_of_image_mem
  statement: {f : Filter β} {m : α -> β} (hf : NeBot f) {s : Set α}
  proof: by
  rw [neBot_inf_comap_iff_map']; rw [map_principal]; rw [← frequently_mem_iff_neBot]
  exact Eventually.frequently hs

中文:
定理 comap_inf_principal_neBot_of_image_mem
  结论: {f : 滤子 β} {m : α -> β} (hf : NeBot f) {s : 集合 α}
  证明: by
  rw [neBot_inf_comap_iff_map']; rw [map_principal]; rw [← frequently_mem_iff_neBot]
  exact Eventually.frequently hs

Depends on / 依赖: Eventually, Eventually.frequently, frequently, frequently_mem_iff_neBot, map_principal, neBot_inf_comap_iff_map
-/
theorem comap_inf_principal_neBot_of_image_mem {f : Filter β} {m : α -> β} (hf : NeBot f) {s : Set α}
    (hs : m '' s in f) : NeBot (comap m f ⊓ 𝓟 s) := by
  rw [neBot_inf_comap_iff_map']; rw [map_principal]; rw [← frequently_mem_iff_neBot]
  exact Eventually.frequently hs

/--
theorem `principal_eq_map_coe_top` / 定理 `principal_eq_map_coe_top`

English:
theorem principal_eq_map_coe_top
  given: (s : Set α)
  statement: 𝓟 s = map ((↑) : s -> α) ⊤
  proof: by simp

中文:
定理 principal_eq_map_coe_top
  条件: (s : 集合 α)
  结论: 𝓟 s = map ((↑) : s -> α) ⊤
  证明: by simp
-/
theorem principal_eq_map_coe_top (s : Set α) : 𝓟 s = map ((↑) : s -> α) ⊤ := by simp

/--
theorem `inf_principal_eq_bot_iff_comap` / 定理 `inf_principal_eq_bot_iff_comap`

English:
theorem inf_principal_eq_bot_iff_comap
  given: {F : Filter α} {s : Set α}
  proof: by
  rw [principal_eq_map_coe_top s]; rw [← Filter.push_pull']; rw [inf_top_eq]; rw [map_eq_bot_iff]

中文:
定理 inf_principal_eq_bot_iff_comap
  条件: {F : 滤子 α} {s : 集合 α}
  证明: by
  rw [principal_eq_map_coe_top s]; rw [← Filter.push_pull']; rw [inf_top_eq]; rw [map_eq_bot_iff]

Depends on / 依赖: Filter, Filter.push_pull, inf_top_eq, map_eq_bot_iff, principal_eq_map_coe_top, push_pull
-/
theorem inf_principal_eq_bot_iff_comap {F : Filter α} {s : Set α} :
    F ⊓ 𝓟 s = ⊥ ↔ comap ((↑) : s -> α) F = ⊥ := by
  rw [principal_eq_map_coe_top s]; rw [← Filter.push_pull']; rw [inf_top_eq]; rw [map_eq_bot_iff]

/--
lemma `map_generate_le_generate_preimage_preimage` / 引理 `map_generate_le_generate_preimage_preimage`

English:
lemma map_generate_le_generate_preimage_preimage
  given: (U : Set (Set β)) (f : β -> α)
  proof: by
  rw [le_generate_iff]
  exact fun u hu => mem_generate_of_mem hu

中文:
引理 map_generate_le_generate_preimage_preimage
  条件: (U : 集合 (集合 β)) (f : β -> α)
  证明: by
  rw [le_generate_iff]
  exact fun u hu => mem_generate_of_mem hu

Depends on / 依赖: le_generate_iff, mem_generate_of_mem
-/
lemma map_generate_le_generate_preimage_preimage (U : Set (Set β)) (f : β -> α) :
    map f (generate U) <= generate ((f ⁻¹' ·) ⁻¹' U) := by
  rw [le_generate_iff]
  exact fun u hu => mem_generate_of_mem hu

/--
lemma `generate_image_preimage_le_comap` / 引理 `generate_image_preimage_le_comap`

English:
lemma generate_image_preimage_le_comap
  given: (U : Set (Set α)) (f : β -> α)
  proof: by
  rw [← map_le_iff_le_comap]; rw [le_generate_iff]
  exact fun u hu => mem_generate_of_mem ⟨u, hu, rfl⟩

中文:
引理 generate_image_preimage_le_comap
  条件: (U : 集合 (集合 α)) (f : β -> α)
  证明: by
  rw [← map_le_iff_le_comap]; rw [le_generate_iff]
  exact fun u hu => mem_generate_of_mem ⟨u, hu, rfl⟩

Depends on / 依赖: le_generate_iff, map_le_iff_le_comap, mem_generate_of_mem
-/
lemma generate_image_preimage_le_comap (U : Set (Set α)) (f : β -> α) :
    generate ((f ⁻¹' ·) '' U) <= comap f (generate U) := by
  rw [← map_le_iff_le_comap]; rw [le_generate_iff]
  exact fun u hu => mem_generate_of_mem ⟨u, hu, rfl⟩

section Applicative

/--
theorem `singleton_mem_pure` / 定理 `singleton_mem_pure`

English:
theorem singleton_mem_pure
  given: {a : α}
  statement: {a} in (pure a : Filter α)
  proof: mem_singleton a

中文:
定理 singleton_mem_pure
  条件: {a : α}
  结论: {a} in (pure a : 滤子 α)
  证明: mem_singleton a

Depends on / 依赖: mem_singleton
-/
theorem singleton_mem_pure {a : α} : {a} in (pure a : Filter α) :=
  mem_singleton a

/--
theorem `pure_injective` / 定理 `pure_injective`

English:
theorem pure_injective
  statement: Injective (pure : α -> Filter α)
  proof: fun a _ hab =>
  (Filter.ext_iff.1 hab { x | a = x }).1 rfl

中文:
定理 pure_injective
  结论: 单射 (pure : α -> 滤子 α)
  证明: fun a _ hab =>
  (Filter.ext_iff.1 hab { x | a = x }).1 rfl
-/
theorem pure_injective : Injective (pure : α -> Filter α) := fun a _ hab =>
  (Filter.ext_iff.1 hab { x | a = x }).1 rfl

/--
Instance `pure_neBot` / 实例 `pure_neBot`

English:
instance pure_neBot
  signature: {α : Type u} {a : α}
  body: ⟨mt empty_mem_iff_bot.2 notMem_empty a⟩

@[simp]

中文:
实例 pure_neBot
  签名: {α : 类型u} {a : α}
  定义体: ⟨mt empty_mem_iff_bot.2 notMem_empty a⟩

@[simp]

Depends on / 依赖: empty_mem_iff_bot, notMem_empty
-/
instance pure_neBot {α : Type u} {a : α} : NeBot (pure a) :=
⟨mt empty_mem_iff_bot.2 notMem_empty a⟩

@[simp]
/--
theorem `le_pure_iff` / 定理 `le_pure_iff`

English:
theorem le_pure_iff
  given: {f : Filter α} {a : α}
  statement: f <= pure a ↔ {a} in f
  proof: by
  rw [← principal_singleton]; rw [le_principal_iff]

中文:
定理 le_pure_iff
  条件: {f : 滤子 α} {a : α}
  结论: f <= pure a ↔ {a} in f
  证明: by
  rw [← principal_singleton]; rw [le_principal_iff]

Depends on / 依赖: le_principal_iff, principal_singleton
-/
theorem le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {a} in f := by
  rw [← principal_singleton]; rw [le_principal_iff]

/--
theorem `mem_seq_def` / 定理 `mem_seq_def`

English:
theorem mem_seq_def
  given: {f : Filter (α -> β)} {g : Filter α} {s : Set β}
  proof: Iff.rfl

中文:
定理 mem_seq_def
  条件: {f : 滤子 (α -> β)} {g : 滤子 α} {s : 集合 β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_seq_def {f : Filter (α -> β)} {g : Filter α} {s : Set β} :
    s in f.seq g ↔ exists u in f, exists t in g, forall x in u, forall y in t, (x : α -> β) y in s :=
  Iff.rfl

/--
theorem `mem_seq_iff` / 定理 `mem_seq_iff`

English:
theorem mem_seq_iff
  given: {f : Filter (α -> β)} {g : Filter α} {s : Set β}
  proof: by
  simp only [mem_seq_def, seq_subset]

中文:
定理 mem_seq_iff
  条件: {f : 滤子 (α -> β)} {g : 滤子 α} {s : 集合 β}
  证明: by
  simp only [mem_seq_def, seq_subset]

Depends on / 依赖: mem_seq_def, seq_subset
-/
theorem mem_seq_iff {f : Filter (α -> β)} {g : Filter α} {s : Set β} :
    s in f.seq g ↔ exists u in f, exists t in g, Set.seq u t subseteq s := by
  simp only [mem_seq_def, seq_subset]

/--
theorem `mem_map_seq_iff` / 定理 `mem_map_seq_iff`

English:
theorem mem_map_seq_iff
  given: {f : Filter α} {g : Filter β} {m : α -> β -> γ} {s : Set γ}
  proof: Iff.intro (fun ⟨t, ht, s, hs, hts⟩ => ⟨s, m ⁻¹' t, hs, ht, fun _ => hts _⟩)
    fun ⟨t, s, ht, hs, hts⟩ =>
    ⟨m '' s, image_mem_map hs, t, ht, fun _ ⟨_, has, Eq⟩ => Eq ▸ hts _ has⟩

中文:
定理 mem_map_seq_iff
  条件: {f : 滤子 α} {g : 滤子 β} {m : α -> β -> γ} {s : 集合 γ}
  证明: Iff.intro (fun ⟨t, ht, s, hs, hts⟩ => ⟨s, m ⁻¹' t, hs, ht, fun _ => hts _⟩)
    fun ⟨t, s, ht, hs, hts⟩ =>
    ⟨m '' s, image_mem_map hs, t, ht, fun _ ⟨_, has, Eq⟩ => Eq ▸ hts _ has⟩

Depends on / 依赖: Iff.intro, image_mem_map
-/
theorem mem_map_seq_iff {f : Filter α} {g : Filter β} {m : α -> β -> γ} {s : Set γ} :
    s in (f.map m).seq g ↔ exists t u, t in g ∧ u in f ∧ forall x in u, forall y in t, m x y in s :=
  Iff.intro (fun ⟨t, ht, s, hs, hts⟩ => ⟨s, m ⁻¹' t, hs, ht, fun _ => hts _⟩)
    fun ⟨t, s, ht, hs, hts⟩ =>
    ⟨m '' s, image_mem_map hs, t, ht, fun _ ⟨_, has, Eq⟩ => Eq ▸ hts _ has⟩

/--
theorem `seq_mem_seq` / 定理 `seq_mem_seq`

English:
theorem seq_mem_seq
  statement: {f : Filter (α -> β)} {g : Filter α} {s : Set (α -> β)} {t : Set α} (hs : s in f)
  proof: ⟨s, hs, t, ht, fun f hf a ha => ⟨f, hf, a, ha, rfl⟩⟩

中文:
定理 seq_mem_seq
  结论: {f : 滤子 (α -> β)} {g : 滤子 α} {s : 集合 (α -> β)} {t : 集合 α} (hs : s in f)
  证明: ⟨s, hs, t, ht, fun f hf a ha => ⟨f, hf, a, ha, rfl⟩⟩
-/
theorem seq_mem_seq {f : Filter (α -> β)} {g : Filter α} {s : Set (α -> β)} {t : Set α} (hs : s in f)
    (ht : t in g) : s.seq t in f.seq g :=
  ⟨s, hs, t, ht, fun f hf a ha => ⟨f, hf, a, ha, rfl⟩⟩

/--
theorem `le_seq` / 定理 `le_seq`

English:
theorem le_seq
  statement: {f : Filter (α -> β)} {g : Filter α} {h : Filter β}
  proof: fun _ ⟨_, ht, _, hu, hs⟩ =>
  mem_of_superset (hh _ ht _ hu) fun _ ⟨_, hm, _, ha, eq⟩ => eq ▸ hs _ hm _ ha

@[gcongr, mono]

中文:
定理 le_seq
  结论: {f : 滤子 (α -> β)} {g : 滤子 α} {h : 滤子 β}
  证明: fun _ ⟨_, ht, _, hu, hs⟩ =>
  mem_of_superset (hh _ ht _ hu) fun _ ⟨_, hm, _, ha, eq⟩ => eq ▸ hs _ hm _ ha

@[gcongr, mono]
-/
theorem le_seq {f : Filter (α -> β)} {g : Filter α} {h : Filter β}
    (hh : forall t in f, forall u in g, Set.seq t u in h) : h <= seq f g := fun _ ⟨_, ht, _, hu, hs⟩ =>
  mem_of_superset (hh _ ht _ hu) fun _ ⟨_, hm, _, ha, eq⟩ => eq ▸ hs _ hm _ ha

@[gcongr, mono]
/--
theorem `seq_mono` / 定理 `seq_mono`

English:
theorem seq_mono
  given: {f₁ f₂ : Filter (α -> β)} {g₁ g₂ : Filter α} (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  proof: le_seq fun _ hs _ ht => seq_mem_seq (hf hs) (hg ht)

@[simp]

中文:
定理 seq_mono
  条件: {f₁ f₂ : 滤子 (α -> β)} {g₁ g₂ : 滤子 α} (hf : f₁ <= f₂) (hg : g₁ <= g₂)
  证明: le_seq fun _ hs _ ht => seq_mem_seq (hf hs) (hg ht)

@[simp]

Depends on / 依赖: le_seq, seq_mem_seq
-/
theorem seq_mono {f₁ f₂ : Filter (α -> β)} {g₁ g₂ : Filter α} (hf : f₁ <= f₂) (hg : g₁ <= g₂) :
    f₁.seq g₁ <= f₂.seq g₂ :=
  le_seq fun _ hs _ ht => seq_mem_seq (hf hs) (hg ht)

@[simp]
/--
theorem `pure_seq_eq_map` / 定理 `pure_seq_eq_map`

English:
theorem pure_seq_eq_map
  given: (g : α -> β) (f : Filter α)
  statement: seq (pure g) f = f.map g
  proof: by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← singleton_seq]
    apply seq_mem_seq _ hs
    exact singleton_mem_pure
  · refine sets_of_superset (map g f) (image_mem_map ht) ?_
    rintro b ⟨a, ha, rfl⟩
    exact ⟨g, hs, a, ha, rfl⟩

@[simp]

中文:
定理 pure_seq_eq_map
  条件: (g : α -> β) (f : 滤子 α)
  结论: seq (pure g) f = f.map g
  证明: by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← singleton_seq]
    apply seq_mem_seq _ hs
    exact singleton_mem_pure
  · refine sets_of_superset (map g f) (image_mem_map ht) ?_
    rintro b ⟨a, ha, rfl⟩
    exact ⟨g, hs, a, ha, rfl⟩

@[simp]

Depends on / 依赖: image_mem_map, le_antisymm, le_map, le_seq, seq_mem_seq, sets_of_superset, singleton_mem_pure, singleton_seq
-/
theorem pure_seq_eq_map (g : α -> β) (f : Filter α) : seq (pure g) f = f.map g := by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← singleton_seq]
    apply seq_mem_seq _ hs
    exact singleton_mem_pure
  · refine sets_of_superset (map g f) (image_mem_map ht) ?_
    rintro b ⟨a, ha, rfl⟩
    exact ⟨g, hs, a, ha, rfl⟩

@[simp]
/--
theorem `seq_pure` / 定理 `seq_pure`

English:
theorem seq_pure
  given: (f : Filter (α -> β)) (a : α)
  statement: seq f (pure a) = map (fun g : α -> β => g a) f
  proof: by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← seq_singleton]
    exact seq_mem_seq hs singleton_mem_pure
  · refine sets_of_superset (map (fun g : α -> β => g a) f) (image_mem_map hs) ?_
    rintro b ⟨g, hg, rfl⟩
    exact ⟨g, hg, a, ht, rfl⟩

@[simp]

中文:
定理 seq_pure
  条件: (f : 滤子 (α -> β)) (a : α)
  结论: seq f (pure a) = map (fun g : α -> β => g a) f
  证明: by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← seq_singleton]
    exact seq_mem_seq hs singleton_mem_pure
  · refine sets_of_superset (map (fun g : α -> β => g a) f) (image_mem_map hs) ?_
    rintro b ⟨g, hg, rfl⟩
    exact ⟨g, hg, a, ht, rfl⟩

@[simp]

Depends on / 依赖: image_mem_map, le_antisymm, le_map, le_seq, seq_mem_seq, seq_singleton, sets_of_superset, singleton_mem_pure
-/
theorem seq_pure (f : Filter (α -> β)) (a : α) : seq f (pure a) = map (fun g : α -> β => g a) f := by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← seq_singleton]
    exact seq_mem_seq hs singleton_mem_pure
  · refine sets_of_superset (map (fun g : α -> β => g a) f) (image_mem_map hs) ?_
    rintro b ⟨g, hg, rfl⟩
    exact ⟨g, hg, a, ht, rfl⟩

@[simp]
/--
theorem `seq_assoc` / 定理 `seq_assoc`

English:
theorem seq_assoc
  given: (x : Filter α) (g : Filter (α -> β)) (h : Filter (β -> γ))
  proof: by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩
    grw [← hs, ← hu]
    rw [← Set.seq_seq]
    exact seq_mem_seq hw (seq_mem_seq hv ht)
  · rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
    grw [← ht]
    rw [Set.seq_seq]
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv

中文:
定理 seq_assoc
  条件: (x : 滤子 α) (g : 滤子 (α -> β)) (h : 滤子 (β -> γ))
  证明: by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩
    grw [← hs, ← hu]
    rw [← Set.seq_seq]
    exact seq_mem_seq hw (seq_mem_seq hv ht)
  · rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
    grw [← ht]
    rw [Set.seq_seq]
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv

Depends on / 依赖: Set.seq_seq, image_mem_map, le_antisymm, le_seq, mem_map_iff_exists_image, mem_seq_iff, seq_mem_seq, seq_seq
-/
theorem seq_assoc (x : Filter α) (g : Filter (α -> β)) (h : Filter (β -> γ)) :
    seq h (seq g x) = seq (seq (map (· ∘ ·) h) g) x := by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩
    grw [← hs, ← hu]
    rw [← Set.seq_seq]
    exact seq_mem_seq hw (seq_mem_seq hv ht)
  · rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
    grw [← ht]
    rw [Set.seq_seq]
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv

/--
theorem `prod_map_seq_comm` / 定理 `prod_map_seq_comm`

English:
theorem prod_map_seq_comm
  given: (f : Filter α) (g : Filter β)
  proof: by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    grw [← hs]
    rw [← Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    grw [← hs]
    rw [Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu

中文:
定理 prod_map_seq_comm
  条件: (f : 滤子 α) (g : 滤子 β)
  证明: by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    grw [← hs]
    rw [← Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    grw [← hs]
    rw [Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu

Depends on / 依赖: Set.prod_image_seq_comm, image_mem_map, le_antisymm, le_seq, mem_map_iff_exists_image, prod_image_seq_comm, seq_mem_seq
-/
theorem prod_map_seq_comm (f : Filter α) (g : Filter β) :
    (map Prod.mk f).seq g = seq (map (fun b a => (a, b)) g) f := by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    grw [← hs]
    rw [← Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    grw [← hs]
    rw [Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu

/--
theorem `seq_eq_filter_seq` / 定理 `seq_eq_filter_seq`

English:
theorem seq_eq_filter_seq
  given: {α β : Type u} (f : Filter (α -> β)) (g : Filter α)
  proof: rfl

中文:
定理 seq_eq_filter_seq
  条件: {α β : 类型u} (f : 滤子 (α -> β)) (g : 滤子 α)
  证明: rfl
-/
theorem seq_eq_filter_seq {α β : Type u} (f : Filter (α -> β)) (g : Filter α) :
    f <*> g = seq f g :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulApplicative (Filter : Type u -> Type u)
  body: map_pure
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  seq_pure := seq_pure
  pure_seq := pure_seq_eq_map
  seq_assoc := seq_assoc

中文:
实例 :
  签名: 合法适用 (滤子 : 类型u -> 类型u)
  定义体: map_pure
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  seq_pure := seq_pure
  pure_seq := pure_seq_eq_map
  seq_assoc := seq_assoc

Depends on / 依赖: map_pure
-/
instance : LawfulApplicative (Filter : Type u -> Type u) where
  map_pure := map_pure
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  seq_pure := seq_pure
  pure_seq := pure_seq_eq_map
  seq_assoc := seq_assoc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommApplicative (Filter : Type u -> Type u)
  body: ⟨fun f g => prod_map_seq_comm f g⟩

中文:
实例 :
  签名: 交换适用 (滤子 : 类型u -> 类型u)
  定义体: ⟨fun f g => prod_map_seq_comm f g⟩

Depends on / 依赖: prod_map_seq_comm
-/
instance : CommApplicative (Filter : Type u -> Type u) :=
  ⟨fun f g => prod_map_seq_comm f g⟩

end Applicative

/-! #### `bind` equations -/


section Bind

@[simp]
/--
theorem `eventually_bind` / 定理 `eventually_bind`

English:
theorem eventually_bind
  given: {f : Filter α} {m : α -> Filter β} {p : β -> Prop}
  proof: Iff.rfl

@[simp]

中文:
定理 eventually_bind
  条件: {f : 滤子 α} {m : α -> 滤子 β} {p : β -> 命题}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem eventually_bind {f : Filter α} {m : α -> Filter β} {p : β -> Prop} :
    (forallᶠ y in bind f m, p y) ↔ forallᶠ x in f, forallᶠ y in m x, p y :=
  Iff.rfl

@[simp]
/--
theorem `frequently_bind` / 定理 `frequently_bind`

English:
theorem frequently_bind
  given: {f : Filter α} {m : α -> Filter β} {p : β -> Prop}
  proof: by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_bind]

@[simp]

中文:
定理 frequently_bind
  条件: {f : 滤子 α} {m : α -> 滤子 β} {p : β -> 命题}
  证明: by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_bind]

@[simp]

Depends on / 依赖: eventually_bind, not_frequently, not_iff_not
-/
theorem frequently_bind {f : Filter α} {m : α -> Filter β} {p : β -> Prop} :
    (existsᶠ y in bind f m, p y) ↔ existsᶠ x in f, existsᶠ y in m x, p y := by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_bind]

@[simp]
/--
theorem `eventuallyEq_bind` / 定理 `eventuallyEq_bind`

English:
theorem eventuallyEq_bind
  given: {f : Filter α} {m : α -> Filter β} {g₁ g₂ : β -> γ}
  proof: Iff.rfl

@[simp]

中文:
定理 eventuallyEq_bind
  条件: {f : 滤子 α} {m : α -> 滤子 β} {g₁ g₂ : β -> γ}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem eventuallyEq_bind {f : Filter α} {m : α -> Filter β} {g₁ g₂ : β -> γ} :
    g₁ =ᶠ[bind f m] g₂ ↔ forallᶠ x in f, g₁ =ᶠ[m x] g₂ :=
  Iff.rfl

@[simp]
/--
theorem `eventuallyLE_bind` / 定理 `eventuallyLE_bind`

English:
theorem eventuallyLE_bind
  given: [LE γ] {f : Filter α} {m : α -> Filter β} {g₁ g₂ : β -> γ}
  proof: Iff.rfl

中文:
定理 eventuallyLE_bind
  条件: [LE γ] {f : 滤子 α} {m : α -> 滤子 β} {g₁ g₂ : β -> γ}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem eventuallyLE_bind [LE γ] {f : Filter α} {m : α -> Filter β} {g₁ g₂ : β -> γ} :
    g₁ <=ᶠ[bind f m] g₂ ↔ forallᶠ x in f, g₁ <=ᶠ[m x] g₂ :=
  Iff.rfl

/--
theorem `mem_bind'` / 定理 `mem_bind'`

English:
theorem mem_bind'
  given: {s : Set β} {f : Filter α} {m : α -> Filter β}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_bind'
  条件: {s : 集合 β} {f : 滤子 α} {m : α -> 滤子 β}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_bind' {s : Set β} {f : Filter α} {m : α -> Filter β} :
    s in bind f m ↔ { a | s in m a } in f :=
  Iff.rfl

@[simp]
/--
theorem `mem_bind` / 定理 `mem_bind`

English:
theorem mem_bind
  given: {s : Set β} {f : Filter α} {m : α -> Filter β}
  proof: calc
    s in bind f m ↔ { a | s in m a } in f := Iff.rfl
    _ ↔ exists t in f, t subseteq { a | s in m a } := exists_mem_subset_iff.symm
    _ ↔ exists t in f, forall x in t, s in m x := Iff.rfl

中文:
定理 mem_bind
  条件: {s : 集合 β} {f : 滤子 α} {m : α -> 滤子 β}
  证明: calc
    s in bind f m ↔ { a | s in m a } in f := Iff.rfl
    _ ↔ exists t in f, t subseteq { a | s in m a } := exists_mem_subset_iff.symm
    _ ↔ exists t in f, forall x in t, s in m x := Iff.rfl

Depends on / 依赖: Iff.rfl, exists_mem_subset_iff, exists_mem_subset_iff.symm, subseteq
-/
theorem mem_bind {s : Set β} {f : Filter α} {m : α -> Filter β} :
    s in bind f m ↔ exists t in f, forall x in t, s in m x :=
  calc
    s in bind f m ↔ { a | s in m a } in f := Iff.rfl
    _ ↔ exists t in f, t subseteq { a | s in m a } := exists_mem_subset_iff.symm
    _ ↔ exists t in f, forall x in t, s in m x := Iff.rfl

/--
theorem `bind_le` / 定理 `bind_le`

English:
theorem bind_le
  given: {f : Filter α} {g : α -> Filter β} {l : Filter β} (h : forallᶠ x in f, g x <= l)
  proof: join_le eventually_map.2 h

@[gcongr, mono]

中文:
定理 bind_le
  条件: {f : 滤子 α} {g : α -> 滤子 β} {l : 滤子 β} (h : 对任意ᶠ x in f, g x <= l)
  证明: join_le eventually_map.2 h

@[gcongr, mono]

Depends on / 依赖: eventually_map, join_le
-/
theorem bind_le {f : Filter α} {g : α -> Filter β} {l : Filter β} (h : forallᶠ x in f, g x <= l) :
    f.bind g <= l :=
join_le eventually_map.2 h

@[gcongr, mono]
/--
theorem `bind_mono` / 定理 `bind_mono`

English:
theorem bind_mono
  given: {f₁ f₂ : Filter α} {g₁ g₂ : α -> Filter β} (hf : f₁ <= f₂) (hg : g₁ <=ᶠ[f₁] g₂)
  proof: by
  refine le_trans (fun s hs => ?_) (join_mono <| map_mono hf)
  simp only [mem_join, mem_bind', mem_map] at hs ⊢
  filter_upwards [hg, hs] with _ hx hs using hx hs

中文:
定理 bind_mono
  条件: {f₁ f₂ : 滤子 α} {g₁ g₂ : α -> 滤子 β} (hf : f₁ <= f₂) (hg : g₁ <=ᶠ[f₁] g₂)
  证明: by
  refine le_trans (fun s hs => ?_) (join_mono <| map_mono hf)
  simp only [mem_join, mem_bind', mem_map] at hs ⊢
  filter_upwards [hg, hs] with _ hx hs using hx hs

Depends on / 依赖: filter_upwards, join_mono, le_trans, map_mono, mem_bind, mem_join, mem_map
-/
theorem bind_mono {f₁ f₂ : Filter α} {g₁ g₂ : α -> Filter β} (hf : f₁ <= f₂) (hg : g₁ <=ᶠ[f₁] g₂) :
    bind f₁ g₁ <= bind f₂ g₂ := by
  refine le_trans (fun s hs => ?_) (join_mono <| map_mono hf)
  simp only [mem_join, mem_bind', mem_map] at hs ⊢
  filter_upwards [hg, hs] with _ hx hs using hx hs

/--
theorem `bind_inf_principal` / 定理 `bind_inf_principal`

English:
theorem bind_inf_principal
  given: {f : Filter α} {g : α -> Filter β} {s : Set β}
  proof: Filter.ext fun s => by simp only [mem_bind, mem_inf_principal]

中文:
定理 bind_inf_principal
  条件: {f : 滤子 α} {g : α -> 滤子 β} {s : 集合 β}
  证明: Filter.ext fun s => by simp only [mem_bind, mem_inf_principal]

Depends on / 依赖: Filter, Filter.ext, mem_bind, mem_inf_principal
-/
theorem bind_inf_principal {f : Filter α} {g : α -> Filter β} {s : Set β} :
    (f.bind fun x => g x ⊓ 𝓟 s) = f.bind g ⊓ 𝓟 s :=
  Filter.ext fun s => by simp only [mem_bind, mem_inf_principal]

/--
theorem `sup_bind` / 定理 `sup_bind`

English:
theorem sup_bind
  given: {f g : Filter α} {h : α -> Filter β}
  statement: bind (f ⊔ g) h = bind f h ⊔ bind g h
  proof: rfl

中文:
定理 sup_bind
  条件: {f g : 滤子 α} {h : α -> 滤子 β}
  结论: bind (f ⊔ g) h = bind f h ⊔ bind g h
  证明: rfl
-/
theorem sup_bind {f g : Filter α} {h : α -> Filter β} : bind (f ⊔ g) h = bind f h ⊔ bind g h := rfl

/--
theorem `principal_bind` / 定理 `principal_bind`

English:
theorem principal_bind
  given: {s : Set α} {f : α -> Filter β}
  statement: bind (𝓟 s) f = ⨆ x in s, f x
  proof: show join (map f (𝓟 s)) = ⨆ x in s, f x by
    simp only [sSup_image, join_principal_eq_sSup, map_principal]

中文:
定理 principal_bind
  条件: {s : 集合 α} {f : α -> 滤子 β}
  结论: bind (𝓟 s) f = ⨆ x in s, f x
  证明: show join (map f (𝓟 s)) = ⨆ x in s, f x by
    simp only [sSup_image, join_principal_eq_sSup, map_principal]

Depends on / 依赖: join_principal_eq_sSup, map_principal, sSup_image
-/
theorem principal_bind {s : Set α} {f : α -> Filter β} : bind (𝓟 s) f = ⨆ x in s, f x :=
  show join (map f (𝓟 s)) = ⨆ x in s, f x by
    simp only [sSup_image, join_principal_eq_sSup, map_principal]

end Bind

end Filter

open Filter

variable {α β : Type*} {F : Filter α} {G : Filter β}

-- TODO(Anatole): unify with the global case
/--
theorem `Filter.map_surjOn_Iic_iff_le_map` / 定理 `Filter.map_surjOn_Iic_iff_le_map`

English:
theorem Filter.map_surjOn_Iic_iff_le_map
  given: {m : α -> β}
  proof: by
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · rcases hm self_mem_Iic with ⟨H, (hHF : H <= F), rfl⟩
    exact map_mono hHF
  · have : RightInvOn (F ⊓ comap m ·) (map m) (Iic G) :=
      fun H (hHG : H <= G) => by simpa [Filter.push_pull] using hHG.trans hm
    exact this.surjOn fun H _ => mem_Iic.mpr inf_le_left

中文:
定理 滤子.map_surjOn_Iic_iff_le_map
  条件: {m : α -> β}
  证明: by
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · rcases hm self_mem_Iic with ⟨H, (hHF : H <= F), rfl⟩
    exact map_mono hHF
  · have : RightInvOn (F ⊓ comap m ·) (map m) (Iic G) :=
      fun H (hHG : H <= G) => by simpa [Filter.push_pull] using hHG.trans hm
    exact this.surjOn fun H _ => mem_Iic.mpr inf_le_left

Depends on / 依赖: Filter, Filter.push_pull, RightInvOn, hHG.trans, inf_le_left, map_mono, mem_Iic, mem_Iic.mpr, push_pull, self_mem_Iic, surjOn, this.surjOn
-/
theorem Filter.map_surjOn_Iic_iff_le_map {m : α -> β} :
    SurjOn (map m) (Iic F) (Iic G) ↔ G <= map m F := by
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · rcases hm self_mem_Iic with ⟨H, (hHF : H <= F), rfl⟩
    exact map_mono hHF
  · have : RightInvOn (F ⊓ comap m ·) (map m) (Iic G) :=
      fun H (hHG : H <= G) => by simpa [Filter.push_pull] using hHG.trans hm
    exact this.surjOn fun H _ => mem_Iic.mpr inf_le_left

/--
theorem `Filter.map_surjOn_Iic_iff_surjOn` / 定理 `Filter.map_surjOn_Iic_iff_surjOn`

English:
theorem Filter.map_surjOn_Iic_iff_surjOn
  given: {s : Set α} {t : Set β} {m : α -> β}
  proof: by
  rw [map_surjOn_Iic_iff_le_map]; rw [map_principal]; rw [principal_mono]; rw [SurjOn]

alias ⟨_, Set.SurjOn.filter_map_Iic⟩ := Filter.map_surjOn_Iic_iff_surjOn

中文:
定理 滤子.map_surjOn_Iic_iff_surjOn
  条件: {s : 集合 α} {t : 集合 β} {m : α -> β}
  证明: by
  rw [map_surjOn_Iic_iff_le_map]; rw [map_principal]; rw [principal_mono]; rw [SurjOn]

alias ⟨_, Set.SurjOn.filter_map_Iic⟩ := Filter.map_surjOn_Iic_iff_surjOn

Depends on / 依赖: SurjOn, map_principal, map_surjOn_Iic_iff_le_map, principal_mono
-/
theorem Filter.map_surjOn_Iic_iff_surjOn {s : Set α} {t : Set β} {m : α -> β} :
    SurjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 t) ↔ SurjOn m s t := by
  rw [map_surjOn_Iic_iff_le_map]; rw [map_principal]; rw [principal_mono]; rw [SurjOn]

alias ⟨_, Set.SurjOn.filter_map_Iic⟩ := Filter.map_surjOn_Iic_iff_surjOn

/--
theorem `Filter.filter_injOn_Iic_iff_injOn` / 定理 `Filter.filter_injOn_Iic_iff_injOn`

English:
theorem Filter.filter_injOn_Iic_iff_injOn
  given: {s : Set α} {m : α -> β}
  proof: by
  refine ⟨fun hm x hx y hy hxy => ?_, fun hm F hF G hG => ?_⟩
  · rwa [← pure_injective.eq_iff, ← map_pure, ← map_pure, hm.eq_iff, pure_injective.eq_iff]
      at hxy <;> rwa [mem_Iic, pure_le_principal]
  · simp [map_eq_map_iff_of_injOn (le_principal_iff.mp hF) (le_principal_iff.mp hG) hm]

alias ⟨_, Set.InjOn.filter_map_Iic⟩ := Filter.filter_injOn_Iic_iff_injOn

中文:
定理 滤子.filter_injOn_Iic_iff_injOn
  条件: {s : 集合 α} {m : α -> β}
  证明: by
  refine ⟨fun hm x hx y hy hxy => ?_, fun hm F hF G hG => ?_⟩
  · rwa [← pure_injective.eq_iff, ← map_pure, ← map_pure, hm.eq_iff, pure_injective.eq_iff]
      at hxy <;> rwa [mem_Iic, pure_le_principal]
  · simp [map_eq_map_iff_of_injOn (le_principal_iff.mp hF) (le_principal_iff.mp hG) hm]

alias ⟨_, Set.InjOn.filter_map_Iic⟩ := Filter.filter_injOn_Iic_iff_injOn

Depends on / 依赖: eq_iff, hm.eq_iff, le_principal_iff, le_principal_iff.mp, map_eq_map_iff_of_injOn, map_pure, mem_Iic, pure_injective, pure_injective.eq_iff, pure_le_principal
-/
theorem Filter.filter_injOn_Iic_iff_injOn {s : Set α} {m : α -> β} :
    InjOn (map m) (Iic <| 𝓟 s) ↔ InjOn m s := by
  refine ⟨fun hm x hx y hy hxy => ?_, fun hm F hF G hG => ?_⟩
  · rwa [← pure_injective.eq_iff, ← map_pure, ← map_pure, hm.eq_iff, pure_injective.eq_iff]
      at hxy <;> rwa [mem_Iic, pure_le_principal]
  · simp [map_eq_map_iff_of_injOn (le_principal_iff.mp hF) (le_principal_iff.mp hG) hm]

alias ⟨_, Set.InjOn.filter_map_Iic⟩ := Filter.filter_injOn_Iic_iff_injOn
