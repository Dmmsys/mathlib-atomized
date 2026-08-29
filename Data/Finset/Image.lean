/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Fintype.Defs

/-! # Image and map operations on finite sets

This file provides the finite analog of `Set.image`, along with some other similar functions.

Note there are two ways to take the image over a finset; via `Finset.image` which applies the
function then removes duplicates (requiring `DecidableEq`), or via `Finset.map` which exploits
injectivity of the function to avoid needing to deduplicate. Choosing between these is similar to
choosing between `insert` and `Finset.cons`, or between `Finset.union` and `Finset.disjUnion`.

## Main definitions

* `Finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `Finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `Finset.filterMap` Given a function `f : α → Option β`, `s.filterMap f` is the
  image finset in `β`, filtering out `none`s.
* `Finset.subtype`: `s.subtype p` is the finset of `Subtype p` whose elements belong to `s`.
* `Finset.fin`:`s.fin n` is the finset of all elements of `s` less than `n`.
-/

@[expose] public section
assert_not_exists Monoid IsOrderedMonoid

variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

/-! ### map -/


section Map

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α ↪ β) (s : Finset α)
  body: ⟨s.1.map f, s.2.map f.2⟩

@[simp]

中文:
定义 map
  签名: (f : α ↪ β) (s : 有限集 α)
  定义体: ⟨s.1.map f, s.2.map f.2⟩

@[simp]
-/
def map (f : α ↪ β) (s : Finset α) : Finset β :=
  ⟨s.1.map f, s.2.map f.2⟩

@[simp]
/--
theorem `map_val` / 定理 `map_val`

English:
theorem map_val
  given: (f : α ↪ β) (s : Finset α)
  statement: (map f s).1 = s.1.map f
  proof: rfl

@[simp]

中文:
定理 map_val
  条件: (f : α ↪ β) (s : 有限集 α)
  结论: (map f s).1 = s.1.map f
  证明: rfl

@[simp]
-/
theorem map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f :=
  rfl

@[simp]
/--
theorem `map_empty` / 定理 `map_empty`

English:
theorem map_empty
  given: (f : α ↪ β)
  statement: (∅ : Finset α).map f = ∅
  proof: rfl

中文:
定理 map_empty
  条件: (f : α ↪ β)
  结论: (∅ : 有限集 α).map f = ∅
  证明: rfl
-/
theorem map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅ :=
  rfl

variable {f : α ↪ β} {s : Finset α}

@[simp, grind =]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {b : β}
  statement: b in s.map f ↔ exists a in s, f a = b
  proof: Multiset.mem_map

中文:
定理 mem_map
  条件: {b : β}
  结论: b in s.map f ↔ 存在 a in s, f a = b
  证明: Multiset.mem_map

Depends on / 依赖: Multiset, Multiset.mem_map, mem_map
-/
theorem mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b :=
  Multiset.mem_map

-- Higher priority to apply before `mem_map`.
@[simp 1100]
/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {f : α ≃ β} {b : β}
  statement: b in s.map f.toEmbedding ↔ f.symm b in s
  proof: by
  simp only [mem_map, Equiv.coe_toEmbedding]
  grind

@[simp 1100]

中文:
定理 mem_map_equiv
  条件: {f : α ≃ β} {b : β}
  结论: b in s.map f.toEmbedding ↔ f.symm b in s
  证明: by
  simp only [mem_map, Equiv.coe_toEmbedding]
  grind

@[simp 1100]

Depends on / 依赖: Equiv.coe_toEmbedding, coe_toEmbedding, mem_map
-/
theorem mem_map_equiv {f : α ≃ β} {b : β} : b in s.map f.toEmbedding ↔ f.symm b in s := by
  simp only [mem_map, Equiv.coe_toEmbedding]
  grind

@[simp 1100]
/--
theorem `mem_map'` / 定理 `mem_map'`

English:
theorem mem_map'
  given: (f : α ↪ β) {a} {s : Finset α}
  statement: f a in s.map f ↔ a in s
  proof: mem_map_of_injective f.2

@[simp 1100]

中文:
定理 mem_map'
  条件: (f : α ↪ β) {a} {s : 有限集 α}
  结论: f a in s.map f ↔ a in s
  证明: mem_map_of_injective f.2

@[simp 1100]

Depends on / 依赖: mem_map_of_injective
-/
theorem mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map f ↔ a in s :=
  mem_map_of_injective f.2

@[simp 1100]
/--
theorem `mem_map_mk` / 定理 `mem_map_mk`

English:
theorem mem_map_mk
  given: (f : α -> β) {a : α} {s : Finset α} (hf : Function.Injective f)
  proof: Finset.mem_map' _

中文:
定理 mem_map_mk
  条件: (f : α -> β) {a : α} {s : 有限集 α} (hf : 函数.单射 f)
  证明: Finset.mem_map' _

Depends on / 依赖: Finset, Finset.mem_map, mem_map
-/
theorem mem_map_mk (f : α -> β) {a : α} {s : Finset α} (hf : Function.Injective f) :
    f a in s.map ⟨f, hf⟩ ↔ a in s :=
  Finset.mem_map' _

/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: (f : α ↪ β) {a} {s : Finset α}
  statement: a in s -> f a in s.map f
  proof: (mem_map' _).2

中文:
定理 mem_map_of_mem
  条件: (f : α ↪ β) {a} {s : 有限集 α}
  结论: a in s -> f a in s.map f
  证明: (mem_map' _).2

Depends on / 依赖: mem_map
-/
theorem mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a in s -> f a in s.map f :=
  (mem_map' _).2

/--
theorem `forall_mem_map` / 定理 `forall_mem_map`

English:
theorem forall_mem_map
  given: {f : α ↪ β} {s : Finset α} {p : forall a, a in s.map f -> Prop}
  proof: by grind

中文:
定理 对任意_mem_map
  条件: {f : α ↪ β} {s : 有限集 α} {p : 对任意 a, a in s.map f -> 命题}
  证明: by grind
-/
theorem forall_mem_map {f : α ↪ β} {s : Finset α} {p : forall a, a in s.map f -> Prop} :
    (forall y (H : y in s.map f), p y H) ↔ forall x (H : x in s), p (f x) (mem_map_of_mem _ H) := by grind

/--
theorem `apply_coe_mem_map` / 定理 `apply_coe_mem_map`

English:
theorem apply_coe_mem_map
  given: (f : α ↪ β) (s : Finset α) (x : s)
  statement: f x in s.map f
  proof: mem_map_of_mem f x.prop

@[simp, norm_cast]

中文:
定理 apply_coe_mem_map
  条件: (f : α ↪ β) (s : 有限集 α) (x : s)
  结论: f x in s.map f
  证明: mem_map_of_mem f x.prop

@[simp, norm_cast]

Depends on / 依赖: mem_map_of_mem, x.prop
-/
theorem apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x in s.map f :=
  mem_map_of_mem f x.prop

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : α ↪ β) (s : Finset α)
  statement: (s.map f : Set β) = f '' s
  proof: by grind

中文:
定理 coe_map
  条件: (f : α ↪ β) (s : 有限集 α)
  结论: (s.map f : 集合 β) = f '' s
  证明: by grind
-/
theorem coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s := by grind

/--
theorem `coe_map_subset_range` / 定理 `coe_map_subset_range`

English:
theorem coe_map_subset_range
  given: (f : α ↪ β) (s : Finset α)
  statement: (s.map f : Set β) subseteq Set.range f
  proof: by
  grind

中文:
定理 coe_map_subset_range
  条件: (f : α ↪ β) (s : 有限集 α)
  结论: (s.map f : 集合 β) subseteq 集合.range f
  证明: by
  grind
-/
theorem coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) subseteq Set.range f := by
  grind

/--
theorem `map_perm` / 定理 `map_perm`

English:
theorem map_perm
  given: {σ : Equiv.Perm α} (hs : { a | σ a != a } subseteq s)
  statement: s.map (σ : α ↪ α) = s
  proof: coe_injective (coe_map _ _).trans Set.image_perm hs

中文:
定理 map_perm
  条件: {σ : 等价.置换 α} (hs : { a | σ a != a } subseteq s)
  结论: s.map (σ : α ↪ α) = s
  证明: coe_injective (coe_map _ _).trans Set.image_perm hs

Depends on / 依赖: Set.image_perm, coe_injective, coe_map, image_perm
-/
theorem map_perm {σ : Equiv.Perm α} (hs : { a | σ a != a } subseteq s) : s.map (σ : α ↪ α) = s :=
coe_injective (coe_map _ _).trans Set.image_perm hs

/--
theorem `map_toFinset` / 定理 `map_toFinset`

English:
theorem map_toFinset
  given: [DecidableEq α] [DecidableEq β] {s : Multiset α}
  proof: ext fun _ => by simp only [mem_map, Multiset.mem_map, Multiset.mem_toFinset]

@[simp]

中文:
定理 map_toFinset
  条件: [DecidableEq α] [DecidableEq β] {s : Multiset α}
  证明: ext fun _ => by simp only [mem_map, Multiset.mem_map, Multiset.mem_toFinset]

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_map, Multiset.mem_toFinset, mem_map, mem_toFinset
-/
theorem map_toFinset [DecidableEq α] [DecidableEq β] {s : Multiset α} :
    s.toFinset.map f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_map, Multiset.mem_map, Multiset.mem_toFinset]

@[simp]
/--
theorem `map_refl` / 定理 `map_refl`

English:
theorem map_refl
  statement: s.map (Embedding.refl _) = s
  proof: ext fun _ => by simpa only [mem_map, exists_prop] using! exists_eq_right

@[simp]

中文:
定理 map_refl
  结论: s.map (嵌入.refl _) = s
  证明: ext fun _ => by simpa only [mem_map, exists_prop] using! exists_eq_right

@[simp]

Depends on / 依赖: exists_eq_right, exists_prop, mem_map
-/
theorem map_refl : s.map (Embedding.refl _) = s :=
  ext fun _ => by simpa only [mem_map, exists_prop] using! exists_eq_right

@[simp]
/--
theorem `map_cast_heq` / 定理 `map_cast_heq`

English:
theorem map_cast_heq
  given: {α β} (h : α = β) (s : Finset α)
  proof: by
  subst h
  simp

中文:
定理 map_cast_heq
  条件: {α β} (h : α = β) (s : 有限集 α)
  证明: by
  subst h
  simp
-/
theorem map_cast_heq {α β} (h : α = β) (s : Finset α) :
    s.map (Equiv.cast h).toEmbedding ≍ s := by
  subst h
  simp

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (f : α ↪ β) (g : β ↪ γ) (s : Finset α)
  statement: (s.map f).map g = s.map (f.trans g)
  proof: eq_of_veq by simp only [map_val, Multiset.map_map]; rfl

中文:
定理 map_map
  条件: (f : α ↪ β) (g : β ↪ γ) (s : 有限集 α)
  结论: (s.map f).map g = s.map (f.trans g)
  证明: eq_of_veq by simp only [map_val, Multiset.map_map]; rfl

Depends on / 依赖: Multiset, Multiset.map_map, eq_of_veq, map_map, map_val
-/
theorem map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map f).map g = s.map (f.trans g) :=
eq_of_veq by simp only [map_val, Multiset.map_map]; rfl

/--
theorem `map_comm` / 定理 `map_comm`

English:
theorem map_comm
  statement: {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
  proof: by
  simp_rw [map_map, Embedding.trans, Function.comp_def, h_comm]

中文:
定理 map_comm
  结论: {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
  证明: by
  simp_rw [map_map, Embedding.trans, Function.comp_def, h_comm]

Depends on / 依赖: Embedding, Embedding.trans, Function, Function.comp_def, comp_def, h_comm, map_map, simp_rw
-/
theorem map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
    (h_comm : forall a, f (g a) = g' (f' a)) : (s.map g).map f = (s.map f').map g' := by
  simp_rw [map_map, Embedding.trans, Function.comp_def, h_comm]

/--
theorem `_root_.Function.Semiconj.finset_map` / 定理 `_root_.Function.Semiconj.finset_map`

English:
theorem _root_.Function.Semiconj.finset_map
  statement: {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
  proof: fun _ =>
  map_comm h

中文:
定理 _root_.函数.Semiconj.finset_map
  结论: {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
  证明: fun _ =>
  map_comm h
-/
theorem _root_.Function.Semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) := fun _ =>
  map_comm h

/--
theorem `_root_.Function.Commute.finset_map` / 定理 `_root_.Function.Commute.finset_map`

English:
theorem _root_.Function.Commute.finset_map
  given: {f g : α ↪ α} (h : Function.Commute f g)
  proof: Function.Semiconj.finset_map h

@[simp, gcongr]

中文:
定理 _root_.函数.Commute.finset_map
  条件: {f g : α ↪ α} (h : 函数.Commute f g)
  证明: Function.Semiconj.finset_map h

@[simp, gcongr]

Depends on / 依赖: Function, Function.Semiconj.finset_map, Semiconj, finset_map
-/
theorem _root_.Function.Commute.finset_map {f g : α ↪ α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  Function.Semiconj.finset_map h

@[simp, gcongr]
/--
theorem `map_subset_map` / 定理 `map_subset_map`

English:
theorem map_subset_map
  given: {s₁ s₂ : Finset α}
  statement: s₁.map f subseteq s₂.map f ↔ s₁ subseteq s₂
  proof: ⟨fun h _ xs => (mem_map' _).1 h (mem_map' f).2 xs,
   fun h => by simp [subset_def, Multiset.map_subset_map h]⟩

中文:
定理 map_subset_map
  条件: {s₁ s₂ : 有限集 α}
  结论: s₁.map f subseteq s₂.map f ↔ s₁ subseteq s₂
  证明: ⟨fun h _ xs => (mem_map' _).1 h (mem_map' f).2 xs,
   fun h => by simp [subset_def, Multiset.map_subset_map h]⟩

Depends on / 依赖: Multiset, Multiset.map_subset_map, map_subset_map, mem_map, subset_def
-/
theorem map_subset_map {s₁ s₂ : Finset α} : s₁.map f subseteq s₂.map f ↔ s₁ subseteq s₂ :=
⟨fun h _ xs => (mem_map' _).1 h (mem_map' f).2 xs,
   fun h => by simp [subset_def, Multiset.map_subset_map h]⟩

/--
theorem `subset_map_symm` / 定理 `subset_map_symm`

English:
theorem subset_map_symm
  given: {t : Finset β} {f : α ≃ β}
  statement: s subseteq t.map f.symm ↔ s.map f subseteq t
  proof: by
  constructor <;> intro h x hx
  · simp only [mem_map_equiv] at hx
    simpa using h hx
  · simp only [mem_map_equiv]
    exact h (by simp [hx])

中文:
定理 subset_map_symm
  条件: {t : 有限集 β} {f : α ≃ β}
  结论: s subseteq t.map f.symm ↔ s.map f subseteq t
  证明: by
  constructor <;> intro h x hx
  · simp only [mem_map_equiv] at hx
    simpa using h hx
  · simp only [mem_map_equiv]
    exact h (by simp [hx])

Depends on / 依赖: mem_map_equiv
-/
theorem subset_map_symm {t : Finset β} {f : α ≃ β} : s subseteq t.map f.symm ↔ s.map f subseteq t := by
  constructor <;> intro h x hx
  · simp only [mem_map_equiv] at hx
    simpa using h hx
  · simp only [mem_map_equiv]
    exact h (by simp [hx])

/--
theorem `map_symm_subset` / 定理 `map_symm_subset`

English:
theorem map_symm_subset
  given: {t : Finset β} {f : α ≃ β}
  statement: t.map f.symm subseteq s ↔ t subseteq s.map f
  proof: by
  simp only [← subset_map_symm, Equiv.symm_symm]

中文:
定理 map_symm_subset
  条件: {t : 有限集 β} {f : α ≃ β}
  结论: t.map f.symm subseteq s ↔ t subseteq s.map f
  证明: by
  simp only [← subset_map_symm, Equiv.symm_symm]

Depends on / 依赖: Equiv.symm_symm, subset_map_symm, symm_symm
-/
theorem map_symm_subset {t : Finset β} {f : α ≃ β} : t.map f.symm subseteq s ↔ t subseteq s.map f := by
  simp only [← subset_map_symm, Equiv.symm_symm]

/--
Definition of `mapEmbedding` / `mapEmbedding` 的定义

English:
definition mapEmbedding
  signature: (f : α ↪ β)
  body: OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_subset_map

@[simp]

中文:
定义 mapEmbedding
  签名: (f : α ↪ β)
  定义体: OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_subset_map

@[simp]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofMapLEIff, map_subset_map, ofMapLEIff
-/
def mapEmbedding (f : α ↪ β) : Finset α ↪o Finset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_subset_map

@[simp]
/--
theorem `map_inj` / 定理 `map_inj`

English:
theorem map_inj
  given: {s₁ s₂ : Finset α}
  statement: s₁.map f = s₂.map f ↔ s₁ = s₂
  proof: (mapEmbedding f).injective.eq_iff

中文:
定理 map_inj
  条件: {s₁ s₂ : 有限集 α}
  结论: s₁.map f = s₂.map f ↔ s₁ = s₂
  证明: (mapEmbedding f).injective.eq_iff

Depends on / 依赖: eq_iff, injective, injective.eq_iff, mapEmbedding
-/
theorem map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
  (mapEmbedding f).injective.eq_iff

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (f : α ↪ β)
  statement: Injective (map f)
  proof: (mapEmbedding f).injective

@[simp, gcongr]

中文:
定理 map_injective
  条件: (f : α ↪ β)
  结论: 单射 (map f)
  证明: (mapEmbedding f).injective

@[simp, gcongr]

Depends on / 依赖: injective, mapEmbedding
-/
theorem map_injective (f : α ↪ β) : Injective (map f) :=
  (mapEmbedding f).injective

@[simp, gcongr]
/--
theorem `map_ssubset_map` / 定理 `map_ssubset_map`

English:
theorem map_ssubset_map
  given: {s t : Finset α}
  statement: s.map f ⊂ t.map f ↔ s ⊂ t
  proof: (mapEmbedding f).lt_iff_lt

@[simp]

中文:
定理 map_ssubset_map
  条件: {s t : 有限集 α}
  结论: s.map f ⊂ t.map f ↔ s ⊂ t
  证明: (mapEmbedding f).lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, mapEmbedding
-/
theorem map_ssubset_map {s t : Finset α} : s.map f ⊂ t.map f ↔ s ⊂ t := (mapEmbedding f).lt_iff_lt

@[simp]
/--
theorem `mapEmbedding_apply` / 定理 `mapEmbedding_apply`

English:
theorem mapEmbedding_apply
  statement: mapEmbedding f s = map f s
  proof: rfl

中文:
定理 mapEmbedding_apply
  结论: mapEmbedding f s = map f s
  证明: rfl
-/
theorem mapEmbedding_apply : mapEmbedding f s = map f s :=
  rfl

/--
theorem `filter_map` / 定理 `filter_map`

English:
theorem filter_map
  given: {p : β -> Prop} [DecidablePred p]
  proof: eq_of_veq (Multiset.filter_map _ _ _)

中文:
定理 filter_map
  条件: {p : β -> 命题} [DecidablePred p]
  证明: eq_of_veq (Multiset.filter_map _ _ _)

Depends on / 依赖: Multiset, Multiset.filter_map, eq_of_veq, filter_map
-/
theorem filter_map {p : β -> Prop} [DecidablePred p] :
    (s.map f).filter p = (s.filter (p ∘ f)).map f :=
  eq_of_veq (Multiset.filter_map _ _ _)

/--
lemma `map_filter'` / 引理 `map_filter'`

English:
lemma map_filter'
  statement: (p : α -> Prop) [DecidablePred p] (f : α ↪ β) (s : Finset α)
  proof: by
  simp [filter_map]

中文:
引理 map_filter'
  结论: (p : α -> 命题) [DecidablePred p] (f : α ↪ β) (s : 有限集 α)
  证明: by
  simp [filter_map]

Depends on / 依赖: filter_map
-/
lemma map_filter' (p : α -> Prop) [DecidablePred p] (f : α ↪ β) (s : Finset α)
    [DecidablePred (exists a, p a ∧ f a = ·)] :
    (s.filter p).map f = (s.map f).filter fun b => exists a, p a ∧ f a = b := by
  simp [filter_map]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `filter_attach'` / 引理 `filter_attach'`

English:
lemma filter_attach'
  given: [DecidableEq α] (s : Finset α) (p : s -> Prop) [DecidablePred p]
  proof: eq_of_veq Multiset.filter_attach' _ _

中文:
引理 filter_attach'
  条件: [DecidableEq α] (s : 有限集 α) (p : s -> 命题) [DecidablePred p]
  证明: eq_of_veq Multiset.filter_attach' _ _

Depends on / 依赖: Multiset, Multiset.filter_attach, eq_of_veq, filter_attach
-/
lemma filter_attach' [DecidableEq α] (s : Finset α) (p : s -> Prop) [DecidablePred p] :
    s.attach.filter p =
      (s.filter fun x => exists h, p ⟨x, h⟩).attach.map
⟨Subtype.map id filter_subset _ _, Subtype.map_injective _ injective_id⟩ :=
eq_of_veq Multiset.filter_attach' _ _

/--
lemma `filter_attach` / 引理 `filter_attach`

English:
lemma filter_attach
  given: (p : α -> Prop) [DecidablePred p] (s : Finset α)
  proof: eq_of_veq Multiset.filter_attach _ _

中文:
引理 filter_attach
  条件: (p : α -> 命题) [DecidablePred p] (s : 有限集 α)
  证明: eq_of_veq Multiset.filter_attach _ _

Depends on / 依赖: Multiset, Multiset.filter_attach, eq_of_veq, filter_attach
-/
lemma filter_attach (p : α -> Prop) [DecidablePred p] (s : Finset α) :
    s.attach.filter (fun a : s => p a) =
      (s.filter p).attach.map ((Embedding.refl _).subtypeMap mem_of_mem_filter) :=
eq_of_veq Multiset.filter_attach _ _

/--
theorem `map_filter` / 定理 `map_filter`

English:
theorem map_filter
  given: {f : α ≃ β} {p : α -> Prop} [DecidablePred p]
  proof: by
  simp only [filter_map, Function.comp_def, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

@[simp]

中文:
定理 map_filter
  条件: {f : α ≃ β} {p : α -> 命题} [DecidablePred p]
  证明: by
  simp only [filter_map, Function.comp_def, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

@[simp]

Depends on / 依赖: Equiv.symm_apply_apply, Equiv.toEmbedding_apply, Function, Function.comp_def, comp_def, filter_map, symm_apply_apply, toEmbedding_apply
-/
theorem map_filter {f : α ≃ β} {p : α -> Prop} [DecidablePred p] :
    (s.filter p).map f.toEmbedding = (s.map f.toEmbedding).filter (p ∘ f.symm) := by
  simp only [filter_map, Function.comp_def, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

@[simp]
/--
theorem `disjoint_map` / 定理 `disjoint_map`

English:
theorem disjoint_map
  given: {s t : Finset α} (f : α ↪ β)
  proof: mod_cast Set.disjoint_image_iff f.injective (s := s) (t := t)

中文:
定理 disjoint_map
  条件: {s t : 有限集 α} (f : α ↪ β)
  证明: mod_cast Set.disjoint_image_iff f.injective (s := s) (t := t)

Depends on / 依赖: Set.disjoint_image_iff, disjoint_image_iff, f.injective, injective, mod_cast
-/
theorem disjoint_map {s t : Finset α} (f : α ↪ β) :
    Disjoint (s.map f) (t.map f) ↔ Disjoint s t :=
  mod_cast Set.disjoint_image_iff f.injective (s := s) (t := t)

/--
theorem `map_disjUnion` / 定理 `map_disjUnion`

English:
theorem map_disjUnion
  given: {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h' := (disjoint_map _).mpr h)
  proof: eq_of_veq Multiset.map_add _ _ _

中文:
定理 map_disjUnion
  条件: {f : α ↪ β} (s₁ s₂ : 有限集 α) (h) (h' := (disjoint_map _).mpr h)
  证明: eq_of_veq Multiset.map_add _ _ _

Depends on / 依赖: disjoint_map
-/
theorem map_disjUnion {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h' := (disjoint_map _).mpr h) :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
eq_of_veq Multiset.map_add _ _ _

/--
theorem `map_disjUnion'` / 定理 `map_disjUnion'`

English:
theorem map_disjUnion'
  given: {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h := (disjoint_map _).mp h')
  proof: map_disjUnion _ _ _

中文:
定理 map_disjUnion'
  条件: {f : α ↪ β} (s₁ s₂ : 有限集 α) (h') (h := (disjoint_map _).mp h')
  证明: map_disjUnion _ _ _

Depends on / 依赖: disjoint_map
-/
theorem map_disjUnion' {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h := (disjoint_map _).mp h') :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  map_disjUnion _ _ _

/--
theorem `map_union` / 定理 `map_union`

English:
theorem map_union
  given: [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α)
  proof: mod_cast Set.image_union f s₁ s₂

中文:
定理 map_union
  条件: [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : 有限集 α)
  证明: mod_cast Set.image_union f s₁ s₂

Depends on / 依赖: Set.image_union, image_union, mod_cast
-/
theorem map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ union s₂).map f = s₁.map f union s₂.map f :=
  mod_cast Set.image_union f s₁ s₂

/--
theorem `map_inter` / 定理 `map_inter`

English:
theorem map_inter
  given: [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α)
  proof: mod_cast Set.image_inter f.injective (s := s₁) (t := s₂)

中文:
定理 map_inter
  条件: [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : 有限集 α)
  证明: mod_cast Set.image_inter f.injective (s := s₁) (t := s₂)

Depends on / 依赖: Set.image_inter, f.injective, image_inter, injective, mod_cast
-/
theorem map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ inter s₂).map f = s₁.map f inter s₂.map f :=
  mod_cast Set.image_inter f.injective (s := s₁) (t := s₂)

/--
theorem `map_sdiff` / 定理 `map_sdiff`

English:
theorem map_sdiff
  given: [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α)
  proof: mod_cast Set.image_sdiff f.injective (s := s₁) (t := s₂)

@[simp]

中文:
定理 map_sdiff
  条件: [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : 有限集 α)
  证明: mod_cast Set.image_sdiff f.injective (s := s₁) (t := s₂)

@[simp]

Depends on / 依赖: Set.image_sdiff, f.injective, image_sdiff, injective, mod_cast
-/
theorem map_sdiff [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ \ s₂).map f = s₁.map f \ s₂.map f :=
  mod_cast Set.image_sdiff f.injective (s := s₁) (t := s₂)

@[simp]
/--
theorem `map_singleton` / 定理 `map_singleton`

English:
theorem map_singleton
  given: (f : α ↪ β) (a : α)
  statement: map f {a} = {f a}
  proof: coe_injective by simp only [coe_map, coe_singleton, Set.image_singleton]

@[simp]

中文:
定理 map_singleton
  条件: (f : α ↪ β) (a : α)
  结论: map f {a} = {f a}
  证明: coe_injective by simp only [coe_map, coe_singleton, Set.image_singleton]

@[simp]

Depends on / 依赖: Set.image_singleton, coe_injective, coe_map, coe_singleton, image_singleton
-/
theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
coe_injective by simp only [coe_map, coe_singleton, Set.image_singleton]

@[simp]
/--
theorem `map_insert` / 定理 `map_insert`

English:
theorem map_insert
  given: [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α)
  proof: by
  simp only [insert_eq, map_union, map_singleton]

@[simp]

中文:
定理 map_insert
  条件: [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : 有限集 α)
  证明: by
  simp only [insert_eq, map_union, map_singleton]

@[simp]

Depends on / 依赖: insert_eq, map_singleton, map_union
-/
theorem map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α) :
    (insert a s).map f = insert (f a) (s.map f) := by
  simp only [insert_eq, map_union, map_singleton]

@[simp]
/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  given: (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s)
  proof: eq_of_veq Multiset.map_cons f a s.val

@[simp]

中文:
定理 map_cons
  条件: (f : α ↪ β) (a : α) (s : 有限集 α) (ha : a ∉ s)
  证明: eq_of_veq Multiset.map_cons f a s.val

@[simp]

Depends on / 依赖: Multiset, Multiset.map_cons, eq_of_veq, map_cons, s.val
-/
theorem map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s) :
    (cons a s ha).map f = cons (f a) (s.map f) (by simpa using ha) :=
eq_of_veq Multiset.map_cons f a s.val

@[simp]
/--
theorem `map_eq_empty` / 定理 `map_eq_empty`

English:
theorem map_eq_empty
  statement: s.map f = ∅ ↔ s = ∅
  proof: (map_injective f).eq_iff' (map_empty f)

@[simp]

中文:
定理 map_eq_empty
  结论: s.map f = ∅ ↔ s = ∅
  证明: (map_injective f).eq_iff' (map_empty f)

@[simp]

Depends on / 依赖: eq_iff, map_empty, map_injective
-/
theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ := (map_injective f).eq_iff' (map_empty f)

@[simp]
/--
theorem `empty_eq_map` / 定理 `empty_eq_map`

English:
theorem empty_eq_map
  statement: ∅ = s.map f ↔ s = ∅
  proof: by rw [eq_comm, map_eq_empty]

@[simp]

中文:
定理 empty_eq_map
  结论: ∅ = s.map f ↔ s = ∅
  证明: by rw [eq_comm, map_eq_empty]

@[simp]

Depends on / 依赖: eq_comm, map_eq_empty
-/
theorem empty_eq_map : ∅ = s.map f ↔ s = ∅ := by rw [eq_comm, map_eq_empty]

@[simp]
/--
theorem `map_nonempty` / 定理 `map_nonempty`

English:
theorem map_nonempty
  statement: (s.map f).Nonempty ↔ s.Nonempty
  proof: mod_cast Set.image_nonempty (f := f) (s := s)

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.map⟩ := map_nonempty

@[simp]

中文:
定理 map_nonempty
  结论: (s.map f).非空 ↔ s.非空
  证明: mod_cast Set.image_nonempty (f := f) (s := s)

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.map⟩ := map_nonempty

@[simp]

Depends on / 依赖: Set.image_nonempty, image_nonempty, mod_cast
-/
theorem map_nonempty : (s.map f).Nonempty ↔ s.Nonempty :=
  mod_cast Set.image_nonempty (f := f) (s := s)

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.map⟩ := map_nonempty

@[simp]
/--
theorem `map_nontrivial` / 定理 `map_nontrivial`

English:
theorem map_nontrivial
  statement: (s.map f).Nontrivial ↔ s.Nontrivial
  proof: mod_cast Set.image_nontrivial f.injective (s := s)

中文:
定理 map_nontrivial
  结论: (s.map f).非平凡 ↔ s.非平凡
  证明: mod_cast Set.image_nontrivial f.injective (s := s)

Depends on / 依赖: Set.image_nontrivial, f.injective, image_nontrivial, injective, mod_cast
-/
theorem map_nontrivial : (s.map f).Nontrivial ↔ s.Nontrivial :=
  mod_cast Set.image_nontrivial f.injective (s := s)

/--
theorem `attach_map_val` / 定理 `attach_map_val`

English:
theorem attach_map_val
  given: {s : Finset α}
  statement: s.attach.map (Embedding.subtype _) = s
  proof: eq_of_veq by rw [map_val, attach_val]; exact Multiset.attach_map_val _

中文:
定理 attach_map_val
  条件: {s : 有限集 α}
  结论: s.attach.map (嵌入.subtype _) = s
  证明: eq_of_veq by rw [map_val, attach_val]; exact Multiset.attach_map_val _

Depends on / 依赖: Multiset, Multiset.attach_map_val, attach_map_val, attach_val, eq_of_veq, map_val
-/
theorem attach_map_val {s : Finset α} : s.attach.map (Embedding.subtype _) = s :=
eq_of_veq by rw [map_val, attach_val]; exact Multiset.attach_map_val _

variable (f s) in
/-- A `Finset` is in bijection with its image under an `Embedding`. -/
@[simps!]
/--
Definition of `equivMap` / `equivMap` 的定义

English:
definition equivMap
  signature: : s ≃ s.map f
  body: .ofBijective (fun x => ⟨f x, s.mem_map_of_mem f x.2⟩) (⟨fun x y => by simp, fun ⟨x, hx⟩ => by
    obtain ⟨x, hxs, rfl⟩ := mem_map.mp hx
    exact ⟨⟨x, hxs⟩, rfl⟩⟩)

中文:
定义 equivMap
  签名: : s ≃ s.map f
  定义体: .ofBijective (fun x => ⟨f x, s.mem_map_of_mem f x.2⟩) (⟨fun x y => by simp, fun ⟨x, hx⟩ => by
    obtain ⟨x, hxs, rfl⟩ := mem_map.mp hx
    exact ⟨⟨x, hxs⟩, rfl⟩⟩)

Depends on / 依赖: mem_map, mem_map.mp, mem_map_of_mem, ofBijective, s.mem_map_of_mem
-/
noncomputable def equivMap : s ≃ s.map f :=
  .ofBijective (fun x => ⟨f x, s.mem_map_of_mem f x.2⟩) (⟨fun x y => by simp, fun ⟨x, hx⟩ => by
    obtain ⟨x, hxs, rfl⟩ := mem_map.mp hx
    exact ⟨⟨x, hxs⟩, rfl⟩⟩)

end Map

set_option backward.isDefEq.respectTransparency false in
/--
theorem `range_add_one'` / 定理 `range_add_one'`

English:
theorem range_add_one'
  given: (n : Nat)
  proof: by
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.zero_lt_succ n]

中文:
定理 range_add_one'
  条件: (n : 自然数)
  证明: by
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.zero_lt_succ n]

Depends on / 依赖: Nat.zero_lt_succ, zero_lt_succ
-/
theorem range_add_one' (n : Nat) :
    range (n + 1) = insert 0 ((range n).map ⟨fun i => i + 1, fun i j => by simp⟩) := by
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.zero_lt_succ n]

/-! ### image -/


section Image

variable [DecidableEq β]

/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (f : α -> β) (s : Finset α)
  body: (s.1.map f).toFinset

@[simp]

中文:
定义 像
  签名: (f : α -> β) (s : 有限集 α)
  定义体: (s.1.map f).toFinset

@[simp]

Depends on / 依赖: toFinset
-/
def image (f : α -> β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset

@[simp]
/--
theorem `image_val` / 定理 `image_val`

English:
theorem image_val
  given: (f : α -> β) (s : Finset α)
  statement: (image f s).1 = (s.1.map f).dedup
  proof: rfl

@[simp]

中文:
定理 image_val
  条件: (f : α -> β) (s : 有限集 α)
  结论: (像 f s).1 = (s.1.map f).dedup
  证明: rfl

@[simp]
-/
theorem image_val (f : α -> β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup :=
  rfl

@[simp]
/--
theorem `image_empty` / 定理 `image_empty`

English:
theorem image_empty
  given: (f : α -> β)
  statement: (∅ : Finset α).image f = ∅
  proof: rfl

中文:
定理 image_empty
  条件: (f : α -> β)
  结论: (∅ : 有限集 α).像 f = ∅
  证明: rfl
-/
theorem image_empty (f : α -> β) : (∅ : Finset α).image f = ∅ :=
  rfl

variable {f g : α -> β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

@[simp, grind =]
/--
theorem `mem_image` / 定理 `mem_image`

English:
theorem mem_image
  statement: b in s.image f ↔ exists a in s, f a = b
  proof: by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map]

中文:
定理 mem_image
  结论: b in s.像 f ↔ 存在 a in s, f a = b
  证明: by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map]

Depends on / 依赖: Multiset, Multiset.mem_map, image_val, mem_dedup, mem_def, mem_map
-/
theorem mem_image : b in s.image f ↔ exists a in s, f a = b := by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map]

/--
theorem `mem_image_of_mem` / 定理 `mem_image_of_mem`

English:
theorem mem_image_of_mem
  given: (f : α -> β) {a} (h : a in s)
  statement: f a in s.image f
  proof: mem_image.2 ⟨_, h, rfl⟩

中文:
定理 mem_image_of_mem
  条件: (f : α -> β) {a} (h : a in s)
  结论: f a in s.像 f
  证明: mem_image.2 ⟨_, h, rfl⟩

Depends on / 依赖: mem_image
-/
theorem mem_image_of_mem (f : α -> β) {a} (h : a in s) : f a in s.image f :=
  mem_image.2 ⟨_, h, rfl⟩

/--
lemma `forall_mem_image` / 引理 `forall_mem_image`

English:
lemma forall_mem_image
  given: {p : β -> Prop}
  statement: (forall y in s.image f, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
  proof: by simp

中文:
引理 对任意_mem_image
  条件: {p : β -> 命题}
  结论: (对任意 y in s.像 f, p y) ↔ 对任意 ⦃x⦄, x in s -> p (f x)
  证明: by simp
-/
lemma forall_mem_image {p : β -> Prop} : (forall y in s.image f, p y) ↔ forall ⦃x⦄, x in s -> p (f x) := by simp
/--
lemma `exists_mem_image` / 引理 `exists_mem_image`

English:
lemma exists_mem_image
  given: {p : β -> Prop}
  statement: (exists y in s.image f, p y) ↔ exists x in s, p (f x)
  proof: by simp

中文:
引理 存在_mem_image
  条件: {p : β -> 命题}
  结论: (存在 y in s.像 f, p y) ↔ 存在 x in s, p (f x)
  证明: by simp
-/
lemma exists_mem_image {p : β -> Prop} : (exists y in s.image f, p y) ↔ exists x in s, p (f x) := by simp

/--
theorem `map_eq_image` / 定理 `map_eq_image`

English:
theorem map_eq_image
  given: (f : α ↪ β) (s : Finset α)
  statement: s.map f = s.image f
  proof: eq_of_veq (s.map f).2.dedup.symm

中文:
定理 map_eq_image
  条件: (f : α ↪ β) (s : 有限集 α)
  结论: s.map f = s.像 f
  证明: eq_of_veq (s.map f).2.dedup.symm

Depends on / 依赖: dedup.symm, eq_of_veq, s.map
-/
theorem map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.image f :=
  eq_of_veq (s.map f).2.dedup.symm

-- Not `@[simp]` since `mem_image` already gets most of the way there.
/--
theorem `mem_image_const` / 定理 `mem_image_const`

English:
theorem mem_image_const
  statement: c in s.image (const α b) ↔ s.Nonempty ∧ b = c
  proof: by
  grind

中文:
定理 mem_image_const
  结论: c in s.像 (const α b) ↔ s.非空 ∧ b = c
  证明: by
  grind
-/
theorem mem_image_const : c in s.image (const α b) ↔ s.Nonempty ∧ b = c := by
  grind

/--
theorem `mem_image_const_self` / 定理 `mem_image_const_self`

English:
theorem mem_image_const_self
  statement: b in s.image (const α b) ↔ s.Nonempty
  proof: mem_image_const.trans and_iff_left rfl

中文:
定理 mem_image_const_self
  结论: b in s.像 (const α b) ↔ s.非空
  证明: mem_image_const.trans and_iff_left rfl

Depends on / 依赖: and_iff_left, mem_image_const, mem_image_const.trans
-/
theorem mem_image_const_self : b in s.image (const α b) ↔ s.Nonempty :=
mem_image_const.trans and_iff_left rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: (c) (p) [CanLift β α c p]
  body: by
    rintro ⟨⟨l⟩, hd : l.Nodup⟩ hl
    lift l to List α using hl
    exact ⟨⟨l, hd.of_map _⟩, ext fun a => by simp⟩

中文:
实例 canLift
  签名: (c) (p) [CanLift β α c p]
  定义体: by
    rintro ⟨⟨l⟩, hd : l.Nodup⟩ hl
    lift l to List α using hl
    exact ⟨⟨l, hd.of_map _⟩, ext fun a => by simp⟩

Depends on / 依赖: hd.of_map, l.Nodup, of_map
-/
instance canLift (c) (p) [CanLift β α c p] :
    CanLift (Finset β) (Finset α) (image c) fun s => forall x in s, p x where
  prf := by
    rintro ⟨⟨l⟩, hd : l.Nodup⟩ hl
    lift l to List α using hl
    exact ⟨⟨l, hd.of_map _⟩, ext fun a => by simp⟩

/--
theorem `image_congr` / 定理 `image_congr`

English:
theorem image_congr
  given: (h : (s : Set α).EqOn f g)
  statement: Finset.image f s = Finset.image g s
  proof: by
  ext
  simp_rw [mem_image, ← bex_def]
  exact exists₂_congr fun x hx => by rw [h hx]

中文:
定理 image_congr
  条件: (h : (s : 集合 α).EqOn f g)
  结论: 有限集.像 f s = 有限集.像 g s
  证明: by
  ext
  simp_rw [mem_image, ← bex_def]
  exact exists₂_congr fun x hx => by rw [h hx]

Depends on / 依赖: bex_def, mem_image, simp_rw
-/
theorem image_congr (h : (s : Set α).EqOn f g) : Finset.image f s = Finset.image g s := by
  ext
  simp_rw [mem_image, ← bex_def]
  exact exists₂_congr fun x hx => by rw [h hx]

/--
theorem `_root_.Function.Injective.mem_finset_image` / 定理 `_root_.Function.Injective.mem_finset_image`

English:
theorem _root_.Function.Injective.mem_finset_image
  given: (hf : Injective f)
  proof: by
  grind


@[simp, norm_cast]

中文:
定理 _root_.函数.单射.mem_finset_image
  条件: (hf : 单射 f)
  证明: by
  grind


@[simp, norm_cast]
-/
theorem _root_.Function.Injective.mem_finset_image (hf : Injective f) :
    f a in s.image f ↔ a in s := by
  grind


@[simp, norm_cast]
/--
theorem `coe_image` / 定理 `coe_image`

English:
theorem coe_image
  statement: ↑(s.image f) = f '' ↑s
  proof: Set.ext by simp only [mem_coe, mem_image, Set.mem_image, implies_true]

@[simp]

中文:
定理 coe_image
  结论: ↑(s.像 f) = f '' ↑s
  证明: Set.ext by simp only [mem_coe, mem_image, Set.mem_image, implies_true]

@[simp]

Depends on / 依赖: Set.ext, Set.mem_image, implies_true, mem_coe, mem_image
-/
theorem coe_image : ↑(s.image f) = f '' ↑s :=
Set.ext by simp only [mem_coe, mem_image, Set.mem_image, implies_true]

@[simp]
/--
lemma `image_nonempty` / 引理 `image_nonempty`

English:
lemma image_nonempty
  statement: (s.image f).Nonempty ↔ s.Nonempty
  proof: mod_cast Set.image_nonempty (f := f) (s := (s : Set α))

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
引理 image_nonempty
  结论: (s.像 f).非空 ↔ s.非空
  证明: mod_cast Set.image_nonempty (f := f) (s := (s : Set α))

@[aesop safe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: Set.image_nonempty, image_nonempty, mod_cast
-/
lemma image_nonempty : (s.image f).Nonempty ↔ s.Nonempty :=
  mod_cast Set.image_nonempty (f := f) (s := (s : Set α))

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `Nonempty.image` / 定理 `Nonempty.image`

English:
theorem Nonempty.image
  given: (h : s.Nonempty) (f : α -> β)
  statement: (s.image f).Nonempty
  proof: image_nonempty.2 h

alias ⟨Nonempty.of_image, _⟩ := image_nonempty

中文:
定理 非空.像
  条件: (h : s.非空) (f : α -> β)
  结论: (s.像 f).非空
  证明: image_nonempty.2 h

alias ⟨Nonempty.of_image, _⟩ := image_nonempty
-/
protected theorem Nonempty.image (h : s.Nonempty) (f : α -> β) : (s.image f).Nonempty :=
  image_nonempty.2 h

alias ⟨Nonempty.of_image, _⟩ := image_nonempty

/--
theorem `nontrivial_of_image` / 定理 `nontrivial_of_image`

English:
theorem nontrivial_of_image
  given: (h : (s.image f).Nontrivial)
  statement: s.Nontrivial
  proof: by
  simp only [Finset.Nontrivial, coe_image] at h ⊢
  exact Set.nontrivial_of_image _ _ h

中文:
定理 nontrivial_of_image
  条件: (h : (s.像 f).非平凡)
  结论: s.非平凡
  证明: by
  simp only [Finset.Nontrivial, coe_image] at h ⊢
  exact Set.nontrivial_of_image _ _ h

Depends on / 依赖: Finset, Finset.Nontrivial, Nontrivial, Set.nontrivial_of_image, coe_image, nontrivial_of_image
-/
theorem nontrivial_of_image (h : (s.image f).Nontrivial) : s.Nontrivial := by
  simp only [Finset.Nontrivial, coe_image] at h ⊢
  exact Set.nontrivial_of_image _ _ h

/--
theorem `Nontrivial.image_of_injOn` / 定理 `Nontrivial.image_of_injOn`

English:
theorem Nontrivial.image_of_injOn
  given: (hs : s.Nontrivial) (hf : Set.InjOn f s)
  proof: by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

中文:
定理 非平凡.image_of_injOn
  条件: (hs : s.非平凡) (hf : 集合.单射限制 f s)
  证明: by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩
-/
protected theorem Nontrivial.image_of_injOn (hs : s.Nontrivial) (hf : Set.InjOn f s) :
    (s.image f).Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

/--
theorem `image_nontrivial_iff_of_injOn` / 定理 `image_nontrivial_iff_of_injOn`

English:
theorem image_nontrivial_iff_of_injOn
  given: (hf : Set.InjOn f s)
  proof: ⟨nontrivial_of_image, (·.image_of_injOn hf)⟩

中文:
定理 image_nontrivial_iff_of_injOn
  条件: (hf : 集合.单射限制 f s)
  证明: ⟨nontrivial_of_image, (·.image_of_injOn hf)⟩

Depends on / 依赖: image_of_injOn, nontrivial_of_image
-/
theorem image_nontrivial_iff_of_injOn (hf : Set.InjOn f s) :
    (s.image f).Nontrivial ↔ s.Nontrivial :=
  ⟨nontrivial_of_image, (·.image_of_injOn hf)⟩

/--
theorem `image_toFinset` / 定理 `image_toFinset`

English:
theorem image_toFinset
  given: [DecidableEq α] {s : Multiset α}
  proof: ext fun _ => by simp only [mem_image, Multiset.mem_toFinset, Multiset.mem_map]

中文:
定理 image_toFinset
  条件: [DecidableEq α] {s : Multiset α}
  证明: ext fun _ => by simp only [mem_image, Multiset.mem_toFinset, Multiset.mem_map]

Depends on / 依赖: Multiset, Multiset.mem_map, Multiset.mem_toFinset, mem_image, mem_map, mem_toFinset
-/
theorem image_toFinset [DecidableEq α] {s : Multiset α} :
    s.toFinset.image f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_image, Multiset.mem_toFinset, Multiset.mem_map]

/--
theorem `image_val_of_injOn` / 定理 `image_val_of_injOn`

English:
theorem image_val_of_injOn
  given: (H : Set.InjOn f s)
  statement: (image f s).1 = s.1.map f
  proof: (s.2.map_on H).dedup

@[simp]

中文:
定理 image_val_of_injOn
  条件: (H : 集合.单射限制 f s)
  结论: (像 f s).1 = s.1.map f
  证明: (s.2.map_on H).dedup

@[simp]

Depends on / 依赖: map_on
-/
theorem image_val_of_injOn (H : Set.InjOn f s) : (image f s).1 = s.1.map f :=
  (s.2.map_on H).dedup

@[simp]
/--
theorem `image_id` / 定理 `image_id`

English:
theorem image_id
  given: [DecidableEq α]
  statement: s.image id = s
  proof: ext fun _ => by simp only [mem_image, id, exists_eq_right]

@[simp]

中文:
定理 image_id
  条件: [DecidableEq α]
  结论: s.像 id = s
  证明: ext fun _ => by simp only [mem_image, id, exists_eq_right]

@[simp]

Depends on / 依赖: exists_eq_right, mem_image
-/
theorem image_id [DecidableEq α] : s.image id = s :=
  ext fun _ => by simp only [mem_image, id, exists_eq_right]

@[simp]
/--
theorem `image_id'` / 定理 `image_id'`

English:
theorem image_id'
  given: [DecidableEq α]
  statement: (s.image fun x => x) = s
  proof: image_id

中文:
定理 image_id'
  条件: [DecidableEq α]
  结论: (s.像 fun x => x) = s
  证明: image_id

Depends on / 依赖: image_id
-/
theorem image_id' [DecidableEq α] : (s.image fun x => x) = s :=
  image_id

/--
theorem `image_image` / 定理 `image_image`

English:
theorem image_image
  given: [DecidableEq γ] {g : β -> γ}
  statement: (s.image f).image g = s.image (g ∘ f)
  proof: eq_of_veq by simp only [image_val, dedup_map_dedup_eq, Multiset.map_map]

中文:
定理 image_image
  条件: [DecidableEq γ] {g : β -> γ}
  结论: (s.像 f).像 g = s.像 (g ∘ f)
  证明: eq_of_veq by simp only [image_val, dedup_map_dedup_eq, Multiset.map_map]

Depends on / 依赖: Multiset, Multiset.map_map, dedup_map_dedup_eq, eq_of_veq, image_val, map_map
-/
theorem image_image [DecidableEq γ] {g : β -> γ} : (s.image f).image g = s.image (g ∘ f) :=
eq_of_veq by simp only [image_val, dedup_map_dedup_eq, Multiset.map_map]

/--
theorem `image_comp` / 定理 `image_comp`

English:
theorem image_comp
  given: [DecidableEq γ] {g : β -> γ}
  statement: s.image (g ∘ f) = (s.image f).image g
  proof: image_image.symm

中文:
定理 image_comp
  条件: [DecidableEq γ] {g : β -> γ}
  结论: s.像 (g ∘ f) = (s.像 f).像 g
  证明: image_image.symm

Depends on / 依赖: image_image, image_image.symm
-/
theorem image_comp [DecidableEq γ] {g : β -> γ} : s.image (g ∘ f) = (s.image f).image g :=
  image_image.symm

/--
theorem `image_comp_image` / 定理 `image_comp_image`

English:
theorem image_comp_image
  given: [DecidableEq γ] {g : β -> γ}
  proof: by ext s; simp [image_image]

中文:
定理 image_comp_image
  条件: [DecidableEq γ] {g : β -> γ}
  证明: by ext s; simp [image_image]

Depends on / 依赖: image_image
-/
theorem image_comp_image [DecidableEq γ] {g : β -> γ} :
    image g ∘ image f = image (g ∘ f) := by ext s; simp [image_image]

/--
theorem `image_comp_eq` / 定理 `image_comp_eq`

English:
theorem image_comp_eq
  given: [DecidableEq γ] {g : β -> γ}
  proof: image_comp_image.symm

中文:
定理 image_comp_eq
  条件: [DecidableEq γ] {g : β -> γ}
  证明: image_comp_image.symm

Depends on / 依赖: image_comp_image, image_comp_image.symm
-/
theorem image_comp_eq [DecidableEq γ] {g : β -> γ} :
    image (g ∘ f) = image g ∘ image f := image_comp_image.symm

/--
theorem `image_comm` / 定理 `image_comm`

English:
theorem image_comm
  statement: {β'} [DecidableEq β'] [DecidableEq γ] {f : β -> γ} {g : α -> β} {f' : α -> β'}
  proof: by simp_rw [image_image, comp_def, h_comm]

中文:
定理 image_comm
  结论: {β'} [DecidableEq β'] [DecidableEq γ] {f : β -> γ} {g : α -> β} {f' : α -> β'}
  证明: by simp_rw [image_image, comp_def, h_comm]

Depends on / 依赖: comp_def, h_comm, image_image, simp_rw
-/
theorem image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f : β -> γ} {g : α -> β} {f' : α -> β'}
    {g' : β' -> γ} (h_comm : forall a, f (g a) = g' (f' a)) :
    (s.image g).image f = (s.image f').image g' := by simp_rw [image_image, comp_def, h_comm]

/--
theorem `_root_.Function.Semiconj.finset_image` / 定理 `_root_.Function.Semiconj.finset_image`

English:
theorem _root_.Function.Semiconj.finset_image
  statement: [DecidableEq α] {f : α -> β} {ga : α -> α} {gb : β -> β}
  proof: fun _ =>
  image_comm h

中文:
定理 _root_.函数.Semiconj.finset_image
  结论: [DecidableEq α] {f : α -> β} {ga : α -> α} {gb : β -> β}
  证明: fun _ =>
  image_comm h
-/
theorem _root_.Function.Semiconj.finset_image [DecidableEq α] {f : α -> β} {ga : α -> α} {gb : β -> β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun _ =>
  image_comm h

/--
theorem `_root_.Function.Commute.finset_image` / 定理 `_root_.Function.Commute.finset_image`

English:
theorem _root_.Function.Commute.finset_image
  statement: [DecidableEq α] {f g : α -> α}
  proof: Function.Semiconj.finset_image h

@[gcongr]

中文:
定理 _root_.函数.Commute.finset_image
  结论: [DecidableEq α] {f g : α -> α}
  证明: Function.Semiconj.finset_image h

@[gcongr]

Depends on / 依赖: Function, Function.Semiconj.finset_image, Semiconj, finset_image
-/
theorem _root_.Function.Commute.finset_image [DecidableEq α] {f g : α -> α}
    (h : Function.Commute f g) : Function.Commute (image f) (image g) :=
  Function.Semiconj.finset_image h

@[gcongr]
/--
theorem `image_subset_image` / 定理 `image_subset_image`

English:
theorem image_subset_image
  given: {s₁ s₂ : Finset α} (h : s₁ subseteq s₂)
  statement: s₁.image f subseteq s₂.image f
  proof: by
  simp only [subset_def, image_val, subset_dedup', dedup_subset', Multiset.map_subset_map h]

中文:
定理 image_subset_image
  条件: {s₁ s₂ : 有限集 α} (h : s₁ subseteq s₂)
  结论: s₁.像 f subseteq s₂.像 f
  证明: by
  simp only [subset_def, image_val, subset_dedup', dedup_subset', Multiset.map_subset_map h]

Depends on / 依赖: Multiset, Multiset.map_subset_map, dedup_subset, image_val, map_subset_map, subset_dedup, subset_def
-/
theorem image_subset_image {s₁ s₂ : Finset α} (h : s₁ subseteq s₂) : s₁.image f subseteq s₂.image f := by
  simp only [subset_def, image_val, subset_dedup', dedup_subset', Multiset.map_subset_map h]

/--
theorem `image_subset_iff` / 定理 `image_subset_iff`

English:
theorem image_subset_iff
  statement: s.image f subseteq t ↔ forall x in s, f x in t
  proof: calc
    s.image f subseteq t ↔ f '' ↑s subseteq ↑t := by norm_cast
    _ ↔ _ := Set.image_subset_iff

中文:
定理 image_subset_iff
  结论: s.像 f subseteq t ↔ 对任意 x in s, f x in t
  证明: calc
    s.image f subseteq t ↔ f '' ↑s subseteq ↑t := by norm_cast
    _ ↔ _ := Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff, s.image, subseteq
-/
theorem image_subset_iff : s.image f subseteq t ↔ forall x in s, f x in t :=
  calc
    s.image f subseteq t ↔ f '' ↑s subseteq ↑t := by norm_cast
    _ ↔ _ := Set.image_subset_iff

/--
lemma `mapsTo_iff_image_subset` / 引理 `mapsTo_iff_image_subset`

English:
lemma mapsTo_iff_image_subset
  statement: Set.MapsTo f s t ↔ s.image f subseteq t
  proof: by
  simp [Set.MapsTo, image_subset_iff]

alias ⟨_root_.Set.MapsTo.finsetImage_subset, _⟩ := mapsTo_iff_image_subset

中文:
引理 mapsTo_iff_image_subset
  结论: 集合.映射到 f s t ↔ s.像 f subseteq t
  证明: by
  simp [Set.MapsTo, image_subset_iff]

alias ⟨_root_.Set.MapsTo.finsetImage_subset, _⟩ := mapsTo_iff_image_subset

Depends on / 依赖: MapsTo, Set.MapsTo, image_subset_iff
-/
lemma mapsTo_iff_image_subset : Set.MapsTo f s t ↔ s.image f subseteq t := by
  simp [Set.MapsTo, image_subset_iff]

alias ⟨_root_.Set.MapsTo.finsetImage_subset, _⟩ := mapsTo_iff_image_subset

/--
lemma `surjOn_iff_subset_image` / 引理 `surjOn_iff_subset_image`

English:
lemma surjOn_iff_subset_image
  statement: Set.SurjOn f s t ↔ t subseteq s.image f
  proof: by
  simp only [Set.SurjOn]
  norm_cast

alias ⟨_root_.Set.SurjOn.subset_finsetImage, _⟩ := surjOn_iff_subset_image

中文:
引理 surjOn_iff_subset_image
  结论: 集合.满射限制 f s t ↔ t subseteq s.像 f
  证明: by
  simp only [Set.SurjOn]
  norm_cast

alias ⟨_root_.Set.SurjOn.subset_finsetImage, _⟩ := surjOn_iff_subset_image

Depends on / 依赖: Set.SurjOn, SurjOn
-/
lemma surjOn_iff_subset_image : Set.SurjOn f s t ↔ t subseteq s.image f := by
  simp only [Set.SurjOn]
  norm_cast

alias ⟨_root_.Set.SurjOn.subset_finsetImage, _⟩ := surjOn_iff_subset_image

/--
lemma `image_eq_iff_surjOn_mapsTo` / 引理 `image_eq_iff_surjOn_mapsTo`

English:
lemma image_eq_iff_surjOn_mapsTo
  statement: s.image f = t ↔ Set.SurjOn f s t ∧ Set.MapsTo f s t
  proof: by
  grind [mapsTo_iff_image_subset, surjOn_iff_subset_image]

alias ⟨_root_.Set.SurjOn.finsetImage_eq_of_mapsTo, _⟩ := image_eq_iff_surjOn_mapsTo

中文:
引理 image_eq_iff_surjOn_mapsTo
  结论: s.像 f = t ↔ 集合.满射限制 f s t ∧ 集合.映射到 f s t
  证明: by
  grind [mapsTo_iff_image_subset, surjOn_iff_subset_image]

alias ⟨_root_.Set.SurjOn.finsetImage_eq_of_mapsTo, _⟩ := image_eq_iff_surjOn_mapsTo

Depends on / 依赖: mapsTo_iff_image_subset, surjOn_iff_subset_image
-/
lemma image_eq_iff_surjOn_mapsTo : s.image f = t ↔ Set.SurjOn f s t ∧ Set.MapsTo f s t := by
  grind [mapsTo_iff_image_subset, surjOn_iff_subset_image]

alias ⟨_root_.Set.SurjOn.finsetImage_eq_of_mapsTo, _⟩ := image_eq_iff_surjOn_mapsTo

/--
theorem `image_mono` / 定理 `image_mono`

English:
theorem image_mono
  given: (f : α -> β)
  statement: Monotone (Finset.image f)
  proof: fun _ _ => image_subset_image

中文:
定理 image_mono
  条件: (f : α -> β)
  结论: 递增 (有限集.像 f)
  证明: fun _ _ => image_subset_image

Depends on / 依赖: image_subset_image
-/
theorem image_mono (f : α -> β) : Monotone (Finset.image f) := fun _ _ => image_subset_image

/--
lemma `image_injective` / 引理 `image_injective`

English:
lemma image_injective
  given: (hf : Injective f)
  statement: Injective (image f)
  proof: by
  simpa only [funext (map_eq_image _)] using! map_injective ⟨f, hf⟩

中文:
引理 image_injective
  条件: (hf : 单射 f)
  结论: 单射 (像 f)
  证明: by
  simpa only [funext (map_eq_image _)] using! map_injective ⟨f, hf⟩

Depends on / 依赖: map_eq_image, map_injective
-/
lemma image_injective (hf : Injective f) : Injective (image f) := by
  simpa only [funext (map_eq_image _)] using! map_injective ⟨f, hf⟩

/--
lemma `image_inj` / 引理 `image_inj`

English:
lemma image_inj
  given: {t : Finset α} (hf : Injective f)
  statement: s.image f = t.image f ↔ s = t
  proof: (image_injective hf).eq_iff

中文:
引理 image_inj
  条件: {t : 有限集 α} (hf : 单射 f)
  结论: s.像 f = t.像 f ↔ s = t
  证明: (image_injective hf).eq_iff

Depends on / 依赖: eq_iff, image_injective
-/
lemma image_inj {t : Finset α} (hf : Injective f) : s.image f = t.image f ↔ s = t :=
  (image_injective hf).eq_iff

/--
theorem `image_subset_image_iff` / 定理 `image_subset_image_iff`

English:
theorem image_subset_image_iff
  given: {t : Finset α} (hf : Injective f)
  proof: mod_cast Set.image_subset_image_iff hf (s := s) (t := t)

中文:
定理 image_subset_image_iff
  条件: {t : 有限集 α} (hf : 单射 f)
  证明: mod_cast Set.image_subset_image_iff hf (s := s) (t := t)

Depends on / 依赖: Set.image_subset_image_iff, image_subset_image_iff, mod_cast
-/
theorem image_subset_image_iff {t : Finset α} (hf : Injective f) :
    s.image f subseteq t.image f ↔ s subseteq t :=
  mod_cast Set.image_subset_image_iff hf (s := s) (t := t)

/--
theorem `image_subset_image_iff_of_injOn` / 定理 `image_subset_image_iff_of_injOn`

English:
theorem image_subset_image_iff_of_injOn
  statement: {s₁ s₂ : Finset α} (ht : (s : Set α).InjOn f)
  proof: by
  exact_mod_cast ht.image_subset_image_iff (mod_cast h₁) (mod_cast h₂)

中文:
定理 image_subset_image_iff_of_injOn
  结论: {s₁ s₂ : 有限集 α} (ht : (s : 集合 α).单射限制 f)
  证明: by
  exact_mod_cast ht.image_subset_image_iff (mod_cast h₁) (mod_cast h₂)

Depends on / 依赖: ht.image_subset_image_iff, image_subset_image_iff, mod_cast
-/
theorem image_subset_image_iff_of_injOn {s₁ s₂ : Finset α} (ht : (s : Set α).InjOn f)
    (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s) : s₁.image f subseteq s₂.image f ↔ s₁ subseteq s₂ := by
  exact_mod_cast ht.image_subset_image_iff (mod_cast h₁) (mod_cast h₂)

/--
theorem `image_eq_image_iff_of_injOn` / 定理 `image_eq_image_iff_of_injOn`

English:
theorem image_eq_image_iff_of_injOn
  statement: {s₁ s₂ : Finset α} (ht : (s : Set α).InjOn f)
  proof: by
  exact_mod_cast ht.image_eq_image_iff (mod_cast h₁) (mod_cast h₂)

中文:
定理 image_eq_image_iff_of_injOn
  结论: {s₁ s₂ : 有限集 α} (ht : (s : 集合 α).单射限制 f)
  证明: by
  exact_mod_cast ht.image_eq_image_iff (mod_cast h₁) (mod_cast h₂)

Depends on / 依赖: ht.image_eq_image_iff, image_eq_image_iff, mod_cast
-/
theorem image_eq_image_iff_of_injOn {s₁ s₂ : Finset α} (ht : (s : Set α).InjOn f)
    (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s) : s₁.image f = s₂.image f ↔ s₁ = s₂ := by
  exact_mod_cast ht.image_eq_image_iff (mod_cast h₁) (mod_cast h₂)

/--
lemma `image_ssubset_image` / 引理 `image_ssubset_image`

English:
lemma image_ssubset_image
  given: {t : Finset α} (hf : Injective f)
  statement: s.image f ⊂ t.image f ↔ s ⊂ t
  proof: by
  exact lt_iff_lt_of_le_iff_le' (image_subset_image_iff hf) (image_subset_image_iff hf)

中文:
引理 image_ssubset_image
  条件: {t : 有限集 α} (hf : 单射 f)
  结论: s.像 f ⊂ t.像 f ↔ s ⊂ t
  证明: by
  exact lt_iff_lt_of_le_iff_le' (image_subset_image_iff hf) (image_subset_image_iff hf)

Depends on / 依赖: image_subset_image_iff, lt_iff_lt_of_le_iff_le
-/
lemma image_ssubset_image {t : Finset α} (hf : Injective f) : s.image f ⊂ t.image f ↔ s ⊂ t := by
  exact lt_iff_lt_of_le_iff_le' (image_subset_image_iff hf) (image_subset_image_iff hf)

/--
theorem `coe_image_subset_range` / 定理 `coe_image_subset_range`

English:
theorem coe_image_subset_range
  statement: ↑(s.image f) subseteq Set.range f
  proof: calc
    ↑(s.image f) = f '' ↑s := coe_image
    _ subseteq Set.range f := Set.image_subset_range f ↑s

中文:
定理 coe_image_subset_range
  结论: ↑(s.像 f) subseteq 集合.range f
  证明: calc
    ↑(s.image f) = f '' ↑s := coe_image
    _ subseteq Set.range f := Set.image_subset_range f ↑s

Depends on / 依赖: Set.image_subset_range, Set.range, coe_image, image_subset_range, s.image, subseteq
-/
theorem coe_image_subset_range : ↑(s.image f) subseteq Set.range f :=
  calc
    ↑(s.image f) = f '' ↑s := coe_image
    _ subseteq Set.range f := Set.image_subset_range f ↑s

/--
theorem `filter_image` / 定理 `filter_image`

English:
theorem filter_image
  given: {p : β -> Prop} [DecidablePred p]
  proof: by grind

中文:
定理 filter_image
  条件: {p : β -> 命题} [DecidablePred p]
  证明: by grind
-/
theorem filter_image {p : β -> Prop} [DecidablePred p] :
    (s.image f).filter p = (s.filter fun a => p (f a)).image f := by grind

/--
theorem `fiber_nonempty_iff_mem_image` / 定理 `fiber_nonempty_iff_mem_image`

English:
theorem fiber_nonempty_iff_mem_image
  given: {y : β}
  statement: (s.filter (f · = y)).Nonempty ↔ y in s.image f
  proof: by
  simp [Finset.Nonempty]

中文:
定理 fiber_nonempty_iff_mem_image
  条件: {y : β}
  结论: (s.filter (f · = y)).非空 ↔ y in s.像 f
  证明: by
  simp [Finset.Nonempty]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty
-/
theorem fiber_nonempty_iff_mem_image {y : β} : (s.filter (f · = y)).Nonempty ↔ y in s.image f := by
  simp [Finset.Nonempty]

/--
theorem `image_union` / 定理 `image_union`

English:
theorem image_union
  given: [DecidableEq α] {f : α -> β} (s₁ s₂ : Finset α)
  proof: mod_cast Set.image_union f s₁ s₂

中文:
定理 image_union
  条件: [DecidableEq α] {f : α -> β} (s₁ s₂ : 有限集 α)
  证明: mod_cast Set.image_union f s₁ s₂

Depends on / 依赖: Set.image_union, image_union, mod_cast
-/
theorem image_union [DecidableEq α] {f : α -> β} (s₁ s₂ : Finset α) :
    (s₁ union s₂).image f = s₁.image f union s₂.image f :=
  mod_cast Set.image_union f s₁ s₂

/--
theorem `image_inter_subset` / 定理 `image_inter_subset`

English:
theorem image_inter_subset
  given: [DecidableEq α] (f : α -> β) (s t : Finset α)
  proof: (image_mono f).map_inf_le s t

中文:
定理 image_inter_subset
  条件: [DecidableEq α] (f : α -> β) (s t : 有限集 α)
  证明: (image_mono f).map_inf_le s t

Depends on / 依赖: image_mono, map_inf_le
-/
theorem image_inter_subset [DecidableEq α] (f : α -> β) (s t : Finset α) :
    (s inter t).image f subseteq s.image f inter t.image f :=
  (image_mono f).map_inf_le s t

/--
theorem `image_inter_of_injOn` / 定理 `image_inter_of_injOn`

English:
theorem image_inter_of_injOn
  statement: [DecidableEq α] {f : α -> β} (s t : Finset α)
  proof: coe_injective by
    push_cast
exact Set.image_inter_on fun a ha b hb => hf (Or.inr ha) Or.inl hb

中文:
定理 image_inter_of_injOn
  结论: [DecidableEq α] {f : α -> β} (s t : 有限集 α)
  证明: coe_injective by
    push_cast
exact Set.image_inter_on fun a ha b hb => hf (Or.inr ha) Or.inl hb

Depends on / 依赖: Or.inl, Or.inr, Set.image_inter_on, coe_injective, image_inter_on
-/
theorem image_inter_of_injOn [DecidableEq α] {f : α -> β} (s t : Finset α)
    (hf : Set.InjOn f (s union t)) : (s inter t).image f = s.image f inter t.image f :=
coe_injective by
    push_cast
exact Set.image_inter_on fun a ha b hb => hf (Or.inr ha) Or.inl hb

/--
theorem `image_inter` / 定理 `image_inter`

English:
theorem image_inter
  given: [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f)
  proof: image_inter_of_injOn _ _ hf.injOn

@[simp]

中文:
定理 image_inter
  条件: [DecidableEq α] (s₁ s₂ : 有限集 α) (hf : 单射 f)
  证明: image_inter_of_injOn _ _ hf.injOn

@[simp]

Depends on / 依赖: hf.injOn, image_inter_of_injOn
-/
theorem image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f) :
    (s₁ inter s₂).image f = s₁.image f inter s₂.image f :=
  image_inter_of_injOn _ _ hf.injOn

@[simp]
/--
theorem `image_singleton` / 定理 `image_singleton`

English:
theorem image_singleton
  given: (f : α -> β) (a : α)
  statement: image f {a} = {f a}
  proof: by grind

@[simp]

中文:
定理 image_singleton
  条件: (f : α -> β) (a : α)
  结论: 像 f {a} = {f a}
  证明: by grind

@[simp]
-/
theorem image_singleton (f : α -> β) (a : α) : image f {a} = {f a} := by grind

@[simp]
/--
theorem `image_insert` / 定理 `image_insert`

English:
theorem image_insert
  given: [DecidableEq α] (f : α -> β) (a : α) (s : Finset α)
  proof: by grind

中文:
定理 image_insert
  条件: [DecidableEq α] (f : α -> β) (a : α) (s : 有限集 α)
  证明: by grind
-/
theorem image_insert [DecidableEq α] (f : α -> β) (a : α) (s : Finset α) :
    (insert a s).image f = insert (f a) (s.image f) := by grind

/--
theorem `erase_image_subset_image_erase` / 定理 `erase_image_subset_image_erase`

English:
theorem erase_image_subset_image_erase
  given: [DecidableEq α] (f : α -> β) (s : Finset α) (a : α)
  proof: by grind

@[simp]

中文:
定理 erase_image_subset_image_erase
  条件: [DecidableEq α] (f : α -> β) (s : 有限集 α) (a : α)
  证明: by grind

@[simp]
-/
theorem erase_image_subset_image_erase [DecidableEq α] (f : α -> β) (s : Finset α) (a : α) :
    (s.image f).erase (f a) subseteq (s.erase a).image f := by grind

@[simp]
/--
theorem `image_erase` / 定理 `image_erase`

English:
theorem image_erase
  given: [DecidableEq α] {f : α -> β} (hf : Injective f) (s : Finset α) (a : α)
  proof: by grind

@[simp]

中文:
定理 image_erase
  条件: [DecidableEq α] {f : α -> β} (hf : 单射 f) (s : 有限集 α) (a : α)
  证明: by grind

@[simp]
-/
theorem image_erase [DecidableEq α] {f : α -> β} (hf : Injective f) (s : Finset α) (a : α) :
    (s.erase a).image f = (s.image f).erase (f a) := by grind

@[simp]
/--
theorem `image_eq_empty` / 定理 `image_eq_empty`

English:
theorem image_eq_empty
  statement: s.image f = ∅ ↔ s = ∅
  proof: mod_cast Set.image_eq_empty (f := f) (s := s)

@[simp]

中文:
定理 image_eq_empty
  结论: s.像 f = ∅ ↔ s = ∅
  证明: mod_cast Set.image_eq_empty (f := f) (s := s)

@[simp]

Depends on / 依赖: Set.image_eq_empty, image_eq_empty, mod_cast
-/
theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ := mod_cast Set.image_eq_empty (f := f) (s := s)

@[simp]
/--
theorem `empty_eq_image` / 定理 `empty_eq_image`

English:
theorem empty_eq_image
  statement: ∅ = s.image f ↔ s = ∅
  proof: by rw [eq_comm, image_eq_empty]

中文:
定理 empty_eq_image
  结论: ∅ = s.像 f ↔ s = ∅
  证明: by rw [eq_comm, image_eq_empty]

Depends on / 依赖: eq_comm, image_eq_empty
-/
theorem empty_eq_image : ∅ = s.image f ↔ s = ∅ := by rw [eq_comm, image_eq_empty]

/--
theorem `image_sdiff` / 定理 `image_sdiff`

English:
theorem image_sdiff
  given: [DecidableEq α] {f : α -> β} (s t : Finset α) (hf : Injective f)
  proof: mod_cast Set.image_sdiff hf s t

中文:
定理 image_sdiff
  条件: [DecidableEq α] {f : α -> β} (s t : 有限集 α) (hf : 单射 f)
  证明: mod_cast Set.image_sdiff hf s t

Depends on / 依赖: Set.image_sdiff, image_sdiff, mod_cast
-/
theorem image_sdiff [DecidableEq α] {f : α -> β} (s t : Finset α) (hf : Injective f) :
    (s \ t).image f = s.image f \ t.image f :=
  mod_cast Set.image_sdiff hf s t

/--
lemma `image_sdiff_of_injOn` / 引理 `image_sdiff_of_injOn`

English:
lemma image_sdiff_of_injOn
  given: [DecidableEq α] {t : Finset α} (hf : Set.InjOn f s) (hts : t subseteq s)
  proof: mod_cast Set.image_sdiff_of_injOn hf coe_subset.2 hts

中文:
引理 image_sdiff_of_injOn
  条件: [DecidableEq α] {t : 有限集 α} (hf : 集合.单射限制 f s) (hts : t subseteq s)
  证明: mod_cast Set.image_sdiff_of_injOn hf coe_subset.2 hts

Depends on / 依赖: Set.image_sdiff_of_injOn, coe_subset, image_sdiff_of_injOn, mod_cast
-/
lemma image_sdiff_of_injOn [DecidableEq α] {t : Finset α} (hf : Set.InjOn f s) (hts : t subseteq s) :
    (s \ t).image f = s.image f \ t.image f :=
mod_cast Set.image_sdiff_of_injOn hf coe_subset.2 hts

/--
theorem `_root_.Disjoint.of_image_finset` / 定理 `_root_.Disjoint.of_image_finset`

English:
theorem _root_.Disjoint.of_image_finset
  statement: {s t : Finset α} {f : α -> β}
  proof: disjoint_iff_ne.2 fun _ ha _ hb =>
ne_of_apply_ne f h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

中文:
定理 _root_.Disjoint.of_image_finset
  结论: {s t : 有限集 α} {f : α -> β}
  证明: disjoint_iff_ne.2 fun _ ha _ hb =>
ne_of_apply_ne f h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

Depends on / 依赖: disjoint_iff_ne, forall_ne_finset, h.forall_ne_finset, mem_image_of_mem, ne_of_apply_ne
-/
theorem _root_.Disjoint.of_image_finset {s t : Finset α} {f : α -> β}
    (h : Disjoint (s.image f) (t.image f)) : Disjoint s t :=
  disjoint_iff_ne.2 fun _ ha _ hb =>
ne_of_apply_ne f h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

/--
theorem `mem_range_iff_mem_finset_range_of_mod_eq'` / 定理 `mem_range_iff_mem_finset_range_of_mod_eq'`

English:
theorem mem_range_iff_mem_finset_range_of_mod_eq'
  statement: [DecidableEq α] {f : Nat -> α} {a : α} {n : Nat}
  proof: by
  constructor
  · rintro ⟨i, hi⟩
    simp only [mem_image, mem_range]
    exact ⟨i % n, Nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩
  · rintro h
    simp only [mem_image, Set.mem_range, mem_range] at *
    rcases h with ⟨i, _, ha⟩
    exact ⟨i, ha⟩

中文:
定理 mem_range_iff_mem_finset_range_of_mod_eq'
  结论: [DecidableEq α] {f : 自然数 -> α} {a : α} {n : 自然数}
  证明: by
  constructor
  · rintro ⟨i, hi⟩
    simp only [mem_image, mem_range]
    exact ⟨i % n, Nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩
  · rintro h
    simp only [mem_image, Set.mem_range, mem_range] at *
    rcases h with ⟨i, _, ha⟩
    exact ⟨i, ha⟩

Depends on / 依赖: Nat.mod_lt, Set.mem_range, mem_image, mem_range, mod_lt, rfl.congr
-/
theorem mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : Nat -> α} {a : α} {n : Nat}
    (hn : 0 < n) (h : forall i, f (i % n) = f i) :
    a in Set.range f ↔ a in (Finset.range n).image fun i => f i := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [mem_image, mem_range]
    exact ⟨i % n, Nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩
  · rintro h
    simp only [mem_image, Set.mem_range, mem_range] at *
    rcases h with ⟨i, _, ha⟩
    exact ⟨i, ha⟩

/--
theorem `mem_range_iff_mem_finset_range_of_mod_eq` / 定理 `mem_range_iff_mem_finset_range_of_mod_eq`

English:
theorem mem_range_iff_mem_finset_range_of_mod_eq
  statement: [DecidableEq α] {f : Int -> α} {a : α} {n : Nat}
  proof: suffices (exists i, f (i % n) = a) ↔ exists i, i < n ∧ f ↑i = a by simpa [h]
  have hn' : 0 < (n : Int) := Int.ofNat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 <= i % ↑n := Int.emod_nonneg _ (ne_of_gt hn')
      ⟨Int.toNat (i % n), by
        rw [← Int.ofNat_lt]; rw [Int.toNat_of_nonneg this]; exact ⟨Int.emod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
    ⟨i, by rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt_ofNat_of_lt hi), ha]⟩

中文:
定理 mem_range_iff_mem_finset_range_of_mod_eq
  结论: [DecidableEq α] {f : 整数 -> α} {a : α} {n : 自然数}
  证明: suffices (exists i, f (i % n) = a) ↔ exists i, i < n ∧ f ↑i = a by simpa [h]
  have hn' : 0 < (n : Int) := Int.ofNat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 <= i % ↑n := Int.emod_nonneg _ (ne_of_gt hn')
      ⟨Int.toNat (i % n), by
        rw [← Int.ofNat_lt]; rw [Int.toNat_of_nonneg this]; exact ⟨Int.emod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
    ⟨i, by rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt_ofNat_of_lt hi), ha]⟩

Depends on / 依赖: Iff.intro, Int.emod_eq_of_lt, Int.emod_lt_of_pos, Int.emod_nonneg, Int.natCast_nonneg, Int.ofNat_lt, Int.ofNat_lt.mpr, Int.ofNat_lt_ofNat_of_lt, Int.toNat, Int.toNat_of_nonneg, emod_eq_of_lt, emod_lt_of_pos, emod_nonneg, natCast_nonneg, ne_of_gt, ofNat_lt, ofNat_lt_ofNat_of_lt, toNat_of_nonneg
-/
theorem mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : Int -> α} {a : α} {n : Nat}
    (hn : 0 < n) (h : forall i, f (i % n) = f i) :
    a in Set.range f ↔ a in (Finset.range n).image (fun (i : Nat) => f i) :=
  suffices (exists i, f (i % n) = a) ↔ exists i, i < n ∧ f ↑i = a by simpa [h]
  have hn' : 0 < (n : Int) := Int.ofNat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 <= i % ↑n := Int.emod_nonneg _ (ne_of_gt hn')
      ⟨Int.toNat (i % n), by
        rw [← Int.ofNat_lt]; rw [Int.toNat_of_nonneg this]; exact ⟨Int.emod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
    ⟨i, by rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt_ofNat_of_lt hi), ha]⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `attach_image_val` / 定理 `attach_image_val`

English:
theorem attach_image_val
  given: [DecidableEq α] {s : Finset α}
  statement: s.attach.image Subtype.val = s
  proof: eq_of_veq by rw [image_val, attach_val, Multiset.attach_map_val, dedup_eq_self]

中文:
定理 attach_image_val
  条件: [DecidableEq α] {s : 有限集 α}
  结论: s.attach.像 子类型.val = s
  证明: eq_of_veq by rw [image_val, attach_val, Multiset.attach_map_val, dedup_eq_self]

Depends on / 依赖: Multiset, Multiset.attach_map_val, attach_map_val, attach_val, dedup_eq_self, eq_of_veq, image_val
-/
theorem attach_image_val [DecidableEq α] {s : Finset α} : s.attach.image Subtype.val = s :=
eq_of_veq by rw [image_val, attach_val, Multiset.attach_map_val, dedup_eq_self]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `attach_cons` / 引理 `attach_cons`

English:
lemma attach_cons
  given: (a : α) (s : Finset α) (ha)
  proof: by ext ⟨x, hx⟩; simpa using hx

@[simp]

中文:
引理 attach_cons
  条件: (a : α) (s : 有限集 α) (ha)
  证明: by ext ⟨x, hx⟩; simpa using hx

@[simp]
-/
lemma attach_cons (a : α) (s : Finset α) (ha) :
    attach (cons a s ha) =
      cons ⟨a, mem_cons_self a s⟩
        ((attach s).map ⟨fun x => ⟨x.1, mem_cons_of_mem x.2⟩, fun x y => by simp⟩)
          (by simpa) := by ext ⟨x, hx⟩; simpa using hx

@[simp]
/--
theorem `attach_insert` / 定理 `attach_insert`

English:
theorem attach_insert
  given: [DecidableEq α] (s : Finset α) (a : α)
  proof: by ext ⟨x, hx⟩; simpa using hx

@[simp]

中文:
定理 attach_insert
  条件: [DecidableEq α] (s : 有限集 α) (a : α)
  证明: by ext ⟨x, hx⟩; simpa using hx

@[simp]
-/
theorem attach_insert [DecidableEq α] (s : Finset α) (a : α) :
    attach (insert a s) =
      insert (⟨a, mem_insert_self a s⟩ : { x // x in insert a s })
        ((attach s).image fun x => ⟨x.1, mem_insert_of_mem x.2⟩) := by ext ⟨x, hx⟩; simpa using hx

@[simp]
/--
theorem `disjoint_image` / 定理 `disjoint_image`

English:
theorem disjoint_image
  given: {s t : Finset α} {f : α -> β} (hf : Injective f)
  proof: mod_cast Set.disjoint_image_iff hf (s := s) (t := t)

中文:
定理 disjoint_image
  条件: {s t : 有限集 α} {f : α -> β} (hf : 单射 f)
  证明: mod_cast Set.disjoint_image_iff hf (s := s) (t := t)

Depends on / 依赖: Set.disjoint_image_iff, disjoint_image_iff, mod_cast
-/
theorem disjoint_image {s t : Finset α} {f : α -> β} (hf : Injective f) :
    Disjoint (s.image f) (t.image f) ↔ Disjoint s t :=
  mod_cast Set.disjoint_image_iff hf (s := s) (t := t)

/--
theorem `image_const` / 定理 `image_const`

English:
theorem image_const
  given: {s : Finset α} (h : s.Nonempty) (b : β)
  statement: (s.image fun _ => b) = singleton b
  proof: mod_cast Set.Nonempty.image_const (coe_nonempty.2 h) b

@[simp]

中文:
定理 image_const
  条件: {s : 有限集 α} (h : s.非空) (b : β)
  结论: (s.像 fun _ => b) = singleton b
  证明: mod_cast Set.Nonempty.image_const (coe_nonempty.2 h) b

@[simp]

Depends on / 依赖: Nonempty, Set.Nonempty.image_const, coe_nonempty, image_const, mod_cast
-/
theorem image_const {s : Finset α} (h : s.Nonempty) (b : β) : (s.image fun _ => b) = singleton b :=
  mod_cast Set.Nonempty.image_const (coe_nonempty.2 h) b

@[simp]
/--
theorem `map_erase` / 定理 `map_erase`

English:
theorem map_erase
  given: [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α)
  proof: by
  simp_rw [map_eq_image]
  exact s.image_erase f.2 a

中文:
定理 map_erase
  条件: [DecidableEq α] (f : α ↪ β) (s : 有限集 α) (a : α)
  证明: by
  simp_rw [map_eq_image]
  exact s.image_erase f.2 a

Depends on / 依赖: image_erase, map_eq_image, s.image_erase, simp_rw
-/
theorem map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) :
    (s.erase a).map f = (s.map f).erase (f a) := by
  simp_rw [map_eq_image]
  exact s.image_erase f.2 a

/--
theorem `iterate_image` / 定理 `iterate_image`

English:
theorem iterate_image
  given: [DecidableEq α] (f : α -> α) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', iterate_succ', ih, image_image]

中文:
定理 iterate_image
  条件: [DecidableEq α] (f : α -> α) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', iterate_succ', ih, image_image]

Depends on / 依赖: image_image, iterate_succ, iterate_succ_apply
-/
theorem iterate_image [DecidableEq α] (f : α -> α) (n : Nat) :
    (Finset.image f)^[n] s = s.image f^[n] := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', iterate_succ', ih, image_image]

end Image

/-! ### filterMap -/

section FilterMap

-- TODO: should there be `filterImage` too?
/--
Definition of `filterMap` / `filterMap` 的定义

English:
definition filterMap
  signature: (f : α -> Option β) (s : Finset α)
  body: ⟨s.val.filterMap f, s.nodup.filterMap f f_inj⟩

中文:
定义 filterMap
  签名: (f : α -> 选项类型 β) (s : 有限集 α)
  定义体: ⟨s.val.filterMap f, s.nodup.filterMap f f_inj⟩

Depends on / 依赖: f_inj, filterMap, s.nodup.filterMap, s.val.filterMap
-/
def filterMap (f : α -> Option β) (s : Finset α)
    (f_inj : forall a a' b, b in f a -> b in f a' -> a = a') : Finset β :=
  ⟨s.val.filterMap f, s.nodup.filterMap f f_inj⟩

variable (f : α -> Option β) (s' : Finset α) {s t : Finset α}
  {f_inj : forall a a' b, b in f a -> b in f a' -> a = a'}

@[simp]
/--
theorem `filterMap_val` / 定理 `filterMap_val`

English:
theorem filterMap_val
  statement: (filterMap f s' f_inj).1 = s'.1.filterMap f
  proof: rfl

@[simp]

中文:
定理 filterMap_val
  结论: (filterMap f s' f_inj).1 = s'.1.filterMap f
  证明: rfl

@[simp]
-/
theorem filterMap_val : (filterMap f s' f_inj).1 = s'.1.filterMap f := rfl

@[simp]
/--
theorem `filterMap_empty` / 定理 `filterMap_empty`

English:
theorem filterMap_empty
  statement: (∅ : Finset α).filterMap f f_inj = ∅
  proof: rfl

@[simp, grind =]

中文:
定理 filterMap_empty
  结论: (∅ : 有限集 α).filterMap f f_inj = ∅
  证明: rfl

@[simp, grind =]
-/
theorem filterMap_empty : (∅ : Finset α).filterMap f f_inj = ∅ := rfl

@[simp, grind =]
/--
theorem `mem_filterMap` / 定理 `mem_filterMap`

English:
theorem mem_filterMap
  given: {b : β}
  statement: b in s.filterMap f f_inj ↔ exists a in s, f a = some b
  proof: s.val.mem_filterMap f

@[simp, norm_cast]

中文:
定理 mem_filterMap
  条件: {b : β}
  结论: b in s.filterMap f f_inj ↔ 存在 a in s, f a = some b
  证明: s.val.mem_filterMap f

@[simp, norm_cast]

Depends on / 依赖: mem_filterMap, s.val.mem_filterMap
-/
theorem mem_filterMap {b : β} : b in s.filterMap f f_inj ↔ exists a in s, f a = some b :=
  s.val.mem_filterMap f

@[simp, norm_cast]
/--
theorem `coe_filterMap` / 定理 `coe_filterMap`

English:
theorem coe_filterMap
  statement: (s.filterMap f f_inj : Set β) = {b | exists a in s, f a = some b}
  proof: Set.ext (by simp only [mem_coe, mem_filterMap, Set.mem_ofPred_eq, implies_true])

@[simp]

中文:
定理 coe_filterMap
  结论: (s.filterMap f f_inj : 集合 β) = {b | 存在 a in s, f a = some b}
  证明: Set.ext (by simp only [mem_coe, mem_filterMap, Set.mem_ofPred_eq, implies_true])

@[simp]

Depends on / 依赖: Set.ext, Set.mem_ofPred_eq, implies_true, mem_coe, mem_filterMap, mem_ofPred_eq
-/
theorem coe_filterMap : (s.filterMap f f_inj : Set β) = {b | exists a in s, f a = some b} :=
  Set.ext (by simp only [mem_coe, mem_filterMap, Set.mem_ofPred_eq, implies_true])

@[simp]
/--
theorem `filterMap_some` / 定理 `filterMap_some`

English:
theorem filterMap_some
  statement: s.filterMap some (by simp) = s
  proof: ext fun _ => by simp only [mem_filterMap, Option.some.injEq, exists_eq_right]

中文:
定理 filterMap_some
  结论: s.filterMap some (by simp) = s
  证明: ext fun _ => by simp only [mem_filterMap, Option.some.injEq, exists_eq_right]

Depends on / 依赖: Option.some.injEq, exists_eq_right, mem_filterMap
-/
theorem filterMap_some : s.filterMap some (by simp) = s :=
  ext fun _ => by simp only [mem_filterMap, Option.some.injEq, exists_eq_right]

/--
theorem `filterMap_mono` / 定理 `filterMap_mono`

English:
theorem filterMap_mono
  given: (h : s subseteq t)
  proof: by grind

中文:
定理 filterMap_mono
  条件: (h : s subseteq t)
  证明: by grind
-/
theorem filterMap_mono (h : s subseteq t) :
    filterMap f s f_inj subseteq filterMap f t f_inj := by grind

/--
theorem `_root_.List.toFinset_filterMap` / 定理 `_root_.List.toFinset_filterMap`

English:
theorem _root_.List.toFinset_filterMap
  statement: [DecidableEq α] [DecidableEq β]
  proof: by
  simp [← Finset.coe_inj]

中文:
定理 _root_.列表.toFinset_filterMap
  结论: [DecidableEq α] [DecidableEq β]
  证明: by
  simp [← Finset.coe_inj]

Depends on / 依赖: Finset, Finset.coe_inj, coe_inj
-/
theorem _root_.List.toFinset_filterMap [DecidableEq α] [DecidableEq β]
    (f_inj : forall (a a' : α) (b : β), f a = some b -> f a' = some b -> a = a') (s : List α) :
    (s.filterMap f).toFinset = s.toFinset.filterMap f f_inj := by
  simp [← Finset.coe_inj]

end FilterMap

/-! ### Subtype -/


section Subtype

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: {α} (p : α -> Prop) [DecidablePred p] (s : Finset α)
  body: (s.filter p).attach.map
    ⟨fun x => ⟨x.1, by simpa using (Finset.mem_filter.1 x.2).2⟩,
fun _ _ H => Subtype.ext Subtype.mk.inj H⟩

中文:
定义 subtype
  签名: {α} (p : α -> 命题) [DecidablePred p] (s : 有限集 α)
  定义体: (s.filter p).attach.map
    ⟨fun x => ⟨x.1, by simpa using (Finset.mem_filter.1 x.2).2⟩,
fun _ _ H => Subtype.ext Subtype.mk.inj H⟩
-/
protected def subtype {α} (p : α -> Prop) [DecidablePred p] (s : Finset α) : Finset (Subtype p) :=
  (s.filter p).attach.map
    ⟨fun x => ⟨x.1, by simpa using (Finset.mem_filter.1 x.2).2⟩,
fun _ _ H => Subtype.ext Subtype.mk.inj H⟩

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
/--
theorem `mem_subtype` / 定理 `mem_subtype`

English:
theorem mem_subtype
  given: {p : α -> Prop} [DecidablePred p] {s : Finset α}

中文:
定理 mem_subtype
  条件: {p : α -> 命题} [DecidablePred p] {s : 有限集 α}
-/
theorem mem_subtype {p : α -> Prop} [DecidablePred p] {s : Finset α} :
    forall {a : Subtype p}, a in s.subtype p ↔ (a : α) in s
  | ⟨a, ha⟩ => by simp [Finset.subtype, ha]

/--
theorem `subtype_eq_empty` / 定理 `subtype_eq_empty`

English:
theorem subtype_eq_empty
  given: {p : α -> Prop} [DecidablePred p] {s : Finset α}
  proof: by simp [Finset.ext_iff, Subtype.forall]

@[gcongr, mono]

中文:
定理 subtype_eq_empty
  条件: {p : α -> 命题} [DecidablePred p] {s : 有限集 α}
  证明: by simp [Finset.ext_iff, Subtype.forall]

@[gcongr, mono]

Depends on / 依赖: Finset, Finset.ext_iff, Subtype, Subtype.forall, ext_iff
-/
theorem subtype_eq_empty {p : α -> Prop} [DecidablePred p] {s : Finset α} :
    s.subtype p = ∅ ↔ forall x, p x -> x ∉ s := by simp [Finset.ext_iff, Subtype.forall]

@[gcongr, mono]
/--
theorem `subtype_mono` / 定理 `subtype_mono`

English:
theorem subtype_mono
  given: {p : α -> Prop} [DecidablePred p]
  statement: Monotone (Finset.subtype p)
  proof: fun _ _ h _ hx => mem_subtype.2 h mem_subtype.1 hx

中文:
定理 subtype_mono
  条件: {p : α -> 命题} [DecidablePred p]
  结论: 递增 (有限集.subtype p)
  证明: fun _ _ h _ hx => mem_subtype.2 h mem_subtype.1 hx

Depends on / 依赖: mem_subtype
-/
theorem subtype_mono {p : α -> Prop} [DecidablePred p] : Monotone (Finset.subtype p) :=
fun _ _ h _ hx => mem_subtype.2 h mem_subtype.1 hx

/-- `s.subtype p` converts back to `s.filter p` with
`Embedding.subtype`. -/
@[simp]
/--
theorem `subtype_map` / 定理 `subtype_map`

English:
theorem subtype_map
  given: (p : α -> Prop) [DecidablePred p] {s : Finset α}
  proof: by
  ext x
  simp [@and_comm _ (_ = _), @and_comm (p x) (x in s)]

中文:
定理 subtype_map
  条件: (p : α -> 命题) [DecidablePred p] {s : 有限集 α}
  证明: by
  ext x
  simp [@and_comm _ (_ = _), @and_comm (p x) (x in s)]

Depends on / 依赖: and_comm
-/
theorem subtype_map (p : α -> Prop) [DecidablePred p] {s : Finset α} :
    (s.subtype p).map (Embedding.subtype _) = s.filter p := by
  ext x
  simp [@and_comm _ (_ = _), @and_comm (p x) (x in s)]

/--
theorem `subtype_map_of_mem` / 定理 `subtype_map_of_mem`

English:
theorem subtype_map_of_mem
  given: {p : α -> Prop} [DecidablePred p] {s : Finset α} (h : forall x in s, p x)
  proof: ext by simpa [subtype_map] using h

@[simp]

中文:
定理 subtype_map_of_mem
  条件: {p : α -> 命题} [DecidablePred p] {s : 有限集 α} (h : 对任意 x in s, p x)
  证明: ext by simpa [subtype_map] using h

@[simp]

Depends on / 依赖: subtype_map
-/
theorem subtype_map_of_mem {p : α -> Prop} [DecidablePred p] {s : Finset α} (h : forall x in s, p x) :
(s.subtype p).map (Embedding.subtype _) = s := ext by simpa [subtype_map] using h

@[simp]
/--
theorem `subtype_mem_eq_attach` / 定理 `subtype_mem_eq_attach`

English:
theorem subtype_mem_eq_attach
  given: (s : Finset α) [DecidablePred (· in s)]
  proof: by
  ext; simp

中文:
定理 subtype_mem_eq_attach
  条件: (s : 有限集 α) [DecidablePred (· in s)]
  证明: by
  ext; simp
-/
theorem subtype_mem_eq_attach (s : Finset α) [DecidablePred (· in s)] :
    s.subtype (· in s) = s.attach := by
  ext; simp

/--
theorem `property_of_mem_map_subtype` / 定理 `property_of_mem_map_subtype`

English:
theorem property_of_mem_map_subtype
  statement: {p : α -> Prop} (s : Finset { x // p x }) {a : α}
  proof: by
  rcases mem_map.1 h with ⟨x, _, rfl⟩
  exact x.2

中文:
定理 property_of_mem_map_subtype
  结论: {p : α -> 命题} (s : 有限集 { x // p x }) {a : α}
  证明: by
  rcases mem_map.1 h with ⟨x, _, rfl⟩
  exact x.2

Depends on / 依赖: mem_map
-/
theorem property_of_mem_map_subtype {p : α -> Prop} (s : Finset { x // p x }) {a : α}
    (h : a in s.map (Embedding.subtype _)) : p a := by
  rcases mem_map.1 h with ⟨x, _, rfl⟩
  exact x.2

/--
theorem `notMem_map_subtype_of_not_property` / 定理 `notMem_map_subtype_of_not_property`

English:
theorem notMem_map_subtype_of_not_property
  statement: {p : α -> Prop} (s : Finset { x // p x }) {a : α}
  proof: mt s.property_of_mem_map_subtype h

中文:
定理 notMem_map_subtype_of_not_property
  结论: {p : α -> 命题} (s : 有限集 { x // p x }) {a : α}
  证明: mt s.property_of_mem_map_subtype h

Depends on / 依赖: property_of_mem_map_subtype, s.property_of_mem_map_subtype
-/
theorem notMem_map_subtype_of_not_property {p : α -> Prop} (s : Finset { x // p x }) {a : α}
    (h : ¬p a) : a ∉ s.map (Embedding.subtype _) :=
  mt s.property_of_mem_map_subtype h

/--
theorem `map_subtype_subset` / 定理 `map_subtype_subset`

English:
theorem map_subtype_subset
  given: {t : Set α} (s : Finset t)
  statement: ↑(s.map (Embedding.subtype _)) subseteq t
  proof: by
  intro a ha
  rw [mem_coe] at ha
  convert! property_of_mem_map_subtype s ha

中文:
定理 map_subtype_subset
  条件: {t : 集合 α} (s : 有限集 t)
  结论: ↑(s.map (嵌入.subtype _)) subseteq t
  证明: by
  intro a ha
  rw [mem_coe] at ha
  convert! property_of_mem_map_subtype s ha

Depends on / 依赖: convert, mem_coe, property_of_mem_map_subtype
-/
theorem map_subtype_subset {t : Set α} (s : Finset t) : ↑(s.map (Embedding.subtype _)) subseteq t := by
  intro a ha
  rw [mem_coe] at ha
  convert! property_of_mem_map_subtype s ha

end Subtype

/--
theorem `subset_set_image_iff` / 定理 `subset_set_image_iff`

English:
theorem subset_set_image_iff
  given: [DecidableEq β] {s : Set α} {t : Finset β} {f : α -> β}
  proof: by
  constructor
  · intro h
    let : CanLift β s (f ∘ (↑)) fun y => y in f '' s := ⟨fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
    lift t to Finset s using h
    refine ⟨t.map (Embedding.subtype _), map_subtype_subset _, ?_⟩
    ext y; simp
  · grind

中文:
定理 subset_set_image_iff
  条件: [DecidableEq β] {s : 集合 α} {t : 有限集 β} {f : α -> β}
  证明: by
  constructor
  · intro h
    let : CanLift β s (f ∘ (↑)) fun y => y in f '' s := ⟨fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
    lift t to Finset s using h
    refine ⟨t.map (Embedding.subtype _), map_subtype_subset _, ?_⟩
    ext y; simp
  · grind

Depends on / 依赖: CanLift, Embedding, Embedding.subtype, Finset, map_subtype_subset, subtype, t.map
-/
theorem subset_set_image_iff [DecidableEq β] {s : Set α} {t : Finset β} {f : α -> β} :
    ↑t subseteq f '' s ↔ exists s' : Finset α, ↑s' subseteq s ∧ s'.image f = t := by
  constructor
  · intro h
    let : CanLift β s (f ∘ (↑)) fun y => y in f '' s := ⟨fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
    lift t to Finset s using h
    refine ⟨t.map (Embedding.subtype _), map_subtype_subset _, ?_⟩
    ext y; simp
  · grind

/--
theorem `subset_image_iff` / 定理 `subset_image_iff`

English:
theorem subset_image_iff
  given: [DecidableEq β] {s : Finset α} {t : Finset β} {f : α -> β}
  proof: by
  simp only [← coe_subset, coe_image, subset_set_image_iff]

中文:
定理 subset_image_iff
  条件: [DecidableEq β] {s : 有限集 α} {t : 有限集 β} {f : α -> β}
  证明: by
  simp only [← coe_subset, coe_image, subset_set_image_iff]

Depends on / 依赖: coe_image, coe_subset, subset_set_image_iff
-/
theorem subset_image_iff [DecidableEq β] {s : Finset α} {t : Finset β} {f : α -> β} :
    t subseteq s.image f ↔ exists s' : Finset α, s' subseteq s ∧ s'.image f = t := by
  simp only [← coe_subset, coe_image, subset_set_image_iff]

/--
theorem `subset_univ_image_iff` / 定理 `subset_univ_image_iff`

English:
theorem subset_univ_image_iff
  given: [Fintype α] [DecidableEq β] {t : Finset β} {f : α -> β}
  proof: by simp [subset_image_iff]

中文:
定理 subset_univ_image_iff
  条件: [有限类型 α] [DecidableEq β] {t : 有限集 β} {f : α -> β}
  证明: by simp [subset_image_iff]

Depends on / 依赖: subset_image_iff
-/
theorem subset_univ_image_iff [Fintype α] [DecidableEq β] {t : Finset β} {f : α -> β} :
    t subseteq univ.image f ↔ exists s' : Finset α, s'.image f = t := by simp [subset_image_iff]

/--
theorem `range_sdiff_zero` / 定理 `range_sdiff_zero`

English:
theorem range_sdiff_zero
  given: {n : Nat}
  statement: range (n + 1) \ {0} = (range n).image Nat.succ
  proof: by
  induction n with
  | zero => simp
  | succ k hk =>
    conv_rhs => rw [range_add_one]
    rw [range_add_one]; rw [image_insert]; rw [← hk]; rw [insert_sdiff_of_notMem]
    simp

中文:
定理 range_sdiff_zero
  条件: {n : 自然数}
  结论: range (n + 1) \ {0} = (range n).像 自然数.succ
  证明: by
  induction n with
  | zero => simp
  | succ k hk =>
    conv_rhs => rw [range_add_one]
    rw [range_add_one]; rw [image_insert]; rw [← hk]; rw [insert_sdiff_of_notMem]
    simp

Depends on / 依赖: conv_rhs, image_insert, insert_sdiff_of_notMem, range_add_one
-/
theorem range_sdiff_zero {n : Nat} : range (n + 1) \ {0} = (range n).image Nat.succ := by
  induction n with
  | zero => simp
  | succ k hk =>
    conv_rhs => rw [range_add_one]
    rw [range_add_one]; rw [image_insert]; rw [← hk]; rw [insert_sdiff_of_notMem]
    simp

end Finset

/--
theorem `Multiset.toFinset_map` / 定理 `Multiset.toFinset_map`

English:
theorem Multiset.toFinset_map
  given: [DecidableEq α] [DecidableEq β] (f : α -> β) (m : Multiset α)
  proof: Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm

中文:
定理 Multiset.toFinset_map
  条件: [DecidableEq α] [DecidableEq β] (f : α -> β) (m : Multiset α)
  证明: Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm

Depends on / 依赖: Finset, Finset.val_inj, Multiset, Multiset.dedup_map_dedup_eq, dedup_map_dedup_eq, val_inj
-/
theorem Multiset.toFinset_map [DecidableEq α] [DecidableEq β] (f : α -> β) (m : Multiset α) :
    (m.map f).toFinset = m.toFinset.image f :=
  Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm

namespace Equiv

/--
Definition of `finsetCongr` / `finsetCongr` 的定义

English:
definition finsetCongr
  signature: (e : α ≃ β)
  body: s.map e.toEmbedding
  invFun s := s.map e.symm.toEmbedding
  left_inv s := by simp [Finset.map_map]
  right_inv s := by simp [Finset.map_map]

@[simp]

中文:
定义 finsetCongr
  签名: (e : α ≃ β)
  定义体: s.map e.toEmbedding
  invFun s := s.map e.symm.toEmbedding
  left_inv s := by simp [Finset.map_map]
  right_inv s := by simp [Finset.map_map]

@[simp]
-/
protected def finsetCongr (e : α ≃ β) : Finset α ≃ Finset β where
  toFun s := s.map e.toEmbedding
  invFun s := s.map e.symm.toEmbedding
  left_inv s := by simp [Finset.map_map]
  right_inv s := by simp [Finset.map_map]

@[simp]
/--
theorem `finsetCongr_apply` / 定理 `finsetCongr_apply`

English:
theorem finsetCongr_apply
  given: (e : α ≃ β) (s : Finset α)
  statement: e.finsetCongr s = s.map e.toEmbedding
  proof: rfl

@[simp]

中文:
定理 finsetCongr_apply
  条件: (e : α ≃ β) (s : 有限集 α)
  结论: e.finsetCongr s = s.map e.toEmbedding
  证明: rfl

@[simp]
-/
theorem finsetCongr_apply (e : α ≃ β) (s : Finset α) : e.finsetCongr s = s.map e.toEmbedding :=
  rfl

@[simp]
/--
theorem `finsetCongr_refl` / 定理 `finsetCongr_refl`

English:
theorem finsetCongr_refl
  statement: (Equiv.refl α).finsetCongr = Equiv.refl _
  proof: by
  ext
  simp

@[simp]

中文:
定理 finsetCongr_refl
  结论: (等价.refl α).finsetCongr = 等价.refl _
  证明: by
  ext
  simp

@[simp]
-/
theorem finsetCongr_refl : (Equiv.refl α).finsetCongr = Equiv.refl _ := by
  ext
  simp

@[simp]
/--
theorem `finsetCongr_symm` / 定理 `finsetCongr_symm`

English:
theorem finsetCongr_symm
  given: (e : α ≃ β)
  statement: e.finsetCongr.symm = e.symm.finsetCongr
  proof: rfl

@[simp]

中文:
定理 finsetCongr_symm
  条件: (e : α ≃ β)
  结论: e.finsetCongr.symm = e.symm.finsetCongr
  证明: rfl

@[simp]
-/
theorem finsetCongr_symm (e : α ≃ β) : e.finsetCongr.symm = e.symm.finsetCongr :=
  rfl

@[simp]
/--
theorem `finsetCongr_trans` / 定理 `finsetCongr_trans`

English:
theorem finsetCongr_trans
  given: (e : α ≃ β) (e' : β ≃ γ)
  proof: by
  ext
  simp [-Finset.mem_map, -Equiv.trans_toEmbedding]

中文:
定理 finsetCongr_trans
  条件: (e : α ≃ β) (e' : β ≃ γ)
  证明: by
  ext
  simp [-Finset.mem_map, -Equiv.trans_toEmbedding]

Depends on / 依赖: Equiv.trans_toEmbedding, Finset, Finset.mem_map, mem_map, trans_toEmbedding
-/
theorem finsetCongr_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.finsetCongr.trans e'.finsetCongr = (e.trans e').finsetCongr := by
  ext
  simp [-Finset.mem_map, -Equiv.trans_toEmbedding]

/--
theorem `finsetCongr_toEmbedding` / 定理 `finsetCongr_toEmbedding`

English:
theorem finsetCongr_toEmbedding
  given: (e : α ≃ β)
  proof: rfl

中文:
定理 finsetCongr_toEmbedding
  条件: (e : α ≃ β)
  证明: rfl
-/
theorem finsetCongr_toEmbedding (e : α ≃ β) :
    e.finsetCongr.toEmbedding = (Finset.mapEmbedding e.toEmbedding).toEmbedding :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a predicate `p : α → Prop`, produces an equivalence between
  `Finset {a : α // p a}` and `{s : Finset α // ∀ a ∈ s, p a}`. -/
@[simps]
/--
Definition of `finsetSubtypeComm` / `finsetSubtypeComm` 的定义

English:
definition finsetSubtypeComm
  signature: (p : α -> Prop)
  body: ⟨s.map ⟨fun a => a.val, Subtype.val_injective⟩, fun _ h =>
    have ⟨v, _, h⟩ := Embedding.coeFn_mk _ _ ▸ mem_map.mp h; h ▸ v.property⟩
  invFun s := s.val.attach.map (Subtype.impEmbedding _ _ s.property)
  left_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk,
      exists_and_right, exists_eq_right, Subtype.impEmbedding] at * <;>
    grind
  right_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, Subtype.exists, Embedding.coeFn_mk,
      Subtype.impEmbedding] at * <;>
    grind

中文:
定义 finsetSubtypeComm
  签名: (p : α -> 命题)
  定义体: ⟨s.map ⟨fun a => a.val, Subtype.val_injective⟩, fun _ h =>
    have ⟨v, _, h⟩ := Embedding.coeFn_mk _ _ ▸ mem_map.mp h; h ▸ v.property⟩
  invFun s := s.val.attach.map (Subtype.impEmbedding _ _ s.property)
  left_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk,
      exists_and_right, exists_eq_right, Subtype.impEmbedding] at * <;>
    grind
  right_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, Subtype.exists, Embedding.coeFn_mk,
      Subtype.impEmbedding] at * <;>
    grind
-/
protected def finsetSubtypeComm (p : α -> Prop) :
    Finset {a : α // p a} ≃ {s : Finset α // forall a in s, p a} where
  toFun s := ⟨s.map ⟨fun a => a.val, Subtype.val_injective⟩, fun _ h =>
    have ⟨v, _, h⟩ := Embedding.coeFn_mk _ _ ▸ mem_map.mp h; h ▸ v.property⟩
  invFun s := s.val.attach.map (Subtype.impEmbedding _ _ s.property)
  left_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk,
      exists_and_right, exists_eq_right, Subtype.impEmbedding] at * <;>
    grind
  right_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, Subtype.exists, Embedding.coeFn_mk,
      Subtype.impEmbedding] at * <;>
    grind

end Equiv
