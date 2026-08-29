/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Oliver Nash
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.OffDiag
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Finsets in product types

This file defines finset constructions on the product type `α × β`. Beware not to confuse with the
`Finset.prod` operation which computes the multiplicative product.

## Main declarations

* `Finset.product`: Turns `s : Finset α`, `t : Finset β` into their product in `Finset (α × β)`.
* `Finset.diag`: For `s : Finset α`, `s.diag` is the `Finset (α × α)` of pairs `(a, a)` with
  `a ∈ s`.
* `Finset.offDiag`: For `s : Finset α`, `s.offDiag` is the `Finset (α × α)` of pairs `(a, b)` with
  `a, b ∈ s` and `a ≠ b`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Multiset

variable {α β γ : Type*}

namespace Finset

/-! ### prod -/


section Prod

variable {s s' : Finset α} {t t' : Finset β} {a : α} {b : β}

/--
Definition of `product` / `product` 的定义

English:
definition product
  signature: (s : Finset α) (t : Finset β)
  body: ⟨_, s.nodup.product t.nodup⟩

中文:
定义 product
  签名: (s : Finset α) (t : Finset β)
  定义体: ⟨_, s.nodup.product t.nodup⟩
-/
protected def product (s : Finset α) (t : Finset β) : Finset (α × β) :=
  ⟨_, s.nodup.product t.nodup⟩

/--
Instance `instSProd` / 实例 `instSProd`

English:
instance instSProd
  signature: : SProd (Finset α) (Finset β) (Finset (α × β)) where
  body: Finset.product

@[simp]

中文:
实例 instSProd
  签名: : SProd (Finset α) (Finset β) (Finset (α × β)) where
  定义体: Finset.product

@[simp]

Depends on / 依赖: Finset, Finset.product, product
-/
instance instSProd : SProd (Finset α) (Finset β) (Finset (α × β)) where
  sprod := Finset.product

@[simp]
/--
theorem `product_eq_sprod` / 定理 `product_eq_sprod`

English:
theorem product_eq_sprod
  statement: Finset.product s t = s ×ˢ t
  proof: rfl

@[simp]

中文:
定理 product_eq_sprod
  结论: Finset.product s t = s ×ˢ t
  证明: rfl

@[simp]
-/
theorem product_eq_sprod : Finset.product s t = s ×ˢ t :=
  rfl

@[simp]
/--
theorem `product_val` / 定理 `product_val`

English:
theorem product_val
  statement: (s ×ˢ t).1 = s.1 ×ˢ t.1
  proof: rfl

@[simp, grind =]

中文:
定理 product_val
  结论: (s ×ˢ t).1 = s.1 ×ˢ t.1
  证明: rfl

@[simp, grind =]
-/
theorem product_val : (s ×ˢ t).1 = s.1 ×ˢ t.1 :=
  rfl

@[simp, grind =]
/--
theorem `mem_product` / 定理 `mem_product`

English:
theorem mem_product
  given: {p : α × β}
  statement: p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
  proof: Multiset.mem_product

中文:
定理 mem_product
  条件: {p : α × β}
  结论: p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
  证明: Multiset.mem_product

Depends on / 依赖: Multiset, Multiset.mem_product, mem_product
-/
theorem mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t :=
  Multiset.mem_product

/--
theorem `mk_mem_product` / 定理 `mk_mem_product`

English:
theorem mk_mem_product
  given: (ha : a in s) (hb : b in t)
  statement: (a, b) in s ×ˢ t
  proof: mem_product.2 ⟨ha, hb⟩

@[simp, norm_cast]

中文:
定理 mk_mem_product
  条件: (ha : a in s) (hb : b in t)
  结论: (a, b) in s ×ˢ t
  证明: mem_product.2 ⟨ha, hb⟩

@[simp, norm_cast]

Depends on / 依赖: mem_product
-/
theorem mk_mem_product (ha : a in s) (hb : b in t) : (a, b) in s ×ˢ t :=
  mem_product.2 ⟨ha, hb⟩

@[simp, norm_cast]
/--
theorem `coe_product` / 定理 `coe_product`

English:
theorem coe_product
  given: (s : Finset α) (t : Finset β)
  proof: Set.ext fun _ => Finset.mem_product

中文:
定理 coe_product
  条件: (s : Finset α) (t : Finset β)
  证明: Set.ext fun _ => Finset.mem_product

Depends on / 依赖: Finset, Finset.mem_product, Set.ext, mem_product
-/
theorem coe_product (s : Finset α) (t : Finset β) :
    (↑(s ×ˢ t) : Set (α × β)) = (s : Set α) ×ˢ t :=
  Set.ext fun _ => Finset.mem_product

/--
Definition of `_root_.Equiv.Finset.prod` / `_root_.Equiv.Finset.prod` 的定义

English:
definition _root_.Equiv.Finset.prod
  signature: (s : Finset α) (t : Finset β)
  body: ⟨⟨x.1.1, (mem_product.mp x.2).1⟩, ⟨x.1.2, (mem_product.mp x.2).2⟩⟩
  invFun x := ⟨⟨x.1.1, x.2.1⟩, mem_product.mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 _root_.Equiv.Finset.prod
  签名: (s : Finset α) (t : Finset β)
  定义体: ⟨⟨x.1.1, (mem_product.mp x.2).1⟩, ⟨x.1.2, (mem_product.mp x.2).2⟩⟩
  invFun x := ⟨⟨x.1.1, x.2.1⟩, mem_product.mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: CoeHTCT, mem_product, mem_product.mp, znumCoe
-/
def _root_.Equiv.Finset.prod (s : Finset α) (t : Finset β) : ↥(s ×ˢ t) ≃ s × t where
  toFun x := ⟨⟨x.1.1, (mem_product.mp x.2).1⟩, ⟨x.1.2, (mem_product.mp x.2).2⟩⟩
  invFun x := ⟨⟨x.1.1, x.2.1⟩, mem_product.mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
theorem `subset_product_image_fst` / 定理 `subset_product_image_fst`

English:
theorem subset_product_image_fst
  given: [DecidableEq α]
  statement: (s ×ˢ t).image Prod.fst subseteq s
  proof: fun i => by
  simp +contextual [mem_image]

中文:
定理 subset_product_image_fst
  条件: [DecidableEq α]
  结论: (s ×ˢ t).image Prod.fst subseteq s
  证明: fun i => by
  simp +contextual [mem_image]

Depends on / 依赖: contextual, mem_image
-/
theorem subset_product_image_fst [DecidableEq α] : (s ×ˢ t).image Prod.fst subseteq s := fun i => by
  simp +contextual [mem_image]

/--
theorem `subset_product_image_snd` / 定理 `subset_product_image_snd`

English:
theorem subset_product_image_snd
  given: [DecidableEq β]
  statement: (s ×ˢ t).image Prod.snd subseteq t
  proof: fun i => by
  simp +contextual [mem_image]

中文:
定理 subset_product_image_snd
  条件: [DecidableEq β]
  结论: (s ×ˢ t).image Prod.snd subseteq t
  证明: fun i => by
  simp +contextual [mem_image]

Depends on / 依赖: contextual, mem_image
-/
theorem subset_product_image_snd [DecidableEq β] : (s ×ˢ t).image Prod.snd subseteq t := fun i => by
  simp +contextual [mem_image]

/--
theorem `product_image_fst` / 定理 `product_image_fst`

English:
theorem product_image_fst
  given: [DecidableEq α] (ht : t.Nonempty)
  statement: (s ×ˢ t).image Prod.fst = s
  proof: by
  ext i
  simp [mem_image, ht.exists_mem]

中文:
定理 product_image_fst
  条件: [DecidableEq α] (ht : t.Nonempty)
  结论: (s ×ˢ t).image Prod.fst = s
  证明: by
  ext i
  simp [mem_image, ht.exists_mem]

Depends on / 依赖: exists_mem, ht.exists_mem, mem_image
-/
theorem product_image_fst [DecidableEq α] (ht : t.Nonempty) : (s ×ˢ t).image Prod.fst = s := by
  ext i
  simp [mem_image, ht.exists_mem]

/--
theorem `product_image_snd` / 定理 `product_image_snd`

English:
theorem product_image_snd
  given: [DecidableEq β] (ht : s.Nonempty)
  statement: (s ×ˢ t).image Prod.snd = t
  proof: by
  ext i
  simp [mem_image, ht.exists_mem]

中文:
定理 product_image_snd
  条件: [DecidableEq β] (ht : s.Nonempty)
  结论: (s ×ˢ t).image Prod.snd = t
  证明: by
  ext i
  simp [mem_image, ht.exists_mem]

Depends on / 依赖: exists_mem, ht.exists_mem, mem_image
-/
theorem product_image_snd [DecidableEq β] (ht : s.Nonempty) : (s ×ˢ t).image Prod.snd = t := by
  ext i
  simp [mem_image, ht.exists_mem]

/--
theorem `subset_product` / 定理 `subset_product`

English:
theorem subset_product
  given: [DecidableEq α] [DecidableEq β] {s : Finset (α × β)}
  proof: by grind

@[gcongr]

中文:
定理 subset_product
  条件: [DecidableEq α] [DecidableEq β] {s : Finset (α × β)}
  证明: by grind

@[gcongr]
-/
theorem subset_product [DecidableEq α] [DecidableEq β] {s : Finset (α × β)} :
    s subseteq s.image Prod.fst ×ˢ s.image Prod.snd := by grind

@[gcongr]
/--
theorem `product_subset_product` / 定理 `product_subset_product`

English:
theorem product_subset_product
  given: (hs : s subseteq s') (ht : t subseteq t')
  statement: s ×ˢ t subseteq s' ×ˢ t'
  proof: fun ⟨_, _⟩ h =>
  mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩

中文:
定理 product_subset_product
  条件: (hs : s subseteq s') (ht : t subseteq t')
  结论: s ×ˢ t subseteq s' ×ˢ t'
  证明: fun ⟨_, _⟩ h =>
  mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩
-/
theorem product_subset_product (hs : s subseteq s') (ht : t subseteq t') : s ×ˢ t subseteq s' ×ˢ t' := fun ⟨_, _⟩ h =>
  mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩

/--
theorem `product_subset_product_left` / 定理 `product_subset_product_left`

English:
theorem product_subset_product_left
  given: (hs : s subseteq s')
  statement: s ×ˢ t subseteq s' ×ˢ t
  proof: product_subset_product hs (Subset.refl _)

中文:
定理 product_subset_product_left
  条件: (hs : s subseteq s')
  结论: s ×ˢ t subseteq s' ×ˢ t
  证明: product_subset_product hs (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, product_subset_product
-/
theorem product_subset_product_left (hs : s subseteq s') : s ×ˢ t subseteq s' ×ˢ t :=
  product_subset_product hs (Subset.refl _)

/--
theorem `product_subset_product_right` / 定理 `product_subset_product_right`

English:
theorem product_subset_product_right
  given: (ht : t subseteq t')
  statement: s ×ˢ t subseteq s ×ˢ t'
  proof: product_subset_product (Subset.refl _) ht

中文:
定理 product_subset_product_right
  条件: (ht : t subseteq t')
  结论: s ×ˢ t subseteq s ×ˢ t'
  证明: product_subset_product (Subset.refl _) ht

Depends on / 依赖: Subset, Subset.refl, product_subset_product
-/
theorem product_subset_product_right (ht : t subseteq t') : s ×ˢ t subseteq s ×ˢ t' :=
  product_subset_product (Subset.refl _) ht

/--
theorem `prodMap_image_product` / 定理 `prodMap_image_product`

English:
theorem prodMap_image_product
  statement: {δ : Type*} [DecidableEq β] [DecidableEq δ]
  proof: mod_cast Set.prodMap_image_prod f g s t

中文:
定理 prodMap_image_product
  结论: {δ : 类型} [DecidableEq β] [DecidableEq δ]
  证明: mod_cast Set.prodMap_image_prod f g s t

Depends on / 依赖: Set.prodMap_image_prod, mod_cast, prodMap_image_prod
-/
theorem prodMap_image_product {δ : Type*} [DecidableEq β] [DecidableEq δ]
    (f : α -> β) (g : γ -> δ) (s : Finset α) (t : Finset γ) :
    (s ×ˢ t).image (Prod.map f g) = s.image f ×ˢ t.image g :=
  mod_cast Set.prodMap_image_prod f g s t

/--
theorem `prodMap_map_product` / 定理 `prodMap_map_product`

English:
theorem prodMap_map_product
  given: {δ : Type*} (f : α ↪ β) (g : γ ↪ δ) (s : Finset α) (t : Finset γ)
  proof: by
  simpa [← coe_inj] using Set.prodMap_image_prod f g s t

中文:
定理 prodMap_map_product
  条件: {δ : 类型} (f : α ↪ β) (g : γ ↪ δ) (s : Finset α) (t : Finset γ)
  证明: by
  simpa [← coe_inj] using Set.prodMap_image_prod f g s t

Depends on / 依赖: Set.prodMap_image_prod, coe_inj, prodMap_image_prod
-/
theorem prodMap_map_product {δ : Type*} (f : α ↪ β) (g : γ ↪ δ) (s : Finset α) (t : Finset γ) :
    (s ×ˢ t).map (f.prodMap g) = s.map f ×ˢ t.map g := by
  simpa [← coe_inj] using Set.prodMap_image_prod f g s t

/--
theorem `map_swap_product` / 定理 `map_swap_product`

English:
theorem map_swap_product
  given: (s : Finset α) (t : Finset β)
  proof: coe_injective by
    push_cast
    exact Set.image_swap_prod _ _

@[simp]

中文:
定理 map_swap_product
  条件: (s : Finset α) (t : Finset β)
  证明: coe_injective by
    push_cast
    exact Set.image_swap_prod _ _

@[simp]

Depends on / 依赖: Set.image_swap_prod, coe_injective, image_swap_prod
-/
theorem map_swap_product (s : Finset α) (t : Finset β) :
    (t ×ˢ s).map ⟨Prod.swap, Prod.swap_injective⟩ = s ×ˢ t :=
coe_injective by
    push_cast
    exact Set.image_swap_prod _ _

@[simp]
/--
theorem `image_swap_product` / 定理 `image_swap_product`

English:
theorem image_swap_product
  given: [DecidableEq (α × β)] (s : Finset α) (t : Finset β)
  proof: coe_injective by
    push_cast
    exact Set.image_swap_prod _ _

中文:
定理 image_swap_product
  条件: [DecidableEq (α × β)] (s : Finset α) (t : Finset β)
  证明: coe_injective by
    push_cast
    exact Set.image_swap_prod _ _

Depends on / 依赖: Set.image_swap_prod, coe_injective, image_swap_prod
-/
theorem image_swap_product [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    (t ×ˢ s).image Prod.swap = s ×ˢ t :=
coe_injective by
    push_cast
    exact Set.image_swap_prod _ _

/--
theorem `product_eq_biUnion` / 定理 `product_eq_biUnion`

English:
theorem product_eq_biUnion
  given: [DecidableEq (α × β)] (s : Finset α) (t : Finset β)
  proof: by grind

中文:
定理 product_eq_biUnion
  条件: [DecidableEq (α × β)] (s : Finset α) (t : Finset β)
  证明: by grind
-/
theorem product_eq_biUnion [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    s ×ˢ t = s.biUnion fun a => t.image fun b => (a, b) := by grind

/--
theorem `product_eq_biUnion_right` / 定理 `product_eq_biUnion_right`

English:
theorem product_eq_biUnion_right
  given: [DecidableEq (α × β)] (s : Finset α) (t : Finset β)
  proof: by grind

中文:
定理 product_eq_biUnion_right
  条件: [DecidableEq (α × β)] (s : Finset α) (t : Finset β)
  证明: by grind
-/
theorem product_eq_biUnion_right [DecidableEq (α × β)] (s : Finset α) (t : Finset β) :
    s ×ˢ t = t.biUnion fun b => s.image fun a => (a, b) := by grind

/-- See also `Finset.sup_product_left`. -/
@[simp]
/--
theorem `product_biUnion` / 定理 `product_biUnion`

English:
theorem product_biUnion
  given: [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β -> Finset γ)
  proof: by grind

@[simp]

中文:
定理 product_biUnion
  条件: [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β -> Finset γ)
  证明: by grind

@[simp]
-/
theorem product_biUnion [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β -> Finset γ) :
    (s ×ˢ t).biUnion f = s.biUnion fun a => t.biUnion fun b => f (a, b) := by grind

@[simp]
/--
theorem `card_product` / 定理 `card_product`

English:
theorem card_product
  given: (s : Finset α) (t : Finset β)
  statement: card (s ×ˢ t) = card s * card t
  proof: Multiset.card_product _ _

中文:
定理 card_product
  条件: (s : Finset α) (t : Finset β)
  结论: card (s ×ˢ t) = card s * card t
  证明: Multiset.card_product _ _

Depends on / 依赖: Multiset, Multiset.card_product, card_product
-/
theorem card_product (s : Finset α) (t : Finset β) : card (s ×ˢ t) = card s * card t :=
  Multiset.card_product _ _

/--
lemma `nontrivial_prod_iff` / 引理 `nontrivial_prod_iff`

English:
lemma nontrivial_prod_iff
  statement: (s ×ˢ t).Nontrivial ↔
  proof: by
  simp_rw [← card_pos, ← one_lt_card_iff_nontrivial, card_product]; apply Nat.one_lt_mul_iff

中文:
引理 nontrivial_prod_iff
  结论: (s ×ˢ t).Nontrivial ↔
  证明: by
  simp_rw [← card_pos, ← one_lt_card_iff_nontrivial, card_product]; apply Nat.one_lt_mul_iff

Depends on / 依赖: Nat.one_lt_mul_iff, card_pos, card_product, one_lt_card_iff_nontrivial, one_lt_mul_iff, simp_rw
-/
lemma nontrivial_prod_iff : (s ×ˢ t).Nontrivial ↔
    s.Nonempty ∧ t.Nonempty ∧ (s.Nontrivial ∨ t.Nontrivial) := by
  simp_rw [← card_pos, ← one_lt_card_iff_nontrivial, card_product]; apply Nat.one_lt_mul_iff

/--
theorem `filter_product` / 定理 `filter_product`

English:
theorem filter_product
  given: (p : α -> Prop) (q : β -> Prop) [DecidablePred p] [DecidablePred q]
  proof: by grind

中文:
定理 filter_product
  条件: (p : α -> 命题) (q : β -> 命题) [DecidablePred p] [DecidablePred q]
  证明: by grind
-/
theorem filter_product (p : α -> Prop) (q : β -> Prop) [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => p x.1 ∧ q x.2) = s.filter p ×ˢ t.filter q := by grind

/--
theorem `filter_product_left` / 定理 `filter_product_left`

English:
theorem filter_product_left
  given: (p : α -> Prop) [DecidablePred p]
  proof: by
  simpa using filter_product p fun _ => true

中文:
定理 filter_product_left
  条件: (p : α -> 命题) [DecidablePred p]
  证明: by
  simpa using filter_product p fun _ => true

Depends on / 依赖: filter_product
-/
theorem filter_product_left (p : α -> Prop) [DecidablePred p] :
    ((s ×ˢ t).filter fun x : α × β => p x.1) = s.filter p ×ˢ t := by
  simpa using filter_product p fun _ => true

/--
theorem `filter_product_right` / 定理 `filter_product_right`

English:
theorem filter_product_right
  given: (q : β -> Prop) [DecidablePred q]
  proof: by
  simpa using filter_product (fun _ : α => true) q

中文:
定理 filter_product_right
  条件: (q : β -> 命题) [DecidablePred q]
  证明: by
  simpa using filter_product (fun _ : α => true) q

Depends on / 依赖: filter_product
-/
theorem filter_product_right (q : β -> Prop) [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => q x.2) = s ×ˢ t.filter q := by
  simpa using filter_product (fun _ : α => true) q

/--
theorem `filter_product_card` / 定理 `filter_product_card`

English:
theorem filter_product_card
  statement: (s : Finset α) (t : Finset β) (p : α -> Prop) (q : β -> Prop)
  proof: by
  classical
  rw [← card_product]; rw [← card_product]; rw [← filter_product]; rw [← filter_product]; rw [← card_union_of_disjoint]
  · apply congr_arg
    grind
  · apply Finset.disjoint_filter_filter'
    exact (disjoint_compl_right.inf_left _).inf_right _

@[simp]

中文:
定理 filter_product_card
  结论: (s : Finset α) (t : Finset β) (p : α -> 命题) (q : β -> 命题)
  证明: by
  classical
  rw [← card_product]; rw [← card_product]; rw [← filter_product]; rw [← filter_product]; rw [← card_union_of_disjoint]
  · apply congr_arg
    grind
  · apply Finset.disjoint_filter_filter'
    exact (disjoint_compl_right.inf_left _).inf_right _

@[simp]

Depends on / 依赖: Finset, Finset.disjoint_filter_filter, card_product, card_union_of_disjoint, classical, congr_arg, disjoint_compl_right, disjoint_compl_right.inf_left, disjoint_filter_filter, filter_product, inf_left, inf_right
-/
theorem filter_product_card (s : Finset α) (t : Finset β) (p : α -> Prop) (q : β -> Prop)
    [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filter fun x : α × β => (p x.1) = (q x.2)).card =
      (s.filter p).card * (t.filter q).card +
        (s.filter (¬ p ·)).card * (t.filter (¬ q ·)).card := by
  classical
  rw [← card_product]; rw [← card_product]; rw [← filter_product]; rw [← filter_product]; rw [← card_union_of_disjoint]
  · apply congr_arg
    grind
  · apply Finset.disjoint_filter_filter'
    exact (disjoint_compl_right.inf_left _).inf_right _

@[simp]
/--
theorem `empty_product` / 定理 `empty_product`

English:
theorem empty_product
  given: (t : Finset β)
  statement: (∅ : Finset α) ×ˢ t = ∅
  proof: rfl

@[simp]

中文:
定理 empty_product
  条件: (t : Finset β)
  结论: (∅ : Finset α) ×ˢ t = ∅
  证明: rfl

@[simp]
-/
theorem empty_product (t : Finset β) : (∅ : Finset α) ×ˢ t = ∅ :=
  rfl

@[simp]
/--
theorem `product_empty` / 定理 `product_empty`

English:
theorem product_empty
  given: (s : Finset α)
  statement: s ×ˢ (∅ : Finset β) = ∅
  proof: eq_empty_of_forall_notMem fun _ h => notMem_empty _ (Finset.mem_product.1 h).2

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 product_empty
  条件: (s : Finset α)
  结论: s ×ˢ (∅ : Finset β) = ∅
  证明: eq_empty_of_forall_notMem fun _ h => notMem_empty _ (Finset.mem_product.1 h).2

@[aesop safe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: Finset, Finset.mem_product, eq_empty_of_forall_notMem, mem_product, notMem_empty
-/
theorem product_empty (s : Finset α) : s ×ˢ (∅ : Finset β) = ∅ :=
  eq_empty_of_forall_notMem fun _ h => notMem_empty _ (Finset.mem_product.1 h).2

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `Nonempty.product` / 定理 `Nonempty.product`

English:
theorem Nonempty.product
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  statement: (s ×ˢ t).Nonempty
  proof: let ⟨x, hx⟩ := hs
  let ⟨y, hy⟩ := ht
  ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩

中文:
定理 Nonempty.product
  条件: (hs : s.Nonempty) (ht : t.Nonempty)
  结论: (s ×ˢ t).Nonempty
  证明: let ⟨x, hx⟩ := hs
  let ⟨y, hy⟩ := ht
  ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩

Depends on / 依赖: mem_product
-/
theorem Nonempty.product (hs : s.Nonempty) (ht : t.Nonempty) : (s ×ˢ t).Nonempty :=
  let ⟨x, hx⟩ := hs
  let ⟨y, hy⟩ := ht
  ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩

/--
theorem `Nonempty.fst` / 定理 `Nonempty.fst`

English:
theorem Nonempty.fst
  given: (h : (s ×ˢ t).Nonempty)
  statement: s.Nonempty
  proof: let ⟨xy, hxy⟩ := h
  ⟨xy.1, (mem_product.1 hxy).1⟩

中文:
定理 Nonempty.fst
  条件: (h : (s ×ˢ t).Nonempty)
  结论: s.Nonempty
  证明: let ⟨xy, hxy⟩ := h
  ⟨xy.1, (mem_product.1 hxy).1⟩

Depends on / 依赖: mem_product
-/
theorem Nonempty.fst (h : (s ×ˢ t).Nonempty) : s.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.1, (mem_product.1 hxy).1⟩

/--
theorem `Nonempty.snd` / 定理 `Nonempty.snd`

English:
theorem Nonempty.snd
  given: (h : (s ×ˢ t).Nonempty)
  statement: t.Nonempty
  proof: let ⟨xy, hxy⟩ := h
  ⟨xy.2, (mem_product.1 hxy).2⟩

@[simp]

中文:
定理 Nonempty.snd
  条件: (h : (s ×ˢ t).Nonempty)
  结论: t.Nonempty
  证明: let ⟨xy, hxy⟩ := h
  ⟨xy.2, (mem_product.1 hxy).2⟩

@[simp]

Depends on / 依赖: mem_product
-/
theorem Nonempty.snd (h : (s ×ˢ t).Nonempty) : t.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.2, (mem_product.1 hxy).2⟩

@[simp]
/--
theorem `nonempty_product` / 定理 `nonempty_product`

English:
theorem nonempty_product
  statement: (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.product h.2⟩

@[simp]

中文:
定理 nonempty_product
  结论: (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.product h.2⟩

@[simp]

Depends on / 依赖: h.fst, h.snd, product
-/
theorem nonempty_product : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.product h.2⟩

@[simp]
/--
theorem `product_eq_empty` / 定理 `product_eq_empty`

English:
theorem product_eq_empty
  given: {s : Finset α} {t : Finset β}
  statement: s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: by
  contrapose!; exact nonempty_product

@[simp]

中文:
定理 product_eq_empty
  条件: {s : Finset α} {t : Finset β}
  结论: s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: by
  contrapose!; exact nonempty_product

@[simp]

Depends on / 依赖: contrapose, nonempty_product
-/
theorem product_eq_empty {s : Finset α} {t : Finset β} : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  contrapose!; exact nonempty_product

@[simp]
/--
theorem `singleton_product` / 定理 `singleton_product`

English:
theorem singleton_product
  given: {a : α}
  proof: by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]

中文:
定理 singleton_product
  条件: {a : α}
  证明: by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]

Depends on / 依赖: and_left_comm, eq_comm
-/
theorem singleton_product {a : α} :
    ({a} : Finset α) ×ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩ := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]
/--
lemma `product_singleton` / 引理 `product_singleton`

English:
lemma product_singleton
  statement: s ×ˢ {b} = s.map ⟨fun i => (i, b), Prod.mk_left_injective _⟩
  proof: by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

中文:
引理 product_singleton
  结论: s ×ˢ {b} = s.map ⟨fun i => (i, b), Prod.mk_left_injective _⟩
  证明: by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

Depends on / 依赖: and_left_comm, eq_comm
-/
lemma product_singleton : s ×ˢ {b} = s.map ⟨fun i => (i, b), Prod.mk_left_injective _⟩ := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

/--
theorem `singleton_product_singleton` / 定理 `singleton_product_singleton`

English:
theorem singleton_product_singleton
  given: {a : α} {b : β}
  proof: by
  simp only [product_singleton, Function.Embedding.coeFn_mk, map_singleton]

@[simp]

中文:
定理 singleton_product_singleton
  条件: {a : α} {b : β}
  证明: by
  simp only [product_singleton, Function.Embedding.coeFn_mk, map_singleton]

@[simp]

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, coeFn_mk, map_singleton, product_singleton
-/
theorem singleton_product_singleton {a : α} {b : β} :
    ({a} ×ˢ {b} : Finset _) = {(a, b)} := by
  simp only [product_singleton, Function.Embedding.coeFn_mk, map_singleton]

@[simp]
/--
theorem `union_product` / 定理 `union_product`

English:
theorem union_product
  given: [DecidableEq α] [DecidableEq β]
  statement: (s union s') ×ˢ t = s ×ˢ t union s' ×ˢ t
  proof: by grind

@[simp]

中文:
定理 union_product
  条件: [DecidableEq α] [DecidableEq β]
  结论: (s union s') ×ˢ t = s ×ˢ t union s' ×ˢ t
  证明: by grind

@[simp]
-/
theorem union_product [DecidableEq α] [DecidableEq β] : (s union s') ×ˢ t = s ×ˢ t union s' ×ˢ t := by grind

@[simp]
/--
theorem `product_union` / 定理 `product_union`

English:
theorem product_union
  given: [DecidableEq α] [DecidableEq β]
  statement: s ×ˢ (t union t') = s ×ˢ t union s ×ˢ t'
  proof: by grind

中文:
定理 product_union
  条件: [DecidableEq α] [DecidableEq β]
  结论: s ×ˢ (t union t') = s ×ˢ t union s ×ˢ t'
  证明: by grind
-/
theorem product_union [DecidableEq α] [DecidableEq β] : s ×ˢ (t union t') = s ×ˢ t union s ×ˢ t' := by grind

/--
theorem `inter_product` / 定理 `inter_product`

English:
theorem inter_product
  given: [DecidableEq α] [DecidableEq β]
  statement: (s inter s') ×ˢ t = s ×ˢ t inter s' ×ˢ t
  proof: by grind

中文:
定理 inter_product
  条件: [DecidableEq α] [DecidableEq β]
  结论: (s inter s') ×ˢ t = s ×ˢ t inter s' ×ˢ t
  证明: by grind
-/
theorem inter_product [DecidableEq α] [DecidableEq β] : (s inter s') ×ˢ t = s ×ˢ t inter s' ×ˢ t := by grind

/--
theorem `product_inter` / 定理 `product_inter`

English:
theorem product_inter
  given: [DecidableEq α] [DecidableEq β]
  statement: s ×ˢ (t inter t') = s ×ˢ t inter s ×ˢ t'
  proof: by grind

中文:
定理 product_inter
  条件: [DecidableEq α] [DecidableEq β]
  结论: s ×ˢ (t inter t') = s ×ˢ t inter s ×ˢ t'
  证明: by grind
-/
theorem product_inter [DecidableEq α] [DecidableEq β] : s ×ˢ (t inter t') = s ×ˢ t inter s ×ˢ t' := by grind

/--
theorem `product_inter_product` / 定理 `product_inter_product`

English:
theorem product_inter_product
  given: [DecidableEq α] [DecidableEq β]
  proof: by grind

中文:
定理 product_inter_product
  条件: [DecidableEq α] [DecidableEq β]
  证明: by grind
-/
theorem product_inter_product [DecidableEq α] [DecidableEq β] :
    s ×ˢ t inter s' ×ˢ t' = (s inter s') ×ˢ (t inter t') := by grind

/--
theorem `disjoint_product` / 定理 `disjoint_product`

English:
theorem disjoint_product
  statement: Disjoint (s ×ˢ t) (s' ×ˢ t') ↔ Disjoint s s' ∨ Disjoint t t'
  proof: by
  simp_rw [← disjoint_coe, coe_product, Set.disjoint_prod]

@[simp]

中文:
定理 disjoint_product
  结论: Disjoint (s ×ˢ t) (s' ×ˢ t') ↔ Disjoint s s' ∨ Disjoint t t'
  证明: by
  simp_rw [← disjoint_coe, coe_product, Set.disjoint_prod]

@[simp]

Depends on / 依赖: Set.disjoint_prod, coe_product, disjoint_coe, disjoint_prod, simp_rw
-/
theorem disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t') ↔ Disjoint s s' ∨ Disjoint t t' := by
  simp_rw [← disjoint_coe, coe_product, Set.disjoint_prod]

@[simp]
/--
theorem `disjUnion_product` / 定理 `disjUnion_product`

English:
theorem disjUnion_product
  given: (hs : Disjoint s s')
  proof: eq_of_veq Multiset.add_product _ _ _

@[simp]

中文:
定理 disjUnion_product
  条件: (hs : Disjoint s s')
  证明: eq_of_veq Multiset.add_product _ _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.add_product, add_product, eq_of_veq
-/
theorem disjUnion_product (hs : Disjoint s s') :
    s.disjUnion s' hs ×ˢ t = (s ×ˢ t).disjUnion (s' ×ˢ t) (disjoint_product.mpr <| Or.inl hs) :=
eq_of_veq Multiset.add_product _ _ _

@[simp]
/--
theorem `product_disjUnion` / 定理 `product_disjUnion`

English:
theorem product_disjUnion
  given: (ht : Disjoint t t')
  proof: eq_of_veq Multiset.product_add _ _ _

中文:
定理 product_disjUnion
  条件: (ht : Disjoint t t')
  证明: eq_of_veq Multiset.product_add _ _ _

Depends on / 依赖: Multiset, Multiset.product_add, eq_of_veq, product_add
-/
theorem product_disjUnion (ht : Disjoint t t') :
    s ×ˢ t.disjUnion t' ht = (s ×ˢ t).disjUnion (s ×ˢ t') (disjoint_product.mpr <| Or.inr ht) :=
eq_of_veq Multiset.product_add _ _ _

end Prod

section Diag

variable (s t : Finset α)

/--
Definition of `diag` / `diag` 的定义

English:
definition diag
  signature: : Finset (α × α)
  body: s.map ⟨Function.diag, Function.diag_injective⟩

中文:
定义 diag
  签名: : Finset (α × α)
  定义体: s.map ⟨Function.diag, Function.diag_injective⟩

Depends on / 依赖: Function, Function.diag, Function.diag_injective, diag_injective, s.map
-/
def diag : Finset (α × α) := s.map ⟨Function.diag, Function.diag_injective⟩

-- TODO: define `Multiset.offDiag`, provide basic API, use it here
/--
Definition of `offDiag` / `offDiag` 的定义

English:
definition offDiag
  signature: : Finset (α × α)
  body: .mk (Quotient.map List.offDiag (fun _ _ => List.Perm.offDiag) s.1) by
    rcases s with ⟨⟨s⟩, hs⟩
    exact hs.offDiag

中文:
定义 offDiag
  签名: : Finset (α × α)
  定义体: .mk (Quotient.map List.offDiag (fun _ _ => List.Perm.offDiag) s.1) by
    rcases s with ⟨⟨s⟩, hs⟩
    exact hs.offDiag

Depends on / 依赖: List.Perm.offDiag, List.offDiag, Quotient, Quotient.map, hs.offDiag, offDiag
-/
def offDiag : Finset (α × α) :=
.mk (Quotient.map List.offDiag (fun _ _ => List.Perm.offDiag) s.1) by
    rcases s with ⟨⟨s⟩, hs⟩
    exact hs.offDiag

variable {s} {x : α × α}

@[simp, grind =]
/--
theorem `mem_diag` / 定理 `mem_diag`

English:
theorem mem_diag
  statement: x in s.diag ↔ x.1 in s ∧ x.1 = x.2
  proof: by
  aesop (add simp diag)

@[simp, grind =]

中文:
定理 mem_diag
  结论: x in s.diag ↔ x.1 in s ∧ x.1 = x.2
  证明: by
  aesop (add simp diag)

@[simp, grind =]
-/
theorem mem_diag : x in s.diag ↔ x.1 in s ∧ x.1 = x.2 := by
  aesop (add simp diag)

@[simp, grind =]
/--
theorem `mem_offDiag` / 定理 `mem_offDiag`

English:
theorem mem_offDiag
  statement: x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧ x.1 != x.2
  proof: by
  rcases s with ⟨⟨s⟩, hs⟩
  exact hs.mem_offDiag

@[simp, grind =]

中文:
定理 mem_offDiag
  结论: x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧ x.1 != x.2
  证明: by
  rcases s with ⟨⟨s⟩, hs⟩
  exact hs.mem_offDiag

@[simp, grind =]

Depends on / 依赖: hs.mem_offDiag, mem_offDiag
-/
theorem mem_offDiag : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧ x.1 != x.2 := by
  rcases s with ⟨⟨s⟩, hs⟩
  exact hs.mem_offDiag

@[simp, grind =]
/--
theorem `diag_nonempty` / 定理 `diag_nonempty`

English:
theorem diag_nonempty
  statement: s.diag.Nonempty ↔ s.Nonempty
  proof: by
  simp [diag]

@[simp, grind =]

中文:
定理 diag_nonempty
  结论: s.diag.Nonempty ↔ s.Nonempty
  证明: by
  simp [diag]

@[simp, grind =]
-/
theorem diag_nonempty : s.diag.Nonempty ↔ s.Nonempty := by
  simp [diag]

@[simp, grind =]
/--
theorem `diag_eq_empty` / 定理 `diag_eq_empty`

English:
theorem diag_eq_empty
  statement: s.diag = ∅ ↔ s = ∅
  proof: by
  simp [diag]

中文:
定理 diag_eq_empty
  结论: s.diag = ∅ ↔ s = ∅
  证明: by
  simp [diag]
-/
theorem diag_eq_empty : s.diag = ∅ ↔ s = ∅ := by
  simp [diag]

/--
theorem `diag_eq_filter` / 定理 `diag_eq_filter`

English:
theorem diag_eq_filter
  given: [DecidableEq α]
  proof: by
  ext; simp +contextual

中文:
定理 diag_eq_filter
  条件: [DecidableEq α]
  证明: by
  ext; simp +contextual

Depends on / 依赖: contextual
-/
theorem diag_eq_filter [DecidableEq α] :
    s.diag = (s ×ˢ s).filter fun a : α × α => a.fst = a.snd := by
  ext; simp +contextual

variable (s)

@[simp]
/--
theorem `image_diag` / 定理 `image_diag`

English:
theorem image_diag
  given: [DecidableEq β] (f : α × α -> β) (s : Finset α)
  proof: by
  grind

@[simp, norm_cast]

中文:
定理 image_diag
  条件: [DecidableEq β] (f : α × α -> β) (s : Finset α)
  证明: by
  grind

@[simp, norm_cast]
-/
theorem image_diag [DecidableEq β] (f : α × α -> β) (s : Finset α) :
    s.diag.image f = s.image fun x => f (x, x) := by
  grind

@[simp, norm_cast]
/--
theorem `coe_offDiag` / 定理 `coe_offDiag`

English:
theorem coe_offDiag
  statement: (s.offDiag : Set (α × α)) = (s : Set α).offDiag
  proof: Set.ext fun _ => mem_offDiag

@[simp]

中文:
定理 coe_offDiag
  结论: (s.offDiag : Set (α × α)) = (s : Set α).offDiag
  证明: Set.ext fun _ => mem_offDiag

@[simp]

Depends on / 依赖: Set.ext, mem_offDiag
-/
theorem coe_offDiag : (s.offDiag : Set (α × α)) = (s : Set α).offDiag :=
  Set.ext fun _ => mem_offDiag

@[simp]
/--
theorem `diag_card` / 定理 `diag_card`

English:
theorem diag_card
  statement: (diag s).card = s.card
  proof: by
  simp [diag]

@[simp]

中文:
定理 diag_card
  结论: (diag s).card = s.card
  证明: by
  simp [diag]

@[simp]

Depends on / 依赖: Num.ofNat
-/
theorem diag_card : (diag s).card = s.card := by
  simp [diag]

@[simp]
/--
theorem `offDiag_card` / 定理 `offDiag_card`

English:
theorem offDiag_card
  statement: (offDiag s).card = s.card * s.card - s.card
  proof: by
  rw [← sq]
  rcases s with ⟨⟨s⟩, hs⟩
  apply List.length_offDiag

@[gcongr, mono]

中文:
定理 offDiag_card
  结论: (offDiag s).card = s.card * s.card - s.card
  证明: by
  rw [← sq]
  rcases s with ⟨⟨s⟩, hs⟩
  apply List.length_offDiag

@[gcongr, mono]

Depends on / 依赖: List.length_offDiag, Nat.binaryRec_eq, binaryRec_eq, length_offDiag
-/
theorem offDiag_card : (offDiag s).card = s.card * s.card - s.card := by
  rw [← sq]
  rcases s with ⟨⟨s⟩, hs⟩
  apply List.length_offDiag

@[gcongr, mono]
/--
theorem `diag_mono` / 定理 `diag_mono`

English:
theorem diag_mono
  statement: Monotone (diag : Finset α -> Finset (α × α))
  proof: fun _ _ => by simp [diag]

@[gcongr, mono]

中文:
定理 diag_mono
  结论: Monotone (diag : Finset α -> Finset (α × α))
  证明: fun _ _ => by simp [diag]

@[gcongr, mono]

Depends on / 依赖: Num.bit1, Num.ofNat
-/
theorem diag_mono : Monotone (diag : Finset α -> Finset (α × α)) := fun _ _ => by simp [diag]

@[gcongr, mono]
/--
theorem `offDiag_mono` / 定理 `offDiag_mono`

English:
theorem offDiag_mono
  statement: Monotone (offDiag : Finset α -> Finset (α × α))
  proof: fun _ _ h _ hx =>
mem_offDiag.2 And.imp (@h _) (And.imp_left <| @h _) mem_offDiag.1 hx

@[simp]

中文:
定理 offDiag_mono
  结论: Monotone (offDiag : Finset α -> Finset (α × α))
  证明: fun _ _ h _ hx =>
mem_offDiag.2 And.imp (@h _) (And.imp_left <| @h _) mem_offDiag.1 hx

@[simp]

Depends on / 依赖: Nat.binaryRec, Nat.bit, _bit, add_one, binaryRec, bit0_of_bit0, bit1_of_bit1, bit1_succ, mul_add, n.bit, zero_add
-/
theorem offDiag_mono : Monotone (offDiag : Finset α -> Finset (α × α)) := fun _ _ h _ hx =>
mem_offDiag.2 And.imp (@h _) (And.imp_left <| @h _) mem_offDiag.1 hx

@[simp]
/--
theorem `diag_empty` / 定理 `diag_empty`

English:
theorem diag_empty
  statement: (∅ : Finset α).diag = ∅
  proof: rfl

@[simp]

中文:
定理 diag_empty
  结论: (∅ : Finset α).diag = ∅
  证明: rfl

@[simp]
-/
theorem diag_empty : (∅ : Finset α).diag = ∅ :=
  rfl

@[simp]
/--
theorem `offDiag_empty` / 定理 `offDiag_empty`

English:
theorem offDiag_empty
  statement: (∅ : Finset α).offDiag = ∅
  proof: rfl

@[simp]

中文:
定理 offDiag_empty
  结论: (∅ : Finset α).offDiag = ∅
  证明: rfl

@[simp]
-/
theorem offDiag_empty : (∅ : Finset α).offDiag = ∅ :=
  rfl

@[simp]
/--
theorem `diag_union_offDiag` / 定理 `diag_union_offDiag`

English:
theorem diag_union_offDiag
  given: [DecidableEq α]
  statement: s.diag union s.offDiag = s ×ˢ s
  proof: by
  grind

@[simp]

中文:
定理 diag_union_offDiag
  条件: [DecidableEq α]
  结论: s.diag union s.offDiag = s ×ˢ s
  证明: by
  grind

@[simp]
-/
theorem diag_union_offDiag [DecidableEq α] : s.diag union s.offDiag = s ×ˢ s := by
  grind

@[simp]
/--
theorem `disjoint_diag_offDiag` / 定理 `disjoint_diag_offDiag`

English:
theorem disjoint_diag_offDiag
  statement: Disjoint s.diag s.offDiag
  proof: by simp [disjoint_left]

中文:
定理 disjoint_diag_offDiag
  结论: Disjoint s.diag s.offDiag
  证明: by simp [disjoint_left]

Depends on / 依赖: disjoint_left
-/
theorem disjoint_diag_offDiag : Disjoint s.diag s.offDiag := by simp [disjoint_left]

/--
theorem `product_sdiff_diag` / 定理 `product_sdiff_diag`

English:
theorem product_sdiff_diag
  given: [DecidableEq α]
  statement: s ×ˢ s \ s.diag = s.offDiag
  proof: by grind

中文:
定理 product_sdiff_diag
  条件: [DecidableEq α]
  结论: s ×ˢ s \ s.diag = s.offDiag
  证明: by grind
-/
theorem product_sdiff_diag [DecidableEq α] : s ×ˢ s \ s.diag = s.offDiag := by grind

/--
theorem `product_sdiff_offDiag` / 定理 `product_sdiff_offDiag`

English:
theorem product_sdiff_offDiag
  given: [DecidableEq α]
  statement: s ×ˢ s \ s.offDiag = s.diag
  proof: by grind

中文:
定理 product_sdiff_offDiag
  条件: [DecidableEq α]
  结论: s ×ˢ s \ s.offDiag = s.diag
  证明: by grind
-/
theorem product_sdiff_offDiag [DecidableEq α] : s ×ˢ s \ s.offDiag = s.diag := by grind

/--
theorem `diag_inter` / 定理 `diag_inter`

English:
theorem diag_inter
  given: [DecidableEq α]
  statement: (s inter t).diag = s.diag inter t.diag
  proof: by
  grind

中文:
定理 diag_inter
  条件: [DecidableEq α]
  结论: (s inter t).diag = s.diag inter t.diag
  证明: by
  grind
-/
theorem diag_inter [DecidableEq α] : (s inter t).diag = s.diag inter t.diag := by
  grind

/--
theorem `offDiag_inter` / 定理 `offDiag_inter`

English:
theorem offDiag_inter
  given: [DecidableEq α]
  statement: (s inter t).offDiag = s.offDiag inter t.offDiag
  proof: coe_injective by
    push_cast
    exact Set.offDiag_inter _ _

中文:
定理 offDiag_inter
  条件: [DecidableEq α]
  结论: (s inter t).offDiag = s.offDiag inter t.offDiag
  证明: coe_injective by
    push_cast
    exact Set.offDiag_inter _ _

Depends on / 依赖: Set.offDiag_inter, coe_injective, offDiag_inter
-/
theorem offDiag_inter [DecidableEq α] : (s inter t).offDiag = s.offDiag inter t.offDiag :=
coe_injective by
    push_cast
    exact Set.offDiag_inter _ _

/--
theorem `diag_union` / 定理 `diag_union`

English:
theorem diag_union
  given: [DecidableEq α]
  statement: (s union t).diag = s.diag union t.diag
  proof: by
  grind

中文:
定理 diag_union
  条件: [DecidableEq α]
  结论: (s union t).diag = s.diag union t.diag
  证明: by
  grind
-/
theorem diag_union [DecidableEq α] : (s union t).diag = s.diag union t.diag := by
  grind

variable {s t}

/--
theorem `offDiag_union` / 定理 `offDiag_union`

English:
theorem offDiag_union
  given: [DecidableEq α] (h : Disjoint s t)
  proof: coe_injective by
    push_cast
    exact Set.offDiag_union (disjoint_coe.2 h)

@[simp]

中文:
定理 offDiag_union
  条件: [DecidableEq α] (h : Disjoint s t)
  证明: coe_injective by
    push_cast
    exact Set.offDiag_union (disjoint_coe.2 h)

@[simp]

Depends on / 依赖: Set.offDiag_union, coe_injective, disjoint_coe, offDiag_union
-/
theorem offDiag_union [DecidableEq α] (h : Disjoint s t) :
    (s union t).offDiag = s.offDiag union t.offDiag union s ×ˢ t union t ×ˢ s :=
coe_injective by
    push_cast
    exact Set.offDiag_union (disjoint_coe.2 h)

@[simp]
/--
theorem `offDiag_singleton` / 定理 `offDiag_singleton`

English:
theorem offDiag_singleton
  given: (a : α)
  statement: ({a} : Finset α).offDiag = ∅
  proof: by simp [← Finset.card_eq_zero]

中文:
定理 offDiag_singleton
  条件: (a : α)
  结论: ({a} : Finset α).offDiag = ∅
  证明: by simp [← Finset.card_eq_zero]

Depends on / 依赖: Finset, Finset.card_eq_zero, card_eq_zero
-/
theorem offDiag_singleton (a : α) : ({a} : Finset α).offDiag = ∅ := by simp [← Finset.card_eq_zero]

/--
theorem `diag_singleton` / 定理 `diag_singleton`

English:
theorem diag_singleton
  given: (a : α)
  statement: ({a} : Finset α).diag = {(a, a)}
  proof: by grind

中文:
定理 diag_singleton
  条件: (a : α)
  结论: ({a} : Finset α).diag = {(a, a)}
  证明: by grind
-/
theorem diag_singleton (a : α) : ({a} : Finset α).diag = {(a, a)} := by grind

/--
theorem `diag_insert` / 定理 `diag_insert`

English:
theorem diag_insert
  given: [DecidableEq α] (a : α)
  proof: by grind

中文:
定理 diag_insert
  条件: [DecidableEq α] (a : α)
  证明: by grind
-/
theorem diag_insert [DecidableEq α] (a : α) :
    (insert a s).diag = insert (a, a) s.diag := by grind

/--
theorem `offDiag_insert` / 定理 `offDiag_insert`

English:
theorem offDiag_insert
  given: [DecidableEq α] {a : α} (has : a ∉ s)
  proof: by
  grind

中文:
定理 offDiag_insert
  条件: [DecidableEq α] {a : α} (has : a ∉ s)
  证明: by
  grind
-/
theorem offDiag_insert [DecidableEq α] {a : α} (has : a ∉ s) :
    (insert a s).offDiag = s.offDiag union {a} ×ˢ s union s ×ˢ {a} := by
  grind

/--
theorem `offDiag_filter_lt_eq_filter_le` / 定理 `offDiag_filter_lt_eq_filter_le`

English:
theorem offDiag_filter_lt_eq_filter_le
  statement: {ι} [PartialOrder ι] [DecidableLE ι] [DecidableLT ι]
  proof: by
  ext
  simpa using fun _ _ a => (Ne.le_iff_lt a).symm

中文:
定理 offDiag_filter_lt_eq_filter_le
  结论: {ι} [PartialOrder ι] [DecidableLE ι] [DecidableLT ι]
  证明: by
  ext
  simpa using fun _ _ a => (Ne.le_iff_lt a).symm

Depends on / 依赖: Ne.le_iff_lt, le_iff_lt
-/
theorem offDiag_filter_lt_eq_filter_le {ι} [PartialOrder ι] [DecidableLE ι] [DecidableLT ι]
    (s : Finset ι) :
    s.offDiag.filter (fun i => i.1 < i.2) = s.offDiag.filter (fun i => i.1 <= i.2) := by
  ext
  simpa using fun _ _ a => (Ne.le_iff_lt a).symm

/--
lemma `card_product_filter_lt` / 引理 `card_product_filter_lt`

English:
lemma card_product_filter_lt
  given: [LinearOrder α]
  proof: by
  set u : Finset (α × α) := {x in s ×ˢ s | x.1 < x.2}
  set v : Finset (α × α) := {x in s ×ˢ s | x.2 < x.1}
  have disj : Disjoint u v := by grind [disjoint_left]
  have union : u.disjUnion v disj = s.offDiag := by grind
  have swap : #u = #v := Finset.card_equiv (Equiv.prodComm α α) (by grind)
 

中文:
引理 card_product_filter_lt
  条件: [LinearOrder α]
  证明: by
  set u : Finset (α × α) := {x in s ×ˢ s | x.1 < x.2}
  set v : Finset (α × α) := {x in s ×ˢ s | x.2 < x.1}
  have disj : Disjoint u v := by grind [disjoint_left]
  have union : u.disjUnion v disj = s.offDiag := by grind
  have swap : #u = #v := Finset.card_equiv (Equiv.prodComm α α) (by grind)
 

Depends on / 依赖: Disjoint, Equiv.prodComm, Finset, Finset.card_equiv, Nat.choose_two_right, Nat.mul_sub_one, card_equiv, choose_two_right, disjUnion, disjoint_left, mul_sub_one, offDiag, offDiag_card, prodComm, s.offDiag, u.disjUnion
-/
lemma card_product_filter_lt [LinearOrder α] :
    #{x in s ×ˢ s | x.1 < x.2} = (#s).choose 2 := by
  set u : Finset (α × α) := {x in s ×ˢ s | x.1 < x.2}
  set v : Finset (α × α) := {x in s ×ˢ s | x.2 < x.1}
  have disj : Disjoint u v := by grind [disjoint_left]
  have union : u.disjUnion v disj = s.offDiag := by grind
  have swap : #u = #v := Finset.card_equiv (Equiv.prodComm α α) (by grind)
  grind [Nat.mul_sub_one, offDiag_card, Nat.choose_two_right]

end Diag

end Finset
