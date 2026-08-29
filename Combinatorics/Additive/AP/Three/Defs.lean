/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Sets without arithmetic progressions of length three and Roth numbers

This file defines sets without arithmetic progressions of length three, aka 3AP-free sets, and the
Roth number of a set.

The corresponding notion, sets without geometric progressions of length three, are called 3GP-free
sets.

The Roth number of a finset is the size of its biggest 3AP-free subset. This is a more general
definition than the one often found in mathematical literature, where the `n`-th Roth number is
the size of the biggest 3AP-free subset of `{0, ..., n - 1}`.

## Main declarations

* `ThreeGPFree`: Predicate for a set to be 3GP-free.
* `ThreeAPFree`: Predicate for a set to be 3AP-free.
* `mulRothNumber`: The multiplicative Roth number of a finset.
* `addRothNumber`: The additive Roth number of a finset.
* `rothNumberNat`: The Roth number of a natural, namely `addRothNumber (Finset.range n)`.

## TODO

* Can `threeAPFree_iff_eq_right` be made more general?
* Generalize `ThreeGPFree.image` to Freiman homs

## References

* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

3AP-free, Salem-Spencer, Roth, arithmetic progression, average, three-free
-/

@[expose] public section

assert_not_exists Field Ideal TwoSidedIdeal

open Finset Function
open scoped Pointwise

variable {F α β : Type*}

section ThreeAPFree

open Set

section Monoid

variable [Monoid α] [Monoid β] (s t : Set α)

/-- A set is **3GP-free** if it does not contain any non-trivial geometric progression of length
three. -/
@[to_additive /-- A set is **3AP-free** if it does not contain any non-trivial arithmetic
progression of length three.

This is also sometimes called a **non-averaging set** or **Salem-Spencer set**. -/]
/--
Definition of `ThreeGPFree` / `ThreeGPFree` 的定义

English:
definition ThreeGPFree
  signature: : Prop
  body: forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a * c = b * b -> a = b

中文:
定义 ThreeGPFree
  签名: : 命题
  定义体: forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a * c = b * b -> a = b
-/
def ThreeGPFree : Prop := forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a * c = b * b -> a = b

/-- Whether a given finset is 3GP-free is decidable. -/
@[to_additive /-- Whether a given finset is 3AP-free is decidable. -/]
/--
Instance `ThreeGPFree.instDecidable` / 实例 `ThreeGPFree.instDecidable`

English:
instance ThreeGPFree.instDecidable
  signature: [DecidableEq α] {s : Finset α}
  body: decidable_of_iff (forall a in s, forall b in s, forall c in s, a * c = b * b -> a = b) Iff.rfl

中文:
实例 ThreeGPFree.instDecidable
  签名: [DecidableEq α] {s : Finset α}
  定义体: decidable_of_iff (forall a in s, forall b in s, forall c in s, a * c = b * b -> a = b) Iff.rfl

Depends on / 依赖: Iff.rfl, decidable_of_iff
-/
instance ThreeGPFree.instDecidable [DecidableEq α] {s : Finset α} :
    Decidable (ThreeGPFree (s : Set α)) :=
  decidable_of_iff (forall a in s, forall b in s, forall c in s, a * c = b * b -> a = b) Iff.rfl

variable {s t}

@[to_additive]
/--
theorem `ThreeGPFree.mono` / 定理 `ThreeGPFree.mono`

English:
theorem ThreeGPFree.mono
  given: (h : t subseteq s) (hs : ThreeGPFree s)
  statement: ThreeGPFree t
  proof: fun _ ha _ hb _ hc => hs (h ha) (h hb) (h hc)

@[to_additive (attr := simp)]

中文:
定理 ThreeGPFree.mono
  条件: (h : t subseteq s) (hs : ThreeGPFree s)
  结论: ThreeGPFree t
  证明: fun _ ha _ hb _ hc => hs (h ha) (h hb) (h hc)

@[to_additive (attr := simp)]
-/
theorem ThreeGPFree.mono (h : t subseteq s) (hs : ThreeGPFree s) : ThreeGPFree t :=
  fun _ ha _ hb _ hc => hs (h ha) (h hb) (h hc)

@[to_additive (attr := simp)]
/--
theorem `threeGPFree_empty` / 定理 `threeGPFree_empty`

English:
theorem threeGPFree_empty
  statement: ThreeGPFree (∅ : Set α)
  proof: fun _ _ _ ha => ha.elim

@[to_additive]

中文:
定理 threeGPFree_empty
  结论: ThreeGPFree (∅ : Set α)
  证明: fun _ _ _ ha => ha.elim

@[to_additive]

Depends on / 依赖: ha.elim
-/
theorem threeGPFree_empty : ThreeGPFree (∅ : Set α) := fun _ _ _ ha => ha.elim

@[to_additive]
/--
theorem `Set.Subsingleton.threeGPFree` / 定理 `Set.Subsingleton.threeGPFree`

English:
theorem Set.Subsingleton.threeGPFree
  given: (hs : s.Subsingleton)
  statement: ThreeGPFree s
  proof: fun _ ha _ hb _ _ _ => hs ha hb

@[to_additive (attr := simp)]

中文:
定理 Set.Subsingleton.threeGPFree
  条件: (hs : s.Subsingleton)
  结论: ThreeGPFree s
  证明: fun _ ha _ hb _ _ _ => hs ha hb

@[to_additive (attr := simp)]
-/
theorem Set.Subsingleton.threeGPFree (hs : s.Subsingleton) : ThreeGPFree s :=
  fun _ ha _ hb _ _ _ => hs ha hb

@[to_additive (attr := simp)]
/--
theorem `threeGPFree_singleton` / 定理 `threeGPFree_singleton`

English:
theorem threeGPFree_singleton
  given: (a : α)
  statement: ThreeGPFree ({a} : Set α)
  proof: subsingleton_singleton.threeGPFree

@[to_additive ThreeAPFree.prod]

中文:
定理 threeGPFree_singleton
  条件: (a : α)
  结论: ThreeGPFree ({a} : Set α)
  证明: subsingleton_singleton.threeGPFree

@[to_additive ThreeAPFree.prod]

Depends on / 依赖: subsingleton_singleton, subsingleton_singleton.threeGPFree, threeGPFree
-/
theorem threeGPFree_singleton (a : α) : ThreeGPFree ({a} : Set α) :=
  subsingleton_singleton.threeGPFree

@[to_additive ThreeAPFree.prod]
/--
theorem `ThreeGPFree.prod` / 定理 `ThreeGPFree.prod`

English:
theorem ThreeGPFree.prod
  given: {t : Set β} (hs : ThreeGPFree s) (ht : ThreeGPFree t)
  proof: fun _ ha _ hb _ hc h =>
  Prod.ext (hs ha.1 hb.1 hc.1 (Prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (Prod.ext_iff.1 h).2)

@[to_additive]

中文:
定理 ThreeGPFree.prod
  条件: {t : Set β} (hs : ThreeGPFree s) (ht : ThreeGPFree t)
  证明: fun _ ha _ hb _ hc h =>
  Prod.ext (hs ha.1 hb.1 hc.1 (Prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (Prod.ext_iff.1 h).2)

@[to_additive]
-/
theorem ThreeGPFree.prod {t : Set β} (hs : ThreeGPFree s) (ht : ThreeGPFree t) :
    ThreeGPFree (s ×ˢ t) := fun _ ha _ hb _ hc h =>
  Prod.ext (hs ha.1 hb.1 hc.1 (Prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (Prod.ext_iff.1 h).2)

@[to_additive]
/--
theorem `threeGPFree_pi` / 定理 `threeGPFree_pi`

English:
theorem threeGPFree_pi
  statement: {ι : Type*} {α : ι -> Type*} [forall i, Monoid (α i)] {s : forall i, Set (α i)}
  proof: fun _ ha _ hb _ hc h =>
funext fun i => hs i (ha i trivial) (hb i trivial) (hc i trivial) congr_fun h i

中文:
定理 threeGPFree_pi
  结论: {ι : 类型} {α : ι -> 类型} [对任意 i, Monoid (α i)] {s : 对任意 i, Set (α i)}
  证明: fun _ ha _ hb _ hc h =>
funext fun i => hs i (ha i trivial) (hb i trivial) (hc i trivial) congr_fun h i

Depends on / 依赖: congr_fun
-/
theorem threeGPFree_pi {ι : Type*} {α : ι -> Type*} [forall i, Monoid (α i)] {s : forall i, Set (α i)}
    (hs : forall i, ThreeGPFree (s i)) : ThreeGPFree ((univ : Set ι).pi s) :=
  fun _ ha _ hb _ hc h =>
funext fun i => hs i (ha i trivial) (hb i trivial) (hc i trivial) congr_fun h i

end Monoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] {s A : Set α} {t : Set β} {f : α -> β}

/-- Geometric progressions of length three are reflected under `2`-Freiman homomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are reflected under `2`-Freiman homomorphisms. -/]
/--
lemma `ThreeGPFree.of_image` / 引理 `ThreeGPFree.of_image`

English:
lemma ThreeGPFree.of_image
  statement: (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f) (hAs : A subseteq s)
  proof: fun _ ha _ hb _ hc habc => hf' (hAs ha) (hAs hb) hA (mem_image_of_mem _ ha)
(mem_image_of_mem _ hb) (mem_image_of_mem _ hc)
    hf.mul_eq_mul (hAs ha) (hAs hc) (hAs hb) (hAs hb) habc

中文:
引理 ThreeGPFree.of_image
  结论: (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f) (hAs : A subseteq s)
  证明: fun _ ha _ hb _ hc habc => hf' (hAs ha) (hAs hb) hA (mem_image_of_mem _ ha)
(mem_image_of_mem _ hb) (mem_image_of_mem _ hc)
    hf.mul_eq_mul (hAs ha) (hAs hc) (hAs hb) (hAs hb) habc

Depends on / 依赖: hf.mul_eq_mul, mem_image_of_mem, mul_eq_mul
-/
lemma ThreeGPFree.of_image (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f) (hAs : A subseteq s)
    (hA : ThreeGPFree (f '' A)) : ThreeGPFree A :=
fun _ ha _ hb _ hc habc => hf' (hAs ha) (hAs hb) hA (mem_image_of_mem _ ha)
(mem_image_of_mem _ hb) (mem_image_of_mem _ hc)
    hf.mul_eq_mul (hAs ha) (hAs hc) (hAs hb) (hAs hb) habc

/-- Geometric progressions of length three are unchanged under `2`-Freiman isomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are unchanged under `2`-Freiman isomorphisms. -/]
/--
lemma `threeGPFree_image` / 引理 `threeGPFree_image`

English:
lemma threeGPFree_image
  given: (hf : IsMulFreimanIso 2 s t f) (hAs : A subseteq s)
  proof: by
  rw [ThreeGPFree]; rw [ThreeGPFree]
  have := (hf.bijOn.injOn.mono hAs).bijOn_image (f := f)
  simp +contextual only
    [((hf.bijOn.injOn.mono hAs).bijOn_image (f := f)).forall,
    hf.mul_eq_mul (hAs _) (hAs _) (hAs _) (hAs _), this.injOn.eq_iff]

@[to_additive] alias ⟨_, ThreeGPFree.image⟩ :=

中文:
引理 threeGPFree_image
  条件: (hf : IsMulFreimanIso 2 s t f) (hAs : A subseteq s)
  证明: by
  rw [ThreeGPFree]; rw [ThreeGPFree]
  have := (hf.bijOn.injOn.mono hAs).bijOn_image (f := f)
  simp +contextual only
    [((hf.bijOn.injOn.mono hAs).bijOn_image (f := f)).forall,
    hf.mul_eq_mul (hAs _) (hAs _) (hAs _) (hAs _), this.injOn.eq_iff]

@[to_additive] alias ⟨_, ThreeGPFree.image⟩ :=

Depends on / 依赖: ThreeGPFree, bijOn_image, contextual, eq_iff, hf.bijOn.injOn.mono, hf.mul_eq_mul, mul_eq_mul, this.injOn.eq_iff
-/
lemma threeGPFree_image (hf : IsMulFreimanIso 2 s t f) (hAs : A subseteq s) :
    ThreeGPFree (f '' A) ↔ ThreeGPFree A := by
  rw [ThreeGPFree]; rw [ThreeGPFree]
  have := (hf.bijOn.injOn.mono hAs).bijOn_image (f := f)
  simp +contextual only
    [((hf.bijOn.injOn.mono hAs).bijOn_image (f := f)).forall,
    hf.mul_eq_mul (hAs _) (hAs _) (hAs _) (hAs _), this.injOn.eq_iff]

@[to_additive] alias ⟨_, ThreeGPFree.image⟩ := threeGPFree_image

/-- Geometric progressions of length three are reflected under `2`-Freiman homomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are reflected under `2`-Freiman homomorphisms. -/]
/--
lemma `IsMulFreimanHom.threeGPFree` / 引理 `IsMulFreimanHom.threeGPFree`

English:
lemma IsMulFreimanHom.threeGPFree
  statement: (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f)
  proof: (ht.mono hf.mapsTo.image_subset).of_image hf hf' subset_rfl

中文:
引理 IsMulFreimanHom.threeGPFree
  结论: (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f)
  证明: (ht.mono hf.mapsTo.image_subset).of_image hf hf' subset_rfl

Depends on / 依赖: hf.mapsTo.image_subset, ht.mono, image_subset, mapsTo, of_image, subset_rfl
-/
lemma IsMulFreimanHom.threeGPFree (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f)
    (ht : ThreeGPFree t) : ThreeGPFree s :=
  (ht.mono hf.mapsTo.image_subset).of_image hf hf' subset_rfl

/-- Geometric progressions of length three are unchanged under `2`-Freiman isomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are unchanged under `2`-Freiman isomorphisms. -/]
/--
lemma `IsMulFreimanIso.threeGPFree_congr` / 引理 `IsMulFreimanIso.threeGPFree_congr`

English:
lemma IsMulFreimanIso.threeGPFree_congr
  given: (hf : IsMulFreimanIso 2 s t f)
  proof: by
  rw [← threeGPFree_image hf subset_rfl]; rw [hf.bijOn.image_eq]

中文:
引理 IsMulFreimanIso.threeGPFree_congr
  条件: (hf : IsMulFreimanIso 2 s t f)
  证明: by
  rw [← threeGPFree_image hf subset_rfl]; rw [hf.bijOn.image_eq]

Depends on / 依赖: hf.bijOn.image_eq, image_eq, subset_rfl, threeGPFree_image
-/
lemma IsMulFreimanIso.threeGPFree_congr (hf : IsMulFreimanIso 2 s t f) :
    ThreeGPFree s ↔ ThreeGPFree t := by
  rw [← threeGPFree_image hf subset_rfl]; rw [hf.bijOn.image_eq]

/-- Geometric progressions of length three are preserved under semigroup homomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are preserved under semigroup homomorphisms. -/]
/--
theorem `ThreeGPFree.image'` / 定理 `ThreeGPFree.image'`

English:
theorem ThreeGPFree.image'
  statement: [FunLike F α β] [MulHomClass F α β] (f : F) (hf : (s * s).InjOn f)
  proof: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ habc
  rw [h ha hb hc (hf (mul_mem_mul ha hc) (mul_mem_mul hb hb) <| by rwa [map_mul]; rw [map_mul])]

中文:
定理 ThreeGPFree.image'
  结论: [FunLike F α β] [MulHomClass F α β] (f : F) (hf : (s * s).InjOn f)
  证明: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ habc
  rw [h ha hb hc (hf (mul_mem_mul ha hc) (mul_mem_mul hb hb) <| by rwa [map_mul]; rw [map_mul])]

Depends on / 依赖: map_mul, mul_mem_mul
-/
theorem ThreeGPFree.image' [FunLike F α β] [MulHomClass F α β] (f : F) (hf : (s * s).InjOn f)
    (h : ThreeGPFree s) : ThreeGPFree (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ habc
  rw [h ha hb hc (hf (mul_mem_mul ha hc) (mul_mem_mul hb hb) <| by rwa [map_mul]; rw [map_mul])]

end CommMonoid

section CancelCommMonoid

variable [CommMonoid α] [IsCancelMul α] {s : Set α} {a : α}

/--
lemma `ThreeGPFree.eq_right` / 引理 `ThreeGPFree.eq_right`

English:
lemma ThreeGPFree.eq_right
  given: (hs : ThreeGPFree s)
  proof: by
  rintro a ha b hb c hc habc
  obtain rfl := hs ha hb hc habc
  simpa using habc.symm

中文:
引理 ThreeGPFree.eq_right
  条件: (hs : ThreeGPFree s)
  证明: by
  rintro a ha b hb c hc habc
  obtain rfl := hs ha hb hc habc
  simpa using habc.symm
-/
@[to_additive] lemma ThreeGPFree.eq_right (hs : ThreeGPFree s) :
    forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a * c = b * b -> b = c := by
  rintro a ha b hb c hc habc
  obtain rfl := hs ha hb hc habc
  simpa using habc.symm

/--
lemma `threeGPFree_insert` / 引理 `threeGPFree_insert`

English:
lemma threeGPFree_insert
  proof: by
  refine ⟨fun hs => ⟨hs.mono (subset_insert _ _),
    fun b hb c hc => hs (Or.inl rfl) (Or.inr hb) (Or.inr hc),
    fun b hb c hc => hs (Or.inr hb) (Or.inl rfl) (Or.inr hc)⟩, ?_⟩
  rintro ⟨hs, ha, ha'⟩ b hb c hc d hd h
  rw [mem_insert_iff] at hb hc hd
  obtain rfl | hb := hb <;> obtain rfl | hc 

中文:
引理 threeGPFree_insert
  证明: by
  refine ⟨fun hs => ⟨hs.mono (subset_insert _ _),
    fun b hb c hc => hs (Or.inl rfl) (Or.inr hb) (Or.inr hc),
    fun b hb c hc => hs (Or.inr hb) (Or.inl rfl) (Or.inr hc)⟩, ?_⟩
  rintro ⟨hs, ha, ha'⟩ b hb c hc d hd h
  rw [mem_insert_iff] at hb hc hd
  obtain rfl | hb := hb <;> obtain rfl | hc 
-/
@[to_additive] lemma threeGPFree_insert :
    ThreeGPFree (insert a s) ↔ ThreeGPFree s ∧
      (forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a * c = b * b -> a = b) ∧
        forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> b * c = a * a -> b = a := by
  refine ⟨fun hs => ⟨hs.mono (subset_insert _ _),
    fun b hb c hc => hs (Or.inl rfl) (Or.inr hb) (Or.inr hc),
    fun b hb c hc => hs (Or.inr hb) (Or.inl rfl) (Or.inr hc)⟩, ?_⟩
  rintro ⟨hs, ha, ha'⟩ b hb c hc d hd h
  rw [mem_insert_iff] at hb hc hd
  obtain rfl | hb := hb <;> obtain rfl | hc := hc
  · rfl
  all_goals obtain rfl | hd := hd
  · exact (ha' hc hc h.symm).symm
  · exact ha hc hd h
  · exact mul_right_cancel h
  · exact ha' hb hd h
  · obtain rfl := ha hc hb ((mul_comm _ _).trans h)
    exact ha' hb hc h
  · exact hs hb hc hd h

@[to_additive]
/--
theorem `ThreeGPFree.smul_set` / 定理 `ThreeGPFree.smul_set`

English:
theorem ThreeGPFree.smul_set
  given: (hs : ThreeGPFree s)
  statement: ThreeGPFree (a • s)
  proof: by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
exact congr_arg (a • ·) hs hb hc hd by simpa [mul_mul_mul_comm _ _ a] using h

中文:
定理 ThreeGPFree.smul_set
  条件: (hs : ThreeGPFree s)
  结论: ThreeGPFree (a • s)
  证明: by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
exact congr_arg (a • ·) hs hb hc hd by simpa [mul_mul_mul_comm _ _ a] using h

Depends on / 依赖: congr_arg, mul_mul_mul_comm
-/
theorem ThreeGPFree.smul_set (hs : ThreeGPFree s) : ThreeGPFree (a • s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
exact congr_arg (a • ·) hs hb hc hd by simpa [mul_mul_mul_comm _ _ a] using h

/--
lemma `threeGPFree_smul_set` / 引理 `threeGPFree_smul_set`

English:
lemma threeGPFree_smul_set
  statement: ThreeGPFree (a • s) ↔ ThreeGPFree s where
  proof: mul_left_cancel
      (hs (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) (mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_mul_mul_comm]; rw [h])
  mpr := ThreeGPFree.smul_set

中文:
引理 threeGPFree_smul_set
  结论: ThreeGPFree (a • s) ↔ ThreeGPFree s where
  证明: mul_left_cancel
      (hs (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) (mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_mul_mul_comm]; rw [h])
  mpr := ThreeGPFree.smul_set
-/
@[to_additive] lemma threeGPFree_smul_set : ThreeGPFree (a • s) ↔ ThreeGPFree s where
  mp hs b hb c hc d hd h := mul_left_cancel
      (hs (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) (mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_mul_mul_comm]; rw [h])
  mpr := ThreeGPFree.smul_set

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Set α} {a : α}

@[to_additive]
/--
theorem `threeGPFree_insert_of_lt` / 定理 `threeGPFree_insert_of_lt`

English:
theorem threeGPFree_insert_of_lt
  given: (hs : forall i in s, i < a)
  proof: by
  refine threeGPFree_insert.trans ?_
  rw [← and_assoc]
  exact and_iff_left fun b hb c hc h => ((mul_lt_mul_of_lt_of_lt (hs _ hb) (hs _ hc)).ne h).elim

中文:
定理 threeGPFree_insert_of_lt
  条件: (hs : 对任意 i in s, i < a)
  证明: by
  refine threeGPFree_insert.trans ?_
  rw [← and_assoc]
  exact and_iff_left fun b hb c hc h => ((mul_lt_mul_of_lt_of_lt (hs _ hb) (hs _ hc)).ne h).elim

Depends on / 依赖: and_assoc, and_iff_left, mul_lt_mul_of_lt_of_lt, threeGPFree_insert, threeGPFree_insert.trans
-/
theorem threeGPFree_insert_of_lt (hs : forall i in s, i < a) :
    ThreeGPFree (insert a s) ↔
      ThreeGPFree s ∧ forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a * c = b * b -> a = b := by
  refine threeGPFree_insert.trans ?_
  rw [← and_assoc]
  exact and_iff_left fun b hb c hc h => ((mul_lt_mul_of_lt_of_lt (hs _ hb) (hs _ hc)).ne h).elim

end OrderedCancelCommMonoid

section CancelCommMonoidWithZero

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NoZeroDivisors α] {s : Set α} {a : α}

/--
lemma `ThreeGPFree.smul_set₀` / 引理 `ThreeGPFree.smul_set₀`

English:
lemma ThreeGPFree.smul_set₀
  given: (hs : ThreeGPFree s) (ha : a != 0)
  statement: ThreeGPFree (a • s)
  proof: by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
exact congr_arg (a • ·) hs hb hc hd by simpa [mul_mul_mul_comm _ _ a, ha] using h

中文:
引理 ThreeGPFree.smul_set₀
  条件: (hs : ThreeGPFree s) (ha : a != 0)
  结论: ThreeGPFree (a • s)
  证明: by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
exact congr_arg (a • ·) hs hb hc hd by simpa [mul_mul_mul_comm _ _ a, ha] using h

Depends on / 依赖: congr_arg, mul_mul_mul_comm
-/
lemma ThreeGPFree.smul_set₀ (hs : ThreeGPFree s) (ha : a != 0) : ThreeGPFree (a • s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
exact congr_arg (a • ·) hs hb hc hd by simpa [mul_mul_mul_comm _ _ a, ha] using h

/--
theorem `threeGPFree_smul_set₀` / 定理 `threeGPFree_smul_set₀`

English:
theorem threeGPFree_smul_set₀
  given: (ha : a != 0)
  statement: ThreeGPFree (a • s) ↔ ThreeGPFree s
  proof: ⟨fun hs b hb c hc d hd h =>
    mul_left_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_mul_mul_comm]; rw [h]; rw [mul_mul_mul_comm]),
    fun hs => hs.smul_set₀ ha⟩

中文:
定理 threeGPFree_smul_set₀
  条件: (ha : a != 0)
  结论: ThreeGPFree (a • s) ↔ ThreeGPFree s
  证明: ⟨fun hs b hb c hc d hd h =>
    mul_left_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_mul_mul_comm]; rw [h]; rw [mul_mul_mul_comm]),
    fun hs => hs.smul_set₀ ha⟩

Depends on / 依赖: Set.mem_image_of_mem, hs.smul_set, mem_image_of_mem, mul_mul_mul_comm, smul_eq_mul
-/
theorem threeGPFree_smul_set₀ (ha : a != 0) : ThreeGPFree (a • s) ↔ ThreeGPFree s :=
  ⟨fun hs b hb c hc d hd h =>
    mul_left_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_mul_mul_comm]; rw [h]; rw [mul_mul_mul_comm]),
    fun hs => hs.smul_set₀ ha⟩

end CancelCommMonoidWithZero

section Nat

/--
theorem `threeAPFree_iff_eq_right` / 定理 `threeAPFree_iff_eq_right`

English:
theorem threeAPFree_iff_eq_right
  given: {s : Set Nat}
  proof: by
  refine forall₄_congr fun a _ha b hb => forall₃_congr fun c hc habc => ⟨?_, ?_⟩
  · rintro rfl
    exact (add_left_cancel habc).symm
  · rintro rfl
    simp_rw [← two_mul] at habc
    exact mul_left_cancel₀ two_ne_zero habc

中文:
定理 threeAPFree_iff_eq_right
  条件: {s : Set 自然数}
  证明: by
  refine forall₄_congr fun a _ha b hb => forall₃_congr fun c hc habc => ⟨?_, ?_⟩
  · rintro rfl
    exact (add_left_cancel habc).symm
  · rintro rfl
    simp_rw [← two_mul] at habc
    exact mul_left_cancel₀ two_ne_zero habc

Depends on / 依赖: add_left_cancel, simp_rw, two_mul, two_ne_zero
-/
theorem threeAPFree_iff_eq_right {s : Set Nat} :
    ThreeAPFree s ↔ forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a + c = b + b -> a = c := by
  refine forall₄_congr fun a _ha b hb => forall₃_congr fun c hc habc => ⟨?_, ?_⟩
  · rintro rfl
    exact (add_left_cancel habc).symm
  · rintro rfl
    simp_rw [← two_mul] at habc
    exact mul_left_cancel₀ two_ne_zero habc

end Nat
end ThreeAPFree

open Finset

section RothNumber

variable [DecidableEq α]

section Monoid

variable [Monoid α] [DecidableEq β] [Monoid β] (s t : Finset α)

/-- The multiplicative Roth number of a finset is the cardinality of its biggest 3GP-free subset. -/
@[to_additive /-- The additive Roth number of a finset is the cardinality of its biggest 3AP-free
subset.

The usual Roth number corresponds to `addRothNumber (Finset.range n)`, see `rothNumberNat`. -/]
/--
Definition of `mulRothNumber` / `mulRothNumber` 的定义

English:
definition mulRothNumber
  signature: : Finset α ->o Nat
  body: ⟨fun s => Nat.findGreatest (fun m => exists t subseteq s, #t = m ∧ ThreeGPFree (t : Set α)) #s, by
    rintro t u htu
    refine Nat.findGreatest_mono (fun m => ?_) (card_le_card htu)
    rintro ⟨v, hvt, hv⟩
    exact ⟨v, hvt.trans htu, hv⟩⟩

@[to_additive]

中文:
定义 mulRothNumber
  签名: : Finset α ->o 自然数
  定义体: ⟨fun s => Nat.findGreatest (fun m => exists t subseteq s, #t = m ∧ ThreeGPFree (t : Set α)) #s, by
    rintro t u htu
    refine Nat.findGreatest_mono (fun m => ?_) (card_le_card htu)
    rintro ⟨v, hvt, hv⟩
    exact ⟨v, hvt.trans htu, hv⟩⟩

@[to_additive]

Depends on / 依赖: Nat.findGreatest, Nat.findGreatest_mono, ThreeGPFree, card_le_card, findGreatest, findGreatest_mono, hvt.trans, subseteq
-/
def mulRothNumber : Finset α ->o Nat :=
  ⟨fun s => Nat.findGreatest (fun m => exists t subseteq s, #t = m ∧ ThreeGPFree (t : Set α)) #s, by
    rintro t u htu
    refine Nat.findGreatest_mono (fun m => ?_) (card_le_card htu)
    rintro ⟨v, hvt, hv⟩
    exact ⟨v, hvt.trans htu, hv⟩⟩

@[to_additive]
/--
theorem `mulRothNumber_le` / 定理 `mulRothNumber_le`

English:
theorem mulRothNumber_le
  statement: mulRothNumber s <= #s
  proof: Nat.findGreatest_le #s

@[to_additive]

中文:
定理 mulRothNumber_le
  结论: mulRothNumber s <= #s
  证明: Nat.findGreatest_le #s

@[to_additive]

Depends on / 依赖: Nat.findGreatest_le, findGreatest_le
-/
theorem mulRothNumber_le : mulRothNumber s <= #s := Nat.findGreatest_le #s

@[to_additive]
/--
theorem `mulRothNumber_spec` / 定理 `mulRothNumber_spec`

English:
theorem mulRothNumber_spec
  proof: Nat.findGreatest_spec (P := fun m => exists t subseteq s, #t = m ∧ ThreeGPFree (t : Set α))
    (Nat.zero_le _) ⟨∅, empty_subset _, card_empty, by norm_cast; exact threeGPFree_empty⟩

中文:
定理 mulRothNumber_spec
  证明: Nat.findGreatest_spec (P := fun m => exists t subseteq s, #t = m ∧ ThreeGPFree (t : Set α))
    (Nat.zero_le _) ⟨∅, empty_subset _, card_empty, by norm_cast; exact threeGPFree_empty⟩

Depends on / 依赖: Nat.findGreatest_spec, Nat.zero_le, ThreeGPFree, card_empty, empty_subset, findGreatest_spec, subseteq, threeGPFree_empty, zero_le
-/
theorem mulRothNumber_spec :
    exists t subseteq s, #t = mulRothNumber s ∧ ThreeGPFree (t : Set α) :=
  Nat.findGreatest_spec (P := fun m => exists t subseteq s, #t = m ∧ ThreeGPFree (t : Set α))
    (Nat.zero_le _) ⟨∅, empty_subset _, card_empty, by norm_cast; exact threeGPFree_empty⟩

variable {s t} {n : Nat}

@[to_additive]
/--
theorem `ThreeGPFree.le_mulRothNumber` / 定理 `ThreeGPFree.le_mulRothNumber`

English:
theorem ThreeGPFree.le_mulRothNumber
  given: (hs : ThreeGPFree (s : Set α)) (h : s subseteq t)
  proof: Nat.le_findGreatest (card_le_card h) ⟨s, h, rfl, hs⟩

@[to_additive]

中文:
定理 ThreeGPFree.le_mulRothNumber
  条件: (hs : ThreeGPFree (s : Set α)) (h : s subseteq t)
  证明: Nat.le_findGreatest (card_le_card h) ⟨s, h, rfl, hs⟩

@[to_additive]

Depends on / 依赖: Nat.le_findGreatest, card_le_card, le_findGreatest
-/
theorem ThreeGPFree.le_mulRothNumber (hs : ThreeGPFree (s : Set α)) (h : s subseteq t) :
    #s <= mulRothNumber t :=
  Nat.le_findGreatest (card_le_card h) ⟨s, h, rfl, hs⟩

@[to_additive]
/--
theorem `ThreeGPFree.mulRothNumber_eq` / 定理 `ThreeGPFree.mulRothNumber_eq`

English:
theorem ThreeGPFree.mulRothNumber_eq
  given: (hs : ThreeGPFree (s : Set α))
  proof: (mulRothNumber_le _).antisymm hs.le_mulRothNumber Subset.refl _

@[to_additive (attr := simp)]

中文:
定理 ThreeGPFree.mulRothNumber_eq
  条件: (hs : ThreeGPFree (s : Set α))
  证明: (mulRothNumber_le _).antisymm hs.le_mulRothNumber Subset.refl _

@[to_additive (attr := simp)]

Depends on / 依赖: Subset, Subset.refl, antisymm, hs.le_mulRothNumber, le_mulRothNumber, mulRothNumber_le
-/
theorem ThreeGPFree.mulRothNumber_eq (hs : ThreeGPFree (s : Set α)) :
    mulRothNumber s = #s :=
(mulRothNumber_le _).antisymm hs.le_mulRothNumber Subset.refl _

@[to_additive (attr := simp)]
/--
theorem `mulRothNumber_empty` / 定理 `mulRothNumber_empty`

English:
theorem mulRothNumber_empty
  statement: mulRothNumber (∅ : Finset α) = 0
  proof: Nat.eq_zero_of_le_zero (mulRothNumber_le _).trans card_empty.le

@[to_additive (attr := simp)]

中文:
定理 mulRothNumber_empty
  结论: mulRothNumber (∅ : Finset α) = 0
  证明: Nat.eq_zero_of_le_zero (mulRothNumber_le _).trans card_empty.le

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.eq_zero_of_le_zero, card_empty, card_empty.le, eq_zero_of_le_zero, mulRothNumber_le
-/
theorem mulRothNumber_empty : mulRothNumber (∅ : Finset α) = 0 :=
Nat.eq_zero_of_le_zero (mulRothNumber_le _).trans card_empty.le

@[to_additive (attr := simp)]
/--
theorem `mulRothNumber_singleton` / 定理 `mulRothNumber_singleton`

English:
theorem mulRothNumber_singleton
  given: (a : α)
  statement: mulRothNumber ({a} : Finset α) = 1
  proof: by
  refine ThreeGPFree.mulRothNumber_eq ?_
  rw [coe_singleton]
  exact threeGPFree_singleton a

@[to_additive]

中文:
定理 mulRothNumber_singleton
  条件: (a : α)
  结论: mulRothNumber ({a} : Finset α) = 1
  证明: by
  refine ThreeGPFree.mulRothNumber_eq ?_
  rw [coe_singleton]
  exact threeGPFree_singleton a

@[to_additive]

Depends on / 依赖: ThreeGPFree, ThreeGPFree.mulRothNumber_eq, coe_singleton, mulRothNumber_eq, threeGPFree_singleton
-/
theorem mulRothNumber_singleton (a : α) : mulRothNumber ({a} : Finset α) = 1 := by
  refine ThreeGPFree.mulRothNumber_eq ?_
  rw [coe_singleton]
  exact threeGPFree_singleton a

@[to_additive]
/--
theorem `mulRothNumber_union_le` / 定理 `mulRothNumber_union_le`

English:
theorem mulRothNumber_union_le
  given: (s t : Finset α)
  proof: let ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s union t)
  calc
    mulRothNumber (s union t) = #u := hcard.symm
    _ = #(u inter s union u inter t) := by rw [← inter_union_distrib_left, inter_eq_left.2 hus]
    _ <= #(u inter s) + #(u inter t) := card_union_le _ _
    _ <= mulRothNumber s + mulRo

中文:
定理 mulRothNumber_union_le
  条件: (s t : Finset α)
  证明: let ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s union t)
  calc
    mulRothNumber (s union t) = #u := hcard.symm
    _ = #(u inter s union u inter t) := by rw [← inter_union_distrib_left, inter_eq_left.2 hus]
    _ <= #(u inter s) + #(u inter t) := card_union_le _ _
    _ <= mulRothNumber s + mulRo

Depends on / 依赖: _root_, _root_.add_le_add, add_le_add, card_union_le, hcard.symm, hu.mono, inter_eq_left, inter_subset_left, inter_subset_right, inter_union_distrib_left, le_mulRothNumber, mulRothNumber, mulRothNumber_spec
-/
theorem mulRothNumber_union_le (s t : Finset α) :
    mulRothNumber (s union t) <= mulRothNumber s + mulRothNumber t :=
  let ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s union t)
  calc
    mulRothNumber (s union t) = #u := hcard.symm
    _ = #(u inter s union u inter t) := by rw [← inter_union_distrib_left, inter_eq_left.2 hus]
    _ <= #(u inter s) + #(u inter t) := card_union_le _ _
    _ <= mulRothNumber s + mulRothNumber t := _root_.add_le_add
      ((hu.mono inter_subset_left).le_mulRothNumber inter_subset_right)
      ((hu.mono inter_subset_left).le_mulRothNumber inter_subset_right)

@[to_additive]
/--
theorem `le_mulRothNumber_product` / 定理 `le_mulRothNumber_product`

English:
theorem le_mulRothNumber_product
  given: (s : Finset α) (t : Finset β)
  proof: by
  obtain ⟨u, hus, hucard, hu⟩ := mulRothNumber_spec s
  obtain ⟨v, hvt, hvcard, hv⟩ := mulRothNumber_spec t
  rw [← hucard]; rw [← hvcard]; rw [← card_product]
  refine ThreeGPFree.le_mulRothNumber ?_ (product_subset_product hus hvt)
  rw [coe_product]
  exact hu.prod hv

@[to_additive]

中文:
定理 le_mulRothNumber_product
  条件: (s : Finset α) (t : Finset β)
  证明: by
  obtain ⟨u, hus, hucard, hu⟩ := mulRothNumber_spec s
  obtain ⟨v, hvt, hvcard, hv⟩ := mulRothNumber_spec t
  rw [← hucard]; rw [← hvcard]; rw [← card_product]
  refine ThreeGPFree.le_mulRothNumber ?_ (product_subset_product hus hvt)
  rw [coe_product]
  exact hu.prod hv

@[to_additive]

Depends on / 依赖: ThreeGPFree, ThreeGPFree.le_mulRothNumber, card_product, coe_product, hu.prod, hucard, hvcard, le_mulRothNumber, mulRothNumber_spec, product_subset_product
-/
theorem le_mulRothNumber_product (s : Finset α) (t : Finset β) :
    mulRothNumber s * mulRothNumber t <= mulRothNumber (s ×ˢ t) := by
  obtain ⟨u, hus, hucard, hu⟩ := mulRothNumber_spec s
  obtain ⟨v, hvt, hvcard, hv⟩ := mulRothNumber_spec t
  rw [← hucard]; rw [← hvcard]; rw [← card_product]
  refine ThreeGPFree.le_mulRothNumber ?_ (product_subset_product hus hvt)
  rw [coe_product]
  exact hu.prod hv

@[to_additive]
/--
theorem `mulRothNumber_lt_of_forall_not_threeGPFree` / 定理 `mulRothNumber_lt_of_forall_not_threeGPFree`

English:
theorem mulRothNumber_lt_of_forall_not_threeGPFree
  proof: by
  obtain ⟨t, hts, hcard, ht⟩ := mulRothNumber_spec s
  rw [← hcard]; rw [← not_le]
  intro hn
  obtain ⟨u, hut, rfl⟩ := exists_subset_card_eq hn
  exact h _ (mem_powersetCard.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut)

中文:
定理 mulRothNumber_lt_of_forall_not_threeGPFree
  证明: by
  obtain ⟨t, hts, hcard, ht⟩ := mulRothNumber_spec s
  rw [← hcard]; rw [← not_le]
  intro hn
  obtain ⟨u, hut, rfl⟩ := exists_subset_card_eq hn
  exact h _ (mem_powersetCard.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut)

Depends on / 依赖: exists_subset_card_eq, ht.mono, hut.trans, mem_powersetCard, mulRothNumber_spec, not_le
-/
theorem mulRothNumber_lt_of_forall_not_threeGPFree
    (h : forall t in powersetCard n s, ¬ThreeGPFree ((t : Finset α) : Set α)) :
    mulRothNumber s < n := by
  obtain ⟨t, hts, hcard, ht⟩ := mulRothNumber_spec s
  rw [← hcard]; rw [← not_le]
  intro hn
  obtain ⟨u, hut, rfl⟩ := exists_subset_card_eq hn
  exact h _ (mem_powersetCard.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut)

end Monoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] [DecidableEq β] {A : Finset α} {B : Finset β} {f : α -> β}

/-- Arithmetic progressions can be pushed forward along bijective 2-Freiman homs. -/
@[to_additive /-- Arithmetic progressions can be pushed forward along bijective 2-Freiman homs. -/]
/--
lemma `IsMulFreimanHom.mulRothNumber_mono` / 引理 `IsMulFreimanHom.mulRothNumber_mono`

English:
lemma IsMulFreimanHom.mulRothNumber_mono
  given: (hf : IsMulFreimanHom 2 A B f) (hf' : Set.BijOn f A B)
  proof: by
  obtain ⟨s, hsB, hcard, hs⟩ := mulRothNumber_spec B
  have hsA : invFunOn f A '' s subseteq A :=
    (hf'.surjOn.mapsTo_invFunOn.mono (coe_subset.2 hsB) Subset.rfl).image_subset
  have hfsA : Set.SurjOn f A s := hf'.surjOn.mono Subset.rfl (coe_subset.2 hsB)
  rw [← hcard]; rw [← s.card_image_of_

中文:
引理 IsMulFreimanHom.mulRothNumber_mono
  条件: (hf : IsMulFreimanHom 2 A B f) (hf' : Set.BijOn f A B)
  证明: by
  obtain ⟨s, hsB, hcard, hs⟩ := mulRothNumber_spec B
  have hsA : invFunOn f A '' s subseteq A :=
    (hf'.surjOn.mapsTo_invFunOn.mono (coe_subset.2 hsB) Subset.rfl).image_subset
  have hfsA : Set.SurjOn f A s := hf'.surjOn.mono Subset.rfl (coe_subset.2 hsB)
  rw [← hcard]; rw [← s.card_image_of_

Depends on / 依赖: Set.SurjOn, Subset, Subset.rfl, SurjOn, ThreeGPFree, ThreeGPFree.le_mulRothNumber, bijOn_subset, card_image_of_injOn, coe_image, coe_subset, hf.subset, hfsA.bijOn_subset.mapsTo, image_subset, injOn.mono, invFunOn, invFunOn_injOn_image, le_mulRothNumber, mapsTo, mapsTo_invFunOn, mod_cast
-/
lemma IsMulFreimanHom.mulRothNumber_mono (hf : IsMulFreimanHom 2 A B f) (hf' : Set.BijOn f A B) :
    mulRothNumber B <= mulRothNumber A := by
  obtain ⟨s, hsB, hcard, hs⟩ := mulRothNumber_spec B
  have hsA : invFunOn f A '' s subseteq A :=
    (hf'.surjOn.mapsTo_invFunOn.mono (coe_subset.2 hsB) Subset.rfl).image_subset
  have hfsA : Set.SurjOn f A s := hf'.surjOn.mono Subset.rfl (coe_subset.2 hsB)
  rw [← hcard]; rw [← s.card_image_of_injOn ((invFunOn_injOn_image f _).mono hfsA)]
  refine ThreeGPFree.le_mulRothNumber ?_ (mod_cast hsA)
  rw [coe_image]
  simpa using (hf.subset hsA hfsA.bijOn_subset.mapsTo).threeGPFree (hf'.injOn.mono hsA) hs

/-- Arithmetic progressions are preserved under 2-Freiman isos. -/
@[to_additive /-- Arithmetic progressions are preserved under 2-Freiman isos. -/]
/--
lemma `IsMulFreimanIso.mulRothNumber_congr` / 引理 `IsMulFreimanIso.mulRothNumber_congr`

English:
lemma IsMulFreimanIso.mulRothNumber_congr
  given: (hf : IsMulFreimanIso 2 A B f)
  proof: by
  refine le_antisymm ?_ (hf.isMulFreimanHom.mulRothNumber_mono hf.bijOn)
  obtain ⟨s, hsA, hcard, hs⟩ := mulRothNumber_spec A
  rw [← coe_subset] at hsA
  have hfs : Set.InjOn f s := hf.bijOn.injOn.mono hsA
  have := (hf.subset hsA hfs.bijOn_image).threeGPFree_congr.1 hs
  rw [← coe_image] at thi

中文:
引理 IsMulFreimanIso.mulRothNumber_congr
  条件: (hf : IsMulFreimanIso 2 A B f)
  证明: by
  refine le_antisymm ?_ (hf.isMulFreimanHom.mulRothNumber_mono hf.bijOn)
  obtain ⟨s, hsA, hcard, hs⟩ := mulRothNumber_spec A
  rw [← coe_subset] at hsA
  have hfs : Set.InjOn f s := hf.bijOn.injOn.mono hsA
  have := (hf.subset hsA hfs.bijOn_image).threeGPFree_congr.1 hs
  rw [← coe_image] at thi

Depends on / 依赖: Finset, Finset.card_image_of_injOn, Set.InjOn, Subset, Subset.rfl, bijOn_image, card_image_of_injOn, coe_image, coe_subset, hf.bijOn, hf.bijOn.injOn.mono, hf.bijOn.mapsTo.mono, hf.isMulFreimanHom.mulRothNumber_mono, hf.subset, hfs.bijOn_image, image_subset, isMulFreimanHom, le_antisymm, le_mulRothNumber, mapsTo
-/
lemma IsMulFreimanIso.mulRothNumber_congr (hf : IsMulFreimanIso 2 A B f) :
    mulRothNumber A = mulRothNumber B := by
  refine le_antisymm ?_ (hf.isMulFreimanHom.mulRothNumber_mono hf.bijOn)
  obtain ⟨s, hsA, hcard, hs⟩ := mulRothNumber_spec A
  rw [← coe_subset] at hsA
  have hfs : Set.InjOn f s := hf.bijOn.injOn.mono hsA
  have := (hf.subset hsA hfs.bijOn_image).threeGPFree_congr.1 hs
  rw [← coe_image] at this
  rw [← hcard]; rw [← Finset.card_image_of_injOn hfs]
  refine this.le_mulRothNumber ?_
  rw [← coe_subset]; rw [coe_image]
  exact (hf.bijOn.mapsTo.mono hsA Subset.rfl).image_subset

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid α] (s : Finset α) (a : α)

@[to_additive (attr := simp)]
/--
theorem `mulRothNumber_map_mul_left` / 定理 `mulRothNumber_map_mul_left`

English:
theorem mulRothNumber_map_mul_left
  proof: by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s.map <| mulLeftEmbedding a)
    rw [subset_map_iff] at hus
    obtain ⟨u, hus, rfl⟩ := hus
    rw [coe_map] at hu
    rw [← hcard]; rw [card_map]
    exact (threeGPFree_smul_set.1 hu).le_mulRothNumber hus
  · obtain

中文:
定理 mulRothNumber_map_mul_left
  证明: by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s.map <| mulLeftEmbedding a)
    rw [subset_map_iff] at hus
    obtain ⟨u, hus, rfl⟩ := hus
    rw [coe_map] at hu
    rw [← hcard]; rw [card_map]
    exact (threeGPFree_smul_set.1 hu).le_mulRothNumber hus
  · obtain

Depends on / 依赖: ThreeGPFree, card_map, coe_map, convert, h.le_mulRothNumber, hu.smul_set, le_antisymm, le_mulRothNumber, map_subset_map, mulLeftEmbedding, mulRothNumber_spec, s.map, smul_set, subset_map_iff, threeGPFree_smul_set, u.map
-/
theorem mulRothNumber_map_mul_left :
    mulRothNumber (s.map <| mulLeftEmbedding a) = mulRothNumber s := by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s.map <| mulLeftEmbedding a)
    rw [subset_map_iff] at hus
    obtain ⟨u, hus, rfl⟩ := hus
    rw [coe_map] at hu
    rw [← hcard]; rw [card_map]
    exact (threeGPFree_smul_set.1 hu).le_mulRothNumber hus
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec s
    have h : ThreeGPFree (u.map <| mulLeftEmbedding a : Set α) := by rw [coe_map]; exact hu.smul_set
    convert! h.le_mulRothNumber (map_subset_map.2 hus) using 1
    rw [card_map]; rw [hcard]

@[to_additive (attr := simp)]
/--
theorem `mulRothNumber_map_mul_right` / 定理 `mulRothNumber_map_mul_right`

English:
theorem mulRothNumber_map_mul_right
  proof: by
  rw [← mulLeftEmbedding_eq_mulRightEmbedding]; rw [mulRothNumber_map_mul_left s a]

中文:
定理 mulRothNumber_map_mul_right
  证明: by
  rw [← mulLeftEmbedding_eq_mulRightEmbedding]; rw [mulRothNumber_map_mul_left s a]

Depends on / 依赖: mulLeftEmbedding_eq_mulRightEmbedding, mulRothNumber_map_mul_left
-/
theorem mulRothNumber_map_mul_right :
    mulRothNumber (s.map <| mulRightEmbedding a) = mulRothNumber s := by
  rw [← mulLeftEmbedding_eq_mulRightEmbedding]; rw [mulRothNumber_map_mul_left s a]

end CancelCommMonoid

end RothNumber

section rothNumberNat

variable {k n : Nat}

/--
Definition of `rothNumberNat` / `rothNumberNat` 的定义

English:
definition rothNumberNat
  signature: : Nat ->o Nat
  body: ⟨fun n => addRothNumber (range n), addRothNumber.mono.comp range_mono⟩

中文:
定义 rothNumberNat
  签名: : 自然数 ->o 自然数
  定义体: ⟨fun n => addRothNumber (range n), addRothNumber.mono.comp range_mono⟩

Depends on / 依赖: addRothNumber, addRothNumber.mono.comp, range_mono
-/
def rothNumberNat : Nat ->o Nat :=
  ⟨fun n => addRothNumber (range n), addRothNumber.mono.comp range_mono⟩

/--
theorem `rothNumberNat_def` / 定理 `rothNumberNat_def`

English:
theorem rothNumberNat_def
  given: (n : Nat)
  statement: rothNumberNat n = addRothNumber (range n)
  proof: rfl

中文:
定理 rothNumberNat_def
  条件: (n : 自然数)
  结论: rothNumber自然数 n = addRothNumber (range n)
  证明: rfl
-/
theorem rothNumberNat_def (n : Nat) : rothNumberNat n = addRothNumber (range n) :=
  rfl

/--
theorem `rothNumberNat_le` / 定理 `rothNumberNat_le`

English:
theorem rothNumberNat_le
  given: (N : Nat)
  statement: rothNumberNat N <= N
  proof: (addRothNumber_le _).trans (card_range _).le

中文:
定理 rothNumberNat_le
  条件: (N : 自然数)
  结论: rothNumber自然数 N <= N
  证明: (addRothNumber_le _).trans (card_range _).le

Depends on / 依赖: addRothNumber_le, card_range
-/
theorem rothNumberNat_le (N : Nat) : rothNumberNat N <= N :=
  (addRothNumber_le _).trans (card_range _).le

/--
theorem `rothNumberNat_spec` / 定理 `rothNumberNat_spec`

English:
theorem rothNumberNat_spec
  given: (n : Nat)
  proof: addRothNumber_spec _

中文:
定理 rothNumberNat_spec
  条件: (n : 自然数)
  证明: addRothNumber_spec _

Depends on / 依赖: addRothNumber_spec
-/
theorem rothNumberNat_spec (n : Nat) :
    exists t subseteq range n, #t = rothNumberNat n ∧ ThreeAPFree (t : Set Nat) :=
  addRothNumber_spec _

/--
theorem `ThreeAPFree.le_rothNumberNat` / 定理 `ThreeAPFree.le_rothNumberNat`

English:
theorem ThreeAPFree.le_rothNumberNat
  statement: (s : Finset Nat) (hs : ThreeAPFree (s : Set Nat))
  proof: hsk.ge.trans hs.le_addRothNumber fun x hx => mem_range.2 hsn x hx

中文:
定理 ThreeAPFree.le_rothNumberNat
  结论: (s : Finset 自然数) (hs : ThreeAPFree (s : Set 自然数))
  证明: hsk.ge.trans hs.le_addRothNumber fun x hx => mem_range.2 hsn x hx

Depends on / 依赖: hs.le_addRothNumber, hsk.ge.trans, le_addRothNumber, mem_range
-/
theorem ThreeAPFree.le_rothNumberNat (s : Finset Nat) (hs : ThreeAPFree (s : Set Nat))
    (hsn : forall x in s, x < n) (hsk : #s = k) : k <= rothNumberNat n :=
hsk.ge.trans hs.le_addRothNumber fun x hx => mem_range.2 hsn x hx

/--
theorem `rothNumberNat_add_le` / 定理 `rothNumberNat_add_le`

English:
theorem rothNumberNat_add_le
  given: (M N : Nat)
  proof: by
  simp_rw [rothNumberNat_def]
  rw [range_add_eq_union]; rw [← addRothNumber_map_add_left (range N) M]
  exact addRothNumber_union_le _ _

@[simp]

中文:
定理 rothNumberNat_add_le
  条件: (M N : 自然数)
  证明: by
  simp_rw [rothNumberNat_def]
  rw [range_add_eq_union]; rw [← addRothNumber_map_add_left (range N) M]
  exact addRothNumber_union_le _ _

@[simp]

Depends on / 依赖: addRothNumber_map_add_left, addRothNumber_union_le, range_add_eq_union, rothNumberNat_def, simp_rw
-/
theorem rothNumberNat_add_le (M N : Nat) :
    rothNumberNat (M + N) <= rothNumberNat M + rothNumberNat N := by
  simp_rw [rothNumberNat_def]
  rw [range_add_eq_union]; rw [← addRothNumber_map_add_left (range N) M]
  exact addRothNumber_union_le _ _

@[simp]
/--
theorem `rothNumberNat_zero` / 定理 `rothNumberNat_zero`

English:
theorem rothNumberNat_zero
  statement: rothNumberNat 0 = 0
  proof: rfl

中文:
定理 rothNumberNat_zero
  结论: rothNumber自然数 0 = 0
  证明: rfl
-/
theorem rothNumberNat_zero : rothNumberNat 0 = 0 :=
  rfl

/--
theorem `addRothNumber_Ico` / 定理 `addRothNumber_Ico`

English:
theorem addRothNumber_Ico
  given: (a b : Nat)
  statement: addRothNumber (Ico a b) = rothNumberNat (b - a)
  proof: by
  obtain h | h := le_total b a
  · rw [Nat.sub_eq_zero_of_le h, Ico_eq_empty_of_le h, rothNumberNat_zero, addRothNumber_empty]
  convert! addRothNumber_map_add_left _ a
  rw [range_eq_Ico]; rw [map_eq_image]
  convert! (image_add_left_Ico 0 (b - a) _).symm
  exact (add_tsub_cancel_of_le h).symm

中文:
定理 addRothNumber_Ico
  条件: (a b : 自然数)
  结论: addRothNumber (Ico a b) = rothNumber自然数 (b - a)
  证明: by
  obtain h | h := le_total b a
  · rw [Nat.sub_eq_zero_of_le h, Ico_eq_empty_of_le h, rothNumberNat_zero, addRothNumber_empty]
  convert! addRothNumber_map_add_left _ a
  rw [range_eq_Ico]; rw [map_eq_image]
  convert! (image_add_left_Ico 0 (b - a) _).symm
  exact (add_tsub_cancel_of_le h).symm

Depends on / 依赖: Ico_eq_empty_of_le, Nat.sub_eq_zero_of_le, addRothNumber_empty, addRothNumber_map_add_left, add_tsub_cancel_of_le, convert, image_add_left_Ico, le_total, map_eq_image, range_eq_Ico, rothNumberNat_zero, sub_eq_zero_of_le
-/
theorem addRothNumber_Ico (a b : Nat) : addRothNumber (Ico a b) = rothNumberNat (b - a) := by
  obtain h | h := le_total b a
  · rw [Nat.sub_eq_zero_of_le h, Ico_eq_empty_of_le h, rothNumberNat_zero, addRothNumber_empty]
  convert! addRothNumber_map_add_left _ a
  rw [range_eq_Ico]; rw [map_eq_image]
  convert! (image_add_left_Ico 0 (b - a) _).symm
  exact (add_tsub_cancel_of_le h).symm

/--
lemma `Fin.addRothNumber_eq_rothNumberNat` / 引理 `Fin.addRothNumber_eq_rothNumberNat`

English:
lemma Fin.addRothNumber_eq_rothNumberNat
  given: {k : Fin (n + 1)} (hkn : 2 * k <= n)
  proof: IsAddFreimanIso.addRothNumber_congr mod_cast isAddFreimanIso_Iio two_ne_zero hkn

中文:
引理 Fin.addRothNumber_eq_rothNumberNat
  条件: {k : Fin (n + 1)} (hkn : 2 * k <= n)
  证明: IsAddFreimanIso.addRothNumber_congr mod_cast isAddFreimanIso_Iio two_ne_zero hkn

Depends on / 依赖: IsAddFreimanIso, IsAddFreimanIso.addRothNumber_congr, addRothNumber_congr, isAddFreimanIso_Iio, mod_cast, two_ne_zero
-/
lemma Fin.addRothNumber_eq_rothNumberNat {k : Fin (n + 1)} (hkn : 2 * k <= n) :
    addRothNumber (Iio k : Finset (Fin n.succ)) = rothNumberNat k :=
IsAddFreimanIso.addRothNumber_congr mod_cast isAddFreimanIso_Iio two_ne_zero hkn

/--
lemma `Fin.addRothNumber_le_rothNumberNat` / 引理 `Fin.addRothNumber_le_rothNumberNat`

English:
lemma Fin.addRothNumber_le_rothNumberNat
  given: {n : Nat} (k : Fin (n + 1))
  proof: by
  open Fin.CommRing in -- TODO: should this be refactored to avoid needing the coercion?
  suffices h : Set.BijOn (Nat.cast : Nat -> Fin n.succ) (range k) (Iio k : Finset (Fin n.succ)) by
    exact (AddHomClass.isAddFreimanHom (Nat.castRingHom _) h.mapsTo).addRothNumber_mono h
  refine ⟨?_, (Char

中文:
引理 Fin.addRothNumber_le_rothNumberNat
  条件: {n : 自然数} (k : Fin (n + 1))
  证明: by
  open Fin.CommRing in -- TODO: should this be refactored to avoid needing the coercion?
  suffices h : Set.BijOn (Nat.cast : Nat -> Fin n.succ) (range k) (Iio k : Finset (Fin n.succ)) by
    exact (AddHomClass.isAddFreimanHom (Nat.castRingHom _) h.mapsTo).addRothNumber_mono h
  refine ⟨?_, (Char

Depends on / 依赖: AddHomClass, AddHomClass.isAddFreimanHom, CharP.natCast_injOn_Iio, CommRing, Fin.CommRing, Finset, Nat.cast, Nat.castRingHom, Set.BijOn, Set.SurjOn, Set.mem_Iio, Set.mem_image, Set.subset_def, SurjOn, addRothNumber_mono, castRingHom, coe_Iio, coe_range, coercion, h.mapsTo
-/
lemma Fin.addRothNumber_le_rothNumberNat {n : Nat} (k : Fin (n + 1)) :
    addRothNumber (Iio k : Finset (Fin n.succ)) <= rothNumberNat k := by
  open Fin.CommRing in -- TODO: should this be refactored to avoid needing the coercion?
  suffices h : Set.BijOn (Nat.cast : Nat -> Fin n.succ) (range k) (Iio k : Finset (Fin n.succ)) by
    exact (AddHomClass.isAddFreimanHom (Nat.castRingHom _) h.mapsTo).addRothNumber_mono h
  refine ⟨?_, (CharP.natCast_injOn_Iio _ n.succ).mono (by simp), ?_⟩
  · simpa using! fun x => natCast_strictMono (is_le k)
  simp only [Set.SurjOn, coe_Iio, Set.subset_def, Set.mem_Iio, Set.mem_image, lt_def, coe_range]
  exact fun x hx => ⟨x, hx, by simp⟩

end rothNumberNat
