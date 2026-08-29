/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.GroupTheory.Subsemigroup.Center
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.NonUnitalSubsemiring.Basic

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring.
We prove that non-unital subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `NonUnitalSubring R`, sending a subset of
`R` to the non-unital subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `instance : CompleteLattice (NonUnitalSubring R)` : the complete lattice structure on the
  non-unital subrings.

* `NonUnitalSubring.center` : the center of a non-unital ring `R`.

* `NonUnitalSubring.closure` : non-unital subring closure of a set, i.e., the smallest
  non-unital subring that includes the set.

* `NonUnitalSubring.gi` : `closure : Set M → NonUnitalSubring M` and coercion
  `coe : NonUnitalSubring M → Set M`
  form a `GaloisInsertion`.

* `comap f B : NonUnitalSubring A` : the preimage of a non-unital subring `B` along the
  non-unital ring homomorphism `f`

* `map f A : NonUnitalSubring B` : the image of a non-unital subring `A` along the
  non-unital ring homomorphism `f`.

* `Prod A B : NonUnitalSubring (R × S)` : the product of non-unital subrings

* `f.range : NonUnitalSubring B` : the range of the non-unital ring homomorphism `f`.

* `eq_locus f g : NonUnitalSubring R` : given non-unital ring homomorphisms `f g : R →ₙ+* S`,
     the non-unital subring of `R` where `f x = g x`

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/

@[expose] public section


universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

namespace NonUnitalSubring

variable (s : NonUnitalSubring R)

/--
theorem `list_sum_mem` / 定理 `list_sum_mem`

English:
theorem list_sum_mem
  given: {l : List R}
  statement: (forall x in l, x in s) -> l.sum in s
  proof: list_sum_mem

中文:
定理 list_sum_mem
  条件: {l : 列表 R}
  结论: (对任意 x in l, x in s) -> l.求和 in s
  证明: list_sum_mem
-/
protected theorem list_sum_mem {l : List R} : (forall x in l, x in s) -> l.sum in s :=
  list_sum_mem

/--
theorem `multiset_sum_mem` / 定理 `multiset_sum_mem`

English:
theorem multiset_sum_mem
  statement: {R} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
  proof: multiset_sum_mem _

中文:
定理 multiset_sum_mem
  结论: {R} [非幺非结合环 R] (s : NonUnital子环 R)
  证明: multiset_sum_mem _
-/
protected theorem multiset_sum_mem {R} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    (m : Multiset R) : (forall a in m, a in s) -> m.sum in s :=
  multiset_sum_mem _

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  statement: {R : Type*} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
  proof: sum_mem h

中文:
定理 sum_mem
  结论: {R : 类型} [非幺非结合环 R] (s : NonUnital子环 R)
  证明: sum_mem h
-/
protected theorem sum_mem {R : Type*} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    {ι : Type*} {t : Finset ι} {f : ι -> R} (h : forall c in t, f c in s) : (∑ i in t, f i) in s :=
  sum_mem h

/-! ## top -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (NonUnitalSubring R)
  body: ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubgroup R) with }⟩

@[simp]

中文:
实例 :
  签名: 顶元素 (NonUnital子环 R)
  定义体: ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubgroup R) with }⟩

@[simp]

Depends on / 依赖: AddSubgroup, Subsemigroup
-/
instance : Top (NonUnitalSubring R) :=
  ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubgroup R) with }⟩

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : R)
  statement: x in (⊤ : NonUnitalSubring R)
  proof: Set.mem_univ x

@[simp]

中文:
定理 mem_top
  条件: (x : R)
  结论: x in (⊤ : NonUnital子环 R)
  证明: Set.mem_univ x

@[simp]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (x : R) : x in (⊤ : NonUnitalSubring R) :=
  Set.mem_univ x

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : NonUnitalSubring R) : Set R) = Set.univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: ((⊤ : NonUnital子环 R) : 集合 R) = 集合.univ
  证明: rfl

@[simp]
-/
theorem coe_top : ((⊤ : NonUnitalSubring R) : Set R) = Set.univ :=
  rfl

@[simp]
/--
lemma `toNonUnitalSubsemiring_top` / 引理 `toNonUnitalSubsemiring_top`

English:
lemma toNonUnitalSubsemiring_top
  statement: (⊤ : NonUnitalSubring R).toNonUnitalSubsemiring = ⊤
  proof: rfl

中文:
引理 toNonUnitalSubsemiring_top
  结论: (⊤ : NonUnital子环 R).toNonUnitalSubsemiring = ⊤
  证明: rfl
-/
lemma toNonUnitalSubsemiring_top : (⊤ : NonUnitalSubring R).toNonUnitalSubsemiring = ⊤ := rfl

/--
lemma `toAddSubgroup_top` / 引理 `toAddSubgroup_top`

English:
lemma toAddSubgroup_top
  statement: (⊤ : NonUnitalSubring R).toAddSubgroup = ⊤
  proof: rfl

@[simp]

中文:
引理 toAddSubgroup_top
  结论: (⊤ : NonUnital子环 R).toAddSubgroup = ⊤
  证明: rfl

@[simp]
-/
@[simp] lemma toAddSubgroup_top : (⊤ : NonUnitalSubring R).toAddSubgroup = ⊤ := rfl

@[simp]
/--
lemma `toNonUnitalSubsemiring_eq_top` / 引理 `toNonUnitalSubsemiring_eq_top`

English:
lemma toNonUnitalSubsemiring_eq_top
  given: {S : NonUnitalSubring R}
  proof: by simp [← SetLike.coe_set_eq]

中文:
引理 toNonUnitalSubsemiring_eq_top
  条件: {S : NonUnital子环 R}
  证明: by simp [← SetLike.coe_set_eq]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
lemma toNonUnitalSubsemiring_eq_top {S : NonUnitalSubring R} :
    S.toNonUnitalSubsemiring = ⊤ ↔ S = ⊤ := by simp [← SetLike.coe_set_eq]

/--
lemma `toAddSubgroup_eq_top` / 引理 `toAddSubgroup_eq_top`

English:
lemma toAddSubgroup_eq_top
  given: {S : NonUnitalSubring R}
  statement: S.toAddSubgroup = ⊤ ↔ S = ⊤
  proof: by
  simp [← SetLike.coe_set_eq]

中文:
引理 toAddSubgroup_eq_top
  条件: {S : NonUnital子环 R}
  结论: S.toAddSubgroup = ⊤ ↔ S = ⊤
  证明: by
  simp [← SetLike.coe_set_eq]
-/
@[simp] lemma toAddSubgroup_eq_top {S : NonUnitalSubring R} : S.toAddSubgroup = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

/-- The ring equiv between the top element of `NonUnitalSubring R` and `R`. -/
@[simps!]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : NonUnitalSubring R) ≃+* R
  body: NonUnitalSubsemiring.topEquiv

中文:
定义 topEquiv
  签名: : (⊤ : NonUnital子环 R) ≃+* R
  定义体: NonUnitalSubsemiring.topEquiv

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.topEquiv, topEquiv
-/
def topEquiv : (⊤ : NonUnitalSubring R) ≃+* R := NonUnitalSubsemiring.topEquiv

end NonUnitalSubring

end Basic

section Hom

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  [FunLike F R S] [NonUnitalRingHomClass F R S] (s : NonUnitalSubring R)

/-! ## comap -/


/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  body: { s.toSubsemigroup.comap (f : R ->ₙ* S), s.toAddSubgroup.comap (f : R ->+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]

中文:
定义 comap
  签名: {F : 类型 w} {R : 类型u} {S : 类型v} [非幺非结合环 R] [非幺非结合环 S]
  定义体: { s.toSubsemigroup.comap (f : R ->ₙ* S), s.toAddSubgroup.comap (f : R ->+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]

Depends on / 依赖: carrier, s.carrier, s.toAddSubgroup.comap, s.toSubsemigroup.comap, toAddSubgroup, toSubsemigroup
-/
def comap {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (s : NonUnitalSubring S) :
    NonUnitalSubring R :=
  { s.toSubsemigroup.comap (f : R ->ₙ* S), s.toAddSubgroup.comap (f : R ->+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (s : NonUnitalSubring S) (f : F)
  statement: (s.comap f : Set R) = f ⁻¹' s
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (s : NonUnital子环 S) (f : F)
  结论: (s.comap f : 集合 R) = f ⁻¹' s
  证明: rfl

@[simp]
-/
theorem coe_comap (s : NonUnitalSubring S) (f : F) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {s : NonUnitalSubring S} {f : F} {x : R}
  statement: x in s.comap f ↔ f x in s
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {s : NonUnital子环 S} {f : F} {x : R}
  结论: x in s.comap f ↔ f x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {s : NonUnitalSubring S} {f : F} {x : R} : x in s.comap f ↔ f x in s :=
  Iff.rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (s : NonUnitalSubring T) (g : S ->ₙ+* T) (f : R ->ₙ+* S)
  proof: rfl

中文:
定理 comap_comap
  条件: (s : NonUnital子环 T) (g : S ->ₙ+* T) (f : R ->ₙ+* S)
  证明: rfl
-/
theorem comap_comap (s : NonUnitalSubring T) (g : S ->ₙ+* T) (f : R ->ₙ+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ## map -/

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  body: { s.toSubsemigroup.map (f : R ->ₙ* S), s.toAddSubgroup.map (f : R ->+ S) with
    carrier := f '' s.carrier }

@[simp]

中文:
定义 map
  签名: {F : 类型 w} {R : 类型u} {S : 类型v} [非幺非结合环 R] [非幺非结合环 S]
  定义体: { s.toSubsemigroup.map (f : R ->ₙ* S), s.toAddSubgroup.map (f : R ->+ S) with
    carrier := f '' s.carrier }

@[simp]

Depends on / 依赖: carrier, s.carrier, s.toAddSubgroup.map, s.toSubsemigroup.map, toAddSubgroup, toSubsemigroup
-/
def map {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (s : NonUnitalSubring R) :
    NonUnitalSubring S :=
  { s.toSubsemigroup.map (f : R ->ₙ* S), s.toAddSubgroup.map (f : R ->+ S) with
    carrier := f '' s.carrier }

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : F) (s : NonUnitalSubring R)
  statement: (s.map f : Set S) = f '' s
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (f : F) (s : NonUnital子环 R)
  结论: (s.map f : 集合 S) = f '' s
  证明: rfl

@[simp]
-/
theorem coe_map (f : F) (s : NonUnitalSubring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : F} {s : NonUnitalSubring R} {y : S}
  statement: y in s.map f ↔ exists x in s, f x = y
  proof: Set.mem_image _ _ _

@[simp]

中文:
定理 mem_map
  条件: {f : F} {s : NonUnital子环 R} {y : S}
  结论: y in s.map f ↔ 存在 x in s, f x = y
  证明: Set.mem_image _ _ _

@[simp]

Depends on / 依赖: Set.mem_image, mem_image
-/
theorem mem_map {f : F} {s : NonUnitalSubring R} {y : S} : y in s.map f ↔ exists x in s, f x = y :=
  Set.mem_image _ _ _

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: s.map (NonUnitalRingHom.id R) = s
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  结论: s.map (非幺环态射.id R) = s
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id : s.map (NonUnitalRingHom.id R) = s :=
SetLike.coe_injective Set.image_id _

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : S ->ₙ+* T) (f : R ->ₙ+* S)
  statement: (s.map f).map g = s.map (g.comp f)
  proof: SetLike.coe_injective Set.image_image _ _ _

中文:
定理 map_map
  条件: (g : S ->ₙ+* T) (f : R ->ₙ+* S)
  结论: (s.map f).map g = s.map (g.comp f)
  证明: SetLike.coe_injective Set.image_image _ _ _

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : S ->ₙ+* T) (f : R ->ₙ+* S) : (s.map f).map g = s.map (g.comp f) :=
SetLike.coe_injective Set.image_image _ _ _

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : F} {s : NonUnitalSubring R} {t : NonUnitalSubring S}
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {f : F} {s : NonUnital子环 R} {t : NonUnital子环 S}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le_iff_le_comap {f : F} {s : NonUnitalSubring R} {t : NonUnitalSubring S} :
    s.map f <= t ↔ s <= t.comap f :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : F)
  proof: fun _S _T =>
  map_le_iff_le_comap

中文:
定理 gc_map_comap
  条件: (f : F)
  证明: fun _S _T =>
  map_le_iff_le_comap
-/
theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalSubring R -> NonUnitalSubring S) (comap f) := fun _S _T =>
  map_le_iff_le_comap

/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (f : F) (hf : Function.Injective (f : R -> S))
  body: {
    Equiv.Set.image f s
      hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]

中文:
定义 equivMapOfInjective
  签名: (f : F) (hf : 函数.单射 (f : R -> S))
  定义体: {
    Equiv.Set.image f s
      hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]

Depends on / 依赖: Equiv.Set.image, Subtype, Subtype.ext, map_add, map_mul
-/
noncomputable def equivMapOfInjective (f : F) (hf : Function.Injective (f : R -> S)) :
    s ≃+* s.map f :=
  {
    Equiv.Set.image f s
      hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]
/--
theorem `coe_equivMapOfInjective_apply` / 定理 `coe_equivMapOfInjective_apply`

English:
theorem coe_equivMapOfInjective_apply
  given: (f : F) (hf : Function.Injective f) (x : s)
  proof: rfl

中文:
定理 coe_equivMapOfInjective_apply
  条件: (f : F) (hf : 函数.单射 f) (x : s)
  证明: rfl
-/
theorem coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end NonUnitalSubring

namespace NonUnitalRingHom

variable {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  (g : S ->ₙ+* T) (f : R ->ₙ+* S)

/-! ## range -/

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  body: ((⊤ : NonUnitalSubring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]

中文:
定义 range
  签名: {R : 类型u} {S : 类型v} [非幺非结合环 R] [非幺非结合环 S]
  定义体: ((⊤ : NonUnitalSubring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]

Depends on / 依赖: NonUnitalSubring, Set.image_univ.symm, Set.range, image_univ
-/
def range {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    (f : R ->ₙ+* S) : NonUnitalSubring S :=
  ((⊤ : NonUnitalSubring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  statement: (f.range : Set S) = Set.range f
  proof: rfl

@[simp]

中文:
定理 coe_range
  结论: (f.range : 集合 S) = 集合.range f
  证明: rfl

@[simp]
-/
theorem coe_range : (f.range : Set S) = Set.range f :=
  rfl

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: {f : R ->ₙ+* S} {y : S}
  statement: y in f.range ↔ exists x, f x = y
  proof: Iff.rfl

中文:
定理 mem_range
  条件: {f : R ->ₙ+* S} {y : S}
  结论: y in f.range ↔ 存在 x, f x = y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_range {f : R ->ₙ+* S} {y : S} : y in f.range ↔ exists x, f x = y :=
  Iff.rfl

/--
theorem `range_eq_map` / 定理 `range_eq_map`

English:
theorem range_eq_map
  given: (f : R ->ₙ+* S)
  statement: f.range = NonUnitalSubring.map f ⊤
  proof: by ext; simp

中文:
定理 range_eq_map
  条件: (f : R ->ₙ+* S)
  结论: f.range = NonUnital子环.map f ⊤
  证明: by ext; simp
-/
theorem range_eq_map (f : R ->ₙ+* S) : f.range = NonUnitalSubring.map f ⊤ := by ext; simp

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (f : R ->ₙ+* S) (x : R)
  statement: f x in f.range
  proof: mem_range.mpr ⟨x, rfl⟩

中文:
定理 mem_range_self
  条件: (f : R ->ₙ+* S) (x : R)
  结论: f x in f.range
  证明: mem_range.mpr ⟨x, rfl⟩

Depends on / 依赖: mem_range, mem_range.mpr
-/
theorem mem_range_self (f : R ->ₙ+* S) (x : R) : f x in f.range :=
  mem_range.mpr ⟨x, rfl⟩

/--
theorem `map_range` / 定理 `map_range`

English:
theorem map_range
  statement: f.range.map g = (g.comp f).range
  proof: by
  simpa only [range_eq_map] using (⊤ : NonUnitalSubring R).map_map g f

中文:
定理 map_range
  结论: f.range.map g = (g.comp f).range
  证明: by
  simpa only [range_eq_map] using (⊤ : NonUnitalSubring R).map_map g f

Depends on / 依赖: NonUnitalSubring, map_map, range_eq_map
-/
theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : NonUnitalSubring R).map_map g f

/--
Instance `fintypeRange` / 实例 `fintypeRange`

English:
instance fintypeRange
  signature: [Fintype R] [DecidableEq S] (f : R ->ₙ+* S)
  body: Set.fintypeRange f

中文:
实例 fintypeRange
  签名: [有限类型 R] [DecidableEq S] (f : R ->ₙ+* S)
  定义体: Set.fintypeRange f

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R ->ₙ+* S) : Fintype (range f) :=
  Set.fintypeRange f

end NonUnitalRingHom

namespace NonUnitalSubring

section Order

variable {R : Type u} [NonUnitalNonAssocRing R]



/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (NonUnitalSubring R)
  body: ⟨(0 : R ->ₙ+* R).range⟩

中文:
实例 :
  签名: 底元素 (NonUnital子环 R)
  定义体: ⟨(0 : R ->ₙ+* R).range⟩
-/
instance : Bot (NonUnitalSubring R) :=
  ⟨(0 : R ->ₙ+* R).range⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (NonUnitalSubring R)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (NonUnital子环 R)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (NonUnitalSubring R) :=
  ⟨⊥⟩

/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : NonUnitalSubring R) : Set R) = {0}
  proof: (NonUnitalRingHom.coe_range (0 : R ->ₙ+* R)).trans (@Set.range_const R R _ 0)

中文:
定理 coe_bot
  结论: ((⊥ : NonUnital子环 R) : 集合 R) = {0}
  证明: (NonUnitalRingHom.coe_range (0 : R ->ₙ+* R)).trans (@Set.range_const R R _ 0)

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.coe_range, Set.range_const, coe_range, range_const
-/
theorem coe_bot : ((⊥ : NonUnitalSubring R) : Set R) = {0} :=
  (NonUnitalRingHom.coe_range (0 : R ->ₙ+* R)).trans (@Set.range_const R R _ 0)

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : R}
  statement: x in (⊥ : NonUnitalSubring R) ↔ x = 0
  proof: show x in ((⊥ : NonUnitalSubring R) : Set R) ↔ x = 0 by rw [coe_bot, Set.mem_singleton_iff]

中文:
定理 mem_bot
  条件: {x : R}
  结论: x in (⊥ : NonUnital子环 R) ↔ x = 0
  证明: show x in ((⊥ : NonUnitalSubring R) : Set R) ↔ x = 0 by rw [coe_bot, Set.mem_singleton_iff]

Depends on / 依赖: NonUnitalSubring, Set.mem_singleton_iff, coe_bot, mem_singleton_iff
-/
theorem mem_bot {x : R} : x in (⊥ : NonUnitalSubring R) ↔ x = 0 :=
  show x in ((⊥ : NonUnitalSubring R) : Set R) ↔ x = 0 by rw [coe_bot, Set.mem_singleton_iff]

/-! ## inf -/

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (NonUnitalSubring R)
  body: ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubgroup ⊓ t.toAddSubgroup with
      carrier := s inter t }⟩

@[simp]

中文:
实例 :
  签名: 最小值 (NonUnital子环 R)
  定义体: ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubgroup ⊓ t.toAddSubgroup with
      carrier := s inter t }⟩

@[simp]

Depends on / 依赖: carrier, s.toAddSubgroup, s.toSubsemigroup, t.toAddSubgroup, t.toSubsemigroup, toAddSubgroup, toSubsemigroup
-/
instance : Min (NonUnitalSubring R) :=
  ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubgroup ⊓ t.toAddSubgroup with
      carrier := s inter t }⟩

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (p p' : NonUnitalSubring R)
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (p p' : NonUnital子环 R)
  证明: rfl

@[simp]
-/
theorem coe_inf (p p' : NonUnitalSubring R) :
    ((p ⊓ p' : NonUnitalSubring R) : Set R) = (p : Set R) inter p' :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p p' : NonUnitalSubring R} {x : R}
  statement: x in p ⊓ p' ↔ x in p ∧ x in p'
  proof: Iff.rfl

中文:
定理 mem_inf
  条件: {p p' : NonUnital子环 R} {x : R}
  结论: x in p ⊓ p' ↔ x in p ∧ x in p'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p p' : NonUnitalSubring R} {x : R} : x in p ⊓ p' ↔ x in p ∧ x in p' :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (NonUnitalSubring R)
  body: ⟨fun s =>
    NonUnitalSubring.mk' (⋂ t in s, ↑t) (⨅ t in s, NonUnitalSubring.toSubsemigroup t)
      (⨅ t in s, NonUnitalSubring.toAddSubgroup t) (by simp) (by simp)⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 下确界集 (NonUnital子环 R)
  定义体: ⟨fun s =>
    NonUnitalSubring.mk' (⋂ t in s, ↑t) (⨅ t in s, NonUnitalSubring.toSubsemigroup t)
      (⨅ t in s, NonUnitalSubring.toAddSubgroup t) (by simp) (by simp)⟩

@[simp, norm_cast]

Depends on / 依赖: NonUnitalSubring, NonUnitalSubring.mk, NonUnitalSubring.toAddSubgroup, NonUnitalSubring.toSubsemigroup, toAddSubgroup, toSubsemigroup
-/
instance : InfSet (NonUnitalSubring R) :=
  ⟨fun s =>
    NonUnitalSubring.mk' (⋂ t in s, ↑t) (⨅ t in s, NonUnitalSubring.toSubsemigroup t)
      (⨅ t in s, NonUnitalSubring.toAddSubgroup t) (by simp) (by simp)⟩

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (NonUnitalSubring R))
  proof: rfl

@[simp]

中文:
定理 coe_sInf
  条件: (S : 集合 (NonUnital子环 R))
  证明: rfl

@[simp]
-/
theorem coe_sInf (S : Set (NonUnitalSubring R)) :
    ((sInf S : NonUnitalSubring R) : Set R) = ⋂ s in S, ↑s :=
  rfl

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (NonUnitalSubring R)} {x : R}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: Set.mem_iInter₂

@[simp, norm_cast]

中文:
定理 mem_sInf
  条件: {S : 集合 (NonUnital子环 R)} {x : R}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: Set.mem_iInter₂

@[simp, norm_cast]

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {S : Set (NonUnitalSubring R)} {x : R} : x in sInf S ↔ forall p in S, x in p :=
  Set.mem_iInter₂

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> NonUnitalSubring R}
  statement: (↑(⨅ i, S i) : Set R) = ⋂ i, S i
  proof: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> NonUnital子环 R}
  结论: (↑(⨅ i, S i) : 集合 R) = ⋂ i, S i
  证明: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

Depends on / 依赖: EquivLike, Set.biInter_range, biInter_range, coe_sInf, continuousSemilinearMapClass
-/
theorem coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> NonUnitalSubring R} {x : R}
  proof: by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> NonUnital子环 R} {x : R}
  证明: by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

Depends on / 依赖: EquivLike, Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> NonUnitalSubring R} {x : R} :
    x in ⨅ i, S i ↔ forall i, x in S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/--
theorem `sInf_toSubsemigroup` / 定理 `sInf_toSubsemigroup`

English:
theorem sInf_toSubsemigroup
  given: (s : Set (NonUnitalSubring R))
  proof: mk'_toSubsemigroup _ _

@[simp]

中文:
定理 sInf_toSubsemigroup
  条件: (s : 集合 (NonUnital子环 R))
  证明: mk'_toSubsemigroup _ _

@[simp]

Depends on / 依赖: _toSubsemigroup
-/
theorem sInf_toSubsemigroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toSubsemigroup = ⨅ t in s, NonUnitalSubring.toSubsemigroup t :=
  mk'_toSubsemigroup _ _

@[simp]
/--
theorem `sInf_toAddSubgroup` / 定理 `sInf_toAddSubgroup`

English:
theorem sInf_toAddSubgroup
  given: (s : Set (NonUnitalSubring R))
  proof: mk'_toAddSubgroup _ _

中文:
定理 sInf_toAddSubgroup
  条件: (s : 集合 (NonUnital子环 R))
  证明: mk'_toAddSubgroup _ _

Depends on / 依赖: _toAddSubgroup
-/
theorem sInf_toAddSubgroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toAddSubgroup = ⨅ t in s, NonUnitalSubring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (NonUnitalSubring R)
  body: { completeLatticeOfInf (NonUnitalSubring R) fun _s =>
      IsGLB.of_image (@fun _ _ : NonUnitalSubring R => SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)

中文:
实例 :
  签名: 完备格 (NonUnital子环 R)
  定义体: { completeLatticeOfInf (NonUnitalSubring R) fun _s =>
      IsGLB.of_image (@fun _ _ : NonUnitalSubring R => SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)

Depends on / 依赖: And.left, And.right, IsGLB.of_image, NonUnitalSubring, SetLike, SetLike.coe_subset_coe, bot_le, coe_subset_coe, completeLatticeOfInf, inf_le_left, inf_le_right, isGLB_biInf, le_inf, le_top, mem_bot, mem_bot.mp, of_image, zero_mem
-/
instance : CompleteLattice (NonUnitalSubring R) :=
  { completeLatticeOfInf (NonUnitalSubring R) fun _s =>
      IsGLB.of_image (@fun _ _ : NonUnitalSubring R => SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }

/--
theorem `eq_top_iff'` / 定理 `eq_top_iff'`

English:
theorem eq_top_iff'
  given: (A : NonUnitalSubring R)
  statement: A = ⊤ ↔ forall x : R, x in A
  proof: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

中文:
定理 eq_top_iff'
  条件: (A : NonUnital子环 R)
  结论: A = ⊤ ↔ 对任意 x : R, x in A
  证明: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

Depends on / 依赖: eq_top_iff, eq_top_iff.trans, mem_top
-/
theorem eq_top_iff' (A : NonUnitalSubring R) : A = ⊤ ↔ forall x : R, x in A :=
eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

end Order

/-! ## Center of a ring -/

section Center
variable {R : Type u}

section NonUnitalNonAssocRing
variable (R) [NonUnitalNonAssocRing R]

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : NonUnitalSubring R
  body: { NonUnitalSubsemiring.center R with
    neg_mem' := Set.neg_mem_center }

中文:
定义 center
  签名: : NonUnital子环 R
  定义体: { NonUnitalSubsemiring.center R with
    neg_mem' := Set.neg_mem_center }

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.center, Set.neg_mem_center, center, neg_mem, neg_mem_center
-/
def center : NonUnitalSubring R :=
  { NonUnitalSubsemiring.center R with
    neg_mem' := Set.neg_mem_center }

/--
theorem `coe_center` / 定理 `coe_center`

English:
theorem coe_center
  statement: ↑(center R) = Set.center R
  proof: rfl

@[simp]

中文:
定理 coe_center
  结论: ↑(center R) = 集合.center R
  证明: rfl

@[simp]
-/
theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
/--
theorem `center_toNonUnitalSubsemiring` / 定理 `center_toNonUnitalSubsemiring`

English:
theorem center_toNonUnitalSubsemiring
  proof: rfl

中文:
定理 center_toNonUnitalSubsemiring
  证明: rfl
-/
theorem center_toNonUnitalSubsemiring :
    (center R).toNonUnitalSubsemiring = NonUnitalSubsemiring.center R :=
  rfl

/--
Instance `center.instNonUnitalCommRing` / 实例 `center.instNonUnitalCommRing`

English:
instance center.instNonUnitalCommRing
  signature: : NonUnitalCommRing (center R) where
  body: inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.center R)
  __ := (inferInstance : NonUnitalNonAssocRing (center R))

中文:
实例 center.instNonUnitalCommRing
  签名: : 非幺交换环 (center R) where
  定义体: inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.center R)
  __ := (inferInstance : NonUnitalNonAssocRing (center R))
-/
instance center.instNonUnitalCommRing : NonUnitalCommRing (center R) where
  __ : NonUnitalCommSemiring (center R) :=
inferInstanceAs NonUnitalCommSemiring (NonUnitalSubsemiring.center R)
  __ := (inferInstance : NonUnitalNonAssocRing (center R))

variable {R}

/--
Definition of `centerCongr` / `centerCongr` 的定义

English:
definition centerCongr
  signature: {S} [NonUnitalNonAssocRing S] (e : R ≃+* S)
  body: NonUnitalSubsemiring.centerCongr e

中文:
定义 centerCongr
  签名: {S} [非幺非结合环 S] (e : R ≃+* S)
  定义体: NonUnitalSubsemiring.centerCongr e
-/
@[simps!] def centerCongr {S} [NonUnitalNonAssocRing S] (e : R ≃+* S) : center R ≃+* center S :=
  NonUnitalSubsemiring.centerCongr e

/--
Definition of `centerToMulOpposite` / `centerToMulOpposite` 的定义

English:
definition centerToMulOpposite
  signature: : center R ≃+* center Rᵐᵒᵖ
  body: NonUnitalSubsemiring.centerToMulOpposite

中文:
定义 centerToMulOpposite
  签名: : center R ≃+* center Rᵐᵒᵖ
  定义体: NonUnitalSubsemiring.centerToMulOpposite
-/
@[simps!] def centerToMulOpposite : center R ≃+* center Rᵐᵒᵖ :=
  NonUnitalSubsemiring.centerToMulOpposite

end NonUnitalNonAssocRing

section NonUnitalRing
variable [NonUnitalRing R]

-- no instance diamond, unlike the unital version
example : (center.instNonUnitalCommRing _).toNonUnitalRing =
      NonUnitalSubringClass.toNonUnitalRing (center R) := by
  with_reducible_and_instances rfl

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {z : R}
  statement: z in center R ↔ forall g, g * z = z * g
  proof: Subsemigroup.mem_center_iff

中文:
定理 mem_center_iff
  条件: {z : R}
  结论: z in center R ↔ 对任意 g, g * z = z * g
  证明: Subsemigroup.mem_center_iff

Depends on / 依赖: Subsemigroup, Subsemigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {z : R} : z in center R ↔ forall g, g * z = z * g := Subsemigroup.mem_center_iff

/--
Instance `decidableMemCenter` / 实例 `decidableMemCenter`

English:
instance decidableMemCenter
  signature: [DecidableEq R] [Fintype R]
  body: fun _ =>
  decidable_of_iff' _ mem_center_iff

@[simp]

中文:
实例 decidableMemCenter
  签名: [DecidableEq R] [有限类型 R]
  定义体: fun _ =>
  decidable_of_iff' _ mem_center_iff

@[simp]
-/
instance decidableMemCenter [DecidableEq R] [Fintype R] : DecidablePred (· in center R) := fun _ =>
  decidable_of_iff' _ mem_center_iff

@[simp]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  given: (R) [NonUnitalCommRing R]
  statement: center R = ⊤
  proof: SetLike.coe_injective (Set.center_eq_univ R)

中文:
定理 center_eq_top
  条件: (R) [非幺交换环 R]
  结论: center R = ⊤
  证明: SetLike.coe_injective (Set.center_eq_univ R)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top (R) [NonUnitalCommRing R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

end NonUnitalRing

section Centralizer

variable {R : Type*} [NonUnitalRing R]

/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: (s : Set R)
  body: { NonUnitalSubsemiring.centralizer s with
    carrier := s.centralizer
    neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]

中文:
定义 centralizer
  签名: (s : 集合 R)
  定义体: { NonUnitalSubsemiring.centralizer s with
    carrier := s.centralizer
    neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.centralizer, Set.neg_mem_centralizer, carrier, centralizer, neg_mem, neg_mem_centralizer, s.centralizer
-/
def centralizer (s : Set R) : NonUnitalSubring R :=
  { NonUnitalSubsemiring.centralizer s with
    carrier := s.centralizer
    neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  given: (s : Set R)
  proof: rfl

中文:
定理 coe_centralizer
  条件: (s : 集合 R)
  证明: rfl
-/
theorem coe_centralizer (s : Set R) :
    (centralizer s : Set R) = s.centralizer :=
  rfl

/--
theorem `centralizer_toNonUnitalSubsemiring` / 定理 `centralizer_toNonUnitalSubsemiring`

English:
theorem centralizer_toNonUnitalSubsemiring
  given: (s : Set R)
  proof: rfl

中文:
定理 centralizer_toNonUnitalSubsemiring
  条件: (s : 集合 R)
  证明: rfl
-/
theorem centralizer_toNonUnitalSubsemiring (s : Set R) :
    (centralizer s).toNonUnitalSubsemiring = NonUnitalSubsemiring.centralizer s :=
  rfl

/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {s : Set R} {z : R}
  proof: Iff.rfl

中文:
定理 mem_centralizer_iff
  条件: {s : 集合 R} {z : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_centralizer_iff {s : Set R} {z : R} :
    z in centralizer s ↔ forall g in s, g * z = z * g :=
  Iff.rfl

/--
theorem `center_le_centralizer` / 定理 `center_le_centralizer`

English:
theorem center_le_centralizer
  given: (s)
  statement: center R <= centralizer s
  proof: s.center_subset_centralizer

中文:
定理 center_le_centralizer
  条件: (s)
  结论: center R <= centralizer s
  证明: s.center_subset_centralizer

Depends on / 依赖: center_subset_centralizer, s.center_subset_centralizer
-/
theorem center_le_centralizer (s) : center R <= centralizer s :=
  s.center_subset_centralizer

/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: (s t : Set R) (h : s subseteq t)
  proof: Set.centralizer_subset h

@[simp]

中文:
定理 centralizer_le
  条件: (s t : 集合 R) (h : s subseteq t)
  证明: Set.centralizer_subset h

@[simp]

Depends on / 依赖: Set.centralizer_subset, centralizer_subset
-/
theorem centralizer_le (s t : Set R) (h : s subseteq t) :
    centralizer t <= centralizer s :=
  Set.centralizer_subset h

@[simp]
/--
theorem `centralizer_eq_top_iff_subset` / 定理 `centralizer_eq_top_iff_subset`

English:
theorem centralizer_eq_top_iff_subset
  given: {s : Set R}
  proof: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]

中文:
定理 centralizer_eq_top_iff_subset
  条件: {s : 集合 R}
  证明: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]

Depends on / 依赖: Set.centralizer_eq_top_iff_subset, SetLike, SetLike.ext, _iff, _iff.trans, centralizer_eq_top_iff_subset
-/
theorem centralizer_eq_top_iff_subset {s : Set R} :
    centralizer s = ⊤ ↔ s subseteq center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  statement: centralizer Set.univ = center R
  proof: SetLike.ext' (Set.centralizer_univ R)

中文:
定理 centralizer_univ
  结论: centralizer 集合.univ = center R
  证明: SetLike.ext' (Set.centralizer_univ R)

Depends on / 依赖: Set.centralizer_univ, SetLike, SetLike.ext, centralizer_univ
-/
theorem centralizer_univ : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

end Center

/-! ## `NonUnitalSubring` closure of a subset -/

variable {F : Type w} {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Set R)
  body: sInf {S | s subseteq S}

中文:
定义 closure
  签名: (s : 集合 R)
  定义体: sInf {S | s subseteq S}

Depends on / 依赖: subseteq
-/
def closure (s : Set R) : NonUnitalSubring R :=
  sInf {S | s subseteq S}

/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {x : R} {s : Set R}
  statement: x in closure s ↔ forall S : NonUnitalSubring R, s subseteq S -> x in S
  proof: mem_sInf

中文:
定理 mem_closure
  条件: {x : R} {s : 集合 R}
  结论: x in closure s ↔ 对任意 S : NonUnital子环 R, s subseteq S -> x in S
  证明: mem_sInf

Depends on / 依赖: mem_sInf
-/
theorem mem_closure {x : R} {s : Set R} : x in closure s ↔ forall S : NonUnitalSubring R, s subseteq S -> x in S :=
  mem_sInf

/-- The `NonUnitalSubring` generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `subset_closure` / 定理 `subset_closure`

English:
theorem subset_closure
  given: {s : Set R}
  statement: s subseteq closure s
  proof: fun _x hx => mem_closure.2 fun _S hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]

中文:
定理 subset_closure
  条件: {s : 集合 R}
  结论: s subseteq closure s
  证明: fun _x hx => mem_closure.2 fun _S hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: mem_closure
-/
theorem subset_closure {s : Set R} : s subseteq closure s := fun _x hx => mem_closure.2 fun _S hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]
/--
theorem `mem_closure_of_mem` / 定理 `mem_closure_of_mem`

English:
theorem mem_closure_of_mem
  given: {s : Set R} {x : R} (hx : x in s)
  statement: x in closure s
  proof: subset_closure hx

中文:
定理 mem_closure_of_mem
  条件: {s : 集合 R} {x : R} (hx : x in s)
  结论: x in closure s
  证明: subset_closure hx

Depends on / 依赖: subset_closure
-/
theorem mem_closure_of_mem {s : Set R} {x : R} (hx : x in s) : x in closure s := subset_closure hx

/--
theorem `notMem_of_notMem_closure` / 定理 `notMem_of_notMem_closure`

English:
theorem notMem_of_notMem_closure
  given: {s : Set R} {P : R} (hP : P ∉ closure s)
  statement: P ∉ s
  proof: fun h =>
  hP (subset_closure h)

中文:
定理 notMem_of_notMem_closure
  条件: {s : 集合 R} {P : R} (hP : P ∉ closure s)
  结论: P ∉ s
  证明: fun h =>
  hP (subset_closure h)
-/
theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A `NonUnitalSubring` `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
/--
theorem `closure_le` / 定理 `closure_le`

English:
theorem closure_le
  given: {s : Set R} {t : NonUnitalSubring R}
  statement: closure s <= t ↔ s subseteq t
  proof: ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

中文:
定理 closure_le
  条件: {s : 集合 R} {t : NonUnital子环 R}
  结论: closure s <= t ↔ s subseteq t
  证明: ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

Depends on / 依赖: Set.Subset.trans, Subset, sInf_le, subset_closure
-/
theorem closure_le {s : Set R} {t : NonUnitalSubring R} : closure s <= t ↔ s subseteq t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- `NonUnitalSubring` closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
/--
theorem `closure_mono` / 定理 `closure_mono`

English:
theorem closure_mono
  given: ⦃s t
  statement: Set R⦄ (h : s subseteq t) : closure s <= closure t
  proof: closure_le.2 Set.Subset.trans h subset_closure

中文:
定理 closure_mono
  条件: ⦃s t
  结论: 集合 R⦄ (h : s subseteq t) : closure s <= closure t
  证明: closure_le.2 Set.Subset.trans h subset_closure

Depends on / 依赖: Set.Subset.trans, Subset, closure_le, subset_closure
-/
theorem closure_mono ⦃s t : Set R⦄ (h : s subseteq t) : closure s <= closure t :=
closure_le.2 Set.Subset.trans h subset_closure

/--
theorem `closure_eq_of_le` / 定理 `closure_eq_of_le`

English:
theorem closure_eq_of_le
  given: {s : Set R} {t : NonUnitalSubring R} (h₁ : s subseteq t) (h₂ : t <= closure s)
  proof: le_antisymm (closure_le.2 h₁) h₂

中文:
定理 closure_eq_of_le
  条件: {s : 集合 R} {t : NonUnital子环 R} (h₁ : s subseteq t) (h₂ : t <= closure s)
  证明: le_antisymm (closure_le.2 h₁) h₂

Depends on / 依赖: closure_le, le_antisymm
-/
theorem closure_eq_of_le {s : Set R} {t : NonUnitalSubring R} (h₁ : s subseteq t) (h₂ : t <= closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
/--
theorem `closure_induction` / 定理 `closure_induction`

English:
theorem closure_induction
  statement: {s : Set R} {p : (x : R) -> x in closure s -> Prop}
  proof: let K : NonUnitalSubring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ => ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩ }
.elim fun

中文:
定理 closure_induction
  结论: {s : 集合 R} {p : (x : R) -> x in closure s -> 命题}
  证明: let K : NonUnitalSubring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ => ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩ }
.elim fun

Depends on / 依赖: NonUnitalSubring, add_mem, carrier, closure_le, mul_mem, neg_mem, subset_closure, zero_mem
-/
theorem closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop}
    (mem : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (neg : forall x hx, p x hx -> p (-x) (neg_mem hx))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    {x} (hx : x in closure s) : p x hx :=
  let K : NonUnitalSubring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ => ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (t := K)

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_elim]
/--
theorem `closure_induction₂` / 定理 `closure_induction₂`

English:
theorem closure_induction₂
  statement: {s : Set R} {p : (x y : R) -> x in closure s -> y in closure s -> Prop}
  proof: by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
 

中文:
定理 closure_induction₂
  结论: {s : 集合 R} {p : (x y : R) -> x in closure s -> y in closure s -> 命题}
  证明: by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
 

Depends on / 依赖: add_left, add_right, closure_induction, mem_mem, mul_left, mul_right, neg_left, neg_right, zero_left, zero_right
-/
theorem closure_induction₂ {s : Set R} {p : (x y : R) -> x in closure s -> y in closure s -> Prop}
    (mem_mem : forall (x) (y) (hx : x in s) (hy : y in s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : forall x hx, p 0 x (zero_mem _) hx) (zero_right : forall x hx, p x 0 hx (zero_mem _))
    (neg_left : forall x y hx hy, p x y hx hy -> p (-x) y (neg_mem hx) hy)
    (neg_right : forall x y hx hy, p x y hx hy -> p x (-y) hx (neg_mem hy))
    (add_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x + y) z (add_mem hx hy) hz)
    (add_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y + z) hx (add_mem hy hz))
    (mul_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x * y) z (mul_mem hx hy) hz)
    (mul_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y * z) hx (mul_mem hy hz))
    {x y : R} (hx : x in closure s) (hy : y in closure s) :
    p x y hx hy := by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | neg _ _ h => exact neg_left _ _ _ _ h
  | zero => exact zero_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | neg _ _ h => exact neg_right _ _ _ _ h

/--
theorem `mem_closure_iff` / 定理 `mem_closure_iff`

English:
theorem mem_closure_iff
  given: {s : Set R} {x}
  proof: ⟨fun h => by
    induction h using closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Subsemigroup.subset_closure hx)
    | zero => exact zero_mem _
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | mul _ _ _hx _hy hx hy =>
      clear 

中文:
定理 mem_closure_iff
  条件: {s : 集合 R} {x}
  证明: ⟨fun h => by
    induction h using closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Subsemigroup.subset_closure hx)
    | zero => exact zero_mem _
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | mul _ _ _hx _hy hx hy =>
      clear 

Depends on / 依赖: AddSubgroup, AddSubgroup.closure_induction, AddSubgroup.subset_closure, Subsemigroup, Subsemigroup.subset_closure, add_left, add_mem, add_mul, closure_induction, mul_mem, neg_mem, subset_closure, zero_left, zero_mem, zero_right
-/
theorem mem_closure_iff {s : Set R} {x} :
    x in closure s ↔ x in AddSubgroup.closure (Subsemigroup.closure s : Set R) :=
  ⟨fun h => by
    induction h using closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Subsemigroup.subset_closure hx)
    | zero => exact zero_mem _
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | mul _ _ _hx _hy hx hy =>
      clear _hx _hy
      induction hx, hy using AddSubgroup.closure_induction₂ with
      | mem _ _ hx hy => exact AddSubgroup.subset_closure (mul_mem hx hy)
      | zero_left => simp
      | zero_right => simp
      | add_left _ _ _ _ _ _ h₁ h₂ => simpa [add_mul] using add_mem h₁ h₂
      | add_right _ _ _ _ _ _ h₁ h₂ => simpa [mul_add] using add_mem h₁ h₂
      | neg_left _ _ _ _ h => simpa [neg_mul] using neg_mem h
      | neg_right _ _ _ _ h => simpa [mul_neg] using neg_mem h,
  fun h => by
    induction h using AddSubgroup.closure_induction with
    | mem _ hx => induction hx using Subsemigroup.closure_induction with
      | mem _ h => exact subset_closure h
      | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | neg _ _ h => exact neg_mem h⟩

/--
lemma `closure_le_centralizer_centralizer` / 引理 `closure_le_centralizer_centralizer`

English:
lemma closure_le_centralizer_centralizer
  given: {R : Type*} [NonUnitalRing R] (s : Set R)
  proof: closure_le.mpr Set.subset_centralizer_centralizer

中文:
引理 closure_le_centralizer_centralizer
  条件: {R : 类型} [非幺环 R] (s : 集合 R)
  证明: closure_le.mpr Set.subset_centralizer_centralizer

Depends on / 依赖: Set.subset_centralizer_centralizer, closure_le, closure_le.mpr, subset_centralizer_centralizer
-/
lemma closure_le_centralizer_centralizer {R : Type*} [NonUnitalRing R] (s : Set R) :
    closure s <= centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/--
theorem `isMulCommutative_closure` / 定理 `isMulCommutative_closure`

English:
theorem isMulCommutative_closure
  statement: {R : Type*} [NonUnitalRing R] {s : Set R}
  proof: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

中文:
定理 isMulCommutative_closure
  结论: {R : 类型} [非幺环 R] {s : 集合 R}
  证明: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, centralizer_centralizer_comm_of_comm, closure_le_centralizer_centralizer, of_setLike_mul_comm
-/
theorem isMulCommutative_closure {R : Type*} [NonUnitalRing R] {s : Set R}
    (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a non-unital commutative
ring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
/--
Definition of `closureNonUnitalCommRingOfComm` / `closureNonUnitalCommRingOfComm` 的定义

English:
abbreviation closureNonUnitalCommRingOfComm
  signature: {R : Type*} [NonUnitalRing R] {s : Set R}
  body: have := isMulCommutative_closure hcomm
  inferInstance

中文:
缩写 closureNonUnitalCommRingOfComm
  签名: {R : 类型} [非幺环 R] {s : 集合 R}
  定义体: have := isMulCommutative_closure hcomm
  inferInstance

Depends on / 依赖: isMulCommutative_closure
-/
abbrev closureNonUnitalCommRingOfComm {R : Type*} [NonUnitalRing R] {s : Set R}
    (hcomm : forall x in s, forall y in s, x * y = y * x) : NonUnitalCommRing (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance

/--
Instance `instIsMulCommutative_closure` / 实例 `instIsMulCommutative_closure`

English:
instance instIsMulCommutative_closure
  signature: {S R : Type*} [NonUnitalRing R]
  body: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

中文:
实例 instIsMulCommutative_closure
  签名: {S R : 类型} [非幺环 R]
  定义体: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

Depends on / 依赖: isMulCommutative_closure, setLike_mul_comm
-/
instance instIsMulCommutative_closure {S R : Type*} [NonUnitalRing R]
    [SetLike S R] [MulMemClass S R] (s : S) [IsMulCommutative s] :
    IsMulCommutative (closure (s : Set R)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

variable (R) in
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (@closure R _) SetLike.coe where
  body: closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

中文:
定义 gi
  签名: : Galois嵌入 (@closure R _) 集合状.coe where
  定义体: closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl
-/
protected def gi : GaloisInsertion (@closure R _) SetLike.coe where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

/-- Closure of a `NonUnitalSubring` `S` equals `S`. -/
@[simp]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  given: (s : NonUnitalSubring R)
  statement: closure (s : Set R) = s
  proof: (NonUnitalSubring.gi R).l_u_eq s

@[simp]

中文:
定理 closure_eq
  条件: (s : NonUnital子环 R)
  结论: closure (s : 集合 R) = s
  证明: (NonUnitalSubring.gi R).l_u_eq s

@[simp]

Depends on / 依赖: NonUnitalSubring, NonUnitalSubring.gi, l_u_eq
-/
theorem closure_eq (s : NonUnitalSubring R) : closure (s : Set R) = s :=
  (NonUnitalSubring.gi R).l_u_eq s

@[simp]
/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure (∅ : Set R) = ⊥
  proof: (NonUnitalSubring.gi R).gc.l_bot

@[simp]

中文:
定理 closure_empty
  结论: closure (∅ : 集合 R) = ⊥
  证明: (NonUnitalSubring.gi R).gc.l_bot

@[simp]

Depends on / 依赖: NonUnitalSubring, NonUnitalSubring.gi, gc.l_bot, l_bot
-/
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (NonUnitalSubring.gi R).gc.l_bot

@[simp]
/--
theorem `closure_univ` / 定理 `closure_univ`

English:
theorem closure_univ
  statement: closure (Set.univ : Set R) = ⊤
  proof: @coe_top R _ ▸ closure_eq ⊤

中文:
定理 closure_univ
  结论: closure (集合.univ : 集合 R) = ⊤
  证明: @coe_top R _ ▸ closure_eq ⊤

Depends on / 依赖: closure_eq, coe_top, h.symm
-/
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

/--
theorem `closure_union` / 定理 `closure_union`

English:
theorem closure_union
  given: (s t : Set R)
  statement: closure (s union t) = closure s ⊔ closure t
  proof: (NonUnitalSubring.gi R).gc.l_sup

中文:
定理 closure_union
  条件: (s t : 集合 R)
  结论: closure (s union t) = closure s ⊔ closure t
  证明: (NonUnitalSubring.gi R).gc.l_sup

Depends on / 依赖: NonUnitalSubring, NonUnitalSubring.gi, gc.l_sup, l_sup
-/
theorem closure_union (s t : Set R) : closure (s union t) = closure s ⊔ closure t :=
  (NonUnitalSubring.gi R).gc.l_sup

/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: {ι} (s : ι -> Set R)
  statement: closure (⋃ i, s i) = ⨆ i, closure (s i)
  proof: (NonUnitalSubring.gi R).gc.l_iSup

中文:
定理 closure_iUnion
  条件: {ι} (s : ι -> 集合 R)
  结论: closure (⋃ i, s i) = ⨆ i, closure (s i)
  证明: (NonUnitalSubring.gi R).gc.l_iSup

Depends on / 依赖: NonUnitalSubring, NonUnitalSubring.gi, gc.l_iSup, l_iSup
-/
theorem closure_iUnion {ι} (s : ι -> Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (NonUnitalSubring.gi R).gc.l_iSup

/--
theorem `closure_sUnion` / 定理 `closure_sUnion`

English:
theorem closure_sUnion
  given: (s : Set (Set R))
  statement: closure (⋃₀ s) = ⨆ t in s, closure t
  proof: (NonUnitalSubring.gi R).gc.l_sSup

中文:
定理 closure_sUnion
  条件: (s : 集合 (集合 R))
  结论: closure (⋃₀ s) = ⨆ t in s, closure t
  证明: (NonUnitalSubring.gi R).gc.l_sSup

Depends on / 依赖: NonUnitalSubring, NonUnitalSubring.gi, gc.l_sSup, l_sSup
-/
theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t in s, closure t :=
  (NonUnitalSubring.gi R).gc.l_sSup

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (s t : NonUnitalSubring R) (f : F)
  statement: (s ⊔ t).map f = s.map f ⊔ t.map f
  proof: (gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (s t : NonUnital子环 R) (f : F)
  结论: (s ⊔ t).map f = s.map f ⊔ t.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (s t : NonUnitalSubring R) (f : F) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : F) (s : ι -> NonUnitalSubring R)
  proof: (gc_map_comap f).l_iSup

中文:
定理 map_iSup
  条件: {ι : 类型层*} (f : F) (s : ι -> NonUnital子环 R)
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : F) (s : ι -> NonUnitalSubring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (s t : NonUnitalSubring R) (f : F) (hf : Function.Injective f)
  proof: SetLike.coe_injective (Set.image_inter hf)

中文:
定理 map_inf
  条件: (s t : NonUnital子环 R) (f : F) (hf : 函数.单射 f)
  证明: SetLike.coe_injective (Set.image_inter hf)

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (s t : NonUnitalSubring R) (f : F) (hf : Function.Injective f) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter hf)

/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  statement: {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

中文:
定理 map_iInf
  结论: {ι : 类型层*} [非空 ι] (f : F) (hf : 函数.单射 f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
    (s : ι -> NonUnitalSubring R) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (s t : NonUnitalSubring S) (f : F)
  statement: (s ⊓ t).comap f = s.comap f ⊓ t.comap f
  proof: (gc_map_comap f).u_inf

中文:
定理 comap_inf
  条件: (s t : NonUnital子环 S) (f : F)
  结论: (s ⊓ t).comap f = s.comap f ⊓ t.comap f
  证明: (gc_map_comap f).u_inf

Depends on / 依赖: gc_map_comap, u_inf
-/
theorem comap_inf (s t : NonUnitalSubring S) (f : F) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : F) (s : ι -> NonUnitalSubring S)
  proof: (gc_map_comap f).u_iInf

@[simp]

中文:
定理 comap_iInf
  条件: {ι : 类型层*} (f : F) (s : ι -> NonUnital子环 S)
  证明: (gc_map_comap f).u_iInf

@[simp]

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : F) (s : ι -> NonUnitalSubring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : R ->ₙ+* S)
  statement: (⊥ : NonUnitalSubring R).map f = ⊥
  proof: (gc_map_comap f).l_bot

@[simp]

中文:
定理 map_bot
  条件: (f : R ->ₙ+* S)
  结论: (⊥ : NonUnital子环 R).map f = ⊥
  证明: (gc_map_comap f).l_bot

@[simp]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : R ->ₙ+* S) : (⊥ : NonUnitalSubring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : R ->ₙ+* S)
  statement: (⊤ : NonUnitalSubring S).comap f = ⊤
  proof: (gc_map_comap f).u_top

中文:
定理 comap_top
  条件: (f : R ->ₙ+* S)
  结论: (⊤ : NonUnital子环 S).comap f = ⊤
  证明: (gc_map_comap f).u_top

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top (f : R ->ₙ+* S) : (⊤ : NonUnitalSubring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (s : NonUnitalSubring R) (t : NonUnitalSubring S)
  body: { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubgroup.prod t.toAddSubgroup with
    carrier := s ×ˢ t }

@[norm_cast]

中文:
定义 乘积
  签名: (s : NonUnital子环 R) (t : NonUnital子环 S)
  定义体: { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubgroup.prod t.toAddSubgroup with
    carrier := s ×ˢ t }

@[norm_cast]

Depends on / 依赖: carrier, s.toAddSubgroup.prod, s.toSubsemigroup.prod, t.toAddSubgroup, t.toSubsemigroup, toAddSubgroup, toSubsemigroup
-/
def prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) : NonUnitalSubring (R × S) :=
  { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubgroup.prod t.toAddSubgroup with
    carrier := s ×ˢ t }

@[norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : NonUnitalSubring R) (t : NonUnitalSubring S)
  proof: rfl

中文:
定理 coe_prod
  条件: (s : NonUnital子环 R) (t : NonUnital子环 S)
  证明: rfl
-/
theorem coe_prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ t :=
  rfl

/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : NonUnitalSubring R} {t : NonUnitalSubring S} {p : R × S}
  proof: Iff.rfl

@[gcongr, mono]

中文:
定理 mem_prod
  条件: {s : NonUnital子环 R} {t : NonUnital子环 S} {p : R × S}
  证明: Iff.rfl

@[gcongr, mono]

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : NonUnitalSubring R} {t : NonUnitalSubring S} {p : R × S} :
    p in s.prod t ↔ p.1 in s ∧ p.2 in t :=
  Iff.rfl

@[gcongr, mono]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: ⦃s₁ s₂
  statement: NonUnitalSubring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubring S⦄
  proof: Set.prod_mono hs ht

中文:
定理 prod_mono
  条件: ⦃s₁ s₂
  结论: NonUnital子环 R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnital子环 S⦄
  证明: Set.prod_mono hs ht

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono ⦃s₁ s₂ : NonUnitalSubring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubring S⦄
    (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂ :=
  Set.prod_mono hs ht

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  given: (s : NonUnitalSubring R)
  proof: prod_mono (le_refl s)

中文:
定理 prod_mono_right
  条件: (s : NonUnital子环 R)
  证明: prod_mono (le_refl s)

Depends on / 依赖: le_refl, prod_mono
-/
theorem prod_mono_right (s : NonUnitalSubring R) :
    Monotone fun t : NonUnitalSubring S => s.prod t :=
  prod_mono (le_refl s)

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  given: (t : NonUnitalSubring S)
  statement: Monotone fun s : NonUnitalSubring R => s.prod t
  proof: fun _s₁ _s₂ hs => prod_mono hs (le_refl t)

中文:
定理 prod_mono_left
  条件: (t : NonUnital子环 S)
  结论: 递增 fun s : NonUnital子环 R => s.乘积 t
  证明: fun _s₁ _s₂ hs => prod_mono hs (le_refl t)

Depends on / 依赖: le_refl, prod_mono
-/
theorem prod_mono_left (t : NonUnitalSubring S) : Monotone fun s : NonUnitalSubring R => s.prod t :=
  fun _s₁ _s₂ hs => prod_mono hs (le_refl t)

/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  given: (s : NonUnitalSubring R)
  proof: ext fun x => by simp [mem_prod]

中文:
定理 prod_top
  条件: (s : NonUnital子环 R)
  证明: ext fun x => by simp [mem_prod]

Depends on / 依赖: mem_prod
-/
theorem prod_top (s : NonUnitalSubring R) :
    s.prod (⊤ : NonUnitalSubring S) = s.comap (NonUnitalRingHom.fst R S) :=
  ext fun x => by simp [mem_prod]

/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  given: (s : NonUnitalSubring S)
  proof: ext fun x => by simp [mem_prod]

@[simp]

中文:
定理 top_prod
  条件: (s : NonUnital子环 S)
  证明: ext fun x => by simp [mem_prod]

@[simp]

Depends on / 依赖: mem_prod
-/
theorem top_prod (s : NonUnitalSubring S) :
    (⊤ : NonUnitalSubring R).prod s = s.comap (NonUnitalRingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
/--
theorem `top_prod_top` / 定理 `top_prod_top`

English:
theorem top_prod_top
  statement: (⊤ : NonUnitalSubring R).prod (⊤ : NonUnitalSubring S) = ⊤
  proof: (top_prod _).trans comap_top _

中文:
定理 top_prod_top
  结论: (⊤ : NonUnital子环 R).乘积 (⊤ : NonUnital子环 S) = ⊤
  证明: (top_prod _).trans comap_top _

Depends on / 依赖: comap_top, top_prod
-/
theorem top_prod_top : (⊤ : NonUnitalSubring R).prod (⊤ : NonUnitalSubring S) = ⊤ :=
(top_prod _).trans comap_top _

/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  statement: center (R × S) = prod (center R) (center S)
  proof: SetLike.coe_injective Set.center_prod

中文:
定理 center_prod
  结论: center (R × S) = 乘积 (center R) (center S)
  证明: SetLike.coe_injective Set.center_prod
-/
protected theorem center_prod : center (R × S) = prod (center R) (center S) :=
  SetLike.coe_injective Set.center_prod

/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: (s : NonUnitalSubring R) (t : NonUnitalSubring S)
  body: { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 prodEquiv
  签名: (s : NonUnital子环 R) (t : NonUnital子环 S)
  定义体: { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: Equiv.Set.prod, map_add, map_mul
-/
def prodEquiv (s : NonUnitalSubring R) (t : NonUnitalSubring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/--
theorem `mem_iSup_of_directed` / 定理 `mem_iSup_of_directed`

English:
theorem mem_iSup_of_directed
  statement: {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubring R}
  proof: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : NonUnitalSubring R :=
    NonUnitalSubring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubsemigroup) (⨆ i, (S i).toAddSubgroup)
      (Subsemigroup.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U

中文:
定理 mem_iSup_of_directed
  结论: {ι} [hι : 非空 ι] {S : ι -> NonUnital子环 R}
  证明: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : NonUnitalSubring R :=
    NonUnitalSubring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubsemigroup) (⨆ i, (S i).toAddSubgroup)
      (Subsemigroup.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_iSup_of_directed, NonUnitalSubring, NonUnitalSubring.mk, Set.mem_iUnion, Subsemigroup, Subsemigroup.coe_iSup_of_directed, coe_iSup_of_directed, iSup_le, le_iSup, mem_iUnion, toAddSubgroup, toSubsemigroup
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubring R}
    (hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exists i, x in S i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : NonUnitalSubring R :=
    NonUnitalSubring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubsemigroup) (⨆ i, (S i).toAddSubgroup)
      (Subsemigroup.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U] using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  statement: {ι} [Nonempty ι] {S : ι -> NonUnitalSubring R}
  proof: Set.ext fun x => by simp [mem_iSup_of_directed hS]

中文:
定理 coe_iSup_of_directed
  结论: {ι} [非空 ι] {S : ι -> NonUnital子环 R}
  证明: Set.ext fun x => by simp [mem_iSup_of_directed hS]

Depends on / 依赖: Set.ext, mem_iSup_of_directed
-/
theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι -> NonUnitalSubring R}
    (hS : Directed (· <= ·) S) : ((⨆ i, S i : NonUnitalSubring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]

/--
theorem `mem_sSup_of_directedOn` / 定理 `mem_sSup_of_directedOn`

English:
theorem mem_sSup_of_directedOn
  statement: {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
  proof: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists,
    exists_prop]

中文:
定理 mem_sSup_of_directedOn
  结论: {S : 集合 (NonUnital子环 R)} (Sne : S.非空)
  证明: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists,
    exists_prop]

Depends on / 依赖: Nonempty, SetCoe, SetCoe.exists, Sne.to_subtype, directed_val, exists_prop, hS.directed_val, mem_iSup_of_directed, sSup_eq_iSup, to_subtype
-/
theorem mem_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) {x : R} : x in sSup S ↔ exists s in S, x in s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists,
    exists_prop]

/--
theorem `coe_sSup_of_directedOn` / 定理 `coe_sSup_of_directedOn`

English:
theorem coe_sSup_of_directedOn
  statement: {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
  proof: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

中文:
定理 coe_sSup_of_directedOn
  结论: {S : 集合 (NonUnital子环 R)} (Sne : S.非空)
  证明: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

Depends on / 依赖: Set.ext, mem_sSup_of_directedOn
-/
theorem coe_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) : (↑(sSup S) : Set R) = ⋃ s in S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

/--
theorem `isMulCommutative_iSup` / 定理 `isMulCommutative_iSup`

English:
theorem isMulCommutative_iSup
  statement: {ι : Sort*} [Nonempty ι] {S : ι -> NonUnitalSubring R}
  proof: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir

中文:
定理 isMulCommutative_iSup
  结论: {ι : 类型层*} [非空 ι] {S : ι -> NonUnital子环 R}
  证明: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.coe_iSup_of_directed, NonUnitalSubsemiring.isMulCommutative_iSup, SetLike, SetLike.mem_coe, coe_iSup_of_directed, isMulCommutative_iSup, isMulCommutative_iff, mem_coe
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι -> NonUnitalSubring R}
    [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalSubring R) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir

/--
Instance `instIsMulCommutative_iSup` / 实例 `instIsMulCommutative_iSup`

English:
instance instIsMulCommutative_iSup
  signature: {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
  body: isMulCommutative_iSup S.monotone.directed_le

中文:
实例 instIsMulCommutative_iSup
  签名: {ι : 类型} [非空 ι] [预序 ι] [IsDirectedOrder ι]
  定义体: isMulCommutative_iSup S.monotone.directed_le

Depends on / 依赖: S.monotone.directed_le, directed_le, isMulCommutative_iSup, monotone
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι ->o NonUnitalSubring R} [hS : forall i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubring R) :=
  isMulCommutative_iSup S.monotone.directed_le

/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {f : R ≃+* S} {K : NonUnitalSubring R} {x : S}
  proof: @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

中文:
定理 mem_map_equiv
  条件: {f : R ≃+* S} {K : NonUnital子环 R} {x : S}
  证明: @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

Depends on / 依赖: Set.mem_image_equiv, f.toEquiv, mem_image_equiv, toEquiv
-/
theorem mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubring R} {x : S} :
    x in K.map (f : R ->ₙ+* S) ↔ f.symm x in K :=
  @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

/--
theorem `map_equiv_eq_comap_symm` / 定理 `map_equiv_eq_comap_symm`

English:
theorem map_equiv_eq_comap_symm
  given: (f : R ≃+* S) (K : NonUnitalSubring R)
  proof: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

中文:
定理 map_equiv_eq_comap_symm
  条件: (f : R ≃+* S) (K : NonUnital子环 R)
  证明: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubring R) :
    K.map (f : R ->ₙ+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

/--
theorem `comap_equiv_eq_map_symm` / 定理 `comap_equiv_eq_map_symm`

English:
theorem comap_equiv_eq_map_symm
  given: (f : R ≃+* S) (K : NonUnitalSubring S)
  proof: (map_equiv_eq_comap_symm f.symm K).symm

中文:
定理 comap_equiv_eq_map_symm
  条件: (f : R ≃+* S) (K : NonUnital子环 S)
  证明: (map_equiv_eq_comap_symm f.symm K).symm

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubring S) :
    K.comap (f : R ->ₙ+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end NonUnitalSubring

namespace NonUnitalRingHom

variable {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]

open NonUnitalSubring

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
definition rangeRestrict
  signature: (f : R ->ₙ+* S)
  body: NonUnitalRingHom.codRestrict f f.range fun x => ⟨x, rfl⟩

@[simp]

中文:
定义 rangeRestrict
  签名: (f : R ->ₙ+* S)
  定义体: NonUnitalRingHom.codRestrict f f.range fun x => ⟨x, rfl⟩

@[simp]

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.codRestrict, codRestrict, f.range
-/
def rangeRestrict (f : R ->ₙ+* S) : R ->ₙ+* f.range :=
  NonUnitalRingHom.codRestrict f f.range fun x => ⟨x, rfl⟩

@[simp]
/--
theorem `coe_rangeRestrict` / 定理 `coe_rangeRestrict`

English:
theorem coe_rangeRestrict
  given: (f : R ->ₙ+* S) (x : R)
  statement: (f.rangeRestrict x : S) = f x
  proof: rfl

中文:
定理 coe_rangeRestrict
  条件: (f : R ->ₙ+* S) (x : R)
  结论: (f.rangeRestrict x : S) = f x
  证明: rfl
-/
theorem coe_rangeRestrict (f : R ->ₙ+* S) (x : R) : (f.rangeRestrict x : S) = f x :=
  rfl

/--
theorem `rangeRestrict_surjective` / 定理 `rangeRestrict_surjective`

English:
theorem rangeRestrict_surjective
  given: (f : R ->ₙ+* S)
  statement: Function.Surjective f.rangeRestrict
  proof: fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

中文:
定理 rangeRestrict_surjective
  条件: (f : R ->ₙ+* S)
  结论: 函数.满射 f.rangeRestrict
  证明: fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

Depends on / 依赖: Subtype, Subtype.ext, mem_range, mem_range.mp
-/
theorem rangeRestrict_surjective (f : R ->ₙ+* S) : Function.Surjective f.rangeRestrict :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  given: {f : R ->ₙ+* S}
  proof: SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

中文:
定理 range_eq_top
  条件: {f : R ->ₙ+* S}
  证明: SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

Depends on / 依赖: Iff.trans, Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, coe_range, coe_top, range_eq_univ
-/
theorem range_eq_top {f : R ->ₙ+* S} :
    f.range = (⊤ : NonUnitalSubring S) ↔ Function.Surjective f :=
SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
/--
theorem `range_eq_top_of_surjective` / 定理 `range_eq_top_of_surjective`

English:
theorem range_eq_top_of_surjective
  given: (f : R ->ₙ+* S) (hf : Function.Surjective f)
  proof: range_eq_top.2 hf

中文:
定理 range_eq_top_of_surjective
  条件: (f : R ->ₙ+* S) (hf : 函数.满射 f)
  证明: range_eq_top.2 hf

Depends on / 依赖: range_eq_top
-/
theorem range_eq_top_of_surjective (f : R ->ₙ+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : NonUnitalSubring S) :=
  range_eq_top.2 hf

/--
Definition of `eqLocus` / `eqLocus` 的定义

English:
definition eqLocus
  signature: (f g : R ->ₙ+* S)
  body: { (f : R ->ₙ* S).eqLocus g, (f : R ->+ S).eqLocus g with carrier := {x | f x = g x} }

@[simp]

中文:
定义 eqLocus
  签名: (f g : R ->ₙ+* S)
  定义体: { (f : R ->ₙ* S).eqLocus g, (f : R ->+ S).eqLocus g with carrier := {x | f x = g x} }

@[simp]

Depends on / 依赖: carrier, eqLocus
-/
def eqLocus (f g : R ->ₙ+* S) : NonUnitalSubring R :=
  { (f : R ->ₙ* S).eqLocus g, (f : R ->+ S).eqLocus g with carrier := {x | f x = g x} }

@[simp]
/--
theorem `mem_eqLocus` / 定理 `mem_eqLocus`

English:
theorem mem_eqLocus
  given: {f g : R ->ₙ+* S} {x : R}
  statement: x in f.eqLocus g ↔ f x = g x
  proof: Iff.rfl

@[simp]

中文:
定理 mem_eqLocus
  条件: {f g : R ->ₙ+* S} {x : R}
  结论: x in f.eqLocus g ↔ f x = g x
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_eqLocus {f g : R ->ₙ+* S} {x : R} : x in f.eqLocus g ↔ f x = g x := Iff.rfl

@[simp]
/--
theorem `eqLocus_same` / 定理 `eqLocus_same`

English:
theorem eqLocus_same
  given: (f : R ->ₙ+* S)
  statement: f.eqLocus f = ⊤
  proof: SetLike.ext fun _ => eq_self_iff_true _

中文:
定理 eqLocus_same
  条件: (f : R ->ₙ+* S)
  结论: f.eqLocus f = ⊤
  证明: SetLike.ext fun _ => eq_self_iff_true _

Depends on / 依赖: SetLike, SetLike.ext, eq_self_iff_true
-/
theorem eqLocus_same (f : R ->ₙ+* S) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/--
theorem `eqOn_set_closure` / 定理 `eqOn_set_closure`

English:
theorem eqOn_set_closure
  given: {f g : R ->ₙ+* S} {s : Set R} (h : Set.EqOn f g s)
  proof: show closure s <= f.eqLocus g from closure_le.2 h

中文:
定理 eqOn_set_closure
  条件: {f g : R ->ₙ+* S} {s : 集合 R} (h : 集合.EqOn f g s)
  证明: show closure s <= f.eqLocus g from closure_le.2 h

Depends on / 依赖: closure, closure_le, eqLocus, f.eqLocus
-/
theorem eqOn_set_closure {f g : R ->ₙ+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s <= f.eqLocus g from closure_le.2 h

/--
theorem `eq_of_eqOn_set_top` / 定理 `eq_of_eqOn_set_top`

English:
theorem eq_of_eqOn_set_top
  given: {f g : R ->ₙ+* S} (h : Set.EqOn f g (⊤ : NonUnitalSubring R))
  statement: f = g
  proof: ext fun _x => h trivial

中文:
定理 eq_of_eqOn_set_top
  条件: {f g : R ->ₙ+* S} (h : 集合.EqOn f g (⊤ : NonUnital子环 R))
  结论: f = g
  证明: ext fun _x => h trivial
-/
theorem eq_of_eqOn_set_top {f g : R ->ₙ+* S} (h : Set.EqOn f g (⊤ : NonUnitalSubring R)) : f = g :=
  ext fun _x => h trivial

/--
theorem `eq_of_eqOn_set_dense` / 定理 `eq_of_eqOn_set_dense`

English:
theorem eq_of_eqOn_set_dense
  given: {s : Set R} (hs : closure s = ⊤) {f g : R ->ₙ+* S} (h : s.EqOn f g)
  proof: eq_of_eqOn_set_top hs ▸ eqOn_set_closure h

中文:
定理 eq_of_eqOn_set_dense
  条件: {s : 集合 R} (hs : closure s = ⊤) {f g : R ->ₙ+* S} (h : s.EqOn f g)
  证明: eq_of_eqOn_set_top hs ▸ eqOn_set_closure h

Depends on / 依赖: eqOn_set_closure, eq_of_eqOn_set_top
-/
theorem eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R ->ₙ+* S} (h : s.EqOn f g) :
    f = g :=
eq_of_eqOn_set_top hs ▸ eqOn_set_closure h

/--
theorem `closure_preimage_le` / 定理 `closure_preimage_le`

English:
theorem closure_preimage_le
  given: (f : R ->ₙ+* S) (s : Set S)
  statement: closure (f ⁻¹' s) <= (closure s).comap f
  proof: closure_le.2 fun _x hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 closure_preimage_le
  条件: (f : R ->ₙ+* S) (s : 集合 S)
  结论: closure (f ⁻¹' s) <= (closure s).comap f
  证明: closure_le.2 fun _x hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem closure_preimage_le (f : R ->ₙ+* S) (s : Set S) : closure (f ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _x hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

/--
theorem `map_closure` / 定理 `map_closure`

English:
theorem map_closure
  given: (f : R ->ₙ+* S) (s : Set R)
  statement: (closure s).map f = closure (f '' s)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubring.gi S).gc
    (NonUnitalSubring.gi R).gc fun _ => rfl

中文:
定理 map_closure
  条件: (f : R ->ₙ+* S) (s : 集合 R)
  结论: (closure s).map f = closure (f '' s)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubring.gi S).gc
    (NonUnitalSubring.gi R).gc fun _ => rfl

Depends on / 依赖: NonUnitalSubring, NonUnitalSubring.gi, Set.image_preimage.l_comm_of_u_comm, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_closure (f : R ->ₙ+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubring.gi S).gc
    (NonUnitalSubring.gi R).gc fun _ => rfl

end NonUnitalRingHom

namespace NonUnitalSubring

variable {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]

open NonUnitalRingHom

@[simp]
/--
theorem `range_subtype` / 定理 `range_subtype`

English:
theorem range_subtype
  given: (s : NonUnitalSubring R)
  statement: (NonUnitalSubringClass.subtype s).range = s
  proof: SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

中文:
定理 range_subtype
  条件: (s : NonUnital子环 R)
  结论: (NonUnital子环类.subtype s).range = s
  证明: SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

Depends on / 依赖: SetLike, SetLike.coe_injective, Subtype, Subtype.range_coe, coe_injective, coe_srange, range_coe
-/
theorem range_subtype (s : NonUnitalSubring R) : (NonUnitalSubringClass.subtype s).range = s :=
SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

/--
theorem `range_fst` / 定理 `range_fst`

English:
theorem range_fst
  statement: NonUnitalRingHom.srange (fst R S) = ⊤
  proof: NonUnitalSubsemiring.range_fst

中文:
定理 range_fst
  结论: 非幺环态射.srange (fst R S) = ⊤
  证明: NonUnitalSubsemiring.range_fst

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.range_fst, range_fst
-/
theorem range_fst : NonUnitalRingHom.srange (fst R S) = ⊤ :=
  NonUnitalSubsemiring.range_fst

/--
theorem `range_snd` / 定理 `range_snd`

English:
theorem range_snd
  statement: NonUnitalRingHom.srange (snd R S) = ⊤
  proof: NonUnitalSubsemiring.range_snd

中文:
定理 range_snd
  结论: 非幺环态射.srange (snd R S) = ⊤
  证明: NonUnitalSubsemiring.range_snd

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.range_snd, range_snd
-/
theorem range_snd : NonUnitalRingHom.srange (snd R S) = ⊤ :=
  NonUnitalSubsemiring.range_snd

end NonUnitalSubring

namespace RingEquiv

variable {R : Type u} {S : Type v} [NonUnitalRing R] [NonUnitalRing S] {s t : NonUnitalSubring R}

/--
Definition of `nonUnitalSubringCongr` / `nonUnitalSubringCongr` 的定义

English:
definition nonUnitalSubringCongr
  signature: (h : s = t)
  body: {
Equiv.setCongr congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 nonUnitalSubringCongr
  签名: (h : s = t)
  定义体: {
Equiv.setCongr congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: Equiv.setCongr, congr_arg, map_add, map_mul, setCongr
-/
def nonUnitalSubringCongr (h : s = t) : s ≃+* t :=
  {
Equiv.setCongr congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/--
Definition of `ofLeftInverse'` / `ofLeftInverse'` 的定义

English:
definition ofLeftInverse'
  signature: {g : S -> R} {f : R ->ₙ+* S} (h : Function.LeftInverse g f)
  body: { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ NonUnitalSubringClass.subtype f.range) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[

中文:
定义 ofLeftInverse'
  签名: {g : S -> R} {f : R ->ₙ+* S} (h : 函数.左逆 g f)
  定义体: { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ NonUnitalSubringClass.subtype f.range) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.mem_range.mp, NonUnitalSubringClass, NonUnitalSubringClass.subtype, Subtype, Subtype.ext, f.range, f.rangeRestrict, invFun, left_inv, mem_range, rangeRestrict, right_inv, subtype, x.prop
-/
def ofLeftInverse' {g : S -> R} {f : R ->ₙ+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ NonUnitalSubringClass.subtype f.range) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/--
theorem `ofLeftInverse'_apply` / 定理 `ofLeftInverse'_apply`

English:
theorem ofLeftInverse'_apply
  given: {g : S -> R} {f : R ->ₙ+* S} (h : Function.LeftInverse g f) (x : R)
  proof: rfl

@[simp]

中文:
定理 ofLeftInverse'_apply
  条件: {g : S -> R} {f : R ->ₙ+* S} (h : 函数.左逆 g f) (x : R)
  证明: rfl

@[simp]
-/
theorem ofLeftInverse'_apply {g : S -> R} {f : R ->ₙ+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse' h x) = f x :=
  rfl

@[simp]
/--
theorem `ofLeftInverse'_symm_apply` / 定理 `ofLeftInverse'_symm_apply`

English:
theorem ofLeftInverse'_symm_apply
  statement: {g : S -> R} {f : R ->ₙ+* S} (h : Function.LeftInverse g f)
  proof: rfl

中文:
定理 ofLeftInverse'_symm_apply
  结论: {g : S -> R} {f : R ->ₙ+* S} (h : 函数.左逆 g f)
  证明: rfl
-/
theorem ofLeftInverse'_symm_apply {g : S -> R} {f : R ->ₙ+* S} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse' h).symm x = g x :=
  rfl

end RingEquiv

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

/--
theorem `closure_preimage_le` / 定理 `closure_preimage_le`

English:
theorem closure_preimage_le
  given: (f : F) (s : Set S)
  proof: closure_le.2 fun _x hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 closure_preimage_le
  条件: (f : F) (s : 集合 S)
  证明: closure_le.2 fun _x hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem closure_preimage_le (f : F) (s : Set S) :
    closure ((f : R -> S) ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _x hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

end NonUnitalSubring

end Hom
