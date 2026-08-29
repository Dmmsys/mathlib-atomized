/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.RingTheory.NonUnitalSubring.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Subrings

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `Subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [Ring R] (S : Type u) [Ring S] (f g : R →+* S)`
`(A : Subring R) (B : Subring S) (s : Set R)`

* `instance : CompleteLattice (Subring R)` : the complete lattice structure on the subrings.

* `Subring.center` : the center of a ring `R`.

* `Subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `Subring.gi` : `closure : Set M → Subring M` and coercion `(↑) : Subring M → et M`
  form a `GaloisInsertion`.

* `comap f B : Subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : Subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : Subring (R × S)` : the product of subrings

* `f.range : Subring B` : the range of the ring homomorphism `f`.

* `eqLocus f g : Subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

A subring is implemented as a subsemiring which is also an additive subgroup.
The initial PR was as a submonoid which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/

@[expose] public section

assert_not_exists IsOrderedRing

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

namespace Subring
variable {s t : Subring R}

@[gcongr, mono]
/--
theorem `toSubsemiring_strictMono` / 定理 `toSubsemiring_strictMono`

English:
theorem toSubsemiring_strictMono
  statement: StrictMono (toSubsemiring : Subring R -> Subsemiring R)
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toSubsemiring_strictMono
  结论: 严格递增 (toSubsemiring : 子环 R -> 子半环 R)
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : Subring R -> Subsemiring R) :=
  fun _ _ => id

@[gcongr, mono]
/--
theorem `toSubsemiring_mono` / 定理 `toSubsemiring_mono`

English:
theorem toSubsemiring_mono
  statement: Monotone (toSubsemiring : Subring R -> Subsemiring R)
  proof: toSubsemiring_strictMono.monotone

@[gcongr, mono]

中文:
定理 toSubsemiring_mono
  结论: 递增 (toSubsemiring : 子环 R -> 子半环 R)
  证明: toSubsemiring_strictMono.monotone

@[gcongr, mono]

Depends on / 依赖: monotone, toSubsemiring_strictMono, toSubsemiring_strictMono.monotone
-/
theorem toSubsemiring_mono : Monotone (toSubsemiring : Subring R -> Subsemiring R) :=
  toSubsemiring_strictMono.monotone

@[gcongr, mono]
/--
theorem `toAddSubgroup_strictMono` / 定理 `toAddSubgroup_strictMono`

English:
theorem toAddSubgroup_strictMono
  statement: StrictMono (toAddSubgroup : Subring R -> AddSubgroup R)
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toAddSubgroup_strictMono
  结论: 严格递增 (toAddSubgroup : 子环 R -> 加法子群 R)
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Subring R -> AddSubgroup R) :=
  fun _ _ => id

@[gcongr, mono]
/--
theorem `toAddSubgroup_mono` / 定理 `toAddSubgroup_mono`

English:
theorem toAddSubgroup_mono
  statement: Monotone (toAddSubgroup : Subring R -> AddSubgroup R)
  proof: toAddSubgroup_strictMono.monotone

@[mono]

中文:
定理 toAddSubgroup_mono
  结论: 递增 (toAddSubgroup : 子环 R -> 加法子群 R)
  证明: toAddSubgroup_strictMono.monotone

@[mono]

Depends on / 依赖: monotone, toAddSubgroup_strictMono, toAddSubgroup_strictMono.monotone
-/
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Subring R -> AddSubgroup R) :=
  toAddSubgroup_strictMono.monotone

@[mono]
/--
theorem `toSubmonoid_strictMono` / 定理 `toSubmonoid_strictMono`

English:
theorem toSubmonoid_strictMono
  statement: StrictMono (fun s : Subring R => s.toSubmonoid)
  proof: fun _ _ => id

@[mono]

中文:
定理 toSubmonoid_strictMono
  结论: 严格递增 (fun s : 子环 R => s.toSubmonoid)
  证明: fun _ _ => id

@[mono]
-/
theorem toSubmonoid_strictMono : StrictMono (fun s : Subring R => s.toSubmonoid) := fun _ _ => id

@[mono]
/--
theorem `toSubmonoid_mono` / 定理 `toSubmonoid_mono`

English:
theorem toSubmonoid_mono
  statement: Monotone (fun s : Subring R => s.toSubmonoid)
  proof: toSubmonoid_strictMono.monotone

中文:
定理 toSubmonoid_mono
  结论: 递增 (fun s : 子环 R => s.toSubmonoid)
  证明: toSubmonoid_strictMono.monotone

Depends on / 依赖: IsOpenImmersion, PresheafedSpace, PresheafedSpace.IsOpenImmersion.comp, monotone, morphismRestrict, toSubmonoid_strictMono, toSubmonoid_strictMono.monotone
-/
theorem toSubmonoid_mono : Monotone (fun s : Subring R => s.toSubmonoid) :=
  toSubmonoid_strictMono.monotone

end Subring

namespace Subring

variable (s : Subring R)

/--
theorem `list_prod_mem` / 定理 `list_prod_mem`

English:
theorem list_prod_mem
  given: {R} [Ring R] (s : Subring R) {l : List R}
  proof: list_prod_mem

中文:
定理 list_prod_mem
  条件: {R} [环 R] (s : 子环 R) {l : 列表 R}
  证明: list_prod_mem
-/
protected theorem list_prod_mem {R} [Ring R] (s : Subring R) {l : List R} :
    (forall x in l, x in s) -> l.prod in s := list_prod_mem

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
theorem `multiset_prod_mem` / 定理 `multiset_prod_mem`

English:
theorem multiset_prod_mem
  given: {R} [CommRing R] (s : Subring R) (m : Multiset R)
  proof: multiset_prod_mem _

中文:
定理 multiset_prod_mem
  条件: {R} [交换环 R] (s : 子环 R) (m : Multiset R)
  证明: multiset_prod_mem _
-/
protected theorem multiset_prod_mem {R} [CommRing R] (s : Subring R) (m : Multiset R) :
    (forall a in m, a in s) -> m.prod in s :=
  multiset_prod_mem _

/--
theorem `multiset_sum_mem` / 定理 `multiset_sum_mem`

English:
theorem multiset_sum_mem
  given: {R} [Ring R] (s : Subring R) (m : Multiset R)
  proof: multiset_sum_mem _

中文:
定理 multiset_sum_mem
  条件: {R} [环 R] (s : 子环 R) (m : Multiset R)
  证明: multiset_sum_mem _
-/
protected theorem multiset_sum_mem {R} [Ring R] (s : Subring R) (m : Multiset R) :
    (forall a in m, a in s) -> m.sum in s :=
  multiset_sum_mem _

/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  statement: {R : Type*} [CommRing R] (s : Subring R) {ι : Type*} {t : Finset ι}
  proof: prod_mem h

中文:
定理 prod_mem
  结论: {R : 类型} [交换环 R] (s : 子环 R) {ι : 类型} {t : 有限集 ι}
  证明: prod_mem h
-/
protected theorem prod_mem {R : Type*} [CommRing R] (s : Subring R) {ι : Type*} {t : Finset ι}
    {f : ι -> R} (h : forall c in t, f c in s) : (∏ i in t, f i) in s :=
  prod_mem h

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  statement: {R : Type*} [Ring R] (s : Subring R) {ι : Type*} {t : Finset ι}
  proof: sum_mem h

中文:
定理 sum_mem
  结论: {R : 类型} [环 R] (s : 子环 R) {ι : 类型} {t : 有限集 ι}
  证明: sum_mem h
-/
protected theorem sum_mem {R : Type*} [Ring R] (s : Subring R) {ι : Type*} {t : Finset ι}
    {f : ι -> R} (h : forall c in t, f c in s) : (∑ i in t, f i) in s :=
  sum_mem h

/-! ## top -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Subring R)
  body: ⟨{ (⊤ : Submonoid R), (⊤ : AddSubgroup R) with }⟩

@[simp]

中文:
实例 :
  签名: 顶元素 (子环 R)
  定义体: ⟨{ (⊤ : Submonoid R), (⊤ : AddSubgroup R) with }⟩

@[simp]

Depends on / 依赖: AddSubgroup, Submonoid
-/
instance : Top (Subring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubgroup R) with }⟩

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : R)
  statement: x in (⊤ : Subring R)
  proof: Set.mem_univ x

@[simp, norm_cast]

中文:
定理 mem_top
  条件: (x : R)
  结论: x in (⊤ : 子环 R)
  证明: Set.mem_univ x

@[simp, norm_cast]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (x : R) : x in (⊤ : Subring R) :=
  Set.mem_univ x

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : Subring R) : Set R) = Set.univ
  proof: rfl

中文:
定理 coe_top
  结论: ((⊤ : 子环 R) : 集合 R) = 集合.univ
  证明: rfl
-/
theorem coe_top : ((⊤ : Subring R) : Set R) = Set.univ :=
  rfl

/--
lemma `toSubsemiring_top` / 引理 `toSubsemiring_top`

English:
lemma toSubsemiring_top
  statement: (⊤ : Subring R).toSubsemiring = ⊤
  proof: rfl

中文:
引理 toSubsemiring_top
  结论: (⊤ : 子环 R).toSubsemiring = ⊤
  证明: rfl
-/
@[simp] lemma toSubsemiring_top : (⊤ : Subring R).toSubsemiring = ⊤ := rfl
/--
lemma `toAddSubgroup_top` / 引理 `toAddSubgroup_top`

English:
lemma toAddSubgroup_top
  statement: (⊤ : Subring R).toAddSubgroup = ⊤
  proof: rfl

中文:
引理 toAddSubgroup_top
  结论: (⊤ : 子环 R).toAddSubgroup = ⊤
  证明: rfl
-/
@[simp] lemma toAddSubgroup_top : (⊤ : Subring R).toAddSubgroup = ⊤ := rfl

/--
lemma `toSubsemiring_eq_top` / 引理 `toSubsemiring_eq_top`

English:
lemma toSubsemiring_eq_top
  given: {S : Subring R}
  statement: S.toSubsemiring = ⊤ ↔ S = ⊤
  proof: by
  simp [← SetLike.coe_set_eq]

中文:
引理 toSubsemiring_eq_top
  条件: {S : 子环 R}
  结论: S.toSubsemiring = ⊤ ↔ S = ⊤
  证明: by
  simp [← SetLike.coe_set_eq]
-/
@[simp] lemma toSubsemiring_eq_top {S : Subring R} : S.toSubsemiring = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

/--
lemma `toAddSubgroup_eq_top` / 引理 `toAddSubgroup_eq_top`

English:
lemma toAddSubgroup_eq_top
  given: {S : Subring R}
  statement: S.toAddSubgroup = ⊤ ↔ S = ⊤
  proof: by
  simp [← SetLike.coe_set_eq]

中文:
引理 toAddSubgroup_eq_top
  条件: {S : 子环 R}
  结论: S.toAddSubgroup = ⊤ ↔ S = ⊤
  证明: by
  simp [← SetLike.coe_set_eq]
-/
@[simp] lemma toAddSubgroup_eq_top {S : Subring R} : S.toAddSubgroup = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

/-- The ring equiv between the top element of `Subring R` and `R`. -/
@[simps!]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : Subring R) ≃+* R
  body: Subsemiring.topEquiv

中文:
定义 topEquiv
  签名: : (⊤ : 子环 R) ≃+* R
  定义体: Subsemiring.topEquiv

Depends on / 依赖: Subsemiring, Subsemiring.topEquiv, topEquiv
-/
def topEquiv : (⊤ : Subring R) ≃+* R :=
  Subsemiring.topEquiv

instance {R : Type*} [NonAssocRing R] [Fintype R] : Fintype (⊤ : Subring R) :=
inferInstanceAs Fintype (⊤ : Set R)

/--
theorem `card_top` / 定理 `card_top`

English:
theorem card_top
  given: (R) [NonAssocRing R] [Fintype R]
  statement: Fintype.card (⊤ : Subring R) = Fintype.card R
  proof: Fintype.card_congr topEquiv.toEquiv

中文:
定理 card_top
  条件: (R) [非结合环 R] [有限类型 R]
  结论: 有限类型.card (⊤ : 子环 R) = 有限类型.card R
  证明: Fintype.card_congr topEquiv.toEquiv

Depends on / 依赖: Fintype, Fintype.card_congr, card_congr, toEquiv, topEquiv, topEquiv.toEquiv
-/
theorem card_top (R) [NonAssocRing R] [Fintype R] : Fintype.card (⊤ : Subring R) = Fintype.card R :=
  Fintype.card_congr topEquiv.toEquiv

/-! ## comap -/


/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : R ->+* S) (s : Subring S)
  body: { s.toSubmonoid.comap (f : R ->* S), s.toAddSubgroup.comap (f : R ->+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]

中文:
定义 comap
  签名: (f : R ->+* S) (s : 子环 S)
  定义体: { s.toSubmonoid.comap (f : R ->* S), s.toAddSubgroup.comap (f : R ->+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]

Depends on / 依赖: carrier, s.carrier, s.toAddSubgroup.comap, s.toSubmonoid.comap, toAddSubgroup, toSubmonoid
-/
def comap (f : R ->+* S) (s : Subring S) : Subring R :=
  { s.toSubmonoid.comap (f : R ->* S), s.toAddSubgroup.comap (f : R ->+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (s : Subring S) (f : R ->+* S)
  statement: (s.comap f : Set R) = f ⁻¹' s
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (s : 子环 S) (f : R ->+* S)
  结论: (s.comap f : 集合 R) = f ⁻¹' s
  证明: rfl

@[simp]
-/
theorem coe_comap (s : Subring S) (f : R ->+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {s : Subring S} {f : R ->+* S} {x : R}
  statement: x in s.comap f ↔ f x in s
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {s : 子环 S} {f : R ->+* S} {x : R}
  结论: x in s.comap f ↔ f x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {s : Subring S} {f : R ->+* S} {x : R} : x in s.comap f ↔ f x in s :=
  Iff.rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (s : Subring T) (g : S ->+* T) (f : R ->+* S)
  proof: rfl

中文:
定理 comap_comap
  条件: (s : 子环 T) (g : S ->+* T) (f : R ->+* S)
  证明: rfl
-/
theorem comap_comap (s : Subring T) (g : S ->+* T) (f : R ->+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ## map -/


/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S) (s : Subring R)
  body: { s.toSubmonoid.map (f : R ->* S), s.toAddSubgroup.map (f : R ->+ S) with
    carrier := f '' s.carrier }

@[simp]

中文:
定义 map
  签名: (f : R ->+* S) (s : 子环 R)
  定义体: { s.toSubmonoid.map (f : R ->* S), s.toAddSubgroup.map (f : R ->+ S) with
    carrier := f '' s.carrier }

@[simp]

Depends on / 依赖: carrier, s.carrier, s.toAddSubgroup.map, s.toSubmonoid.map, toAddSubgroup, toSubmonoid
-/
def map (f : R ->+* S) (s : Subring R) : Subring S :=
  { s.toSubmonoid.map (f : R ->* S), s.toAddSubgroup.map (f : R ->+ S) with
    carrier := f '' s.carrier }

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : R ->+* S) (s : Subring R)
  statement: (s.map f : Set S) = f '' s
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (f : R ->+* S) (s : 子环 R)
  结论: (s.map f : 集合 S) = f '' s
  证明: rfl

@[simp]
-/
theorem coe_map (f : R ->+* S) (s : Subring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : R ->+* S} {s : Subring R} {y : S}
  statement: y in s.map f ↔ exists x in s, f x = y
  proof: Iff.rfl

@[simp]

中文:
定理 mem_map
  条件: {f : R ->+* S} {s : 子环 R} {y : S}
  结论: y in s.map f ↔ 存在 x in s, f x = y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, f.base
-/
theorem mem_map {f : R ->+* S} {s : Subring R} {y : S} : y in s.map f ↔ exists x in s, f x = y := Iff.rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: s.map (RingHom.id R) = s
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  结论: s.map (环态射.id R) = s
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: CommRingCat, CommRingCat.subsingleton_of_isTerminal, Set.image_id, SetLike, SetLike.coe_injective, X.sheaf.isTerminalOfEmpty, coe_injective, image_id, isTerminalOfEmpty, subsingleton_of_isTerminal
-/
theorem map_id : s.map (RingHom.id R) = s :=
SetLike.coe_injective Set.image_id _

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : S ->+* T) (f : R ->+* S)
  statement: (s.map f).map g = s.map (g.comp f)
  proof: SetLike.coe_injective Set.image_image _ _ _

中文:
定理 map_map
  条件: (g : S ->+* T) (f : R ->+* S)
  结论: (s.map f).map g = s.map (g.comp f)
  证明: SetLike.coe_injective Set.image_image _ _ _

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : S ->+* T) (f : R ->+* S) : (s.map f).map g = s.map (g.comp f) :=
SetLike.coe_injective Set.image_image _ _ _

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : R ->+* S} {s : Subring R} {t : Subring S}
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {f : R ->+* S} {s : 子环 R} {t : 子环 S}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff, specializationPreorder
-/
theorem map_le_iff_le_comap {f : R ->+* S} {s : Subring R} {t : Subring S} :
    s.map f <= t ↔ s <= t.comap f :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : R ->+* S)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ =>
  map_le_iff_le_comap

中文:
定理 gc_map_comap
  条件: (f : R ->+* S)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ =>
  map_le_iff_le_comap
-/
theorem gc_map_comap (f : R ->+* S) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (f : R ->+* S) (hf : Function.Injective f)
  body: { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]

中文:
定义 equivMapOfInjective
  签名: (f : R ->+* S) (hf : 函数.单射 f)
  定义体: { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]

Depends on / 依赖: Equiv.Set.image, Subtype, Subtype.ext, f.map_add, f.map_mul, map_add, map_mul
-/
noncomputable def equivMapOfInjective (f : R ->+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]
/--
theorem `coe_equivMapOfInjective_apply` / 定理 `coe_equivMapOfInjective_apply`

English:
theorem coe_equivMapOfInjective_apply
  given: (f : R ->+* S) (hf : Function.Injective f) (x : s)
  proof: rfl

中文:
定理 coe_equivMapOfInjective_apply
  条件: (f : R ->+* S) (hf : 函数.单射 f) (x : s)
  证明: rfl
-/
theorem coe_equivMapOfInjective_apply (f : R ->+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subring

namespace RingHom

variable (g : S ->+* T) (f : R ->+* S)

/-! ## range -/


/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (f : R ->+* S)
  body: ((⊤ : Subring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]

中文:
定义 range
  签名: (f : R ->+* S)
  定义体: ((⊤ : Subring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]

Depends on / 依赖: Set.image_univ.symm, Set.range, Subring, image_univ
-/
def range (f : R ->+* S) : Subring S :=
  ((⊤ : Subring R).map f).copy (Set.range f) Set.image_univ.symm

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
  given: {f : R ->+* S} {y : S}
  statement: y in f.range ↔ exists x, f x = y
  proof: Iff.rfl

中文:
定理 mem_range
  条件: {f : R ->+* S} {y : S}
  结论: y in f.range ↔ 存在 x, f x = y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exists x, f x = y :=
  Iff.rfl

/--
theorem `range_eq_map` / 定理 `range_eq_map`

English:
theorem range_eq_map
  given: (f : R ->+* S)
  statement: f.range = Subring.map f ⊤
  proof: by
  ext
  simp

中文:
定理 range_eq_map
  条件: (f : R ->+* S)
  结论: f.range = 子环.map f ⊤
  证明: by
  ext
  simp
-/
theorem range_eq_map (f : R ->+* S) : f.range = Subring.map f ⊤ := by
  ext
  simp

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (f : R ->+* S) (x : R)
  statement: f x in f.range
  proof: mem_range.mpr ⟨x, rfl⟩

中文:
定理 mem_range_self
  条件: (f : R ->+* S) (x : R)
  结论: f x in f.range
  证明: mem_range.mpr ⟨x, rfl⟩

Depends on / 依赖: mem_range, mem_range.mpr
-/
theorem mem_range_self (f : R ->+* S) (x : R) : f x in f.range :=
  mem_range.mpr ⟨x, rfl⟩

/--
theorem `map_range` / 定理 `map_range`

English:
theorem map_range
  statement: f.range.map g = (g.comp f).range
  proof: by
  simpa only [range_eq_map] using (⊤ : Subring R).map_map g f

中文:
定理 map_range
  结论: f.range.map g = (g.comp f).range
  证明: by
  simpa only [range_eq_map] using (⊤ : Subring R).map_map g f

Depends on / 依赖: Subring, map_map, range_eq_map
-/
theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : Subring R).map_map g f

/--
Instance `fintypeRange` / 实例 `fintypeRange`

English:
instance fintypeRange
  signature: [Fintype R] [DecidableEq S] (f : R ->+* S)
  body: Set.fintypeRange f

中文:
实例 fintypeRange
  签名: [有限类型 R] [DecidableEq S] (f : R ->+* S)
  定义体: Set.fintypeRange f

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R ->+* S) : Fintype (range f) :=
  Set.fintypeRange f

end RingHom

namespace Subring



/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Subring R)
  body: ⟨(Int.castRingHom R).range⟩

中文:
实例 :
  签名: 底元素 (子环 R)
  定义体: ⟨(Int.castRingHom R).range⟩

Depends on / 依赖: Int.castRingHom, castRingHom
-/
instance : Bot (Subring R) :=
  ⟨(Int.castRingHom R).range⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Subring R)
  body: ⟨⊥⟩

@[norm_cast]

中文:
实例 :
  签名: 可居 (子环 R)
  定义体: ⟨⊥⟩

@[norm_cast]
-/
instance : Inhabited (Subring R) :=
  ⟨⊥⟩

@[norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Subring R) : Set R) = Set.range ((↑) : Int -> R)
  proof: RingHom.coe_range (Int.castRingHom R)

中文:
定理 coe_bot
  结论: ((⊥ : 子环 R) : 集合 R) = 集合.range ((↑) : 整数 -> R)
  证明: RingHom.coe_range (Int.castRingHom R)

Depends on / 依赖: Int.castRingHom, RingHom, RingHom.coe_range, castRingHom, coe_range
-/
theorem coe_bot : ((⊥ : Subring R) : Set R) = Set.range ((↑) : Int -> R) :=
  RingHom.coe_range (Int.castRingHom R)

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : R}
  statement: x in (⊥ : Subring R) ↔ exists n : Int, ↑n = x
  proof: RingHom.mem_range

中文:
定理 mem_bot
  条件: {x : R}
  结论: x in (⊥ : 子环 R) ↔ 存在 n : 整数, ↑n = x
  证明: RingHom.mem_range

Depends on / 依赖: RingHom, RingHom.mem_range, mem_range
-/
theorem mem_bot {x : R} : x in (⊥ : Subring R) ↔ exists n : Int, ↑n = x :=
  RingHom.mem_range

/-! ## inf -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Subring R)
  body: ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubgroup ⊓ t.toAddSubgroup with carrier := s inter t }⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 最小值 (子环 R)
  定义体: ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubgroup ⊓ t.toAddSubgroup with carrier := s inter t }⟩

@[simp, norm_cast]

Depends on / 依赖: carrier, s.toAddSubgroup, s.toSubmonoid, t.toAddSubgroup, t.toSubmonoid, toAddSubgroup, toSubmonoid
-/
instance : Min (Subring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubgroup ⊓ t.toAddSubgroup with carrier := s inter t }⟩

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (p p' : Subring R)
  statement: ((p ⊓ p' : Subring R) : Set R) = (p : Set R) inter p'
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (p p' : 子环 R)
  结论: ((p ⊓ p' : 子环 R) : 集合 R) = (p : 集合 R) inter p'
  证明: rfl

@[simp]
-/
theorem coe_inf (p p' : Subring R) : ((p ⊓ p' : Subring R) : Set R) = (p : Set R) inter p' :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p p' : Subring R} {x : R}
  statement: x in p ⊓ p' ↔ x in p ∧ x in p'
  proof: Iff.rfl

中文:
定理 mem_inf
  条件: {p p' : 子环 R} {x : R}
  结论: x in p ⊓ p' ↔ x in p ∧ x in p'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p p' : Subring R} {x : R} : x in p ⊓ p' ↔ x in p ∧ x in p' :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Subring R)
  body: ⟨fun s =>
    Subring.mk' (⋂ t in s, ↑t) (⨅ t in s, t.toSubmonoid) (⨅ t in s, Subring.toAddSubgroup t)
      (by simp) (by simp)⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 下确界集 (子环 R)
  定义体: ⟨fun s =>
    Subring.mk' (⋂ t in s, ↑t) (⨅ t in s, t.toSubmonoid) (⨅ t in s, Subring.toAddSubgroup t)
      (by simp) (by simp)⟩

@[simp, norm_cast]

Depends on / 依赖: Subring, Subring.mk, Subring.toAddSubgroup, t.toSubmonoid, toAddSubgroup, toSubmonoid
-/
instance : InfSet (Subring R) :=
  ⟨fun s =>
    Subring.mk' (⋂ t in s, ↑t) (⨅ t in s, t.toSubmonoid) (⨅ t in s, Subring.toAddSubgroup t)
      (by simp) (by simp)⟩

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (Subring R))
  statement: ((sInf S : Subring R) : Set R) = ⋂ s in S, ↑s
  proof: rfl

@[simp]

中文:
定理 coe_sInf
  条件: (S : 集合 (子环 R))
  结论: ((sInf S : 子环 R) : 集合 R) = ⋂ s in S, ↑s
  证明: rfl

@[simp]
-/
theorem coe_sInf (S : Set (Subring R)) : ((sInf S : Subring R) : Set R) = ⋂ s in S, ↑s :=
  rfl

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (Subring R)} {x : R}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: Set.mem_iInter₂

@[simp, norm_cast]

中文:
定理 mem_sInf
  条件: {S : 集合 (子环 R)} {x : R}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: Set.mem_iInter₂

@[simp, norm_cast]

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {S : Set (Subring R)} {x : R} : x in sInf S ↔ forall p in S, x in p :=
  Set.mem_iInter₂

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> Subring R}
  statement: (↑(⨅ i, S i) : Set R) = ⋂ i, S i
  proof: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> 子环 R}
  结论: (↑(⨅ i, S i) : 集合 R) = ⋂ i, S i
  证明: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

Depends on / 依赖: Set.biInter_range, biInter_range, coe_sInf
-/
theorem coe_iInf {ι : Sort*} {S : ι -> Subring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> Subring R} {x : R}
  statement: x in ⨅ i, S i ↔ forall i, x in S i
  proof: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> 子环 R} {x : R}
  结论: x in ⨅ i, S i ↔ 对任意 i, x in S i
  证明: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> Subring R} {x : R} : x in ⨅ i, S i ↔ forall i, x in S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/--
theorem `sInf_toSubmonoid` / 定理 `sInf_toSubmonoid`

English:
theorem sInf_toSubmonoid
  given: (s : Set (Subring R))
  proof: mk'_toSubmonoid _ _

@[simp]

中文:
定理 sInf_toSubmonoid
  条件: (s : 集合 (子环 R))
  证明: mk'_toSubmonoid _ _

@[simp]

Depends on / 依赖: _toSubmonoid
-/
theorem sInf_toSubmonoid (s : Set (Subring R)) :
    (sInf s).toSubmonoid = ⨅ t in s, t.toSubmonoid :=
  mk'_toSubmonoid _ _

@[simp]
/--
theorem `sInf_toAddSubgroup` / 定理 `sInf_toAddSubgroup`

English:
theorem sInf_toAddSubgroup
  given: (s : Set (Subring R))
  proof: mk'_toAddSubgroup _ _

中文:
定理 sInf_toAddSubgroup
  条件: (s : 集合 (子环 R))
  证明: mk'_toAddSubgroup _ _

Depends on / 依赖: _toAddSubgroup
-/
theorem sInf_toAddSubgroup (s : Set (Subring R)) :
    (sInf s).toAddSubgroup = ⨅ t in s, Subring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subring R)
  body: { completeLatticeOfInf (Subring R) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ intCast_mem s n
    top := ⊤
    le_top := fun _s _x _hx => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _s _t _x => And.left
    inf_le_right := fun _s _t _x => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }

中文:
实例 :
  签名: 完备格 (子环 R)
  定义体: { completeLatticeOfInf (Subring R) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ intCast_mem s n
    top := ⊤
    le_top := fun _s _x _hx => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _s _t _x => And.left
    inf_le_right := fun _s _t _x => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }

Depends on / 依赖: And.left, And.right, IsGLB.of_image, SetLike, SetLike.coe_subset_coe, Subring, bot_le, coe_subset_coe, completeLatticeOfInf, inf_le_left, inf_le_right, intCast_mem, isGLB_biInf, le_inf, le_top, mem_bot, of_image
-/
instance : CompleteLattice (Subring R) :=
  { completeLatticeOfInf (Subring R) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ intCast_mem s n
    top := ⊤
    le_top := fun _s _x _hx => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _s _t _x => And.left
    inf_le_right := fun _s _t _x => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }

/--
theorem `eq_top_iff'` / 定理 `eq_top_iff'`

English:
theorem eq_top_iff'
  given: (A : Subring R)
  statement: A = ⊤ ↔ forall x : R, x in A
  proof: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

中文:
定理 eq_top_iff'
  条件: (A : 子环 R)
  结论: A = ⊤ ↔ 对任意 x : R, x in A
  证明: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

Depends on / 依赖: eq_top_iff, eq_top_iff.trans, mem_top
-/
theorem eq_top_iff' (A : Subring R) : A = ⊤ ↔ forall x : R, x in A :=
eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

/-! ## Center of a ring -/


section

variable (R)

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : Subring R
  body: { Subsemiring.center R with
    carrier := Set.center R
    neg_mem' := Set.neg_mem_center }

中文:
定义 center
  签名: : 子环 R
  定义体: { Subsemiring.center R with
    carrier := Set.center R
    neg_mem' := Set.neg_mem_center }

Depends on / 依赖: Set.center, Set.neg_mem_center, Subsemiring, Subsemiring.center, carrier, center, neg_mem, neg_mem_center
-/
def center : Subring R :=
  { Subsemiring.center R with
    carrier := Set.center R
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
theorem `center_toSubsemiring` / 定理 `center_toSubsemiring`

English:
theorem center_toSubsemiring
  statement: (center R).toSubsemiring = Subsemiring.center R
  proof: rfl

中文:
定理 center_toSubsemiring
  结论: (center R).toSubsemiring = 子半环.center R
  证明: rfl
-/
theorem center_toSubsemiring : (center R).toSubsemiring = Subsemiring.center R :=
  rfl

variable {R}

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {R : Type*} [Ring R] {z : R}
  statement: z in center R ↔ forall g, g * z = z * g
  proof: Subsemigroup.mem_center_iff

中文:
定理 mem_center_iff
  条件: {R : 类型} [环 R] {z : R}
  结论: z in center R ↔ 对任意 g, g * z = z * g
  证明: Subsemigroup.mem_center_iff

Depends on / 依赖: Subsemigroup, Subsemigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {R : Type*} [Ring R] {z : R} : z in center R ↔ forall g, g * z = z * g :=
  Subsemigroup.mem_center_iff

/--
Instance `decidableMemCenter` / 实例 `decidableMemCenter`

English:
instance decidableMemCenter
  signature: {R} [Ring R] [DecidableEq R] [Fintype R]
  body: fun _ => decidable_of_iff' _ mem_center_iff

@[simp]

中文:
实例 decidableMemCenter
  签名: {R} [环 R] [DecidableEq R] [有限类型 R]
  定义体: fun _ => decidable_of_iff' _ mem_center_iff

@[simp]

Depends on / 依赖: decidable_of_iff, mem_center_iff
-/
instance decidableMemCenter {R} [Ring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· in center R) := fun _ => decidable_of_iff' _ mem_center_iff

@[simp]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  given: (R) [CommRing R]
  statement: center R = ⊤
  proof: SetLike.coe_injective (Set.center_eq_univ R)

中文:
定理 center_eq_top
  条件: (R) [交换环 R]
  结论: center R = ⊤
  证明: SetLike.coe_injective (Set.center_eq_univ R)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top (R) [CommRing R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

/-- The center is commutative. -/
instance {R} [Ring R] : CommRing (center R) where
  __ := (center R).toRing
__ : CommSemiring (center R) := inferInstanceAs CommSemiring (Subsemiring.center R)

/--
Definition of `centerCongr` / `centerCongr` 的定义

English:
definition centerCongr
  signature: (e : R ≃+* S)
  body: NonUnitalSubsemiring.centerCongr e

中文:
定义 centerCongr
  签名: (e : R ≃+* S)
  定义体: NonUnitalSubsemiring.centerCongr e
-/
@[simps!] def centerCongr (e : R ≃+* S) : center R ≃+* center S :=
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

end

section DivisionRing

variable {K : Type u} [DivisionRing K]

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field (center K) where
  body: ⟨a⁻¹, Set.inv_mem_center a.prop⟩
mul_inv_cancel _ ha := Subtype.ext mul_inv_cancel₀ Subtype.coe_injective.ne ha
  div a b := ⟨a / b, Set.div_mem_center a.prop b.prop⟩
div_eq_mul_inv _ _ := Subtype.ext div_eq_mul_inv _ _
  inv_zero := Subtype.ext inv_zero
  -- TODO: use a nicer defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

@[simp]

中文:
实例 instField
  签名: : 域 (center K) where
  定义体: ⟨a⁻¹, Set.inv_mem_center a.prop⟩
mul_inv_cancel _ ha := Subtype.ext mul_inv_cancel₀ Subtype.coe_injective.ne ha
  div a b := ⟨a / b, Set.div_mem_center a.prop b.prop⟩
div_eq_mul_inv _ _ := Subtype.ext div_eq_mul_inv _ _
  inv_zero := Subtype.ext inv_zero
  -- TODO: use a nicer defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

@[simp]

Depends on / 依赖: Set.inv_mem_center, a.prop, inv_mem_center
-/
instance instField : Field (center K) where
  inv a := ⟨a⁻¹, Set.inv_mem_center a.prop⟩
mul_inv_cancel _ ha := Subtype.ext mul_inv_cancel₀ Subtype.coe_injective.ne ha
  div a b := ⟨a / b, Set.div_mem_center a.prop b.prop⟩
div_eq_mul_inv _ _ := Subtype.ext div_eq_mul_inv _ _
  inv_zero := Subtype.ext inv_zero
  -- TODO: use a nicer defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

@[simp]
/--
theorem `center.coe_inv` / 定理 `center.coe_inv`

English:
theorem center.coe_inv
  given: (a : center K)
  statement: ((a⁻¹ : center K) : K) = (a : K)⁻¹
  proof: rfl

@[simp]

中文:
定理 center.coe_inv
  条件: (a : center K)
  结论: ((a⁻¹ : center K) : K) = (a : K)⁻¹
  证明: rfl

@[simp]
-/
theorem center.coe_inv (a : center K) : ((a⁻¹ : center K) : K) = (a : K)⁻¹ :=
  rfl

@[simp]
/--
theorem `center.coe_div` / 定理 `center.coe_div`

English:
theorem center.coe_div
  given: (a b : center K)
  statement: ((a / b : center K) : K) = (a : K) / (b : K)
  proof: rfl

中文:
定理 center.coe_div
  条件: (a b : center K)
  结论: ((a / b : center K) : K) = (a : K) / (b : K)
  证明: rfl
-/
theorem center.coe_div (a b : center K) : ((a / b : center K) : K) = (a : K) / (b : K) :=
  rfl

end DivisionRing

section Centralizer

/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: {R} [Ring R] (s : Set R)
  body: { Subsemiring.centralizer s with neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]

中文:
定义 centralizer
  签名: {R} [环 R] (s : 集合 R)
  定义体: { Subsemiring.centralizer s with neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]

Depends on / 依赖: Set.neg_mem_centralizer, Subsemiring, Subsemiring.centralizer, centralizer, neg_mem, neg_mem_centralizer
-/
def centralizer {R} [Ring R] (s : Set R) : Subring R :=
  { Subsemiring.centralizer s with neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  given: {R} [Ring R] (s : Set R)
  statement: (centralizer s : Set R) = s.centralizer
  proof: rfl

中文:
定理 coe_centralizer
  条件: {R} [环 R] (s : 集合 R)
  结论: (centralizer s : 集合 R) = s.centralizer
  证明: rfl
-/
theorem coe_centralizer {R} [Ring R] (s : Set R) : (centralizer s : Set R) = s.centralizer :=
  rfl

/--
theorem `centralizer_toSubmonoid` / 定理 `centralizer_toSubmonoid`

English:
theorem centralizer_toSubmonoid
  given: {R} [Ring R] (s : Set R)
  proof: rfl

中文:
定理 centralizer_toSubmonoid
  条件: {R} [环 R] (s : 集合 R)
  证明: rfl
-/
theorem centralizer_toSubmonoid {R} [Ring R] (s : Set R) :
    (centralizer s).toSubmonoid = Submonoid.centralizer s :=
  rfl

/--
theorem `centralizer_toSubsemiring` / 定理 `centralizer_toSubsemiring`

English:
theorem centralizer_toSubsemiring
  given: {R} [Ring R] (s : Set R)
  proof: rfl

中文:
定理 centralizer_toSubsemiring
  条件: {R} [环 R] (s : 集合 R)
  证明: rfl
-/
theorem centralizer_toSubsemiring {R} [Ring R] (s : Set R) :
    (centralizer s).toSubsemiring = Subsemiring.centralizer s :=
  rfl

/--
theorem `centralizer_toNonUnitalSubring` / 定理 `centralizer_toNonUnitalSubring`

English:
theorem centralizer_toNonUnitalSubring
  given: {R} [Ring R] (s : Set R)
  proof: rfl

中文:
定理 centralizer_toNonUnitalSubring
  条件: {R} [环 R] (s : 集合 R)
  证明: rfl
-/
theorem centralizer_toNonUnitalSubring {R} [Ring R] (s : Set R) :
    (centralizer s).toNonUnitalSubring = NonUnitalSubring.centralizer s :=
  rfl

/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {R} [Ring R] {s : Set R} {z : R}
  proof: Iff.rfl

中文:
定理 mem_centralizer_iff
  条件: {R} [环 R] {s : 集合 R} {z : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_centralizer_iff {R} [Ring R] {s : Set R} {z : R} :
    z in centralizer s ↔ forall g in s, g * z = z * g := Iff.rfl

/--
theorem `center_le_centralizer` / 定理 `center_le_centralizer`

English:
theorem center_le_centralizer
  given: {R} [Ring R] (s)
  statement: center R <= centralizer s
  proof: s.center_subset_centralizer

中文:
定理 center_le_centralizer
  条件: {R} [环 R] (s)
  结论: center R <= centralizer s
  证明: s.center_subset_centralizer

Depends on / 依赖: center_subset_centralizer, s.center_subset_centralizer
-/
theorem center_le_centralizer {R} [Ring R] (s) : center R <= centralizer s :=
  s.center_subset_centralizer

/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: {R} [Ring R] (s t : Set R) (h : s subseteq t)
  statement: centralizer t <= centralizer s
  proof: Set.centralizer_subset h

@[simp]

中文:
定理 centralizer_le
  条件: {R} [环 R] (s t : 集合 R) (h : s subseteq t)
  结论: centralizer t <= centralizer s
  证明: Set.centralizer_subset h

@[simp]

Depends on / 依赖: Set.centralizer_subset, centralizer_subset
-/
theorem centralizer_le {R} [Ring R] (s t : Set R) (h : s subseteq t) : centralizer t <= centralizer s :=
  Set.centralizer_subset h

@[simp]
/--
theorem `centralizer_eq_top_iff_subset` / 定理 `centralizer_eq_top_iff_subset`

English:
theorem centralizer_eq_top_iff_subset
  given: {R} [Ring R] {s : Set R}
  statement: centralizer s = ⊤ ↔ s subseteq center R
  proof: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]

中文:
定理 centralizer_eq_top_iff_subset
  条件: {R} [环 R] {s : 集合 R}
  结论: centralizer s = ⊤ ↔ s subseteq center R
  证明: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]

Depends on / 依赖: Set.centralizer_eq_top_iff_subset, SetLike, SetLike.ext, _iff, _iff.trans, centralizer_eq_top_iff_subset
-/
theorem centralizer_eq_top_iff_subset {R} [Ring R] {s : Set R} : centralizer s = ⊤ ↔ s subseteq center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  given: {R} [Ring R]
  statement: centralizer Set.univ = center R
  proof: SetLike.ext' (Set.centralizer_univ R)

中文:
定理 centralizer_univ
  条件: {R} [环 R]
  结论: centralizer 集合.univ = center R
  证明: SetLike.ext' (Set.centralizer_univ R)

Depends on / 依赖: Set.centralizer_univ, SetLike, SetLike.ext, centralizer_univ
-/
theorem centralizer_univ {R} [Ring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

/-! ## subring closure of a subset -/


/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Set R)
  body: sInf { S | s subseteq S }

中文:
定义 closure
  签名: (s : 集合 R)
  定义体: sInf { S | s subseteq S }

Depends on / 依赖: subseteq
-/
def closure (s : Set R) : Subring R :=
  sInf { S | s subseteq S }

/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {x : R} {s : Set R}
  statement: x in closure s ↔ forall S : Subring R, s subseteq S -> x in S
  proof: mem_sInf

中文:
定理 mem_closure
  条件: {x : R} {s : 集合 R}
  结论: x in closure s ↔ 对任意 S : 子环 R, s subseteq S -> x in S
  证明: mem_sInf

Depends on / 依赖: mem_sInf
-/
theorem mem_closure {x : R} {s : Set R} : x in closure s ↔ forall S : Subring R, s subseteq S -> x in S :=
  mem_sInf

/-- The subring generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `subset_closure` / 定理 `subset_closure`

English:
theorem subset_closure
  given: {s : Set R}
  statement: s subseteq closure s
  proof: fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]

中文:
定理 subset_closure
  条件: {s : 集合 R}
  结论: s subseteq closure s
  证明: fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: mem_closure
-/
theorem subset_closure {s : Set R} : s subseteq closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

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

/-- A subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
/--
theorem `closure_le` / 定理 `closure_le`

English:
theorem closure_le
  given: {s : Set R} {t : Subring R}
  statement: closure s <= t ↔ s subseteq t
  proof: ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

中文:
定理 closure_le
  条件: {s : 集合 R} {t : 子环 R}
  结论: closure s <= t ↔ s subseteq t
  证明: ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

Depends on / 依赖: Set.Subset.trans, Subset, sInf_le, subset_closure
-/
theorem closure_le {s : Set R} {t : Subring R} : closure s <= t ↔ s subseteq t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- Subring closure of a set is monotone in its argument: if `s ⊆ t`,
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
  given: {s : Set R} {t : Subring R} (h₁ : s subseteq t) (h₂ : t <= closure s)
  proof: le_antisymm (closure_le.2 h₁) h₂

中文:
定理 closure_eq_of_le
  条件: {s : 集合 R} {t : 子环 R} (h₁ : s subseteq t) (h₂ : t <= closure s)
  证明: le_antisymm (closure_le.2 h₁) h₂

Depends on / 依赖: NatIso, NatIso.isIso_app_of_isIso, PresheafedSpace, PresheafedSpace.c_isIso_of_iso, c_isIso_of_iso, closure_le, f.toPshHom, isIso_app_of_isIso, le_antisymm, toPshHom
-/
theorem closure_eq_of_le {s : Set R} {t : Subring R} (h₁ : s subseteq t) (h₂ : t <= closure s) :
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
  proof: let K : Subring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ => ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩
      one_mem' := ⟨_, one⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (t := K)

中文:
定理 closure_induction
  结论: {s : 集合 R} {p : (x : R) -> x in closure s -> 命题}
  证明: let K : Subring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ => ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩
      one_mem' := ⟨_, one⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (t := K)

Depends on / 依赖: Subring, add_mem, carrier, closure_le, mul_mem, neg_mem, one_mem, subset_closure, zero_mem
-/
theorem closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop}
    (mem : forall (x) (hx : x in s), p x (subset_closure hx))
    (zero : p 0 (zero_mem _)) (one : p 1 (one_mem _))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (neg : forall x hx, p x hx -> p (-x) (neg_mem hx))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    {x} (hx : x in closure s) : p x hx :=
  let K : Subring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ => ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩
      one_mem' := ⟨_, one⟩ }
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
    | one => exact one_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | neg _ _ h => exact neg_left _ _ _ _ h
  | zero => exact zero_right x hx
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | neg _ _ h => exact neg_right _ _ _ _ h

中文:
定理 closure_induction₂
  结论: {s : 集合 R} {p : (x y : R) -> x in closure s -> y in closure s -> 命题}
  证明: by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | one => exact one_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | neg _ _ h => exact neg_left _ _ _ _ h
  | zero => exact zero_right x hx
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | neg _ _ h => exact neg_right _ _ _ _ h

Depends on / 依赖: add_left, add_r, closure_induction, mem_mem, mul_left, mul_right, neg_left, one_left, one_right, zero_left, zero_right
-/
theorem closure_induction₂ {s : Set R} {p : (x y : R) -> x in closure s -> y in closure s -> Prop}
    (mem_mem : forall (x) (y) (hx : x in s) (hy : y in s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : forall x hx, p 0 x (zero_mem _) hx) (zero_right : forall x hx, p x 0 hx (zero_mem _))
    (one_left : forall x hx, p 1 x (one_mem _) hx) (one_right : forall x hx, p x 1 hx (one_mem _))
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
    | one => exact one_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | neg _ _ h => exact neg_left _ _ _ _ h
  | zero => exact zero_right x hx
  | one => exact one_right x hx
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
    | mem _ hx => exact AddSubgroup.subset_closure (Submonoid.subset_closure hx)
    | zero => exact zero_mem _
    | one => exact AddSubgroup.subset_closure (one_mem _)
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg _ _ hx => exact neg_mem hx
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
      | mem x hx =>
        induction hx using Submonoid.closure_induction with
        | mem _ h => exact subset_closure h
        | one => exact one_mem _
        | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
      | zero => exact zero_mem _
      | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
      | neg _ _ h => exact neg_mem h⟩

中文:
定理 mem_closure_iff
  条件: {s : 集合 R} {x}
  证明: ⟨fun h => by
    induction h using closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Submonoid.subset_closure hx)
    | zero => exact zero_mem _
    | one => exact AddSubgroup.subset_closure (one_mem _)
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg _ _ hx => exact neg_mem hx
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
      | mem x hx =>
        induction hx using Submonoid.closure_induction with
        | mem _ h => exact subset_closure h
        | one => exact one_mem _
        | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
      | zero => exact zero_mem _
      | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
      | neg _ _ h => exact neg_mem h⟩

Depends on / 依赖: AddSubgroup, AddSubgroup.closure_induction, AddSubgroup.subset_closure, Submonoid, Submonoid.subset_closure, add_mem, closure_induction, mul_mem, neg_mem, one_mem, subset_closure, zero_left, zero_mem, zero_right
-/
theorem mem_closure_iff {s : Set R} {x} :
    x in closure s ↔ x in AddSubgroup.closure (Submonoid.closure s : Set R) :=
  ⟨fun h => by
    induction h using closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Submonoid.subset_closure hx)
    | zero => exact zero_mem _
    | one => exact AddSubgroup.subset_closure (one_mem _)
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg _ _ hx => exact neg_mem hx
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
      | mem x hx =>
        induction hx using Submonoid.closure_induction with
        | mem _ h => exact subset_closure h
        | one => exact one_mem _
        | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
      | zero => exact zero_mem _
      | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
      | neg _ _ h => exact neg_mem h⟩

/--
lemma `closure_le_centralizer_centralizer` / 引理 `closure_le_centralizer_centralizer`

English:
lemma closure_le_centralizer_centralizer
  given: {R} [Ring R] (s : Set R)
  proof: closure_le.mpr Set.subset_centralizer_centralizer

中文:
引理 closure_le_centralizer_centralizer
  条件: {R} [环 R] (s : 集合 R)
  证明: closure_le.mpr Set.subset_centralizer_centralizer

Depends on / 依赖: Set.subset_centralizer_centralizer, closure_le, closure_le.mpr, subset_centralizer_centralizer
-/
lemma closure_le_centralizer_centralizer {R} [Ring R] (s : Set R) :
    closure s <= centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/--
theorem `isMulCommutative_closure` / 定理 `isMulCommutative_closure`

English:
theorem isMulCommutative_closure
  statement: {R} [Ring R] {s : Set R}
  proof: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

中文:
定理 isMulCommutative_closure
  结论: {R} [环 R] {s : 集合 R}
  证明: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, centralizer_centralizer_comm_of_comm, closure_le_centralizer_centralizer, of_setLike_mul_comm
-/
theorem isMulCommutative_closure {R} [Ring R] {s : Set R}
    (hcomm : forall x in s, forall y in s, x * y = y * x) :
    IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all elements of `s : Set R` commute pairwise, then `closure s` is a commutative ring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
/--
Definition of `closureCommRingOfComm` / `closureCommRingOfComm` 的定义

English:
abbreviation closureCommRingOfComm
  signature: {R} [Ring R] {s : Set R} (hcomm : forall x in s, forall y in s, x * y = y * x)
  body: have := isMulCommutative_closure hcomm
  inferInstance

中文:
缩写 closureCommRingOfComm
  签名: {R} [环 R] {s : 集合 R} (hcomm : 对任意 x in s, 对任意 y in s, x * y = y * x)
  定义体: have := isMulCommutative_closure hcomm
  inferInstance

Depends on / 依赖: isMulCommutative_closure
-/
abbrev closureCommRingOfComm {R} [Ring R] {s : Set R} (hcomm : forall x in s, forall y in s, x * y = y * x) :
    CommRing (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance

/--
Instance `instIsMulCommutative_closure` / 实例 `instIsMulCommutative_closure`

English:
instance instIsMulCommutative_closure
  signature: {S R : Type*} [Ring R] [SetLike S R] [MulMemClass S R] (s : S)
  body: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

中文:
实例 instIsMulCommutative_closure
  签名: {S R : 类型} [环 R] [集合状 S R] [MulMem类 S R] (s : S)
  定义体: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

Depends on / 依赖: isMulCommutative_closure, setLike_mul_comm
-/
instance instIsMulCommutative_closure {S R : Type*} [Ring R] [SetLike S R] [MulMemClass S R] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set R)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

/--
theorem `exists_list_of_mem_closure` / 定理 `exists_list_of_mem_closure`

English:
theorem exists_list_of_mem_closure
  given: {R} [Ring R] {s : Set R} {x : R} (hx : x in closure s)
  proof: by
  rw [mem_closure_iff] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem _ hx =>
    obtain ⟨l, hl, h⟩ := Submonoid.exists_list_of_mem_closure hx
    exact ⟨[l], by simp_all⟩
  | zero => exact ⟨[], List.forall_mem_nil _, rfl⟩
  | add _ _ _ _ hL hM =>
    obtain ⟨⟨L, HL1, HL2⟩, ⟨M, HM1, HM2⟩⟩ := And.intro hL hM
    exact ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
      rw [List.map_append]; rw [List.sum_append]; rw [HL2]; rw [HM2]⟩
  | neg _ _ hL =>
    obtain ⟨L, hL⟩ := hL
    exact ⟨L.map (List.cons (-1)),
      List.forall_mem_map.2 fun j hj => List.forall_mem_cons.2 ⟨Or.inr rfl, hL.1 j hj⟩,
      hL.2 ▸
        List.recOn L (by simp)
          (by simp +contextual [List.map_cons, add_comm])⟩

中文:
定理 存在_list_of_mem_closure
  条件: {R} [环 R] {s : 集合 R} {x : R} (hx : x in closure s)
  证明: by
  rw [mem_closure_iff] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem _ hx =>
    obtain ⟨l, hl, h⟩ := Submonoid.exists_list_of_mem_closure hx
    exact ⟨[l], by simp_all⟩
  | zero => exact ⟨[], List.forall_mem_nil _, rfl⟩
  | add _ _ _ _ hL hM =>
    obtain ⟨⟨L, HL1, HL2⟩, ⟨M, HM1, HM2⟩⟩ := And.intro hL hM
    exact ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
      rw [List.map_append]; rw [List.sum_append]; rw [HL2]; rw [HM2]⟩
  | neg _ _ hL =>
    obtain ⟨L, hL⟩ := hL
    exact ⟨L.map (List.cons (-1)),
      List.forall_mem_map.2 fun j hj => List.forall_mem_cons.2 ⟨Or.inr rfl, hL.1 j hj⟩,
      hL.2 ▸
        List.recOn L (by simp)
          (by simp +contextual [List.map_cons, add_comm])⟩

Depends on / 依赖: AddSubgroup, AddSubgroup.closure_induction, And.intro, L.map, List.cons, List.forall_mem_append, List.forall_mem_nil, List.map_append, List.sum_append, Submonoid, Submonoid.exists_list_of_mem_closure, closure_induction, exists_list_of_mem_closure, forall_mem_append, forall_mem_nil, map_append, mem_closure_iff, sum_append
-/
theorem exists_list_of_mem_closure {R} [Ring R] {s : Set R} {x : R} (hx : x in closure s) :
    exists L : List (List R), (forall t in L, forall y in t, y in s ∨ y = (-1 : R)) ∧ (L.map List.prod).sum = x := by
  rw [mem_closure_iff] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem _ hx =>
    obtain ⟨l, hl, h⟩ := Submonoid.exists_list_of_mem_closure hx
    exact ⟨[l], by simp_all⟩
  | zero => exact ⟨[], List.forall_mem_nil _, rfl⟩
  | add _ _ _ _ hL hM =>
    obtain ⟨⟨L, HL1, HL2⟩, ⟨M, HM1, HM2⟩⟩ := And.intro hL hM
    exact ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
      rw [List.map_append]; rw [List.sum_append]; rw [HL2]; rw [HM2]⟩
  | neg _ _ hL =>
    obtain ⟨L, hL⟩ := hL
    exact ⟨L.map (List.cons (-1)),
      List.forall_mem_map.2 fun j hj => List.forall_mem_cons.2 ⟨Or.inr rfl, hL.1 j hj⟩,
      hL.2 ▸
        List.recOn L (by simp)
          (by simp +contextual [List.map_cons, add_comm])⟩

variable (R) in
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (@closure R _) (↑) where
  body: closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

中文:
定义 gi
  签名: : Galois嵌入 (@closure R _) (↑) where
  定义体: closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl
-/
protected def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

/-- Closure of a subring `S` equals `S`. -/
@[simp]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  given: (s : Subring R)
  statement: closure (s : Set R) = s
  proof: (Subring.gi R).l_u_eq s

@[simp]

中文:
定理 closure_eq
  条件: (s : 子环 R)
  结论: closure (s : 集合 R) = s
  证明: (Subring.gi R).l_u_eq s

@[simp]

Depends on / 依赖: Subring, Subring.gi, l_u_eq
-/
theorem closure_eq (s : Subring R) : closure (s : Set R) = s :=
  (Subring.gi R).l_u_eq s

@[simp]
/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure (∅ : Set R) = ⊥
  proof: (Subring.gi R).gc.l_bot

@[simp]

中文:
定理 closure_empty
  结论: closure (∅ : 集合 R) = ⊥
  证明: (Subring.gi R).gc.l_bot

@[simp]

Depends on / 依赖: Scheme, Scheme.Spec.map, Subring, Subring.gi, f.op, gc.l_bot, l_bot
-/
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subring.gi R).gc.l_bot

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

Depends on / 依赖: closure_eq, coe_top
-/
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

/--
theorem `closure_union` / 定理 `closure_union`

English:
theorem closure_union
  given: (s t : Set R)
  statement: closure (s union t) = closure s ⊔ closure t
  proof: (Subring.gi R).gc.l_sup

中文:
定理 closure_union
  条件: (s t : 集合 R)
  结论: closure (s union t) = closure s ⊔ closure t
  证明: (Subring.gi R).gc.l_sup

Depends on / 依赖: Subring, Subring.gi, gc.l_sup, l_sup
-/
theorem closure_union (s t : Set R) : closure (s union t) = closure s ⊔ closure t :=
  (Subring.gi R).gc.l_sup

/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: {ι} (s : ι -> Set R)
  statement: closure (⋃ i, s i) = ⨆ i, closure (s i)
  proof: (Subring.gi R).gc.l_iSup

中文:
定理 closure_iUnion
  条件: {ι} (s : ι -> 集合 R)
  结论: closure (⋃ i, s i) = ⨆ i, closure (s i)
  证明: (Subring.gi R).gc.l_iSup

Depends on / 依赖: Subring, Subring.gi, gc.l_iSup, l_iSup
-/
theorem closure_iUnion {ι} (s : ι -> Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subring.gi R).gc.l_iSup

/--
theorem `closure_sUnion` / 定理 `closure_sUnion`

English:
theorem closure_sUnion
  given: (s : Set (Set R))
  statement: closure (⋃₀ s) = ⨆ t in s, closure t
  proof: (Subring.gi R).gc.l_sSup

@[simp]

中文:
定理 closure_sUnion
  条件: (s : 集合 (集合 R))
  结论: closure (⋃₀ s) = ⨆ t in s, closure t
  证明: (Subring.gi R).gc.l_sSup

@[simp]

Depends on / 依赖: Subring, Subring.gi, gc.l_sSup, l_sSup
-/
theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t in s, closure t :=
  (Subring.gi R).gc.l_sSup

@[simp]
/--
theorem `closure_singleton_intCast` / 定理 `closure_singleton_intCast`

English:
theorem closure_singleton_intCast
  given: (n : Int)
  statement: closure {(n : R)} = ⊥
  proof: bot_unique closure_le.2 Set.singleton_subset_iff.mpr intCast_mem _ _

@[simp]

中文:
定理 closure_singleton_intCast
  条件: (n : 整数)
  结论: closure {(n : R)} = ⊥
  证明: bot_unique closure_le.2 Set.singleton_subset_iff.mpr intCast_mem _ _

@[simp]

Depends on / 依赖: Set.singleton_subset_iff.mpr, bot_unique, closure_le, intCast_mem, singleton_subset_iff
-/
theorem closure_singleton_intCast (n : Int) : closure {(n : R)} = ⊥ :=
bot_unique closure_le.2 Set.singleton_subset_iff.mpr intCast_mem _ _

@[simp]
/--
theorem `closure_singleton_natCast` / 定理 `closure_singleton_natCast`

English:
theorem closure_singleton_natCast
  given: (n : Nat)
  statement: closure {(n : R)} = ⊥
  proof: mod_cast closure_singleton_intCast n

@[simp]

中文:
定理 closure_singleton_natCast
  条件: (n : 自然数)
  结论: closure {(n : R)} = ⊥
  证明: mod_cast closure_singleton_intCast n

@[simp]

Depends on / 依赖: closure_singleton_intCast, mod_cast
-/
theorem closure_singleton_natCast (n : Nat) : closure {(n : R)} = ⊥ :=
  mod_cast closure_singleton_intCast n

@[simp]
/--
theorem `closure_singleton_zero` / 定理 `closure_singleton_zero`

English:
theorem closure_singleton_zero
  statement: closure {(0 : R)} = ⊥
  proof: mod_cast closure_singleton_natCast 0

@[simp]

中文:
定理 closure_singleton_zero
  结论: closure {(0 : R)} = ⊥
  证明: mod_cast closure_singleton_natCast 0

@[simp]

Depends on / 依赖: closure_singleton_natCast, mod_cast
-/
theorem closure_singleton_zero : closure {(0 : R)} = ⊥ := mod_cast closure_singleton_natCast 0

@[simp]
/--
theorem `closure_singleton_one` / 定理 `closure_singleton_one`

English:
theorem closure_singleton_one
  statement: closure {(1 : R)} = ⊥
  proof: mod_cast closure_singleton_natCast 1

@[simp]

中文:
定理 closure_singleton_one
  结论: closure {(1 : R)} = ⊥
  证明: mod_cast closure_singleton_natCast 1

@[simp]

Depends on / 依赖: closure_singleton_natCast, mod_cast
-/
theorem closure_singleton_one : closure {(1 : R)} = ⊥ := mod_cast closure_singleton_natCast 1

@[simp]
/--
theorem `closure_insert_intCast` / 定理 `closure_insert_intCast`

English:
theorem closure_insert_intCast
  given: (n : Int) (s : Set R)
  statement: closure (insert (n : R) s) = closure s
  proof: by
  rw [Set.insert_eq]; rw [closure_union]
  simp

@[simp]

中文:
定理 closure_insert_intCast
  条件: (n : 整数) (s : 集合 R)
  结论: closure (insert (n : R) s) = closure s
  证明: by
  rw [Set.insert_eq]; rw [closure_union]
  simp

@[simp]

Depends on / 依赖: Set.insert_eq, closure_union, insert_eq
-/
theorem closure_insert_intCast (n : Int) (s : Set R) : closure (insert (n : R) s) = closure s := by
  rw [Set.insert_eq]; rw [closure_union]
  simp

@[simp]
/--
theorem `closure_insert_natCast` / 定理 `closure_insert_natCast`

English:
theorem closure_insert_natCast
  given: (n : Nat) (s : Set R)
  statement: closure (insert (n : R) s) = closure s
  proof: mod_cast closure_insert_intCast n s

@[simp]

中文:
定理 closure_insert_natCast
  条件: (n : 自然数) (s : 集合 R)
  结论: closure (insert (n : R) s) = closure s
  证明: mod_cast closure_insert_intCast n s

@[simp]

Depends on / 依赖: closure_insert_intCast, mod_cast
-/
theorem closure_insert_natCast (n : Nat) (s : Set R) : closure (insert (n : R) s) = closure s :=
  mod_cast closure_insert_intCast n s

@[simp]
/--
theorem `closure_insert_zero` / 定理 `closure_insert_zero`

English:
theorem closure_insert_zero
  given: (s : Set R)
  statement: closure (insert 0 s) = closure s
  proof: mod_cast closure_insert_natCast 0 s

@[simp]

中文:
定理 closure_insert_zero
  条件: (s : 集合 R)
  结论: closure (insert 0 s) = closure s
  证明: mod_cast closure_insert_natCast 0 s

@[simp]

Depends on / 依赖: Nonempty, PrimeSpectrum, closure_insert_natCast, mod_cast
-/
theorem closure_insert_zero (s : Set R) : closure (insert 0 s) = closure s :=
  mod_cast closure_insert_natCast 0 s

@[simp]
/--
theorem `closure_insert_one` / 定理 `closure_insert_one`

English:
theorem closure_insert_one
  given: (s : Set R)
  statement: closure (insert 1 s) = closure s
  proof: mod_cast closure_insert_natCast 1 s

中文:
定理 closure_insert_one
  条件: (s : 集合 R)
  结论: closure (insert 1 s) = closure s
  证明: mod_cast closure_insert_natCast 1 s

Depends on / 依赖: closure_insert_natCast, mod_cast
-/
theorem closure_insert_one (s : Set R) : closure (insert 1 s) = closure s :=
  mod_cast closure_insert_natCast 1 s

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (s t : Subring R) (f : R ->+* S)
  statement: (s ⊔ t).map f = s.map f ⊔ t.map f
  proof: (gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (s t : 子环 R) (f : R ->+* S)
  结论: (s ⊔ t).map f = s.map f ⊔ t.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (s t : Subring R) (f : R ->+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : R ->+* S) (s : ι -> Subring R)
  proof: (gc_map_comap f).l_iSup

中文:
定理 map_iSup
  条件: {ι : 类型层*} (f : R ->+* S) (s : ι -> 子环 R)
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : R ->+* S) (s : ι -> Subring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (s t : Subring R) (f : R ->+* S) (hf : Function.Injective f)
  proof: SetLike.coe_injective (Set.image_inter hf)

中文:
定理 map_inf
  条件: (s t : 子环 R) (f : R ->+* S) (hf : 函数.单射 f)
  证明: SetLike.coe_injective (Set.image_inter hf)

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (s t : Subring R) (f : R ->+* S) (hf : Function.Injective f) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter hf)

/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  statement: {ι : Sort*} [Nonempty ι] (f : R ->+* S) (hf : Function.Injective f)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

中文:
定理 map_iInf
  结论: {ι : 类型层*} [非空 ι] (f : R ->+* S) (hf : 函数.单射 f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : R ->+* S) (hf : Function.Injective f)
    (s : ι -> Subring R) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (s t : Subring S) (f : R ->+* S)
  statement: (s ⊓ t).comap f = s.comap f ⊓ t.comap f
  proof: (gc_map_comap f).u_inf

中文:
定理 comap_inf
  条件: (s t : 子环 S) (f : R ->+* S)
  结论: (s ⊓ t).comap f = s.comap f ⊓ t.comap f
  证明: (gc_map_comap f).u_inf

Depends on / 依赖: gc_map_comap, u_inf
-/
theorem comap_inf (s t : Subring S) (f : R ->+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : R ->+* S) (s : ι -> Subring S)
  proof: (gc_map_comap f).u_iInf

@[simp]

中文:
定理 comap_iInf
  条件: {ι : 类型层*} (f : R ->+* S) (s : ι -> 子环 S)
  证明: (gc_map_comap f).u_iInf

@[simp]

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : R ->+* S) (s : ι -> Subring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : R ->+* S)
  statement: (⊥ : Subring R).map f = ⊥
  proof: (gc_map_comap f).l_bot

@[simp]

中文:
定理 map_bot
  条件: (f : R ->+* S)
  结论: (⊥ : 子环 R).map f = ⊥
  证明: (gc_map_comap f).l_bot

@[simp]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : R ->+* S) : (⊥ : Subring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : R ->+* S)
  statement: (⊤ : Subring S).comap f = ⊤
  proof: (gc_map_comap f).u_top

中文:
定理 comap_top
  条件: (f : R ->+* S)
  结论: (⊤ : 子环 S).comap f = ⊤
  证明: (gc_map_comap f).u_top

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top (f : R ->+* S) : (⊤ : Subring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (s : Subring R) (t : Subring S)
  body: { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubgroup.prod t.toAddSubgroup with carrier := s ×ˢ t }

@[norm_cast]

中文:
定义 乘积
  签名: (s : 子环 R) (t : 子环 S)
  定义体: { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubgroup.prod t.toAddSubgroup with carrier := s ×ˢ t }

@[norm_cast]

Depends on / 依赖: carrier, s.toAddSubgroup.prod, s.toSubmonoid.prod, t.toAddSubgroup, t.toSubmonoid, toAddSubgroup, toSubmonoid
-/
def prod (s : Subring R) (t : Subring S) : Subring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubgroup.prod t.toAddSubgroup with carrier := s ×ˢ t }

@[norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : Subring R) (t : Subring S)
  proof: rfl

中文:
定理 coe_prod
  条件: (s : 子环 R) (t : 子环 S)
  证明: rfl
-/
theorem coe_prod (s : Subring R) (t : Subring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl

/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : Subring R} {t : Subring S} {p : R × S}
  statement: p in s.prod t ↔ p.1 in s ∧ p.2 in t
  proof: Iff.rfl

@[gcongr, mono]

中文:
定理 mem_prod
  条件: {s : 子环 R} {t : 子环 S} {p : R × S}
  结论: p in s.乘积 t ↔ p.1 in s ∧ p.2 in t
  证明: Iff.rfl

@[gcongr, mono]

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : Subring R} {t : Subring S} {p : R × S} : p in s.prod t ↔ p.1 in s ∧ p.2 in t :=
  Iff.rfl

@[gcongr, mono]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: ⦃s₁ s₂
  statement: Subring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : Subring S⦄ (ht : t₁ <= t₂) :
  proof: Set.prod_mono hs ht

中文:
定理 prod_mono
  条件: ⦃s₁ s₂
  结论: 子环 R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : 子环 S⦄ (ht : t₁ <= t₂) :
  证明: Set.prod_mono hs ht

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : Subring S⦄ (ht : t₁ <= t₂) :
    s₁.prod t₁ <= s₂.prod t₂ :=
  Set.prod_mono hs ht

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  given: (s : Subring R)
  statement: Monotone fun t : Subring S => s.prod t
  proof: prod_mono (le_refl s)

中文:
定理 prod_mono_right
  条件: (s : 子环 R)
  结论: 递增 fun t : 子环 S => s.乘积 t
  证明: prod_mono (le_refl s)

Depends on / 依赖: le_refl, prod_mono
-/
theorem prod_mono_right (s : Subring R) : Monotone fun t : Subring S => s.prod t :=
  prod_mono (le_refl s)

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  given: (t : Subring S)
  statement: Monotone fun s : Subring R => s.prod t
  proof: fun _ _ hs =>
  prod_mono hs (le_refl t)

中文:
定理 prod_mono_left
  条件: (t : 子环 S)
  结论: 递增 fun s : 子环 R => s.乘积 t
  证明: fun _ _ hs =>
  prod_mono hs (le_refl t)
-/
theorem prod_mono_left (t : Subring S) : Monotone fun s : Subring R => s.prod t := fun _ _ hs =>
  prod_mono hs (le_refl t)

/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  given: (s : Subring R)
  statement: s.prod (⊤ : Subring S) = s.comap (RingHom.fst R S)
  proof: ext fun x => by simp [mem_prod]

中文:
定理 prod_top
  条件: (s : 子环 R)
  结论: s.乘积 (⊤ : 子环 S) = s.comap (环态射.fst R S)
  证明: ext fun x => by simp [mem_prod]

Depends on / 依赖: PrimeSpectrum, Unique, mem_prod
-/
theorem prod_top (s : Subring R) : s.prod (⊤ : Subring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by simp [mem_prod]

/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  given: (s : Subring S)
  statement: (⊤ : Subring R).prod s = s.comap (RingHom.snd R S)
  proof: ext fun x => by simp [mem_prod]

@[simp]

中文:
定理 top_prod
  条件: (s : 子环 S)
  结论: (⊤ : 子环 R).乘积 s = s.comap (环态射.snd R S)
  证明: ext fun x => by simp [mem_prod]

@[simp]

Depends on / 依赖: mem_prod
-/
theorem top_prod (s : Subring S) : (⊤ : Subring R).prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
/--
theorem `top_prod_top` / 定理 `top_prod_top`

English:
theorem top_prod_top
  statement: (⊤ : Subring R).prod (⊤ : Subring S) = ⊤
  proof: (top_prod _).trans comap_top _

中文:
定理 top_prod_top
  结论: (⊤ : 子环 R).乘积 (⊤ : 子环 S) = ⊤
  证明: (top_prod _).trans comap_top _

Depends on / 依赖: comap_top, top_prod
-/
theorem top_prod_top : (⊤ : Subring R).prod (⊤ : Subring S) = ⊤ :=
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
  signature: (s : Subring R) (t : Subring S)
  body: { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _x _y => rfl
    map_add' := fun _x _y => rfl }

中文:
定义 prodEquiv
  签名: (s : 子环 R) (t : 子环 S)
  定义体: { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _x _y => rfl
    map_add' := fun _x _y => rfl }

Depends on / 依赖: Equiv.Set.prod, map_add, map_mul
-/
def prodEquiv (s : Subring R) (t : Subring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _x _y => rfl
    map_add' := fun _x _y => rfl }

/--
theorem `mem_iSup_of_directed` / 定理 `mem_iSup_of_directed`

English:
theorem mem_iSup_of_directed
  statement: {ι} [hι : Nonempty ι] {S : ι -> Subring R} (hS : Directed (· <= ·) S)
  proof: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : Subring R :=
    Subring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid) (⨆ i, (S i).toAddSubgroup)
      (Submonoid.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U] using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩

中文:
定理 mem_iSup_of_directed
  结论: {ι} [hι : 非空 ι] {S : ι -> 子环 R} (hS : Directed (· <= ·) S)
  证明: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : Subring R :=
    Subring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid) (⨆ i, (S i).toAddSubgroup)
      (Submonoid.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U] using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_iSup_of_directed, Set.mem_iUnion, Submonoid, Submonoid.coe_iSup_of_directed, Subring, Subring.mk, coe_iSup_of_directed, iSup_le, le_iSup, mem_iUnion, toAddSubgroup, toSubmonoid
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subring R} (hS : Directed (· <= ·) S)
    {x : R} : (x in ⨆ i, S i) ↔ exists i, x in S i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : Subring R :=
    Subring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid) (⨆ i, (S i).toAddSubgroup)
      (Submonoid.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U] using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  given: {ι} [hι : Nonempty ι] {S : ι -> Subring R} (hS : Directed (· <= ·) S)
  proof: Set.ext fun x => by simp [mem_iSup_of_directed hS]

中文:
定理 coe_iSup_of_directed
  条件: {ι} [hι : 非空 ι] {S : ι -> 子环 R} (hS : Directed (· <= ·) S)
  证明: Set.ext fun x => by simp [mem_iSup_of_directed hS]

Depends on / 依赖: Set.ext, mem_iSup_of_directed
-/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subring R} (hS : Directed (· <= ·) S) :
    ((⨆ i, S i : Subring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]

/--
theorem `mem_sSup_of_directedOn` / 定理 `mem_sSup_of_directedOn`

English:
theorem mem_sSup_of_directedOn
  statement: {S : Set (Subring R)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S)
  proof: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

中文:
定理 mem_sSup_of_directedOn
  结论: {S : 集合 (子环 R)} (Sne : S.非空) (hS : DirectedOn (· <= ·) S)
  证明: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

Depends on / 依赖: Nonempty, SetCoe, SetCoe.exists, Sne.to_subtype, directed_val, exists_prop, hS.directed_val, mem_iSup_of_directed, sSup_eq_iSup, to_subtype
-/
theorem mem_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S)
    {x : R} : x in sSup S ↔ exists s in S, x in s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

/--
theorem `coe_sSup_of_directedOn` / 定理 `coe_sSup_of_directedOn`

English:
theorem coe_sSup_of_directedOn
  statement: {S : Set (Subring R)} (Sne : S.Nonempty)
  proof: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

中文:
定理 coe_sSup_of_directedOn
  结论: {S : 集合 (子环 R)} (Sne : S.非空)
  证明: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

Depends on / 依赖: Set.ext, mem_sSup_of_directedOn
-/
theorem coe_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) : (↑(sSup S) : Set R) = ⋃ s in S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

/--
theorem `isMulCommutative_iSup` / 定理 `isMulCommutative_iSup`

English:
theorem isMulCommutative_iSup
  statement: {ι : Sort*} [Nonempty ι] {S : ι -> Subring R}
  proof: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using! Subsemigroup.isMulCommutative_iSup dir

中文:
定理 isMulCommutative_iSup
  结论: {ι : 类型层*} [非空 ι] {S : ι -> 子环 R}
  证明: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using! Subsemigroup.isMulCommutative_iSup dir

Depends on / 依赖: SetLike, SetLike.mem_coe, Subsemigroup, Subsemigroup.coe_iSup_of_directed, Subsemigroup.isMulCommutative_iSup, coe_iSup_of_directed, isMulCommutative_iSup, isMulCommutative_iff, mem_coe
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι -> Subring R}
    [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) :
    IsMulCommutative (⨆ i, S i : Subring R) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using! Subsemigroup.isMulCommutative_iSup dir

/--
Instance `instIsMulCommutative_iSup` / 实例 `instIsMulCommutative_iSup`

English:
instance instIsMulCommutative_iSup
  signature: {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
  body: Subring.isMulCommutative_iSup S.monotone.directed_le

中文:
实例 instIsMulCommutative_iSup
  签名: {ι : 类型} [非空 ι] [预序 ι] [IsDirectedOrder ι]
  定义体: Subring.isMulCommutative_iSup S.monotone.directed_le

Depends on / 依赖: S.monotone.directed_le, Subring, Subring.isMulCommutative_iSup, directed_le, isMulCommutative_iSup, monotone
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι ->o Subring R} [hS : forall i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subring R) :=
  Subring.isMulCommutative_iSup S.monotone.directed_le

/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {f : R ≃+* S} {K : Subring R} {x : S}
  proof: @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

中文:
定理 mem_map_equiv
  条件: {f : R ≃+* S} {K : 子环 R} {x : S}
  证明: @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

Depends on / 依赖: Set.mem_image_equiv, f.toEquiv, mem_image_equiv, toEquiv
-/
theorem mem_map_equiv {f : R ≃+* S} {K : Subring R} {x : S} :
    x in K.map (f : R ->+* S) ↔ f.symm x in K :=
  @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x

/--
theorem `map_equiv_eq_comap_symm` / 定理 `map_equiv_eq_comap_symm`

English:
theorem map_equiv_eq_comap_symm
  given: (f : R ≃+* S) (K : Subring R)
  proof: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

中文:
定理 map_equiv_eq_comap_symm
  条件: (f : R ≃+* S) (K : 子环 R)
  证明: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subring R) :
    K.map (f : R ->+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

/--
theorem `comap_equiv_eq_map_symm` / 定理 `comap_equiv_eq_map_symm`

English:
theorem comap_equiv_eq_map_symm
  given: (f : R ≃+* S) (K : Subring S)
  proof: (map_equiv_eq_comap_symm f.symm K).symm

中文:
定理 comap_equiv_eq_map_symm
  条件: (f : R ≃+* S) (K : 子环 S)
  证明: (map_equiv_eq_comap_symm f.symm K).symm

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subring S) :
    K.comap (f : R ->+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subring

namespace RingHom

variable {s : Subring R}

open Subring

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
definition rangeRestrict
  signature: (f : R ->+* S)
  body: f.codRestrict f.range fun x => ⟨x, rfl⟩

@[simp]

中文:
定义 rangeRestrict
  签名: (f : R ->+* S)
  定义体: f.codRestrict f.range fun x => ⟨x, rfl⟩

@[simp]

Depends on / 依赖: codRestrict, f.codRestrict, f.range
-/
def rangeRestrict (f : R ->+* S) : R ->+* f.range :=
  f.codRestrict f.range fun x => ⟨x, rfl⟩

@[simp]
/--
theorem `coe_rangeRestrict` / 定理 `coe_rangeRestrict`

English:
theorem coe_rangeRestrict
  given: (f : R ->+* S) (x : R)
  statement: (f.rangeRestrict x : S) = f x
  proof: rfl

中文:
定理 coe_rangeRestrict
  条件: (f : R ->+* S) (x : R)
  结论: (f.rangeRestrict x : S) = f x
  证明: rfl
-/
theorem coe_rangeRestrict (f : R ->+* S) (x : R) : (f.rangeRestrict x : S) = f x :=
  rfl

/--
theorem `rangeRestrict_surjective` / 定理 `rangeRestrict_surjective`

English:
theorem rangeRestrict_surjective
  given: (f : R ->+* S)
  statement: Function.Surjective f.rangeRestrict
  proof: fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

中文:
定理 rangeRestrict_surjective
  条件: (f : R ->+* S)
  结论: 函数.满射 f.rangeRestrict
  证明: fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

Depends on / 依赖: Subtype, Subtype.ext, mem_range, mem_range.mp
-/
theorem rangeRestrict_surjective (f : R ->+* S) : Function.Surjective f.rangeRestrict :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  given: {f : R ->+* S}
  proof: SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

中文:
定理 range_eq_top
  条件: {f : R ->+* S}
  证明: SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

Depends on / 依赖: Iff.trans, Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, coe_range, coe_top, range_eq_univ
-/
theorem range_eq_top {f : R ->+* S} :
    f.range = (⊤ : Subring S) ↔ Function.Surjective f :=
SetLike.ext'_iff.trans Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
/--
theorem `range_eq_top_of_surjective` / 定理 `range_eq_top_of_surjective`

English:
theorem range_eq_top_of_surjective
  given: (f : R ->+* S) (hf : Function.Surjective f)
  proof: range_eq_top.2 hf

@[simp]

中文:
定理 range_eq_top_of_surjective
  条件: (f : R ->+* S) (hf : 函数.满射 f)
  证明: range_eq_top.2 hf

@[simp]

Depends on / 依赖: range_eq_top
-/
theorem range_eq_top_of_surjective (f : R ->+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : Subring S) :=
  range_eq_top.2 hf

@[simp]
/--
theorem `domRestrict_comp_rangeRestrict` / 定理 `domRestrict_comp_rangeRestrict`

English:
theorem domRestrict_comp_rangeRestrict
  given: (g : S ->+* T) (f : R ->+* S)
  proof: rfl

@[simp]

中文:
定理 domRestrict_comp_rangeRestrict
  条件: (g : S ->+* T) (f : R ->+* S)
  证明: rfl

@[simp]
-/
theorem domRestrict_comp_rangeRestrict (g : S ->+* T) (f : R ->+* S) :
    (g.domRestrict f.range).comp (f.rangeRestrict) = g.comp f :=
  rfl

@[simp]
/--
theorem `range_prodMap` / 定理 `range_prodMap`

English:
theorem range_prodMap
  given: {R' S' : Type*} [Ring R'] [Ring S'] (f : R ->+* S) (g : R' ->+* S')
  proof: SetLike.coe_injective Set.range_prodMap

中文:
定理 range_prodMap
  条件: {R' S' : 类型} [环 R'] [环 S'] (f : R ->+* S) (g : R' ->+* S')
  证明: SetLike.coe_injective Set.range_prodMap

Depends on / 依赖: Set.range_prodMap, SetLike, SetLike.coe_injective, coe_injective, range_prodMap
-/
theorem range_prodMap {R' S' : Type*} [Ring R'] [Ring S'] (f : R ->+* S) (g : R' ->+* S') :
    (f.prodMap g).range = f.range.prod g.range :=
  SetLike.coe_injective Set.range_prodMap

section eqLocus

variable {S : Type v} [Semiring S]

/--
Definition of `eqLocus` / `eqLocus` 的定义

English:
definition eqLocus
  signature: (f g : R ->+* S)
  body: { (f : R ->* S).eqLocusM g, (f : R ->+ S).eqLocus g with carrier := { x | f x = g x } }

@[simp]

中文:
定义 eqLocus
  签名: (f g : R ->+* S)
  定义体: { (f : R ->* S).eqLocusM g, (f : R ->+ S).eqLocus g with carrier := { x | f x = g x } }

@[simp]

Depends on / 依赖: carrier, eqLocus, eqLocusM
-/
def eqLocus (f g : R ->+* S) : Subring R :=
  { (f : R ->* S).eqLocusM g, (f : R ->+ S).eqLocus g with carrier := { x | f x = g x } }

@[simp]
/--
theorem `mem_eqLocus` / 定理 `mem_eqLocus`

English:
theorem mem_eqLocus
  given: {f g : R ->+* S} {x : R}
  statement: x in f.eqLocus g ↔ f x = g x
  proof: Iff.rfl

@[simp]

中文:
定理 mem_eqLocus
  条件: {f g : R ->+* S} {x : R}
  结论: x in f.eqLocus g ↔ f x = g x
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_eqLocus {f g : R ->+* S} {x : R} : x in f.eqLocus g ↔ f x = g x := Iff.rfl

@[simp]
/--
theorem `eqLocus_same` / 定理 `eqLocus_same`

English:
theorem eqLocus_same
  given: (f : R ->+* S)
  statement: f.eqLocus f = ⊤
  proof: SetLike.ext fun _ => eq_self_iff_true _

中文:
定理 eqLocus_same
  条件: (f : R ->+* S)
  结论: f.eqLocus f = ⊤
  证明: SetLike.ext fun _ => eq_self_iff_true _

Depends on / 依赖: SetLike, SetLike.ext, eq_self_iff_true
-/
theorem eqLocus_same (f : R ->+* S) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/--
theorem `eqOn_set_closure` / 定理 `eqOn_set_closure`

English:
theorem eqOn_set_closure
  given: {f g : R ->+* S} {s : Set R} (h : Set.EqOn f g s)
  proof: show closure s <= f.eqLocus g from closure_le.2 h

中文:
定理 eqOn_set_closure
  条件: {f g : R ->+* S} {s : 集合 R} (h : 集合.EqOn f g s)
  证明: show closure s <= f.eqLocus g from closure_le.2 h

Depends on / 依赖: closure, closure_le, eqLocus, f.eqLocus
-/
theorem eqOn_set_closure {f g : R ->+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s <= f.eqLocus g from closure_le.2 h

/--
theorem `eq_of_eqOn_set_top` / 定理 `eq_of_eqOn_set_top`

English:
theorem eq_of_eqOn_set_top
  given: {f g : R ->+* S} (h : Set.EqOn f g (⊤ : Subring R))
  statement: f = g
  proof: ext fun _x => h trivial

中文:
定理 eq_of_eqOn_set_top
  条件: {f g : R ->+* S} (h : 集合.EqOn f g (⊤ : 子环 R))
  结论: f = g
  证明: ext fun _x => h trivial
-/
theorem eq_of_eqOn_set_top {f g : R ->+* S} (h : Set.EqOn f g (⊤ : Subring R)) : f = g :=
  ext fun _x => h trivial

/--
theorem `eq_of_eqOn_set_dense` / 定理 `eq_of_eqOn_set_dense`

English:
theorem eq_of_eqOn_set_dense
  given: {s : Set R} (hs : closure s = ⊤) {f g : R ->+* S} (h : s.EqOn f g)
  proof: eq_of_eqOn_set_top hs ▸ eqOn_set_closure h

中文:
定理 eq_of_eqOn_set_dense
  条件: {s : 集合 R} (hs : closure s = ⊤) {f g : R ->+* S} (h : s.EqOn f g)
  证明: eq_of_eqOn_set_top hs ▸ eqOn_set_closure h

Depends on / 依赖: eqOn_set_closure, eq_of_eqOn_set_top
-/
theorem eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R ->+* S} (h : s.EqOn f g) :
    f = g :=
eq_of_eqOn_set_top hs ▸ eqOn_set_closure h

end eqLocus

/--
theorem `closure_preimage_le` / 定理 `closure_preimage_le`

English:
theorem closure_preimage_le
  given: (f : R ->+* S) (s : Set S)
  statement: closure (f ⁻¹' s) <= (closure s).comap f
  proof: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 closure_preimage_le
  条件: (f : R ->+* S) (s : 集合 S)
  结论: closure (f ⁻¹' s) <= (closure s).comap f
  证明: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem closure_preimage_le (f : R ->+* S) (s : Set S) : closure (f ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

/--
theorem `map_closure` / 定理 `map_closure`

English:
theorem map_closure
  given: (f : R ->+* S) (s : Set R)
  statement: (closure s).map f = closure (f '' s)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subring.gi S).gc (Subring.gi R).gc
    fun _ => rfl

中文:
定理 map_closure
  条件: (f : R ->+* S) (s : 集合 R)
  结论: (closure s).map f = closure (f '' s)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subring.gi S).gc (Subring.gi R).gc
    fun _ => rfl

Depends on / 依赖: Set.image_preimage.l_comm_of_u_comm, Subring, Subring.gi, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_closure (f : R ->+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subring.gi S).gc (Subring.gi R).gc
    fun _ => rfl

end RingHom

namespace Subring

open RingHom

/--
theorem `mem_closure_image_of` / 定理 `mem_closure_image_of`

English:
theorem mem_closure_image_of
  given: (f : R ->+* S) {s : Set R} {x : R} (hx : x in Subring.closure s)
  proof: by
  rw [← f.map_closure]; rw [Subring.mem_map]
  exact ⟨x, hx, rfl⟩

中文:
定理 mem_closure_image_of
  条件: (f : R ->+* S) {s : 集合 R} {x : R} (hx : x in 子环.closure s)
  证明: by
  rw [← f.map_closure]; rw [Subring.mem_map]
  exact ⟨x, hx, rfl⟩

Depends on / 依赖: Subring, Subring.mem_map, f.map_closure, map_closure, mem_map
-/
theorem mem_closure_image_of (f : R ->+* S) {s : Set R} {x : R} (hx : x in Subring.closure s) :
    f x in Subring.closure (f '' s) := by
  rw [← f.map_closure]; rw [Subring.mem_map]
  exact ⟨x, hx, rfl⟩

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : Subring R} (h : S <= T)
  body: S.subtype.codRestrict _ fun x => h x.2

@[simp]

中文:
定义 inclusion
  签名: {S T : 子环 R} (h : S <= T)
  定义体: S.subtype.codRestrict _ fun x => h x.2

@[simp]

Depends on / 依赖: S.subtype.codRestrict, codRestrict, subtype
-/
def inclusion {S T : Subring R} (h : S <= T) : S ->+* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: {S T : Subring R} (h : S <= T) (x : S)
  proof: by simp [Subring.inclusion]

中文:
定理 coe_inclusion
  条件: {S T : 子环 R} (h : S <= T) (x : S)
  证明: by simp [Subring.inclusion]

Depends on / 依赖: Subring, Subring.inclusion, inclusion
-/
theorem coe_inclusion {S T : Subring R} (h : S <= T) (x : S) :
    (Subring.inclusion h x : R) = x := by simp [Subring.inclusion]

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {S T : Subring R} (h : S <= T)
  proof: RingHom.injective_codRestrict.mpr S.subtype_injective

@[simp]

中文:
定理 inclusion_injective
  条件: {S T : 子环 R} (h : S <= T)
  证明: RingHom.injective_codRestrict.mpr S.subtype_injective

@[simp]

Depends on / 依赖: RingHom, RingHom.injective_codRestrict.mpr, S.subtype_injective, injective_codRestrict, subtype_injective
-/
theorem inclusion_injective {S T : Subring R} (h : S <= T) :
    Function.Injective (Subring.inclusion h) :=
  RingHom.injective_codRestrict.mpr S.subtype_injective

@[simp]
/--
theorem `range_subtype` / 定理 `range_subtype`

English:
theorem range_subtype
  given: (s : Subring R)
  statement: s.subtype.range = s
  proof: SetLike.coe_injective (coe_rangeS _).trans Subtype.range_coe

中文:
定理 range_subtype
  条件: (s : 子环 R)
  结论: s.subtype.range = s
  证明: SetLike.coe_injective (coe_rangeS _).trans Subtype.range_coe

Depends on / 依赖: SetLike, SetLike.coe_injective, Subtype, Subtype.range_coe, coe_injective, coe_rangeS, range_coe
-/
theorem range_subtype (s : Subring R) : s.subtype.range = s :=
SetLike.coe_injective (coe_rangeS _).trans Subtype.range_coe

/--
theorem `range_fst` / 定理 `range_fst`

English:
theorem range_fst
  statement: (fst R S).rangeS = ⊤
  proof: (fst R S).rangeS_top_of_surjective Prod.fst_surjective

中文:
定理 range_fst
  结论: (fst R S).rangeS = ⊤
  证明: (fst R S).rangeS_top_of_surjective Prod.fst_surjective

Depends on / 依赖: Prod.fst_surjective, fst_surjective, rangeS_top_of_surjective
-/
theorem range_fst : (fst R S).rangeS = ⊤ :=
(fst R S).rangeS_top_of_surjective Prod.fst_surjective

/--
theorem `range_snd` / 定理 `range_snd`

English:
theorem range_snd
  statement: (snd R S).rangeS = ⊤
  proof: (snd R S).rangeS_top_of_surjective Prod.snd_surjective

@[simp]

中文:
定理 range_snd
  结论: (snd R S).rangeS = ⊤
  证明: (snd R S).rangeS_top_of_surjective Prod.snd_surjective

@[simp]

Depends on / 依赖: Prod.snd_surjective, rangeS_top_of_surjective, snd_surjective
-/
theorem range_snd : (snd R S).rangeS = ⊤ :=
(snd R S).rangeS_top_of_surjective Prod.snd_surjective

@[simp]
/--
theorem `prod_bot_sup_bot_prod` / 定理 `prod_bot_sup_bot_prod`

English:
theorem prod_bot_sup_bot_prod
  given: (s : Subring R) (t : Subring S)
  statement: s.prod ⊥ ⊔ prod ⊥ t = s.prod t
  proof: le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ <= s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t <= s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

中文:
定理 prod_bot_sup_bot_prod
  条件: (s : 子环 R) (t : 子环 S)
  结论: s.乘积 ⊥ ⊔ 乘积 ⊥ t = s.乘积 t
  证明: le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ <= s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t <= s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

Depends on / 依赖: Prod.fst_mul_snd, SetLike, SetLike.mem_coe, bot_le, fst_mul_snd, le_antisymm, le_sup_left, le_sup_right, mem_coe, mul_mem, one_mem, prod_mono_left, prod_mono_right, s.prod, sup_le
-/
theorem prod_bot_sup_bot_prod (s : Subring R) (t : Subring S) : s.prod ⊥ ⊔ prod ⊥ t = s.prod t :=
  le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ <= s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t <= s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subring

namespace RingEquiv

variable {s t : Subring R}

/--
Definition of `subringCongr` / `subringCongr` 的定义

English:
definition subringCongr
  signature: (h : s = t)
  body: { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

@[simp]

中文:
定义 subringCongr
  签名: (h : s = t)
  定义体: { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

@[simp]

Depends on / 依赖: Equiv.setCongr, congr_arg, map_add, map_mul, setCongr
-/
def subringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

@[simp]
/--
theorem `subringCongr_symm` / 定理 `subringCongr_symm`

English:
theorem subringCongr_symm
  given: (h : s = t)
  proof: rfl

@[simp]

中文:
定理 subringCongr_symm
  条件: (h : s = t)
  证明: rfl

@[simp]
-/
theorem subringCongr_symm (h : s = t) :
    (subringCongr h).symm = subringCongr h.symm := rfl

@[simp]
/--
theorem `coe_subringCongr_apply` / 定理 `coe_subringCongr_apply`

English:
theorem coe_subringCongr_apply
  given: (h : s = t) (x : s)
  proof: rfl

中文:
定理 coe_subringCongr_apply
  条件: (h : s = t) (x : s)
  证明: rfl
-/
theorem coe_subringCongr_apply (h : s = t) (x : s) :
    (subringCongr h x).val = x.val := rfl

/--
Definition of `ofLeftInverse` / `ofLeftInverse` 的定义

English:
definition ofLeftInverse
  signature: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f)
  body: { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ f.range.subtype) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := RingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]

中文:
定义 ofLeftInverse
  签名: {g : S -> R} {f : R ->+* S} (h : 函数.左逆 g f)
  定义体: { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ f.range.subtype) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := RingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]

Depends on / 依赖: RingHom, RingHom.mem_range.mp, Subtype, Subtype.ext, f.range.subtype, f.rangeRestrict, invFun, left_inv, mem_range, rangeRestrict, right_inv, subtype, x.prop
-/
def ofLeftInverse {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ f.range.subtype) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := RingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/--
theorem `ofLeftInverse_apply` / 定理 `ofLeftInverse_apply`

English:
theorem ofLeftInverse_apply
  given: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) (x : R)
  proof: rfl

@[simp]

中文:
定理 ofLeftInverse_apply
  条件: {g : S -> R} {f : R ->+* S} (h : 函数.左逆 g f) (x : R)
  证明: rfl

@[simp]
-/
theorem ofLeftInverse_apply {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
/--
theorem `ofLeftInverse_symm_apply` / 定理 `ofLeftInverse_symm_apply`

English:
theorem ofLeftInverse_symm_apply
  statement: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f)
  proof: rfl

中文:
定理 ofLeftInverse_symm_apply
  结论: {g : S -> R} {f : R ->+* S} (h : 函数.左逆 g f)
  证明: rfl
-/
theorem ofLeftInverse_symm_apply {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/--
Definition of `subringMap` / `subringMap` 的定义

English:
definition subringMap
  signature: (e : R ≃+* S)
  body: e.subsemiringMap s.toSubsemiring

中文:
定义 subringMap
  签名: (e : R ≃+* S)
  定义体: e.subsemiringMap s.toSubsemiring

Depends on / 依赖: e.subsemiringMap, s.toSubsemiring, subsemiringMap, toSubsemiring
-/
def subringMap (e : R ≃+* S) : s ≃+* s.map e.toRingHom :=
  e.subsemiringMap s.toSubsemiring

set_option backward.isDefEq.respectTransparency false in
/-- A ring isomorphism `e : R ≃+* S` descends to subrings `s' ≃+* s` provided
`x ∈ s' ↔ e x ∈ s`. -/
@[simps!]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
  body: RingHom.restrict e _ _ fun _ => (h _).1
  invFun := RingHom.restrict e.symm _ _ fun y hy => by
    obtain ⟨x, rfl⟩ := e.surjective y; simp [(h _).2 hy]
  left_inv y := by simp [← Subtype.val_inj]
  right_inv x := by simp [← Subtype.val_inj]

中文:
定义 restrict
  签名: {R : 类型u} {S : 类型v} [非结合半环 R] [非结合半环 S]
  定义体: RingHom.restrict e _ _ fun _ => (h _).1
  invFun := RingHom.restrict e.symm _ _ fun y hy => by
    obtain ⟨x, rfl⟩ := e.surjective y; simp [(h _).2 hy]
  left_inv y := by simp [← Subtype.val_inj]
  right_inv x := by simp [← Subtype.val_inj]

Depends on / 依赖: RingHom, RingHom.restrict, restrict
-/
def restrict {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
    {σR : Type*} {σS : Type*} [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R]
    [SubsemiringClass σS S] (e : R ≃+* S) (s' : σR) (s : σS) (h : forall x, x in s' ↔ e x in s) :
    s' ≃+* s where
  __ := RingHom.restrict e _ _ fun _ => (h _).1
  invFun := RingHom.restrict e.symm _ _ fun y hy => by
    obtain ⟨x, rfl⟩ := e.surjective y; simp [(h _).2 hy]
  left_inv y := by simp [← Subtype.val_inj]
  right_inv x := by simp [← Subtype.val_inj]

end RingEquiv

namespace Subring

variable {s : Set R}

@[elab_as_elim]
/--
theorem `InClosure.recOn` / 定理 `InClosure.recOn`

English:
theorem InClosure.recOn
  statement: {R} [Ring R] {s : Set R}
  proof: by
  have h0 : C 0 := add_neg_cancel (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction L with
  | nil => exact h0
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons]; rw [List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    exists L : List R, (forall x in L, x in s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact h1
    | cons hd tl ih =>
      rw [List.forall_mem_cons] at HL'
      rw [List.prod_cons]
      exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact hneg1
    | cons hd tl ih =>
      rw [List.prod_cons]; rw [neg_mul_eq_mul_neg]
      rw [List.forall_mem_cons] at HL'
      exact hs _ HL'.1 _ (ih HL'.2)
  induction hd with
  | nil => exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> rcases HL.1 with hhd | hhd
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
Or.inl by rw [List.prod_cons, List.prod_cons, HP]⟩
· exact ⟨L, HL', Or.inr by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
Or.inr by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
· exact ⟨L, HL', Or.inl by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩

中文:
定理 InClosure.recOn
  结论: {R} [环 R] {s : 集合 R}
  证明: by
  have h0 : C 0 := add_neg_cancel (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction L with
  | nil => exact h0
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons]; rw [List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    exists L : List R, (forall x in L, x in s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact h1
    | cons hd tl ih =>
      rw [List.forall_mem_cons] at HL'
      rw [List.prod_cons]
      exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact hneg1
    | cons hd tl ih =>
      rw [List.prod_cons]; rw [neg_mul_eq_mul_neg]
      rw [List.forall_mem_cons] at HL'
      exact hs _ HL'.1 _ (ih HL'.2)
  induction hd with
  | nil => exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> rcases HL.1 with hhd | hhd
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
Or.inl by rw [List.prod_cons, List.prod_cons, HP]⟩
· exact ⟨L, HL', Or.inr by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
Or.inr by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
· exact ⟨L, HL', Or.inl by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩
-/
protected theorem InClosure.recOn {R} [Ring R] {s : Set R}
    {C : R -> Prop} {x : R} (hx : x in closure s) (h1 : C 1)
    (hneg1 : C (-1)) (hs : forall z in s, forall n, C n -> C (z * n)) (ha : forall {x y}, C x -> C y -> C (x + y)) :
    C x := by
  have h0 : C 0 := add_neg_cancel (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction L with
  | nil => exact h0
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons]; rw [List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    exists L : List R, (forall x in L, x in s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact h1
    | cons hd tl ih =>
      rw [List.forall_mem_cons] at HL'
      rw [List.prod_cons]
      exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact hneg1
    | cons hd tl ih =>
      rw [List.prod_cons]; rw [neg_mul_eq_mul_neg]
      rw [List.forall_mem_cons] at HL'
      exact hs _ HL'.1 _ (ih HL'.2)
  induction hd with
  | nil => exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> rcases HL.1 with hhd | hhd
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
Or.inl by rw [List.prod_cons, List.prod_cons, HP]⟩
· exact ⟨L, HL', Or.inr by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
Or.inr by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
· exact ⟨L, HL', Or.inl by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩

/--
theorem `closure_preimage_le` / 定理 `closure_preimage_le`

English:
theorem closure_preimage_le
  given: (f : R ->+* S) (s : Set S)
  statement: closure (f ⁻¹' s) <= (closure s).comap f
  proof: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 closure_preimage_le
  条件: (f : R ->+* S) (s : 集合 S)
  结论: closure (f ⁻¹' s) <= (closure s).comap f
  证明: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem closure_preimage_le (f : R ->+* S) (s : Set S) : closure (f ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

end Subring

/-! ## Actions by `Subring`s

These are just copies of the definitions about `Subsemiring` starting from
`Subsemiring.MulAction`.

When `R` is commutative, `Algebra.ofSubring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subring

variable {α β : Type*}


/-- The action by a subring is the action by the underlying ring. -/
example [SMul R α] (S : Subring R) : SMul S α := by infer_instance

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: [SMul R α] {S : Subring R} (g : S) (m : α)
  statement: g • m = (g : R) • m
  proof: rfl

example [SMul R β] [SMul α β] [SMulCommClass R α β] (S : Subring R) :
    SMulCommClass S α β := by infer_instance

example [SMul α β] [SMul R β] [SMulCommClass α R β] (S : Subring R) :
    SMulCommClass α S β := by infer_instance

中文:
定理 smul_def
  条件: [标量乘法 R α] {S : 子环 R} (g : S) (m : α)
  结论: g • m = (g : R) • m
  证明: rfl

example [SMul R β] [SMul α β] [SMulCommClass R α β] (S : Subring R) :
    SMulCommClass S α β := by infer_instance

example [SMul α β] [SMul R β] [SMulCommClass α R β] (S : Subring R) :
    SMulCommClass α S β := by infer_instance
-/
theorem smul_def [SMul R α] {S : Subring R} (g : S) (m : α) : g • m = (g : R) • m :=
  rfl

example [SMul R β] [SMul α β] [SMulCommClass R α β] (S : Subring R) :
    SMulCommClass S α β := by infer_instance

example [SMul α β] [SMul R β] [SMulCommClass α R β] (S : Subring R) :
    SMulCommClass α S β := by infer_instance

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
example [SMul α β] [SMul R α] [SMul R β] [IsScalarTower R α β] (S : Subring R) :
    IsScalarTower S α β := by infer_instance

example [SMul R α] [FaithfulSMul R α] (S : Subring R) : FaithfulSMul S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
example {R} [Ring R] [MulAction R α] (S : Subring R) : MulAction S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
example {R} [Ring R] [AddMonoid α] [DistribMulAction R α] (S : Subring R) :
    DistribMulAction S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
example {R} [Ring R] [Monoid α] [MulDistribMulAction R α] (S : Subring R) :
    MulDistribMulAction S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
example [Zero α] [SMulWithZero R α] (S : Subring R) : SMulWithZero S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
example {R} [Ring R] [Zero α] [MulActionWithZero R α] (S : Subring R) :
    MulActionWithZero S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
example {R} [Ring R] [AddCommMonoid α] [Module R α] (S : Subring R) :
    Module S α := by infer_instance

/-- The action by a subsemiring is the action by the underlying ring. -/
example {R} [Ring R] [Semiring α] [MulSemiringAction R α] (S : Subring R) :
    MulSemiringAction S α := by infer_instance

/--
Instance `center.smulCommClass_left` / 实例 `center.smulCommClass_left`

English:
instance center.smulCommClass_left
  signature: {R} [Ring R]
  body: Subsemiring.center.smulCommClass_left

中文:
实例 center.smulCommClass_left
  签名: {R} [环 R]
  定义体: Subsemiring.center.smulCommClass_left
-/
instance center.smulCommClass_left {R} [Ring R] : SMulCommClass (center R) R R :=
  Subsemiring.center.smulCommClass_left

/--
Instance `center.smulCommClass_right` / 实例 `center.smulCommClass_right`

English:
instance center.smulCommClass_right
  signature: {R} [Ring R]
  body: Subsemiring.center.smulCommClass_right

中文:
实例 center.smulCommClass_right
  签名: {R} [环 R]
  定义体: Subsemiring.center.smulCommClass_right

Depends on / 依赖: f.prop
-/
instance center.smulCommClass_right {R} [Ring R] : SMulCommClass R (center R) R :=
  Subsemiring.center.smulCommClass_right

/-- The center of a semiring acts commutatively on any `R`-module -/
instance {R M : Type*} [Ring R] [MulAction R M] :
    SMulCommClass R (Subring.center R) M :=
inferInstanceAs SMulCommClass R (Submonoid.center R) M

/-- The center of a semiring acts commutatively on any `R`-module -/
instance {R M : Type*} [Ring R] [MulAction R M] :
    SMulCommClass (Subring.center R) R M :=
inferInstanceAs SMulCommClass (Submonoid.center R) R M

end Subring

end Actions

namespace Subring

/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (f : R ->+* S) (t : Subring S)
  statement: (t.comap f).map f = t ⊓ f.range
  proof: SetLike.coe_injective Set.image_preimage_eq_inter_range

中文:
定理 map_comap_eq
  条件: (f : R ->+* S) (t : 子环 S)
  结论: (t.comap f).map f = t ⊓ f.range
  证明: SetLike.coe_injective Set.image_preimage_eq_inter_range

Depends on / 依赖: Set.image_preimage_eq_inter_range, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq_inter_range
-/
theorem map_comap_eq (f : R ->+* S) (t : Subring S) : (t.comap f).map f = t ⊓ f.range :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

/--
theorem `map_comap_eq_self` / 定理 `map_comap_eq_self`

English:
theorem map_comap_eq_self
  proof: by
  simpa only [inf_of_le_left h] using Subring.map_comap_eq f t

中文:
定理 map_comap_eq_self
  证明: by
  simpa only [inf_of_le_left h] using Subring.map_comap_eq f t

Depends on / 依赖: Subring, Subring.map_comap_eq, inf_of_le_left, map_comap_eq
-/
theorem map_comap_eq_self
    {f : R ->+* S} {t : Subring S} (h : t <= f.range) : (t.comap f).map f = t := by
  simpa only [inf_of_le_left h] using Subring.map_comap_eq f t

/--
theorem `map_comap_eq_self_of_surjective` / 定理 `map_comap_eq_self_of_surjective`

English:
theorem map_comap_eq_self_of_surjective
  proof: map_comap_eq_self by simp [hf]

中文:
定理 map_comap_eq_self_of_surjective
  证明: map_comap_eq_self by simp [hf]

Depends on / 依赖: map_comap_eq_self
-/
theorem map_comap_eq_self_of_surjective
    {f : R ->+* S} (hf : Function.Surjective f) (t : Subring S) : (t.comap f).map f = t :=
map_comap_eq_self by simp [hf]

/--
theorem `comap_map_eq` / 定理 `comap_map_eq`

English:
theorem comap_map_eq
  given: (f : R ->+* S) (s : Subring R)
  proof: by
  apply le_antisymm
  · intro x hx
    rw [mem_comap]; rw [mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y in f ⁻¹' {0} := by simp [hxy]
    rw [← closure_eq s]; rw [← closure_union]; rw [← add_sub_cancel y x]
    exact Subring.add_mem _ (subset_closure <| Or.inl hy) (subset_closure <| Or.inr hxy)
  · rw [← map_le_iff_le_comap, map_sup, f.map_closure]
    apply le_of_eq
    rw [sup_eq_left]; rw [closure_le]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (s.map f).zero_mem)

中文:
定理 comap_map_eq
  条件: (f : R ->+* S) (s : 子环 R)
  证明: by
  apply le_antisymm
  · intro x hx
    rw [mem_comap]; rw [mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y in f ⁻¹' {0} := by simp [hxy]
    rw [← closure_eq s]; rw [← closure_union]; rw [← add_sub_cancel y x]
    exact Subring.add_mem _ (subset_closure <| Or.inl hy) (subset_closure <| Or.inr hxy)
  · rw [← map_le_iff_le_comap, map_sup, f.map_closure]
    apply le_of_eq
    rw [sup_eq_left]; rw [closure_le]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (s.map f).zero_mem)

Depends on / 依赖: Or.inl, Or.inr, Set.image_preimage_subset, Set.singleton_subset_iff, Subring, Subring.add_mem, add_mem, add_sub_cancel, closure_eq, closure_le, closure_union, f.map_closure, image_preimage_subset, le_antisymm, le_of_eq, map_closure, map_le_iff_le_comap, map_sup, mem_comap, mem_map
-/
theorem comap_map_eq (f : R ->+* S) (s : Subring R) :
    (s.map f).comap f = s ⊔ closure (f ⁻¹' {0}) := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap]; rw [mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y in f ⁻¹' {0} := by simp [hxy]
    rw [← closure_eq s]; rw [← closure_union]; rw [← add_sub_cancel y x]
    exact Subring.add_mem _ (subset_closure <| Or.inl hy) (subset_closure <| Or.inr hxy)
  · rw [← map_le_iff_le_comap, map_sup, f.map_closure]
    apply le_of_eq
    rw [sup_eq_left]; rw [closure_le]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (s.map f).zero_mem)

/--
theorem `comap_map_eq_self` / 定理 `comap_map_eq_self`

English:
theorem comap_map_eq_self
  statement: {f : R ->+* S} {s : Subring R}
  proof: by
  convert! comap_map_eq f s
  rwa [left_eq_sup, closure_le]

中文:
定理 comap_map_eq_self
  结论: {f : R ->+* S} {s : 子环 R}
  证明: by
  convert! comap_map_eq f s
  rwa [left_eq_sup, closure_le]

Depends on / 依赖: closure_le, comap_map_eq, convert, left_eq_sup
-/
theorem comap_map_eq_self {f : R ->+* S} {s : Subring R}
    (h : f ⁻¹' {0} subseteq s) : (s.map f).comap f = s := by
  convert! comap_map_eq f s
  rwa [left_eq_sup, closure_le]

/--
theorem `comap_map_eq_self_of_injective` / 定理 `comap_map_eq_self_of_injective`

English:
theorem comap_map_eq_self_of_injective
  proof: SetLike.coe_injective (Set.preimage_image_eq _ hf)

中文:
定理 comap_map_eq_self_of_injective
  证明: SetLike.coe_injective (Set.preimage_image_eq _ hf)

Depends on / 依赖: Set.preimage_image_eq, SetLike, SetLike.coe_injective, coe_injective, preimage_image_eq
-/
theorem comap_map_eq_self_of_injective
    {f : R ->+* S} (hf : Function.Injective f) (s : Subring R) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subring

/--
theorem `AddSubgroup.int_mul_mem` / 定理 `AddSubgroup.int_mul_mem`

English:
theorem AddSubgroup.int_mul_mem
  given: {G : AddSubgroup R} (k : Int) {g : R} (h : g in G)
  proof: by
  convert AddSubgroup.zsmul_mem G h k
  rw [zsmul_eq_mul]

中文:
定理 加法子群.int_mul_mem
  条件: {G : 加法子群 R} (k : 整数) {g : R} (h : g in G)
  证明: by
  convert AddSubgroup.zsmul_mem G h k
  rw [zsmul_eq_mul]

Depends on / 依赖: AddSubgroup, AddSubgroup.zsmul_mem, convert, zsmul_eq_mul, zsmul_mem
-/
theorem AddSubgroup.int_mul_mem {G : AddSubgroup R} (k : Int) {g : R} (h : g in G) :
    (k : R) * g in G := by
  convert AddSubgroup.zsmul_mem G h k
  rw [zsmul_eq_mul]
