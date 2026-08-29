/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Subfields

Let `K` be a division ring, for example a field.
This file concerns the "bundled" subfield type `Subfield K`, a type
whose terms correspond to subfields of `K`. Note we do not require the "subfields" to be
commutative, so they are really sub-division rings / skew fields. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : Set K` and `IsSubfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set K` to `Subfield K`, sending a subset of `K`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [DivisionRing K] (L : Type u) [DivisionRing L] (f g : K →+* L)`
`(A : Subfield K) (B : Subfield L) (s : Set K)`

* `instance : CompleteLattice (Subfield K)` : the complete lattice structure on the subfields.

* `Subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `Subfield.gi` : `closure : Set M → Subfield M` and coercion `(↑) : Subfield M → Set M`
  form a `GaloisInsertion`.

* `comap f B : Subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : Subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `f.fieldRange : Subfield L` : the range of the ring homomorphism `f`.

* `eqLocusField f g : Subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

## Implementation notes

A subfield is implemented as a subring which is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/

@[expose] public section


universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

namespace Subfield

variable (s t : Subfield K)

section DerivedFromSubfieldClass

/--
theorem `list_prod_mem` / 定理 `list_prod_mem`

English:
theorem list_prod_mem
  given: {l : List K}
  statement: (forall x in l, x in s) -> l.prod in s
  proof: list_prod_mem

中文:
定理 list_prod_mem
  条件: {l : 列表 K}
  结论: (对任意 x in l, x in s) -> l.乘积 in s
  证明: list_prod_mem
-/
protected theorem list_prod_mem {l : List K} : (forall x in l, x in s) -> l.prod in s :=
  list_prod_mem

/--
theorem `list_sum_mem` / 定理 `list_sum_mem`

English:
theorem list_sum_mem
  given: {l : List K}
  statement: (forall x in l, x in s) -> l.sum in s
  proof: list_sum_mem

中文:
定理 list_sum_mem
  条件: {l : 列表 K}
  结论: (对任意 x in l, x in s) -> l.求和 in s
  证明: list_sum_mem
-/
protected theorem list_sum_mem {l : List K} : (forall x in l, x in s) -> l.sum in s :=
  list_sum_mem

/--
theorem `multiset_sum_mem` / 定理 `multiset_sum_mem`

English:
theorem multiset_sum_mem
  given: (m : Multiset K)
  statement: (forall a in m, a in s) -> m.sum in s
  proof: multiset_sum_mem m

中文:
定理 multiset_sum_mem
  条件: (m : Multiset K)
  结论: (对任意 a in m, a in s) -> m.求和 in s
  证明: multiset_sum_mem m
-/
protected theorem multiset_sum_mem (m : Multiset K) : (forall a in m, a in s) -> m.sum in s :=
  multiset_sum_mem m

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  given: {ι : Type*} {t : Finset ι} {f : ι -> K} (h : forall c in t, f c in s)
  proof: sum_mem h

中文:
定理 sum_mem
  条件: {ι : 类型} {t : 有限集 ι} {f : ι -> K} (h : 对任意 c in t, f c in s)
  证明: sum_mem h
-/
protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι -> K} (h : forall c in t, f c in s) :
    (∑ i in t, f i) in s :=
  sum_mem h

end DerivedFromSubfieldClass

/-! ### top -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Subfield K)
  body: ⟨{ (⊤ : Subring K) with inv_mem' := fun x _ => Subring.mem_top x }⟩

中文:
实例 :
  签名: 顶元素 (子域 K)
  定义体: ⟨{ (⊤ : Subring K) with inv_mem' := fun x _ => Subring.mem_top x }⟩

Depends on / 依赖: Subring, Subring.mem_top, inv_mem, mem_top
-/
instance : Top (Subfield K) :=
  ⟨{ (⊤ : Subring K) with inv_mem' := fun x _ => Subring.mem_top x }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Subfield K)
  body: ⟨⊤⟩

@[simp]

中文:
实例 :
  签名: 可居 (子域 K)
  定义体: ⟨⊤⟩

@[simp]
-/
instance : Inhabited (Subfield K) :=
  ⟨⊤⟩

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : K)
  statement: x in (⊤ : Subfield K)
  proof: Set.mem_univ x

@[simp, norm_cast]

中文:
定理 mem_top
  条件: (x : K)
  结论: x in (⊤ : 子域 K)
  证明: Set.mem_univ x

@[simp, norm_cast]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (x : K) : x in (⊤ : Subfield K) :=
  Set.mem_univ x

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : Subfield K) : Set K) = Set.univ
  proof: rfl

中文:
定理 coe_top
  结论: ((⊤ : 子域 K) : 集合 K) = 集合.univ
  证明: rfl
-/
theorem coe_top : ((⊤ : Subfield K) : Set K) = Set.univ :=
  rfl

/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : Subfield K) ≃+* K
  body: Subsemiring.topEquiv

中文:
定义 topEquiv
  签名: : (⊤ : 子域 K) ≃+* K
  定义体: Subsemiring.topEquiv

Depends on / 依赖: Subsemiring, Subsemiring.topEquiv, topEquiv
-/
def topEquiv : (⊤ : Subfield K) ≃+* K :=
  Subsemiring.topEquiv

/-! ### comap -/


variable (f : K ->+* L)

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (s : Subfield L)
  body: { s.toSubring.comap f with
    inv_mem' := fun x hx =>
      show f x⁻¹ in s by
        rw [map_inv₀ f]
        exact s.inv_mem hx }

@[simp]

中文:
定义 comap
  签名: (s : 子域 L)
  定义体: { s.toSubring.comap f with
    inv_mem' := fun x hx =>
      show f x⁻¹ in s by
        rw [map_inv₀ f]
        exact s.inv_mem hx }

@[simp]

Depends on / 依赖: inv_mem, s.inv_mem, s.toSubring.comap, toSubring
-/
def comap (s : Subfield L) : Subfield K :=
  { s.toSubring.comap f with
    inv_mem' := fun x hx =>
      show f x⁻¹ in s by
        rw [map_inv₀ f]
        exact s.inv_mem hx }

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (s : Subfield L)
  statement: (s.comap f : Set K) = f ⁻¹' s
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (s : 子域 L)
  结论: (s.comap f : 集合 K) = f ⁻¹' s
  证明: rfl

@[simp]

Depends on / 依赖: AddCommGroup, FiniteDimensional, Module, castSucc, i.castSucc, i.succ
-/
theorem coe_comap (s : Subfield L) : (s.comap f : Set K) = f ⁻¹' s :=
  rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {s : Subfield L} {f : K ->+* L} {x : K}
  statement: x in s.comap f ↔ f x in s
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {s : 子域 L} {f : K ->+* L} {x : K}
  结论: x in s.comap f ↔ f x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {s : Subfield L} {f : K ->+* L} {x : K} : x in s.comap f ↔ f x in s :=
  Iff.rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (s : Subfield M) (g : L ->+* M) (f : K ->+* L)
  proof: rfl

中文:
定理 comap_comap
  条件: (s : 子域 M) (g : L ->+* M) (f : K ->+* L)
  证明: rfl
-/
theorem comap_comap (s : Subfield M) (g : L ->+* M) (f : K ->+* L) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ### map -/


/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (s : Subfield K)
  body: { s.toSubring.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, s.inv_mem hx, map_inv₀ f x⟩ }

@[simp, norm_cast]

中文:
定义 map
  签名: (s : 子域 K)
  定义体: { s.toSubring.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, s.inv_mem hx, map_inv₀ f x⟩ }

@[simp, norm_cast]

Depends on / 依赖: inv_mem, s.inv_mem, s.toSubring.map, toSubring
-/
def map (s : Subfield K) : Subfield L :=
  { s.toSubring.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, s.inv_mem hx, map_inv₀ f x⟩ }

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  statement: (s.map f : Set L) = f '' s
  proof: rfl

@[simp]

中文:
定理 coe_map
  结论: (s.map f : 集合 L) = f '' s
  证明: rfl

@[simp]
-/
theorem coe_map : (s.map f : Set L) = f '' s :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : K ->+* L} {s : Subfield K} {y : L}
  statement: y in s.map f ↔ exists x in s, f x = y
  proof: by
  unfold map
  simp only [mem_mk, Subring.mem_map, mem_toSubring]

中文:
定理 mem_map
  条件: {f : K ->+* L} {s : 子域 K} {y : L}
  结论: y in s.map f ↔ 存在 x in s, f x = y
  证明: by
  unfold map
  simp only [mem_mk, Subring.mem_map, mem_toSubring]

Depends on / 依赖: Subring, Subring.mem_map, mem_map, mem_mk, mem_toSubring
-/
theorem mem_map {f : K ->+* L} {s : Subfield K} {y : L} : y in s.map f ↔ exists x in s, f x = y := by
  unfold map
  simp only [mem_mk, Subring.mem_map, mem_toSubring]

-- Higher priority to apply before `mem_map`.
@[simp 1100]
/--
theorem `map_mem_map` / 定理 `map_mem_map`

English:
theorem map_mem_map
  given: (f : K ->+* L) {s : Subfield K} {x : K}
  statement: f x in s.map f ↔ x in s
  proof: calc
    _ ↔ f x in (s.map f : Set L) := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]

中文:
定理 map_mem_map
  条件: (f : K ->+* L) {s : 子域 K} {x : K}
  结论: f x in s.map f ↔ x in s
  证明: calc
    _ ↔ f x in (s.map f : Set L) := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]

Depends on / 依赖: Function, Function.Injective.mem_set_image, Iff.rfl, Injective, f.injective, injective, mem_set_image, s.map
-/
theorem map_mem_map (f : K ->+* L) {s : Subfield K} {x : K} : f x in s.map f ↔ x in s :=
  calc
    _ ↔ f x in (s.map f : Set L) := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : L ->+* M) (f : K ->+* L)
  statement: (s.map f).map g = s.map (g.comp f)
  proof: SetLike.ext' Set.image_image _ _ _

中文:
定理 map_map
  条件: (g : L ->+* M) (f : K ->+* L)
  结论: (s.map f).map g = s.map (g.comp f)
  证明: SetLike.ext' Set.image_image _ _ _

Depends on / 依赖: Set.image_image, SetLike, SetLike.ext, image_image
-/
theorem map_map (g : L ->+* M) (f : K ->+* L) : (s.map f).map g = s.map (g.comp f) :=
SetLike.ext' Set.image_image _ _ _

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : K ->+* L} {s : Subfield K} {t : Subfield L}
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {f : K ->+* L} {s : 子域 K} {t : 子域 L}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le_iff_le_comap {f : K ->+* L} {s : Subfield K} {t : Subfield L} :
    s.map f <= t ↔ s <= t.comap f :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : K ->+* L)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ =>
  map_le_iff_le_comap

中文:
定理 gc_map_comap
  条件: (f : K ->+* L)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ =>
  map_le_iff_le_comap
-/
theorem gc_map_comap (f : K ->+* L) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

end Subfield

namespace RingHom

variable (g : L ->+* M) (f : K ->+* L)

/-! ### range -/


/--
Definition of `fieldRange` / `fieldRange` 的定义

English:
definition fieldRange
  signature: : Subfield L
  body: ((⊤ : Subfield K).map f).copy (Set.range f) Set.image_univ.symm

@[simp, norm_cast]

中文:
定义 fieldRange
  签名: : 子域 L
  定义体: ((⊤ : Subfield K).map f).copy (Set.range f) Set.image_univ.symm

@[simp, norm_cast]

Depends on / 依赖: Set.image_univ.symm, Set.range, Subfield, image_univ
-/
def fieldRange : Subfield L :=
  ((⊤ : Subfield K).map f).copy (Set.range f) Set.image_univ.symm

@[simp, norm_cast]
/--
theorem `coe_fieldRange` / 定理 `coe_fieldRange`

English:
theorem coe_fieldRange
  statement: (f.fieldRange : Set L) = Set.range f
  proof: rfl

@[simp]

中文:
定理 coe_fieldRange
  结论: (f.fieldRange : 集合 L) = 集合.range f
  证明: rfl

@[simp]
-/
theorem coe_fieldRange : (f.fieldRange : Set L) = Set.range f :=
  rfl

@[simp]
/--
theorem `mem_fieldRange` / 定理 `mem_fieldRange`

English:
theorem mem_fieldRange
  given: {f : K ->+* L} {y : L}
  statement: y in f.fieldRange ↔ exists x, f x = y
  proof: Iff.rfl

中文:
定理 mem_fieldRange
  条件: {f : K ->+* L} {y : L}
  结论: y in f.fieldRange ↔ 存在 x, f x = y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_fieldRange {f : K ->+* L} {y : L} : y in f.fieldRange ↔ exists x, f x = y :=
  Iff.rfl

/--
theorem `fieldRange_eq_map` / 定理 `fieldRange_eq_map`

English:
theorem fieldRange_eq_map
  statement: f.fieldRange = Subfield.map f ⊤
  proof: by
  ext
  simp

中文:
定理 fieldRange_eq_map
  结论: f.fieldRange = 子域.map f ⊤
  证明: by
  ext
  simp
-/
theorem fieldRange_eq_map : f.fieldRange = Subfield.map f ⊤ := by
  ext
  simp

/--
theorem `map_fieldRange` / 定理 `map_fieldRange`

English:
theorem map_fieldRange
  statement: f.fieldRange.map g = (g.comp f).fieldRange
  proof: by
  simpa only [fieldRange_eq_map] using (⊤ : Subfield K).map_map g f

中文:
定理 map_fieldRange
  结论: f.fieldRange.map g = (g.comp f).fieldRange
  证明: by
  simpa only [fieldRange_eq_map] using (⊤ : Subfield K).map_map g f

Depends on / 依赖: Subfield, fieldRange_eq_map, map_map
-/
theorem map_fieldRange : f.fieldRange.map g = (g.comp f).fieldRange := by
  simpa only [fieldRange_eq_map] using (⊤ : Subfield K).map_map g f

/--
theorem `mem_fieldRange_self` / 定理 `mem_fieldRange_self`

English:
theorem mem_fieldRange_self
  given: (x : K)
  statement: f x in f.fieldRange
  proof: exists_apply_eq_apply _ _

中文:
定理 mem_fieldRange_self
  条件: (x : K)
  结论: f x in f.fieldRange
  证明: exists_apply_eq_apply _ _

Depends on / 依赖: exists_apply_eq_apply
-/
theorem mem_fieldRange_self (x : K) : f x in f.fieldRange :=
  exists_apply_eq_apply _ _

/--
theorem `fieldRange_eq_top_iff` / 定理 `fieldRange_eq_top_iff`

English:
theorem fieldRange_eq_top_iff
  given: {f : K ->+* L}
  proof: SetLike.ext'_iff.trans Set.range_eq_univ

中文:
定理 fieldRange_eq_top_iff
  条件: {f : K ->+* L}
  证明: SetLike.ext'_iff.trans Set.range_eq_univ

Depends on / 依赖: Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, range_eq_univ
-/
theorem fieldRange_eq_top_iff {f : K ->+* L} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_eq_univ

/--
Instance `fintypeFieldRange` / 实例 `fintypeFieldRange`

English:
instance fintypeFieldRange
  signature: [Fintype K] [DecidableEq L] (f : K ->+* L)
  body: Set.fintypeRange f

中文:
实例 fintypeFieldRange
  签名: [有限类型 K] [DecidableEq L] (f : K ->+* L)
  定义体: Set.fintypeRange f

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeFieldRange [Fintype K] [DecidableEq L] (f : K ->+* L) : Fintype f.fieldRange :=
  Set.fintypeRange f

end RingHom

namespace Subfield

/-! ### inf -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Subfield K)
  body: ⟨fun s t =>
    { s.toSubring ⊓ t.toSubring with
      inv_mem' := fun _ hx =>
        Subring.mem_inf.mpr
          ⟨s.inv_mem (Subring.mem_inf.mp hx).1, t.inv_mem (Subring.mem_inf.mp hx).2⟩ }⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 最小值 (子域 K)
  定义体: ⟨fun s t =>
    { s.toSubring ⊓ t.toSubring with
      inv_mem' := fun _ hx =>
        Subring.mem_inf.mpr
          ⟨s.inv_mem (Subring.mem_inf.mp hx).1, t.inv_mem (Subring.mem_inf.mp hx).2⟩ }⟩

@[simp, norm_cast]

Depends on / 依赖: Subring, Subring.mem_inf.mp, Subring.mem_inf.mpr, inv_mem, mem_inf, s.inv_mem, s.toSubring, t.inv_mem, t.toSubring, toSubring
-/
instance : Min (Subfield K) :=
  ⟨fun s t =>
    { s.toSubring ⊓ t.toSubring with
      inv_mem' := fun _ hx =>
        Subring.mem_inf.mpr
          ⟨s.inv_mem (Subring.mem_inf.mp hx).1, t.inv_mem (Subring.mem_inf.mp hx).2⟩ }⟩

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (p p' : Subfield K)
  statement: ((p ⊓ p' : Subfield K) : Set K) = p.carrier inter p'.carrier
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (p p' : 子域 K)
  结论: ((p ⊓ p' : 子域 K) : 集合 K) = p.carrier inter p'.carrier
  证明: rfl

@[simp]
-/
theorem coe_inf (p p' : Subfield K) : ((p ⊓ p' : Subfield K) : Set K) = p.carrier inter p'.carrier :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p p' : Subfield K} {x : K}
  statement: x in p ⊓ p' ↔ x in p ∧ x in p'
  proof: Iff.rfl

中文:
定理 mem_inf
  条件: {p p' : 子域 K} {x : K}
  结论: x in p ⊓ p' ↔ x in p ∧ x in p'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p p' : Subfield K} {x : K} : x in p ⊓ p' ↔ x in p ∧ x in p' :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Subfield K)
  body: ⟨fun S =>
    { sInf (Subfield.toSubring '' S) with
      inv_mem' := by
        rintro x hx
        apply Subring.mem_sInf.mpr
        rintro _ ⟨p, p_mem, rfl⟩
        exact p.inv_mem (Subring.mem_sInf.mp hx p.toSubring ⟨p, p_mem, rfl⟩) }⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 下确界集 (子域 K)
  定义体: ⟨fun S =>
    { sInf (Subfield.toSubring '' S) with
      inv_mem' := by
        rintro x hx
        apply Subring.mem_sInf.mpr
        rintro _ ⟨p, p_mem, rfl⟩
        exact p.inv_mem (Subring.mem_sInf.mp hx p.toSubring ⟨p, p_mem, rfl⟩) }⟩

@[simp, norm_cast]

Depends on / 依赖: Subfield, Subfield.toSubring, Subring, Subring.mem_sInf.mp, Subring.mem_sInf.mpr, inv_mem, mem_sInf, p.inv_mem, p.toSubring, p_mem, toSubring
-/
instance : InfSet (Subfield K) :=
  ⟨fun S =>
    { sInf (Subfield.toSubring '' S) with
      inv_mem' := by
        rintro x hx
        apply Subring.mem_sInf.mpr
        rintro _ ⟨p, p_mem, rfl⟩
        exact p.inv_mem (Subring.mem_sInf.mp hx p.toSubring ⟨p, p_mem, rfl⟩) }⟩

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (Subfield K))
  statement: ((sInf S : Subfield K) : Set K) = ⋂ s in S, ↑s
  proof: show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s in S, ↑s by simp

@[simp]

中文:
定理 coe_sInf
  条件: (S : 集合 (子域 K))
  结论: ((sInf S : 子域 K) : 集合 K) = ⋂ s in S, ↑s
  证明: show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s in S, ↑s by simp

@[simp]

Depends on / 依赖: Subfield, Subfield.toSubring, Subring, toSubring
-/
theorem coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s in S, ↑s :=
  show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s in S, ↑s by simp

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (Subfield K)} {x : K}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: by
  simpa only [Set.mem_iInter] using! Set.ext_iff.1 (coe_sInf S) x

@[simp, norm_cast]

中文:
定理 mem_sInf
  条件: {S : 集合 (子域 K)} {x : K}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: by
  simpa only [Set.mem_iInter] using! Set.ext_iff.1 (coe_sInf S) x

@[simp, norm_cast]

Depends on / 依赖: DivisionRing, DivisionRing.isDomain, IsDomain, Set.ext_iff, Set.mem_iInter, coe_sInf, ext_iff, isDomain, mem_iInter
-/
theorem mem_sInf {S : Set (Subfield K)} {x : K} : x in sInf S ↔ forall p in S, x in p := by
  simpa only [Set.mem_iInter] using! Set.ext_iff.1 (coe_sInf S) x

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> Subfield K}
  statement: (↑(⨅ i, S i) : Set K) = ⋂ i, S i
  proof: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> 子域 K}
  结论: (↑(⨅ i, S i) : 集合 K) = ⋂ i, S i
  证明: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

Depends on / 依赖: Set.biInter_range, biInter_range, coe_sInf
-/
theorem coe_iInf {ι : Sort*} {S : ι -> Subfield K} : (↑(⨅ i, S i) : Set K) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> Subfield K} {x : K}
  statement: x in ⨅ i, S i ↔ forall i, x in S i
  proof: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> 子域 K} {x : K}
  结论: x in ⨅ i, S i ↔ 对任意 i, x in S i
  证明: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> Subfield K} {x : K} : x in ⨅ i, S i ↔ forall i, x in S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/--
theorem `sInf_toSubring` / 定理 `sInf_toSubring`

English:
theorem sInf_toSubring
  given: (s : Set (Subfield K))
  proof: by
  ext x
  simp [mem_sInf]

中文:
定理 sInf_toSubring
  条件: (s : 集合 (子域 K))
  证明: by
  ext x
  simp [mem_sInf]

Depends on / 依赖: mem_sInf
-/
theorem sInf_toSubring (s : Set (Subfield K)) :
    (sInf s).toSubring = ⨅ t in s, Subfield.toSubring t := by
  ext x
  simp [mem_sInf]

/--
theorem `isGLB_sInf` / 定理 `isGLB_sInf`

English:
theorem isGLB_sInf
  given: (S : Set (Subfield K))
  statement: IsGLB S (sInf S)
  proof: by
  have : forall {s t : Subfield K}, (s : Set K) <= t ↔ s <= t := by simp [SetLike.coe_subset_coe]
  refine IsGLB.of_image this ?_
  convert! isGLB_biInf (s := S) (f := SetLike.coe)
  exact coe_sInf _

中文:
定理 isGLB_sInf
  条件: (S : 集合 (子域 K))
  结论: IsGLB S (sInf S)
  证明: by
  have : forall {s t : Subfield K}, (s : Set K) <= t ↔ s <= t := by simp [SetLike.coe_subset_coe]
  refine IsGLB.of_image this ?_
  convert! isGLB_biInf (s := S) (f := SetLike.coe)
  exact coe_sInf _

Depends on / 依赖: IsGLB.of_image, SetLike, SetLike.coe, SetLike.coe_subset_coe, Subfield, coe_sInf, coe_subset_coe, convert, isGLB_biInf, of_image
-/
theorem isGLB_sInf (S : Set (Subfield K)) : IsGLB S (sInf S) := by
  have : forall {s t : Subfield K}, (s : Set K) <= t ↔ s <= t := by simp [SetLike.coe_subset_coe]
  refine IsGLB.of_image this ?_
  convert! isGLB_biInf (s := S) (f := SetLike.coe)
  exact coe_sInf _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subfield K)
  body: { completeLatticeOfInf (Subfield K) isGLB_sInf with
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

中文:
实例 :
  签名: 完备格 (子域 K)
  定义体: { completeLatticeOfInf (Subfield K) isGLB_sInf with
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

Depends on / 依赖: And.left, And.right, Subfield, completeLatticeOfInf, inf_le_left, inf_le_right, isGLB_sInf, le_inf, le_top
-/
instance : CompleteLattice (Subfield K) :=
  { completeLatticeOfInf (Subfield K) isGLB_sInf with
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

/-! ### subfield closure of a subset -/

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Set K)
  body: sInf {S | s subseteq S}

中文:
定义 closure
  签名: (s : 集合 K)
  定义体: sInf {S | s subseteq S}

Depends on / 依赖: Field.toGrindField, Lean.Grind.Field, subseteq, toGrindField
-/
def closure (s : Set K) : Subfield K := sInf {S | s subseteq S}

/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {x : K} {s : Set K}
  statement: x in closure s ↔ forall S : Subfield K, s subseteq S -> x in S
  proof: mem_sInf

中文:
定理 mem_closure
  条件: {x : K} {s : 集合 K}
  结论: x in closure s ↔ 对任意 S : 子域 K, s subseteq S -> x in S
  证明: mem_sInf

Depends on / 依赖: mem_sInf
-/
theorem mem_closure {x : K} {s : Set K} : x in closure s ↔ forall S : Subfield K, s subseteq S -> x in S :=
  mem_sInf

/-- The subfield generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `subset_closure` / 定理 `subset_closure`

English:
theorem subset_closure
  given: {s : Set K}
  statement: s subseteq closure s
  proof: fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]

中文:
定理 subset_closure
  条件: {s : 集合 K}
  结论: s subseteq closure s
  证明: fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: mem_closure
-/
theorem subset_closure {s : Set K} : s subseteq closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]
/--
theorem `mem_closure_of_mem` / 定理 `mem_closure_of_mem`

English:
theorem mem_closure_of_mem
  given: {s : Set K} {x : K} (hx : x in s)
  statement: x in closure s
  proof: subset_closure hx

中文:
定理 mem_closure_of_mem
  条件: {s : 集合 K} {x : K} (hx : x in s)
  结论: x in closure s
  证明: subset_closure hx

Depends on / 依赖: subset_closure
-/
theorem mem_closure_of_mem {s : Set K} {x : K} (hx : x in s) : x in closure s := subset_closure hx

/--
theorem `subring_closure_le` / 定理 `subring_closure_le`

English:
theorem subring_closure_le
  given: (s : Set K)
  statement: Subring.closure s <= (closure s).toSubring
  proof: Subring.closure_le.mpr subset_closure

中文:
定理 subring_closure_le
  条件: (s : 集合 K)
  结论: 子环.closure s <= (closure s).toSubring
  证明: Subring.closure_le.mpr subset_closure

Depends on / 依赖: Subring, Subring.closure_le.mpr, closure_le, subset_closure
-/
theorem subring_closure_le (s : Set K) : Subring.closure s <= (closure s).toSubring :=
  Subring.closure_le.mpr subset_closure

/--
theorem `notMem_of_notMem_closure` / 定理 `notMem_of_notMem_closure`

English:
theorem notMem_of_notMem_closure
  given: {s : Set K} {P : K} (hP : P ∉ closure s)
  statement: P ∉ s
  proof: fun h =>
  hP (subset_closure h)

中文:
定理 notMem_of_notMem_closure
  条件: {s : 集合 K} {P : K} (hP : P ∉ closure s)
  结论: P ∉ s
  证明: fun h =>
  hP (subset_closure h)

Depends on / 依赖: Field.isDomain, IsDomain, isDomain
-/
theorem notMem_of_notMem_closure {s : Set K} {P : K} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A subfield `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
/--
theorem `closure_le` / 定理 `closure_le`

English:
theorem closure_le
  given: {s : Set K} {t : Subfield K}
  statement: closure s <= t ↔ s subseteq t
  proof: ⟨Set.Subset.trans subset_closure, fun h _ hx => mem_closure.mp hx t h⟩

中文:
定理 closure_le
  条件: {s : 集合 K} {t : 子域 K}
  结论: closure s <= t ↔ s subseteq t
  证明: ⟨Set.Subset.trans subset_closure, fun h _ hx => mem_closure.mp hx t h⟩

Depends on / 依赖: Set.Subset.trans, Subset, mem_closure, mem_closure.mp, subset_closure
-/
theorem closure_le {s : Set K} {t : Subfield K} : closure s <= t ↔ s subseteq t :=
  ⟨Set.Subset.trans subset_closure, fun h _ hx => mem_closure.mp hx t h⟩

/-- Subfield closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
/--
theorem `closure_mono` / 定理 `closure_mono`

English:
theorem closure_mono
  given: ⦃s t
  statement: Set K⦄ (h : s subseteq t) : closure s <= closure t
  proof: closure_le.2 Set.Subset.trans h subset_closure

中文:
定理 closure_mono
  条件: ⦃s t
  结论: 集合 K⦄ (h : s subseteq t) : closure s <= closure t
  证明: closure_le.2 Set.Subset.trans h subset_closure

Depends on / 依赖: Set.Subset.trans, Subset, closure_le, subset_closure
-/
theorem closure_mono ⦃s t : Set K⦄ (h : s subseteq t) : closure s <= closure t :=
closure_le.2 Set.Subset.trans h subset_closure

/--
theorem `closure_eq_of_le` / 定理 `closure_eq_of_le`

English:
theorem closure_eq_of_le
  given: {s : Set K} {t : Subfield K} (h₁ : s subseteq t) (h₂ : t <= closure s)
  proof: le_antisymm (closure_le.2 h₁) h₂

中文:
定理 closure_eq_of_le
  条件: {s : 集合 K} {t : 子域 K} (h₁ : s subseteq t) (h₂ : t <= closure s)
  证明: le_antisymm (closure_le.2 h₁) h₂

Depends on / 依赖: closure_le, le_antisymm
-/
theorem closure_eq_of_le {s : Set K} {t : Subfield K} (h₁ : s subseteq t) (h₂ : t <= closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
/--
theorem `closure_induction` / 定理 `closure_induction`

English:
theorem closure_induction
  statement: {s : Set K} {p : forall x in closure s, Prop}
  proof: letI : Subfield K :=
    { carrier := {x | exists hx, p x hx}
      mul_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, mul _ _ _ _ hx hy⟩
      one_mem' := ⟨_, one⟩
      add_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, add _ _ _ _ hx hy⟩
      zero_mem' := ⟨zero_mem _, by
        simp_rw [← @

中文:
定理 closure_induction
  结论: {s : 集合 K} {p : 对任意 x in closure s, 命题}
  证明: letI : Subfield K :=
    { carrier := {x | exists hx, p x hx}
      mul_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, mul _ _ _ _ hx hy⟩
      one_mem' := ⟨_, one⟩
      add_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, add _ _ _ _ hx hy⟩
      zero_mem' := ⟨zero_mem _, by
        simp_rw [← @

Depends on / 依赖: Subfield, add_mem, add_neg_cancel, carrier, closure_le, inv_mem, mul_mem, neg_mem, one_mem, simp_rw, zero_mem
-/
theorem closure_induction {s : Set K} {p : forall x in closure s, Prop}
    (mem : forall x hx, p x (subset_closure hx))
    (one : p 1 (one_mem _)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (neg : forall x hx, p x hx -> p (-x) (neg_mem hx)) (inv : forall x hx, p x hx -> p x⁻¹ (inv_mem hx))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    {x} (h : x in closure s) : p x h :=
  letI : Subfield K :=
    { carrier := {x | exists hx, p x hx}
      mul_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, mul _ _ _ _ hx hy⟩
      one_mem' := ⟨_, one⟩
      add_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, add _ _ _ _ hx hy⟩
      zero_mem' := ⟨zero_mem _, by
        simp_rw [← @add_neg_cancel K _ 1]; exact add _ _ _ _ one (neg _ _ one)⟩
      neg_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, neg _ _ hx⟩
      inv_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, inv _ _ hx⟩ }
  ((closure_le (t := this)).2 (fun x hx => ⟨_, mem x hx⟩) h).2

variable (K) in
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (@closure K _) (↑) where
  body: closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

中文:
定义 gi
  签名: : Galois嵌入 (@closure K _) (↑) where
  定义体: closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
-/
protected def gi : GaloisInsertion (@closure K _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

/-- Closure of a subfield `S` equals `S`. -/
@[simp]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  given: (s : Subfield K)
  statement: closure (s : Set K) = s
  proof: (Subfield.gi K).l_u_eq s

@[simp]

中文:
定理 closure_eq
  条件: (s : 子域 K)
  结论: closure (s : 集合 K) = s
  证明: (Subfield.gi K).l_u_eq s

@[simp]

Depends on / 依赖: Subfield, Subfield.gi, l_u_eq
-/
theorem closure_eq (s : Subfield K) : closure (s : Set K) = s :=
  (Subfield.gi K).l_u_eq s

@[simp]
/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure (∅ : Set K) = ⊥
  proof: (Subfield.gi K).gc.l_bot

@[simp]

中文:
定理 closure_empty
  结论: closure (∅ : 集合 K) = ⊥
  证明: (Subfield.gi K).gc.l_bot

@[simp]

Depends on / 依赖: Subfield, Subfield.gi, gc.l_bot, l_bot
-/
theorem closure_empty : closure (∅ : Set K) = ⊥ :=
  (Subfield.gi K).gc.l_bot

@[simp]
/--
theorem `closure_univ` / 定理 `closure_univ`

English:
theorem closure_univ
  statement: closure (Set.univ : Set K) = ⊤
  proof: @coe_top K _ ▸ closure_eq ⊤

中文:
定理 closure_univ
  结论: closure (集合.univ : 集合 K) = ⊤
  证明: @coe_top K _ ▸ closure_eq ⊤

Depends on / 依赖: closure_eq, coe_top
-/
theorem closure_univ : closure (Set.univ : Set K) = ⊤ :=
  @coe_top K _ ▸ closure_eq ⊤

/--
theorem `closure_union` / 定理 `closure_union`

English:
theorem closure_union
  given: (s t : Set K)
  statement: closure (s union t) = closure s ⊔ closure t
  proof: (Subfield.gi K).gc.l_sup

中文:
定理 closure_union
  条件: (s t : 集合 K)
  结论: closure (s union t) = closure s ⊔ closure t
  证明: (Subfield.gi K).gc.l_sup

Depends on / 依赖: Subfield, Subfield.gi, gc.l_sup, l_sup
-/
theorem closure_union (s t : Set K) : closure (s union t) = closure s ⊔ closure t :=
  (Subfield.gi K).gc.l_sup

/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: {ι} (s : ι -> Set K)
  statement: closure (⋃ i, s i) = ⨆ i, closure (s i)
  proof: (Subfield.gi K).gc.l_iSup

中文:
定理 closure_iUnion
  条件: {ι} (s : ι -> 集合 K)
  结论: closure (⋃ i, s i) = ⨆ i, closure (s i)
  证明: (Subfield.gi K).gc.l_iSup

Depends on / 依赖: Subfield, Subfield.gi, gc.l_iSup, l_iSup
-/
theorem closure_iUnion {ι} (s : ι -> Set K) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subfield.gi K).gc.l_iSup

/--
theorem `closure_sUnion` / 定理 `closure_sUnion`

English:
theorem closure_sUnion
  given: (s : Set (Set K))
  statement: closure (⋃₀ s) = ⨆ t in s, closure t
  proof: (Subfield.gi K).gc.l_sSup

中文:
定理 closure_sUnion
  条件: (s : 集合 (集合 K))
  结论: closure (⋃₀ s) = ⨆ t in s, closure t
  证明: (Subfield.gi K).gc.l_sSup

Depends on / 依赖: Subfield, Subfield.gi, gc.l_sSup, l_sSup
-/
theorem closure_sUnion (s : Set (Set K)) : closure (⋃₀ s) = ⨆ t in s, closure t :=
  (Subfield.gi K).gc.l_sSup

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (s t : Subfield K) (f : K ->+* L)
  statement: (s ⊔ t).map f = s.map f ⊔ t.map f
  proof: (gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (s t : 子域 K) (f : K ->+* L)
  结论: (s ⊔ t).map f = s.map f ⊔ t.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (s t : Subfield K) (f : K ->+* L) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : K ->+* L) (s : ι -> Subfield K)
  proof: (gc_map_comap f).l_iSup

中文:
定理 map_iSup
  条件: {ι : 类型层*} (f : K ->+* L) (s : ι -> 子域 K)
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : K ->+* L) (s : ι -> Subfield K) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (s t : Subfield K) (f : K ->+* L)
  statement: (s ⊓ t).map f = s.map f ⊓ t.map f
  proof: SetLike.coe_injective (Set.image_inter f.injective)

中文:
定理 map_inf
  条件: (s t : 子域 K) (f : K ->+* L)
  结论: (s ⊓ t).map f = s.map f ⊓ t.map f
  证明: SetLike.coe_injective (Set.image_inter f.injective)

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, f.injective, image_inter, injective
-/
theorem map_inf (s t : Subfield K) (f : K ->+* L) : (s ⊓ t).map f = s.map f ⊓ t.map f :=
  SetLike.coe_injective (Set.image_inter f.injective)

/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  given: {ι : Sort*} [Nonempty ι] (f : K ->+* L) (s : ι -> Subfield K)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

中文:
定理 map_iInf
  条件: {ι : 类型层*} [非空 ι] (f : K ->+* L) (s : ι -> 子域 K)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, f.injective, image_iInter_eq, injOn_of_injective, injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : K ->+* L) (s : ι -> Subfield K) :
    (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (s t : Subfield L) (f : K ->+* L)
  statement: (s ⊓ t).comap f = s.comap f ⊓ t.comap f
  proof: (gc_map_comap f).u_inf

中文:
定理 comap_inf
  条件: (s t : 子域 L) (f : K ->+* L)
  结论: (s ⊓ t).comap f = s.comap f ⊓ t.comap f
  证明: (gc_map_comap f).u_inf

Depends on / 依赖: gc_map_comap, u_inf
-/
theorem comap_inf (s t : Subfield L) (f : K ->+* L) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : K ->+* L) (s : ι -> Subfield L)
  proof: (gc_map_comap f).u_iInf

@[simp]

中文:
定理 comap_iInf
  条件: {ι : 类型层*} (f : K ->+* L) (s : ι -> 子域 L)
  证明: (gc_map_comap f).u_iInf

@[simp]

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : K ->+* L) (s : ι -> Subfield L) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : K ->+* L)
  statement: (⊥ : Subfield K).map f = ⊥
  proof: (gc_map_comap f).l_bot

@[simp]

中文:
定理 map_bot
  条件: (f : K ->+* L)
  结论: (⊥ : 子域 K).map f = ⊥
  证明: (gc_map_comap f).l_bot

@[simp]

Depends on / 依赖: DivisionRing, DivisionRing.toDivisionSemiring, DivisionSemiring, gc_map_comap, l_bot, toDivisionSemiring
-/
theorem map_bot (f : K ->+* L) : (⊥ : Subfield K).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : K ->+* L)
  statement: (⊤ : Subfield L).comap f = ⊤
  proof: (gc_map_comap f).u_top

中文:
定理 comap_top
  条件: (f : K ->+* L)
  结论: (⊤ : 子域 L).comap f = ⊤
  证明: (gc_map_comap f).u_top

Depends on / 依赖: Field.toSemifield, Semifield, gc_map_comap, toSemifield, u_top
-/
theorem comap_top (f : K ->+* L) : (⊤ : Subfield L).comap f = ⊤ :=
  (gc_map_comap f).u_top

/--
theorem `mem_iSup_of_directed` / 定理 `mem_iSup_of_directed`

English:
theorem mem_iSup_of_directed
  statement: {ι} [hι : Nonempty ι] {S : ι -> Subfield K} (hS : Directed (· <= ·) S)
  proof: by
  let s : Subfield K :=
    { __ := Subring.copy _ _ (Subring.coe_iSup_of_directed hS).symm
      inv_mem' := fun _ hx => have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).inv_mem hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (S i : Set K

中文:
定理 mem_iSup_of_directed
  结论: {ι} [hι : 非空 ι] {S : ι -> 子域 K} (hS : Directed (· <= ·) S)
  证明: by
  let s : Subfield K :=
    { __ := Subring.copy _ _ (Subring.coe_iSup_of_directed hS).symm
      inv_mem' := fun _ hx => have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).inv_mem hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (S i : Set K

Depends on / 依赖: DivisionSemiring, DivisionSemiring.nnqsmul, Set.iUnion_subset, Set.mem_iUnion, Set.mem_iUnion.mp, Set.mem_iUnion.mpr, Subfield, Subring, Subring.coe_iSup_of_directed, Subring.copy, coe_iSup_of_directed, iSup_le, iUnion_subset, inv_mem, le_antisymm, le_iSup, mem_iUnion, nnqsmul, smulDivisionSemiring
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subfield K} (hS : Directed (· <= ·) S)
    {x : K} : (x in ⨆ i, S i) ↔ exists i, x in S i := by
  let s : Subfield K :=
    { __ := Subring.copy _ _ (Subring.coe_iSup_of_directed hS).symm
      inv_mem' := fun _ hx => have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).inv_mem hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (S i : Set K)) i) (Set.iUnion_subset fun _ => le_iSup S _)
  exact this ▸ Set.mem_iUnion

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  given: {ι} [hι : Nonempty ι] {S : ι -> Subfield K} (hS : Directed (· <= ·) S)
  proof: Set.ext fun x => by simp [mem_iSup_of_directed hS]

中文:
定理 coe_iSup_of_directed
  条件: {ι} [hι : 非空 ι] {S : ι -> 子域 K} (hS : Directed (· <= ·) S)
  证明: Set.ext fun x => by simp [mem_iSup_of_directed hS]

Depends on / 依赖: Set.ext, mem_iSup_of_directed
-/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subfield K} (hS : Directed (· <= ·) S) :
    ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]

/--
theorem `mem_sSup_of_directedOn` / 定理 `mem_sSup_of_directedOn`

English:
theorem mem_sSup_of_directedOn
  statement: {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S)
  proof: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

中文:
定理 mem_sSup_of_directedOn
  结论: {S : 集合 (子域 K)} (Sne : S.非空) (hS : DirectedOn (· <= ·) S)
  证明: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

Depends on / 依赖: Nonempty, Sne.to_subtype, Subtype, Subtype.exists, directed_val, exists_prop, hS.directed_val, mem_iSup_of_directed, sSup_eq_iSup, to_subtype
-/
theorem mem_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S)
    {x : K} : x in sSup S ↔ exists s in S, x in s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

/--
theorem `coe_sSup_of_directedOn` / 定理 `coe_sSup_of_directedOn`

English:
theorem coe_sSup_of_directedOn
  statement: {S : Set (Subfield K)} (Sne : S.Nonempty)
  proof: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

中文:
定理 coe_sSup_of_directedOn
  结论: {S : 集合 (子域 K)} (Sne : S.非空)
  证明: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

Depends on / 依赖: Set.ext, mem_sSup_of_directedOn
-/
theorem coe_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) : (↑(sSup S) : Set K) = ⋃ s in S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

end Subfield

variable (L) in
/-- A field is finitely generated if it is the closure of a finite subset. -/
@[mk_iff fg_iff]
/--
Definition of `Field.FG` / `Field.FG` 的定义

English:
class Field.FG
  parameters: : Prop where
  axioms and operations (1):
    - finitely_generated : exists S : Finset L, Subfield.closure (S : Set L) = ⊤

中文:
类 域.FG
  参数: : 命题 where
  公理与运算 (1 个):
    - finitely_generated : 存在 S : 有限集 L, 子域.closure (S : 集合 L) = ⊤
-/
protected class Field.FG : Prop where
  finitely_generated : exists S : Finset L, Subfield.closure (S : Set L) = ⊤

namespace RingHom

variable {s : Subfield K}

open Subfield

/--
Definition of `rangeRestrictField` / `rangeRestrictField` 的定义

English:
definition rangeRestrictField
  signature: (f : K ->+* L)
  body: f.rangeSRestrict

@[simp]

中文:
定义 rangeRestrictField
  签名: (f : K ->+* L)
  定义体: f.rangeSRestrict

@[simp]

Depends on / 依赖: f.rangeSRestrict, rangeSRestrict, smulDivisionRing
-/
def rangeRestrictField (f : K ->+* L) : K ->+* f.fieldRange :=
  f.rangeSRestrict

@[simp]
/--
theorem `coe_rangeRestrictField` / 定理 `coe_rangeRestrictField`

English:
theorem coe_rangeRestrictField
  given: (f : K ->+* L) (x : K)
  statement: (f.rangeRestrictField x : L) = f x
  proof: rfl

中文:
定理 coe_rangeRestrictField
  条件: (f : K ->+* L) (x : K)
  结论: (f.rangeRestrictField x : L) = f x
  证明: rfl
-/
theorem coe_rangeRestrictField (f : K ->+* L) (x : K) : (f.rangeRestrictField x : L) = f x :=
  rfl

/--
theorem `rangeRestrictField_bijective` / 定理 `rangeRestrictField_bijective`

English:
theorem rangeRestrictField_bijective
  given: (f : K ->+* L)
  statement: Function.Bijective (rangeRestrictField f)
  proof: (Equiv.ofInjective f f.injective).bijective

中文:
定理 rangeRestrictField_bijective
  条件: (f : K ->+* L)
  结论: 函数.双射 (rangeRestrictField f)
  证明: (Equiv.ofInjective f f.injective).bijective

Depends on / 依赖: Equiv.ofInjective, bijective, f.injective, injective, ofInjective
-/
theorem rangeRestrictField_bijective (f : K ->+* L) : Function.Bijective (rangeRestrictField f) :=
  (Equiv.ofInjective f f.injective).bijective

/--
`RingHom.rangeRestrictField` as a `RingEquiv`.
-/
@[simps! apply_coe]
/--
Definition of `rangeRestrictFieldEquiv` / `rangeRestrictFieldEquiv` 的定义

English:
definition rangeRestrictFieldEquiv
  signature: (f : K ->+* L)
  body: RingEquiv.ofBijective f.rangeRestrictField f.rangeRestrictField_bijective

@[simp]

中文:
定义 rangeRestrictFieldEquiv
  签名: (f : K ->+* L)
  定义体: RingEquiv.ofBijective f.rangeRestrictField f.rangeRestrictField_bijective

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, f.rangeRestrictField, f.rangeRestrictField_bijective, ofBijective, rangeRestrictField, rangeRestrictField_bijective
-/
noncomputable def rangeRestrictFieldEquiv (f : K ->+* L) : K ≃+* f.fieldRange :=
  RingEquiv.ofBijective f.rangeRestrictField f.rangeRestrictField_bijective

@[simp]
/--
theorem `rangeRestrictFieldEquiv_apply_symm_apply` / 定理 `rangeRestrictFieldEquiv_apply_symm_apply`

English:
theorem rangeRestrictFieldEquiv_apply_symm_apply
  given: (f : K ->+* L) (x : f.fieldRange)
  proof: by
  rw [← rangeRestrictFieldEquiv_apply_coe]; rw [RingEquiv.apply_symm_apply]

中文:
定理 rangeRestrictFieldEquiv_apply_symm_apply
  条件: (f : K ->+* L) (x : f.fieldRange)
  证明: by
  rw [← rangeRestrictFieldEquiv_apply_coe]; rw [RingEquiv.apply_symm_apply]

Depends on / 依赖: RingEquiv, RingEquiv.apply_symm_apply, apply_symm_apply, rangeRestrictFieldEquiv_apply_coe
-/
theorem rangeRestrictFieldEquiv_apply_symm_apply (f : K ->+* L) (x : f.fieldRange) :
    f (f.rangeRestrictFieldEquiv.symm x) = x := by
  rw [← rangeRestrictFieldEquiv_apply_coe]; rw [RingEquiv.apply_symm_apply]

section eqLocus

variable {L : Type v} [Semiring L]

/--
Definition of `eqLocusField` / `eqLocusField` 的定义

English:
definition eqLocusField
  signature: (f g : K ->+* L)
  body: (f : K ->+* L).eqLocus g
  inv_mem' _ := eq_on_inv₀ f g
  carrier := { x | f x = g x }

@[simp]

中文:
定义 eqLocusField
  签名: (f g : K ->+* L)
  定义体: (f : K ->+* L).eqLocus g
  inv_mem' _ := eq_on_inv₀ f g
  carrier := { x | f x = g x }

@[simp]

Depends on / 依赖: eqLocus
-/
def eqLocusField (f g : K ->+* L) : Subfield K where
  __ := (f : K ->+* L).eqLocus g
  inv_mem' _ := eq_on_inv₀ f g
  carrier := { x | f x = g x }

@[simp]
/--
theorem `mem_eqLocusField` / 定理 `mem_eqLocusField`

English:
theorem mem_eqLocusField
  given: {f g : K ->+* L} {x : K}
  statement: x in f.eqLocusField g ↔ f x = g x
  proof: Iff.rfl

中文:
定理 mem_eqLocusField
  条件: {f g : K ->+* L} {x : K}
  结论: x in f.eqLocusField g ↔ f x = g x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_eqLocusField {f g : K ->+* L} {x : K} : x in f.eqLocusField g ↔ f x = g x := Iff.rfl

/--
theorem `eqOn_field_closure` / 定理 `eqOn_field_closure`

English:
theorem eqOn_field_closure
  given: {f g : K ->+* L} {s : Set K} (h : Set.EqOn f g s)
  proof: show closure s <= f.eqLocusField g from closure_le.2 h

中文:
定理 eqOn_field_closure
  条件: {f g : K ->+* L} {s : 集合 K} (h : 集合.EqOn f g s)
  证明: show closure s <= f.eqLocusField g from closure_le.2 h

Depends on / 依赖: closure, closure_le, eqLocusField, f.eqLocusField
-/
theorem eqOn_field_closure {f g : K ->+* L} {s : Set K} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s <= f.eqLocusField g from closure_le.2 h

/--
theorem `eq_of_eqOn_subfield_top` / 定理 `eq_of_eqOn_subfield_top`

English:
theorem eq_of_eqOn_subfield_top
  given: {f g : K ->+* L} (h : Set.EqOn f g (⊤ : Subfield K))
  statement: f = g
  proof: ext fun _ => h trivial

中文:
定理 eq_of_eqOn_subfield_top
  条件: {f g : K ->+* L} (h : 集合.EqOn f g (⊤ : 子域 K))
  结论: f = g
  证明: ext fun _ => h trivial
-/
theorem eq_of_eqOn_subfield_top {f g : K ->+* L} (h : Set.EqOn f g (⊤ : Subfield K)) : f = g :=
  ext fun _ => h trivial

/--
theorem `eq_of_eqOn_of_field_closure_eq_top` / 定理 `eq_of_eqOn_of_field_closure_eq_top`

English:
theorem eq_of_eqOn_of_field_closure_eq_top
  statement: {s : Set K} (hs : closure s = ⊤) {f g : K ->+* L}
  proof: eq_of_eqOn_subfield_top hs ▸ eqOn_field_closure h

中文:
定理 eq_of_eqOn_of_field_closure_eq_top
  结论: {s : 集合 K} (hs : closure s = ⊤) {f g : K ->+* L}
  证明: eq_of_eqOn_subfield_top hs ▸ eqOn_field_closure h

Depends on / 依赖: eqOn_field_closure, eq_of_eqOn_subfield_top
-/
theorem eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : closure s = ⊤) {f g : K ->+* L}
    (h : s.EqOn f g) : f = g :=
eq_of_eqOn_subfield_top hs ▸ eqOn_field_closure h

end eqLocus

/--
theorem `field_closure_preimage_le` / 定理 `field_closure_preimage_le`

English:
theorem field_closure_preimage_le
  given: (f : K ->+* L) (s : Set L)
  proof: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 field_closure_preimage_le
  条件: (f : K ->+* L) (s : 集合 L)
  证明: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem field_closure_preimage_le (f : K ->+* L) (s : Set L) :
    closure (f ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

/--
theorem `map_field_closure` / 定理 `map_field_closure`

English:
theorem map_field_closure
  given: (f : K ->+* L) (s : Set K)
  statement: (closure s).map f = closure (f '' s)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subfield.gi L).gc (Subfield.gi K).gc
    fun _ => rfl

中文:
定理 map_field_closure
  条件: (f : K ->+* L) (s : 集合 K)
  结论: (closure s).map f = closure (f '' s)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subfield.gi L).gc (Subfield.gi K).gc
    fun _ => rfl

Depends on / 依赖: Set.image_preimage.l_comm_of_u_comm, Subfield, Subfield.gi, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_field_closure (f : K ->+* L) (s : Set K) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subfield.gi L).gc (Subfield.gi K).gc
    fun _ => rfl

end RingHom

namespace Subfield

open RingHom

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : Subfield K} (h : S <= T)
  body: S.subtype.codRestrict _ fun x => h x.2

@[simp]

中文:
定义 inclusion
  签名: {S T : 子域 K} (h : S <= T)
  定义体: S.subtype.codRestrict _ fun x => h x.2

@[simp]

Depends on / 依赖: S.subtype.codRestrict, codRestrict, subtype
-/
def inclusion {S T : Subfield K} (h : S <= T) : S ->+* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
/--
theorem `fieldRange_subtype` / 定理 `fieldRange_subtype`

English:
theorem fieldRange_subtype
  given: (s : Subfield K)
  statement: s.subtype.fieldRange = s
  proof: SetLike.ext' (coe_rangeS _).trans Subtype.range_coe

中文:
定理 fieldRange_subtype
  条件: (s : 子域 K)
  结论: s.subtype.fieldRange = s
  证明: SetLike.ext' (coe_rangeS _).trans Subtype.range_coe

Depends on / 依赖: SetLike, SetLike.ext, Subtype, Subtype.range_coe, coe_rangeS, range_coe
-/
theorem fieldRange_subtype (s : Subfield K) : s.subtype.fieldRange = s :=
SetLike.ext' (coe_rangeS _).trans Subtype.range_coe

end Subfield

namespace RingEquiv

variable {s t : Subfield K}

/--
Definition of `subfieldCongr` / `subfieldCongr` 的定义

English:
definition subfieldCongr
  signature: (h : s = t)
  body: { Equiv.setCongr <| SetLike.ext'_iff.1 h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 subfieldCongr
  签名: (h : s = t)
  定义体: { Equiv.setCongr <| SetLike.ext'_iff.1 h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: Equiv.setCongr, Semifield, Semifield.toIsField, SetLike, SetLike.ext, _iff, isDomain, map_add, map_mul, setCongr, toIsField
-/
def subfieldCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| SetLike.ext'_iff.1 h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

end RingEquiv

namespace Subfield

variable {s : Set K}

/--
theorem `closure_preimage_le` / 定理 `closure_preimage_le`

English:
theorem closure_preimage_le
  given: (f : K ->+* L) (s : Set L)
  statement: closure (f ⁻¹' s) <= (closure s).comap f
  proof: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 closure_preimage_le
  条件: (f : K ->+* L) (s : 集合 L)
  结论: closure (f ⁻¹' s) <= (closure s).comap f
  证明: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem closure_preimage_le (f : K ->+* L) (s : Set L) : closure (f ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

section Commutative

variable {K : Type u} [Field K] (s : Subfield K)

/--
theorem `multiset_prod_mem` / 定理 `multiset_prod_mem`

English:
theorem multiset_prod_mem
  given: (m : Multiset K)
  statement: (forall a in m, a in s) -> m.prod in s
  proof: multiset_prod_mem m

中文:
定理 multiset_prod_mem
  条件: (m : Multiset K)
  结论: (对任意 a in m, a in s) -> m.乘积 in s
  证明: multiset_prod_mem m
-/
protected theorem multiset_prod_mem (m : Multiset K) : (forall a in m, a in s) -> m.prod in s :=
  multiset_prod_mem m

/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  given: {ι : Type*} {t : Finset ι} {f : ι -> K} (h : forall c in t, f c in s)
  proof: prod_mem h

中文:
定理 prod_mem
  条件: {ι : 类型} {t : 有限集 ι} {f : ι -> K} (h : 对任意 c in t, f c in s)
  证明: prod_mem h
-/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι -> K} (h : forall c in t, f c in s) :
    (∏ i in t, f i) in s :=
  prod_mem h

/--
Instance `toAlgebra` / 实例 `toAlgebra`

English:
instance toAlgebra
  signature: : Algebra s K
  body: inferInstance

中文:
实例 toAlgebra
  签名: : 代数 s K
  定义体: inferInstance
-/
instance toAlgebra : Algebra s K :=
  inferInstance

/--
theorem `algebraMap_ofSubfield` / 定理 `algebraMap_ofSubfield`

English:
theorem algebraMap_ofSubfield
  statement: algebraMap s K = s.subtype
  proof: rfl

中文:
定理 algebraMap_ofSubfield
  结论: algebraMap s K = s.subtype
  证明: rfl
-/
theorem algebraMap_ofSubfield : algebraMap s K = s.subtype :=
  rfl

/--
Definition of `commClosure` / `commClosure` 的定义

English:
definition commClosure
  signature: (s : Set K)
  body: {z : K | exists x in Subring.closure s, exists y in Subring.closure s, x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    exact ⟨-y, Subring.

中文:
定义 commClosure
  签名: (s : 集合 K)
  定义体: {z : K | exists x in Subring.closure s, exists y in Subring.closure s, x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    exact ⟨-y, Subring.
-/
private def commClosure (s : Set K) : Subfield K where
  carrier := {z : K | exists x in Subring.closure s, exists y in Subring.closure s, x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    exact ⟨-y, Subring.neg_mem _ hy, z, hz, x_eq ▸ neg_div _ _⟩
  inv_mem' x := by rintro ⟨y, hy, z, hz, x_eq⟩; exact ⟨z, hz, y, hy, x_eq ▸ (inv_div _ _).symm⟩
  add_mem' x_mem y_mem := by
    -- Use `id` in the next 2 `obtain`s so that assumptions stay there for the `rwa`s below
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem
    by_cases hx0 : dx = 0; · rwa [hx0, div_zero, zero_add]
    by_cases hy0 : dy = 0; · rwa [hy0, div_zero, add_zero]
    exact
      ⟨nx * dy + dx * ny, Subring.add_mem _ (Subring.mul_mem _ hnx hdy) (Subring.mul_mem _ hdx hny),
        dx * dy, Subring.mul_mem _ hdx hdy, (div_add_div nx ny hx0 hy0).symm⟩
  mul_mem' := by
    rintro _ _ ⟨nx, hnx, dx, hdx, rfl⟩ ⟨ny, hny, dy, hdy, rfl⟩
    exact ⟨nx * ny, Subring.mul_mem _ hnx hny, dx * dy, Subring.mul_mem _ hdx hdy,
      (div_mul_div_comm _ _ _ _).symm⟩

/--
theorem `commClosure_eq_closure` / 定理 `commClosure_eq_closure`

English:
theorem commClosure_eq_closure
  given: {s : Set K}
  statement: commClosure s = closure s
  proof: le_antisymm
    (fun _ ⟨_, hy, _, hz, eq⟩ => eq ▸ div_mem (subring_closure_le s hy) (subring_closure_le s hz))
    (closure_le.mpr fun x hx => ⟨x, Subring.subset_closure hx, 1, Subring.one_mem _, div_one x⟩)

中文:
定理 commClosure_eq_closure
  条件: {s : 集合 K}
  结论: commClosure s = closure s
  证明: le_antisymm
    (fun _ ⟨_, hy, _, hz, eq⟩ => eq ▸ div_mem (subring_closure_le s hy) (subring_closure_le s hz))
    (closure_le.mpr fun x hx => ⟨x, Subring.subset_closure hx, 1, Subring.one_mem _, div_one x⟩)
-/
private theorem commClosure_eq_closure {s : Set K} : commClosure s = closure s :=
  le_antisymm
    (fun _ ⟨_, hy, _, hz, eq⟩ => eq ▸ div_mem (subring_closure_le s hy) (subring_closure_le s hz))
    (closure_le.mpr fun x hx => ⟨x, Subring.subset_closure hx, 1, Subring.one_mem _, div_one x⟩)

/--
theorem `mem_closure_iff` / 定理 `mem_closure_iff`

English:
theorem mem_closure_iff
  given: {s : Set K} {x}
  proof: by
  rw [← commClosure_eq_closure]; rfl

中文:
定理 mem_closure_iff
  条件: {s : 集合 K} {x}
  证明: by
  rw [← commClosure_eq_closure]; rfl

Depends on / 依赖: commClosure_eq_closure
-/
theorem mem_closure_iff {s : Set K} {x} :
    x in closure s ↔ exists y in Subring.closure s, exists z in Subring.closure s, y / z = x := by
  rw [← commClosure_eq_closure]; rfl

end Commutative

end Subfield

namespace Subfield

/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (f : K ->+* L) (s : Subfield L)
  statement: (s.comap f).map f = s ⊓ f.fieldRange
  proof: SetLike.coe_injective Set.image_preimage_eq_inter_range

中文:
定理 map_comap_eq
  条件: (f : K ->+* L) (s : 子域 L)
  结论: (s.comap f).map f = s ⊓ f.fieldRange
  证明: SetLike.coe_injective Set.image_preimage_eq_inter_range

Depends on / 依赖: Set.image_preimage_eq_inter_range, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq_inter_range
-/
theorem map_comap_eq (f : K ->+* L) (s : Subfield L) : (s.comap f).map f = s ⊓ f.fieldRange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

/--
theorem `map_comap_eq_self` / 定理 `map_comap_eq_self`

English:
theorem map_comap_eq_self
  proof: by
  simpa only [inf_of_le_left h] using map_comap_eq f s

中文:
定理 map_comap_eq_self
  证明: by
  simpa only [inf_of_le_left h] using map_comap_eq f s

Depends on / 依赖: inf_of_le_left, map_comap_eq
-/
theorem map_comap_eq_self
    {f : K ->+* L} {s : Subfield L} (h : s <= f.fieldRange) : (s.comap f).map f = s := by
  simpa only [inf_of_le_left h] using map_comap_eq f s

/--
theorem `map_comap_eq_self_of_surjective` / 定理 `map_comap_eq_self_of_surjective`

English:
theorem map_comap_eq_self_of_surjective
  proof: SetLike.coe_injective (Set.image_preimage_eq _ hf)

中文:
定理 map_comap_eq_self_of_surjective
  证明: SetLike.coe_injective (Set.image_preimage_eq _ hf)

Depends on / 依赖: Set.image_preimage_eq, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq
-/
theorem map_comap_eq_self_of_surjective
    {f : K ->+* L} (hf : Function.Surjective f) (s : Subfield L) : (s.comap f).map f = s :=
  SetLike.coe_injective (Set.image_preimage_eq _ hf)

/--
theorem `comap_map` / 定理 `comap_map`

English:
theorem comap_map
  given: (f : K ->+* L) (s : Subfield K)
  statement: (s.map f).comap f = s
  proof: SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

中文:
定理 comap_map
  条件: (f : K ->+* L) (s : 子域 K)
  结论: (s.map f).comap f = s
  证明: SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

Depends on / 依赖: Set.preimage_image_eq, SetLike, SetLike.coe_injective, coe_injective, f.injective, injective, preimage_image_eq
-/
theorem comap_map (f : K ->+* L) (s : Subfield K) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

end Subfield

/-! ### Actions by `Subfield`s

These are just copies of the definitions about `Subsemiring` starting from
`Subsemiring.MulAction`.
-/
section Actions

namespace Subfield

variable {X Y}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: K X] (F
  body: inferInstanceAs (SMul F.toSubsemiring X)

中文:
实例 [标量乘法
  签名: K X] (F
  定义体: inferInstanceAs (SMul F.toSubsemiring X)

Depends on / 依赖: F.toSubsemiring, toSubsemiring
-/
instance [SMul K X] (F : Subfield K) : SMul F X :=
  inferInstanceAs (SMul F.toSubsemiring X)

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: [SMul K X] {F : Subfield K} (g : F) (m : X)
  statement: g • m = (g : K) • m
  proof: rfl

中文:
定理 smul_def
  条件: [标量乘法 K X] {F : 子域 K} (g : F) (m : X)
  结论: g • m = (g : K) • m
  证明: rfl
-/
theorem smul_def [SMul K X] {F : Subfield K} (g : F) (m : X) : g • m = (g : K) • m :=
  rfl

/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: [SMul K Y] [SMul X Y] [SMulCommClass K X Y] (F : Subfield K)
  body: inferInstanceAs (SMulCommClass F.toSubsemiring X Y)

中文:
实例 smulCommClass_left
  签名: [标量乘法 K Y] [标量乘法 X Y] [标量交换类 K X Y] (F : 子域 K)
  定义体: inferInstanceAs (SMulCommClass F.toSubsemiring X Y)

Depends on / 依赖: F.toSubsemiring, SMulCommClass, toSubsemiring
-/
instance smulCommClass_left [SMul K Y] [SMul X Y] [SMulCommClass K X Y] (F : Subfield K) :
    SMulCommClass F X Y :=
  inferInstanceAs (SMulCommClass F.toSubsemiring X Y)

/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: [SMul X Y] [SMul K Y] [SMulCommClass X K Y] (F : Subfield K)
  body: inferInstanceAs (SMulCommClass X F.toSubsemiring Y)

中文:
实例 smulCommClass_right
  签名: [标量乘法 X Y] [标量乘法 K Y] [标量交换类 X K Y] (F : 子域 K)
  定义体: inferInstanceAs (SMulCommClass X F.toSubsemiring Y)

Depends on / 依赖: F.toSubsemiring, SMulCommClass, toSubsemiring
-/
instance smulCommClass_right [SMul X Y] [SMul K Y] [SMulCommClass X K Y] (F : Subfield K) :
    SMulCommClass X F Y :=
  inferInstanceAs (SMulCommClass X F.toSubsemiring Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: X Y] [SMul K X] [SMul K Y] [IsScalarTower K X Y] (F
  body: inferInstanceAs (IsScalarTower F.toSubsemiring X Y)

中文:
实例 [标量乘法
  签名: X Y] [标量乘法 K X] [标量乘法 K Y] [标量塔 K X Y] (F
  定义体: inferInstanceAs (IsScalarTower F.toSubsemiring X Y)

Depends on / 依赖: F.toSubsemiring, IsScalarTower, toSubsemiring
-/
instance [SMul X Y] [SMul K X] [SMul K Y] [IsScalarTower K X Y] (F : Subfield K) :
    IsScalarTower F X Y :=
  inferInstanceAs (IsScalarTower F.toSubsemiring X Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: K X] [FaithfulSMul K X] (F
  body: inferInstanceAs (FaithfulSMul F.toSubsemiring X)

中文:
实例 [标量乘法
  签名: K X] [忠实标量乘法 K X] (F
  定义体: inferInstanceAs (FaithfulSMul F.toSubsemiring X)

Depends on / 依赖: F.toSubsemiring, FaithfulSMul, toSubsemiring
-/
instance [SMul K X] [FaithfulSMul K X] (F : Subfield K) : FaithfulSMul F X :=
  inferInstanceAs (FaithfulSMul F.toSubsemiring X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulAction
  signature: K X] (F
  body: inferInstanceAs (MulAction F.toSubsemiring X)

中文:
实例 [乘法作用
  签名: K X] (F
  定义体: inferInstanceAs (MulAction F.toSubsemiring X)

Depends on / 依赖: F.toSubsemiring, MulAction, toSubsemiring
-/
instance [MulAction K X] (F : Subfield K) : MulAction F X :=
  inferInstanceAs (MulAction F.toSubsemiring X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: X] [DistribMulAction K X] (F
  body: inferInstanceAs (DistribMulAction F.toSubsemiring X)

中文:
实例 [加法幺半群
  签名: X] [分配乘法作用 K X] (F
  定义体: inferInstanceAs (DistribMulAction F.toSubsemiring X)

Depends on / 依赖: DistribMulAction, F.toSubsemiring, toSubsemiring
-/
instance [AddMonoid X] [DistribMulAction K X] (F : Subfield K) : DistribMulAction F X :=
  inferInstanceAs (DistribMulAction F.toSubsemiring X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: X] [MulDistribMulAction K X] (F
  body: inferInstanceAs (MulDistribMulAction F.toSubsemiring X)

中文:
实例 [幺半群
  签名: X] [MulDistribMul作用 K X] (F
  定义体: inferInstanceAs (MulDistribMulAction F.toSubsemiring X)

Depends on / 依赖: F.toSubsemiring, MulDistribMulAction, toSubsemiring
-/
instance [Monoid X] [MulDistribMulAction K X] (F : Subfield K) : MulDistribMulAction F X :=
  inferInstanceAs (MulDistribMulAction F.toSubsemiring X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: X] [SMulWithZero K X] (F
  body: inferInstanceAs (SMulWithZero F.toSubsemiring X)

中文:
实例 [零
  签名: X] [带零标量乘法 K X] (F
  定义体: inferInstanceAs (SMulWithZero F.toSubsemiring X)

Depends on / 依赖: F.toSubsemiring, SMulWithZero, toSubsemiring
-/
instance [Zero X] [SMulWithZero K X] (F : Subfield K) : SMulWithZero F X :=
  inferInstanceAs (SMulWithZero F.toSubsemiring X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: X] [MulActionWithZero K X] (F
  body: inferInstanceAs (MulActionWithZero F.toSubsemiring X)

中文:
实例 [零
  签名: X] [带零乘法作用 K X] (F
  定义体: inferInstanceAs (MulActionWithZero F.toSubsemiring X)

Depends on / 依赖: F.toSubsemiring, MulActionWithZero, toSubsemiring
-/
instance [Zero X] [MulActionWithZero K X] (F : Subfield K) : MulActionWithZero F X :=
  inferInstanceAs (MulActionWithZero F.toSubsemiring X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: X] [Module K X] (F
  body: inferInstanceAs (Module F.toSubsemiring X)

中文:
实例 [加法交换幺半群
  签名: X] [模 K X] (F
  定义体: inferInstanceAs (Module F.toSubsemiring X)

Depends on / 依赖: F.toSubsemiring, Module, toSubsemiring
-/
instance [AddCommMonoid X] [Module K X] (F : Subfield K) : Module F X :=
  inferInstanceAs (Module F.toSubsemiring X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: X] [MulSemiringAction K X] (F
  body: inferInstanceAs (MulSemiringAction F.toSubsemiring X)

中文:
实例 [半环
  签名: X] [MulSemiring作用 K X] (F
  定义体: inferInstanceAs (MulSemiringAction F.toSubsemiring X)

Depends on / 依赖: F.toSubsemiring, MulSemiringAction, toSubsemiring
-/
instance [Semiring X] [MulSemiringAction K X] (F : Subfield K) : MulSemiringAction F X :=
  inferInstanceAs (MulSemiringAction F.toSubsemiring X)

end Subfield

end Actions
