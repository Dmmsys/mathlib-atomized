/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Subsemigroup.Membership
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.GroupWithZero.Center
public import Mathlib.Algebra.Ring.Center
public import Mathlib.Algebra.Ring.Centralizer
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Submonoid.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.GroupTheory.Submonoid.Center
public import Mathlib.GroupTheory.Subsemigroup.Centralizer
public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs

/-!
# Bundled non-unital subsemirings

We define the `CompleteLattice` structure, and non-unital subsemiring
`map`, `comap` and range (`srange`) of a `NonUnitalRingHom` etc.
-/

@[expose] public section


universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonUnitalNonAssocSemiring R] (M : Subsemigroup R)

namespace NonUnitalSubsemiring

@[gcongr, mono]
/--
theorem `toSubsemigroup_strictMono` / 定理 `toSubsemigroup_strictMono`

English:
theorem toSubsemigroup_strictMono
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toSubsemigroup_strictMono
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toSubsemigroup_strictMono :
    StrictMono (toSubsemigroup : NonUnitalSubsemiring R -> Subsemigroup R) := fun _ _ => id

@[gcongr, mono]
/--
theorem `toSubsemigroup_mono` / 定理 `toSubsemigroup_mono`

English:
theorem toSubsemigroup_mono
  statement: Monotone (toSubsemigroup : NonUnitalSubsemiring R -> Subsemigroup R)
  proof: toSubsemigroup_strictMono.monotone

@[gcongr, mono]

中文:
定理 toSubsemigroup_mono
  结论: Monotone (toSubsemigroup : NonUnitalSubsemiring R -> Subsemigroup R)
  证明: toSubsemigroup_strictMono.monotone

@[gcongr, mono]

Depends on / 依赖: monotone, toSubsemigroup_strictMono, toSubsemigroup_strictMono.monotone
-/
theorem toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubsemiring R -> Subsemigroup R) :=
  toSubsemigroup_strictMono.monotone

@[gcongr, mono]
/--
theorem `toAddSubmonoid_strictMono` / 定理 `toAddSubmonoid_strictMono`

English:
theorem toAddSubmonoid_strictMono
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toAddSubmonoid_strictMono
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toAddSubmonoid_strictMono :
    StrictMono (toAddSubmonoid : NonUnitalSubsemiring R -> AddSubmonoid R) := fun _ _ => id

@[gcongr, mono]
/--
theorem `toAddSubmonoid_mono` / 定理 `toAddSubmonoid_mono`

English:
theorem toAddSubmonoid_mono
  statement: Monotone (toAddSubmonoid : NonUnitalSubsemiring R -> AddSubmonoid R)
  proof: toAddSubmonoid_strictMono.monotone

中文:
定理 toAddSubmonoid_mono
  结论: Monotone (toAddSubmonoid : NonUnitalSubsemiring R -> AddSubmonoid R)
  证明: toAddSubmonoid_strictMono.monotone

Depends on / 依赖: monotone, toAddSubmonoid_strictMono, toAddSubmonoid_strictMono.monotone
-/
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : NonUnitalSubsemiring R -> AddSubmonoid R) :=
  toAddSubmonoid_strictMono.monotone

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

variable [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring T]
variable {F G : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]
  [FunLike G S T] [NonUnitalRingHomClass G S T]
  (s : NonUnitalSubsemiring R)

/-- The ring equiv between the top element of `NonUnitalSubsemiring R` and `R`. -/
@[simps!]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : NonUnitalSubsemiring R) ≃+* R
  body: { Subsemigroup.topEquiv, AddSubmonoid.topEquiv with }

中文:
定义 topEquiv
  签名: : (⊤ : NonUnitalSubsemiring R) ≃+* R
  定义体: { Subsemigroup.topEquiv, AddSubmonoid.topEquiv with }

Depends on / 依赖: AddSubmonoid, AddSubmonoid.topEquiv, Subsemigroup, Subsemigroup.topEquiv, topEquiv
-/
def topEquiv : (⊤ : NonUnitalSubsemiring R) ≃+* R :=
  { Subsemigroup.topEquiv, AddSubmonoid.topEquiv with }

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : F) (s : NonUnitalSubsemiring S)
  body: { s.toSubsemigroup.comap (f : MulHom R S), s.toAddSubmonoid.comap (f : R ->+ S) with
    carrier := f ⁻¹' s }

@[simp]

中文:
定义 comap
  签名: (f : F) (s : NonUnitalSubsemiring S)
  定义体: { s.toSubsemigroup.comap (f : MulHom R S), s.toAddSubmonoid.comap (f : R ->+ S) with
    carrier := f ⁻¹' s }

@[simp]

Depends on / 依赖: MulHom, carrier, s.toAddSubmonoid.comap, s.toSubsemigroup.comap, toAddSubmonoid, toSubsemigroup
-/
def comap (f : F) (s : NonUnitalSubsemiring S) : NonUnitalSubsemiring R :=
  { s.toSubsemigroup.comap (f : MulHom R S), s.toAddSubmonoid.comap (f : R ->+ S) with
    carrier := f ⁻¹' s }

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (s : NonUnitalSubsemiring S) (f : F)
  statement: (s.comap f : Set R) = f ⁻¹' s
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (s : NonUnitalSubsemiring S) (f : F)
  结论: (s.comap f : Set R) = f ⁻¹' s
  证明: rfl

@[simp]
-/
theorem coe_comap (s : NonUnitalSubsemiring S) (f : F) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {s : NonUnitalSubsemiring S} {f : F} {x : R}
  statement: x in s.comap f ↔ f x in s
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {s : NonUnitalSubsemiring S} {f : F} {x : R}
  结论: x in s.comap f ↔ f x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {s : NonUnitalSubsemiring S} {f : F} {x : R} : x in s.comap f ↔ f x in s :=
  Iff.rfl

-- this has some nasty coercions, how to deal with it?
/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (s : NonUnitalSubsemiring T) (g : G) (f : F)
  proof: rfl

中文:
定理 comap_comap
  条件: (s : NonUnitalSubsemiring T) (g : G) (f : F)
  证明: rfl
-/
theorem comap_comap (s : NonUnitalSubsemiring T) (g : G) (f : F) :
    ((s.comap g : NonUnitalSubsemiring S).comap f : NonUnitalSubsemiring R) =
      s.comap ((g : S ->ₙ+* T).comp (f : R ->ₙ+* S)) :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : F) (s : NonUnitalSubsemiring R)
  body: { s.toSubsemigroup.map (f : R ->ₙ* S), s.toAddSubmonoid.map (f : R ->+ S) with carrier := f '' s }

@[simp]

中文:
定义 map
  签名: (f : F) (s : NonUnitalSubsemiring R)
  定义体: { s.toSubsemigroup.map (f : R ->ₙ* S), s.toAddSubmonoid.map (f : R ->+ S) with carrier := f '' s }

@[simp]

Depends on / 依赖: carrier, s.toAddSubmonoid.map, s.toSubsemigroup.map, toAddSubmonoid, toSubsemigroup
-/
def map (f : F) (s : NonUnitalSubsemiring R) : NonUnitalSubsemiring S :=
  { s.toSubsemigroup.map (f : R ->ₙ* S), s.toAddSubmonoid.map (f : R ->+ S) with carrier := f '' s }

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : F) (s : NonUnitalSubsemiring R)
  statement: (s.map f : Set S) = f '' s
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (f : F) (s : NonUnitalSubsemiring R)
  结论: (s.map f : Set S) = f '' s
  证明: rfl

@[simp]
-/
theorem coe_map (f : F) (s : NonUnitalSubsemiring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : F} {s : NonUnitalSubsemiring R} {y : S}
  statement: y in s.map f ↔ exists x in s, f x = y
  proof: Iff.rfl

@[simp]

中文:
定理 mem_map
  条件: {f : F} {s : NonUnitalSubsemiring R} {y : S}
  结论: y in s.map f ↔ 存在 x in s, f x = y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_map {f : F} {s : NonUnitalSubsemiring R} {y : S} : y in s.map f ↔ exists x in s, f x = y :=
  Iff.rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: s.map (NonUnitalRingHom.id R) = s
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  结论: s.map (NonUnitalRingHom.id R) = s
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id : s.map (NonUnitalRingHom.id R) = s :=
SetLike.coe_injective Set.image_id _

-- unavoidable coercions?
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : G) (f : F)
  proof: SetLike.coe_injective Set.image_image _ _ _

中文:
定理 map_map
  条件: (g : G) (f : F)
  证明: SetLike.coe_injective Set.image_image _ _ _

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : G) (f : F) :
    (s.map (f : R ->ₙ+* S)).map (g : S ->ₙ+* T) = s.map ((g : S ->ₙ+* T).comp (f : R ->ₙ+* S)) :=
SetLike.coe_injective Set.image_image _ _ _

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : F} {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S}
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {f : F} {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le_iff_le_comap {f : F} {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} :
    s.map f <= t ↔ s <= t.comap f :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : F)
  proof: fun _ _ => map_le_iff_le_comap

中文:
定理 gc_map_comap
  条件: (f : F)
  证明: fun _ _ => map_le_iff_le_comap

Depends on / 依赖: map_le_iff_le_comap
-/
theorem gc_map_comap (f : F) :
    @GaloisConnection (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f) :=
  fun _ _ => map_le_iff_le_comap

/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (f : F) (hf : Function.Injective (f : R -> S))
  body: { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]

中文:
定义 equivMapOfInjective
  签名: (f : F) (hf : Function.Injective (f : R -> S))
  定义体: { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]

Depends on / 依赖: Equiv.Set.image, Subtype, Subtype.ext, map_add, map_mul
-/
noncomputable def equivMapOfInjective (f : F) (hf : Function.Injective (f : R -> S)) :
    s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
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
  条件: (f : F) (hf : Function.Injective f) (x : s)
  证明: rfl
-/
theorem coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end NonUnitalSubsemiring

namespace NonUnitalRingHom

open NonUnitalSubsemiring

variable [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring T]
variable {F G : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]
variable [FunLike G S T] [NonUnitalRingHomClass G S T] (f : F) (g : G)

/--
Definition of `srange` / `srange` 的定义

English:
definition srange
  signature: : NonUnitalSubsemiring S
  body: ((⊤ : NonUnitalSubsemiring R).map (f : R ->ₙ+* S)).copy (Set.range f) Set.image_univ.symm

@[simp]

中文:
定义 srange
  签名: : NonUnitalSubsemiring S
  定义体: ((⊤ : NonUnitalSubsemiring R).map (f : R ->ₙ+* S)).copy (Set.range f) Set.image_univ.symm

@[simp]

Depends on / 依赖: NonUnitalSubsemiring, Set.image_univ.symm, Set.range, image_univ
-/
def srange : NonUnitalSubsemiring S :=
  ((⊤ : NonUnitalSubsemiring R).map (f : R ->ₙ+* S)).copy (Set.range f) Set.image_univ.symm

@[simp]
/--
theorem `coe_srange` / 定理 `coe_srange`

English:
theorem coe_srange
  statement: (srange f : Set S) = Set.range f
  proof: rfl

@[simp]

中文:
定理 coe_srange
  结论: (srange f : Set S) = Set.range f
  证明: rfl

@[simp]
-/
theorem coe_srange : (srange f : Set S) = Set.range f :=
  rfl

@[simp]
/--
theorem `mem_srange` / 定理 `mem_srange`

English:
theorem mem_srange
  given: {f : F} {y : S}
  statement: y in srange f ↔ exists x, f x = y
  proof: Iff.rfl

中文:
定理 mem_srange
  条件: {f : F} {y : S}
  结论: y in srange f ↔ 存在 x, f x = y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_srange {f : F} {y : S} : y in srange f ↔ exists x, f x = y :=
  Iff.rfl

/--
theorem `srange_eq_map` / 定理 `srange_eq_map`

English:
theorem srange_eq_map
  statement: srange f = (⊤ : NonUnitalSubsemiring R).map f
  proof: by
  ext
  simp

中文:
定理 srange_eq_map
  结论: srange f = (⊤ : NonUnitalSubsemiring R).map f
  证明: by
  ext
  simp
-/
theorem srange_eq_map : srange f = (⊤ : NonUnitalSubsemiring R).map f := by
  ext
  simp

/--
theorem `mem_srange_self` / 定理 `mem_srange_self`

English:
theorem mem_srange_self
  given: (f : F) (x : R)
  statement: f x in srange f
  proof: mem_srange.mpr ⟨x, rfl⟩

中文:
定理 mem_srange_self
  条件: (f : F) (x : R)
  结论: f x in srange f
  证明: mem_srange.mpr ⟨x, rfl⟩

Depends on / 依赖: mem_srange, mem_srange.mpr
-/
theorem mem_srange_self (f : F) (x : R) : f x in srange f :=
  mem_srange.mpr ⟨x, rfl⟩

/--
theorem `map_srange` / 定理 `map_srange`

English:
theorem map_srange
  given: (g : S ->ₙ+* T) (f : R ->ₙ+* S)
  statement: map g (srange f) = srange (g.comp f)
  proof: by
  simpa only [srange_eq_map] using! (⊤ : NonUnitalSubsemiring R).map_map g f

中文:
定理 map_srange
  条件: (g : S ->ₙ+* T) (f : R ->ₙ+* S)
  结论: map g (srange f) = srange (g.comp f)
  证明: by
  simpa only [srange_eq_map] using! (⊤ : NonUnitalSubsemiring R).map_map g f

Depends on / 依赖: NonUnitalSubsemiring, map_map, srange_eq_map
-/
theorem map_srange (g : S ->ₙ+* T) (f : R ->ₙ+* S) : map g (srange f) = srange (g.comp f) := by
  simpa only [srange_eq_map] using! (⊤ : NonUnitalSubsemiring R).map_map g f

/--
Instance `finite_srange` / 实例 `finite_srange`

English:
instance finite_srange
  signature: [Finite R] (f : F)
  body: (Set.finite_range f).to_subtype

中文:
实例 finite_srange
  签名: [Finite R] (f : F)
  定义体: (Set.finite_range f).to_subtype

Depends on / 依赖: Set.finite_range, finite_range, to_subtype
-/
instance finite_srange [Finite R] (f : F) : Finite (srange f : NonUnitalSubsemiring S) :=
  (Set.finite_range f).to_subtype

end NonUnitalRingHom

namespace NonUnitalSubsemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (NonUnitalSubsemiring R)
  body: ⟨fun s =>
    NonUnitalSubsemiring.mk' (⋂ t in s, ↑t) (⨅ t in s, NonUnitalSubsemiring.toSubsemigroup t)
      (by simp) (⨅ t in s, NonUnitalSubsemiring.toAddSubmonoid t) (by simp)⟩

@[simp, norm_cast]

中文:
实例 :
  签名: InfSet (NonUnitalSubsemiring R)
  定义体: ⟨fun s =>
    NonUnitalSubsemiring.mk' (⋂ t in s, ↑t) (⨅ t in s, NonUnitalSubsemiring.toSubsemigroup t)
      (by simp) (⨅ t in s, NonUnitalSubsemiring.toAddSubmonoid t) (by simp)⟩

@[simp, norm_cast]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.mk, NonUnitalSubsemiring.toAddSubmonoid, NonUnitalSubsemiring.toSubsemigroup, toAddSubmonoid, toSubsemigroup
-/
instance : InfSet (NonUnitalSubsemiring R) :=
  ⟨fun s =>
    NonUnitalSubsemiring.mk' (⋂ t in s, ↑t) (⨅ t in s, NonUnitalSubsemiring.toSubsemigroup t)
      (by simp) (⨅ t in s, NonUnitalSubsemiring.toAddSubmonoid t) (by simp)⟩

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (NonUnitalSubsemiring R))
  proof: rfl

@[simp]

中文:
定理 coe_sInf
  条件: (S : Set (NonUnitalSubsemiring R))
  证明: rfl

@[simp]
-/
theorem coe_sInf (S : Set (NonUnitalSubsemiring R)) :
    ((sInf S : NonUnitalSubsemiring R) : Set R) = ⋂ s in S, ↑s :=
  rfl

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (NonUnitalSubsemiring R)} {x : R}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: Set.mem_iInter₂

@[simp, norm_cast]

中文:
定理 mem_sInf
  条件: {S : Set (NonUnitalSubsemiring R)} {x : R}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: Set.mem_iInter₂

@[simp, norm_cast]

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {S : Set (NonUnitalSubsemiring R)} {x : R} : x in sInf S ↔ forall p in S, x in p :=
  Set.mem_iInter₂

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> NonUnitalSubsemiring R}
  proof: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : Sort*} {S : ι -> NonUnitalSubsemiring R}
  证明: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

Depends on / 依赖: Set.biInter_range, biInter_range, coe_sInf
-/
theorem coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubsemiring R} :
    (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> NonUnitalSubsemiring R} {x : R}
  proof: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

中文:
定理 mem_iInf
  条件: {ι : Sort*} {S : ι -> NonUnitalSubsemiring R} {x : R}
  证明: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> NonUnitalSubsemiring R} {x : R} :
    x in ⨅ i, S i ↔ forall i, x in S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/--
theorem `sInf_toSubsemigroup` / 定理 `sInf_toSubsemigroup`

English:
theorem sInf_toSubsemigroup
  given: (s : Set (NonUnitalSubsemiring R))
  proof: mk'_toSubsemigroup _ _

@[simp]

中文:
定理 sInf_toSubsemigroup
  条件: (s : Set (NonUnitalSubsemiring R))
  证明: mk'_toSubsemigroup _ _

@[simp]

Depends on / 依赖: _toSubsemigroup
-/
theorem sInf_toSubsemigroup (s : Set (NonUnitalSubsemiring R)) :
    (sInf s).toSubsemigroup = ⨅ t in s, NonUnitalSubsemiring.toSubsemigroup t :=
  mk'_toSubsemigroup _ _

@[simp]
/--
theorem `sInf_toAddSubmonoid` / 定理 `sInf_toAddSubmonoid`

English:
theorem sInf_toAddSubmonoid
  given: (s : Set (NonUnitalSubsemiring R))
  proof: mk'_toAddSubmonoid _ _

中文:
定理 sInf_toAddSubmonoid
  条件: (s : Set (NonUnitalSubsemiring R))
  证明: mk'_toAddSubmonoid _ _

Depends on / 依赖: _toAddSubmonoid
-/
theorem sInf_toAddSubmonoid (s : Set (NonUnitalSubsemiring R)) :
    (sInf s).toAddSubmonoid = ⨅ t in s, NonUnitalSubsemiring.toAddSubmonoid t :=
  mk'_toAddSubmonoid _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (NonUnitalSubsemiring R)
  body: { completeLatticeOfInf (NonUnitalSubsemiring R)
      fun _ => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left

中文:
实例 :
  签名: CompleteLattice (NonUnitalSubsemiring R)
  定义体: { completeLatticeOfInf (NonUnitalSubsemiring R)
      fun _ => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left

Depends on / 依赖: And.left, And.right, IsGLB.of_image, NonUnitalSubsemiring, SetLike, SetLike.coe_subset_coe, bot_le, coe_subset_coe, completeLatticeOfInf, inf_le_left, inf_le_right, isGLB_biInf, le_inf, le_top, mem_bot, mem_bot.mp, of_image, zero_mem
-/
instance : CompleteLattice (NonUnitalSubsemiring R) :=
  { completeLatticeOfInf (NonUnitalSubsemiring R)
      fun _ => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

/--
theorem `eq_top_iff'` / 定理 `eq_top_iff'`

English:
theorem eq_top_iff'
  given: (A : NonUnitalSubsemiring R)
  statement: A = ⊤ ↔ forall x : R, x in A
  proof: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

中文:
定理 eq_top_iff'
  条件: (A : NonUnitalSubsemiring R)
  结论: A = ⊤ ↔ 对任意 x : R, x in A
  证明: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

Depends on / 依赖: eq_top_iff, eq_top_iff.trans, mem_top
-/
theorem eq_top_iff' (A : NonUnitalSubsemiring R) : A = ⊤ ↔ forall x : R, x in A :=
eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

section NonUnitalNonAssocSemiring

variable (R)

/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : NonUnitalSubsemiring R
  body: { Subsemigroup.center R with
    zero_mem' := Set.zero_mem_center
    add_mem' := Set.add_mem_center }

中文:
定义 center
  签名: : NonUnitalSubsemiring R
  定义体: { Subsemigroup.center R with
    zero_mem' := Set.zero_mem_center
    add_mem' := Set.add_mem_center }

Depends on / 依赖: Set.add_mem_center, Set.zero_mem_center, Subsemigroup, Subsemigroup.center, add_mem, add_mem_center, center, zero_mem, zero_mem_center
-/
def center : NonUnitalSubsemiring R :=
  { Subsemigroup.center R with
    zero_mem' := Set.zero_mem_center
    add_mem' := Set.add_mem_center }

/--
theorem `coe_center` / 定理 `coe_center`

English:
theorem coe_center
  statement: ↑(center R) = Set.center R
  proof: rfl

@[simp]

中文:
定理 coe_center
  结论: ↑(center R) = Set.center R
  证明: rfl

@[simp]
-/
theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
/--
theorem `center_toSubsemigroup` / 定理 `center_toSubsemigroup`

English:
theorem center_toSubsemigroup
  proof: rfl

中文:
定理 center_toSubsemigroup
  证明: rfl
-/
theorem center_toSubsemigroup :
    (center R).toSubsemigroup = Subsemigroup.center R :=
  rfl

/--
Instance `center.instNonUnitalCommSemiring` / 实例 `center.instNonUnitalCommSemiring`

English:
instance center.instNonUnitalCommSemiring
  signature: : NonUnitalCommSemiring (center R)
  body: { Subsemigroup.center.commSemigroup,
    NonUnitalSubsemiringClass.toNonUnitalNonAssocSemiring (center R) with }

中文:
实例 center.instNonUnitalCommSemiring
  签名: : NonUnitalCommSemiring (center R)
  定义体: { Subsemigroup.center.commSemigroup,
    NonUnitalSubsemiringClass.toNonUnitalNonAssocSemiring (center R) with }
-/
instance center.instNonUnitalCommSemiring : NonUnitalCommSemiring (center R) :=
  { Subsemigroup.center.commSemigroup,
    NonUnitalSubsemiringClass.toNonUnitalNonAssocSemiring (center R) with }

/--
lemma `_root_.Set.mem_center_iff_addMonoidHom` / 引理 `_root_.Set.mem_center_iff_addMonoidHom`

English:
lemma _root_.Set.mem_center_iff_addMonoidHom
  given: (a : R)
  proof: by
  rw [Set.mem_center_iff]; rw [isMulCentral_iff]
  simp [DFunLike.ext_iff, commute_iff_eq]

中文:
引理 _root_.Set.mem_center_iff_addMonoidHom
  条件: (a : R)
  证明: by
  rw [Set.mem_center_iff]; rw [isMulCentral_iff]
  simp [DFunLike.ext_iff, commute_iff_eq]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Set.mem_center_iff, commute_iff_eq, ext_iff, isMulCentral_iff, mem_center_iff
-/
lemma _root_.Set.mem_center_iff_addMonoidHom (a : R) :
    a in Set.center R ↔
      AddMonoidHom.mulLeft a = .mulRight a ∧
      AddMonoidHom.compr₂ .mul (.mulLeft a) = .comp .mul (.mulLeft a) ∧
      AddMonoidHom.compr₂ .mul (.mulRight a) = .compl₂ .mul (.mulRight a) := by
  rw [Set.mem_center_iff]; rw [isMulCentral_iff]
  simp [DFunLike.ext_iff, commute_iff_eq]

variable {R}

/--
Definition of `centerCongr` / `centerCongr` 的定义

English:
definition centerCongr
  signature: [NonUnitalNonAssocSemiring S] (e : R ≃+* S)
  body: Subsemigroup.centerCongr e
map_add' _ _ := Subtype.ext by exact map_add e ..

中文:
定义 centerCongr
  签名: [NonUnitalNonAssocSemiring S] (e : R ≃+* S)
  定义体: Subsemigroup.centerCongr e
map_add' _ _ := Subtype.ext by exact map_add e ..
-/
@[simps!] def centerCongr [NonUnitalNonAssocSemiring S] (e : R ≃+* S) : center R ≃+* center S where
  __ := Subsemigroup.centerCongr e
map_add' _ _ := Subtype.ext by exact map_add e ..

/--
Definition of `centerToMulOpposite` / `centerToMulOpposite` 的定义

English:
definition centerToMulOpposite
  signature: : center R ≃+* center Rᵐᵒᵖ where
  body: Subsemigroup.centerToMulOpposite
  map_add' _ _ := rfl

中文:
定义 centerToMulOpposite
  签名: : center R ≃+* center Rᵐᵒᵖ where
  定义体: Subsemigroup.centerToMulOpposite
  map_add' _ _ := rfl
-/
@[simps!] def centerToMulOpposite : center R ≃+* center Rᵐᵒᵖ where
  __ := Subsemigroup.centerToMulOpposite
  map_add' _ _ := rfl

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

set_option backward.isDefEq.respectTransparency false in
-- no instance diamond, unlike the unital version
example {R} [NonUnitalSemiring R] :
    (center.instNonUnitalCommSemiring _).toNonUnitalSemiring =
      NonUnitalSubsemiringClass.toNonUnitalSemiring (center R) := by
  with_reducible_and_instances rfl

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {R} [NonUnitalSemiring R] {z : R}
  statement: z in center R ↔ forall g, g * z = z * g
  proof: by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

中文:
定理 mem_center_iff
  条件: {R} [NonUnitalSemiring R] {z : R}
  结论: z in center R ↔ 对任意 g, g * z = z * g
  证明: by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, Semigroup, Semigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {R} [NonUnitalSemiring R] {z : R} : z in center R ↔ forall g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

/--
Instance `decidableMemCenter` / 实例 `decidableMemCenter`

English:
instance decidableMemCenter
  signature: {R} [NonUnitalSemiring R] [DecidableEq R] [Fintype R]
  body: fun _ => decidable_of_iff' _ mem_center_iff

@[simp]

中文:
实例 decidableMemCenter
  签名: {R} [NonUnitalSemiring R] [DecidableEq R] [Fintype R]
  定义体: fun _ => decidable_of_iff' _ mem_center_iff

@[simp]

Depends on / 依赖: decidable_of_iff, mem_center_iff
-/
instance decidableMemCenter {R} [NonUnitalSemiring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· in center R) := fun _ => decidable_of_iff' _ mem_center_iff

@[simp]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  given: (R) [NonUnitalCommSemiring R]
  statement: center R = ⊤
  proof: SetLike.coe_injective (Set.center_eq_univ R)

中文:
定理 center_eq_top
  条件: (R) [NonUnitalCommSemiring R]
  结论: center R = ⊤
  证明: SetLike.coe_injective (Set.center_eq_univ R)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top (R) [NonUnitalCommSemiring R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

end NonUnitalSemiring

section Centralizer

/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: {R} [NonUnitalSemiring R] (s : Set R)
  body: { Subsemigroup.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]

中文:
定义 centralizer
  签名: {R} [NonUnitalSemiring R] (s : Set R)
  定义体: { Subsemigroup.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]

Depends on / 依赖: Set.add_mem_centralizer, Set.zero_mem_centralizer, Subsemigroup, Subsemigroup.centralizer, add_mem, add_mem_centralizer, carrier, centralizer, s.centralizer, zero_mem, zero_mem_centralizer
-/
def centralizer {R} [NonUnitalSemiring R] (s : Set R) : NonUnitalSubsemiring R :=
  { Subsemigroup.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  given: {R} [NonUnitalSemiring R] (s : Set R)
  proof: rfl

中文:
定理 coe_centralizer
  条件: {R} [NonUnitalSemiring R] (s : Set R)
  证明: rfl
-/
theorem coe_centralizer {R} [NonUnitalSemiring R] (s : Set R) :
    (centralizer s : Set R) = s.centralizer :=
  rfl

/--
theorem `centralizer_toSubsemigroup` / 定理 `centralizer_toSubsemigroup`

English:
theorem centralizer_toSubsemigroup
  given: {R} [NonUnitalSemiring R] (s : Set R)
  proof: rfl

中文:
定理 centralizer_toSubsemigroup
  条件: {R} [NonUnitalSemiring R] (s : Set R)
  证明: rfl
-/
theorem centralizer_toSubsemigroup {R} [NonUnitalSemiring R] (s : Set R) :
    (centralizer s).toSubsemigroup = Subsemigroup.centralizer s :=
  rfl

/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {R} [NonUnitalSemiring R] {s : Set R} {z : R}
  proof: Iff.rfl

中文:
定理 mem_centralizer_iff
  条件: {R} [NonUnitalSemiring R] {s : Set R} {z : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_centralizer_iff {R} [NonUnitalSemiring R] {s : Set R} {z : R} :
    z in centralizer s ↔ forall g in s, g * z = z * g :=
  Iff.rfl

/--
theorem `center_le_centralizer` / 定理 `center_le_centralizer`

English:
theorem center_le_centralizer
  given: {R} [NonUnitalSemiring R] (s)
  statement: center R <= centralizer s
  proof: s.center_subset_centralizer

中文:
定理 center_le_centralizer
  条件: {R} [NonUnitalSemiring R] (s)
  结论: center R <= centralizer s
  证明: s.center_subset_centralizer

Depends on / 依赖: center_subset_centralizer, s.center_subset_centralizer
-/
theorem center_le_centralizer {R} [NonUnitalSemiring R] (s) : center R <= centralizer s :=
  s.center_subset_centralizer

/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: {R} [NonUnitalSemiring R] (s t : Set R) (h : s subseteq t)
  proof: Set.centralizer_subset h

@[simp]

中文:
定理 centralizer_le
  条件: {R} [NonUnitalSemiring R] (s t : Set R) (h : s subseteq t)
  证明: Set.centralizer_subset h

@[simp]

Depends on / 依赖: Set.centralizer_subset, centralizer_subset
-/
theorem centralizer_le {R} [NonUnitalSemiring R] (s t : Set R) (h : s subseteq t) :
    centralizer t <= centralizer s :=
  Set.centralizer_subset h

@[simp]
/--
theorem `centralizer_eq_top_iff_subset` / 定理 `centralizer_eq_top_iff_subset`

English:
theorem centralizer_eq_top_iff_subset
  given: {R} [NonUnitalSemiring R] {s : Set R}
  proof: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]

中文:
定理 centralizer_eq_top_iff_subset
  条件: {R} [NonUnitalSemiring R] {s : Set R}
  证明: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]

Depends on / 依赖: Set.centralizer_eq_top_iff_subset, SetLike, SetLike.ext, _iff, _iff.trans, centralizer_eq_top_iff_subset
-/
theorem centralizer_eq_top_iff_subset {R} [NonUnitalSemiring R] {s : Set R} :
    centralizer s = ⊤ ↔ s subseteq center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  given: {R} [NonUnitalSemiring R]
  statement: centralizer Set.univ = center R
  proof: SetLike.ext' (Set.centralizer_univ R)

中文:
定理 centralizer_univ
  条件: {R} [NonUnitalSemiring R]
  结论: centralizer Set.univ = center R
  证明: SetLike.ext' (Set.centralizer_univ R)

Depends on / 依赖: Set.centralizer_univ, SetLike, SetLike.ext, centralizer_univ
-/
theorem centralizer_univ {R} [NonUnitalSemiring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Set R)
  body: sInf { S | s subseteq S }

中文:
定义 closure
  签名: (s : Set R)
  定义体: sInf { S | s subseteq S }

Depends on / 依赖: subseteq
-/
def closure (s : Set R) : NonUnitalSubsemiring R :=
  sInf { S | s subseteq S }

/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {x : R} {s : Set R}
  proof: mem_sInf

中文:
定理 mem_closure
  条件: {x : R} {s : Set R}
  证明: mem_sInf

Depends on / 依赖: mem_sInf
-/
theorem mem_closure {x : R} {s : Set R} :
    x in closure s ↔ forall S : NonUnitalSubsemiring R, s subseteq S -> x in S :=
  mem_sInf

/-- The non-unital subsemiring generated by a set includes the set. -/
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
  条件: {s : Set R}
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
  条件: {s : Set R} {x : R} (hx : x in s)
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
  条件: {s : Set R} {P : R} (hP : P ∉ closure s)
  结论: P ∉ s
  证明: fun h =>
  hP (subset_closure h)
-/
theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A non-unital subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
/--
theorem `closure_le` / 定理 `closure_le`

English:
theorem closure_le
  given: {s : Set R} {t : NonUnitalSubsemiring R}
  statement: closure s <= t ↔ s subseteq t
  proof: ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

中文:
定理 closure_le
  条件: {s : Set R} {t : NonUnitalSubsemiring R}
  结论: closure s <= t ↔ s subseteq t
  证明: ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

Depends on / 依赖: Set.Subset.trans, Subset, sInf_le, subset_closure
-/
theorem closure_le {s : Set R} {t : NonUnitalSubsemiring R} : closure s <= t ↔ s subseteq t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
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
  结论: Set R⦄ (h : s subseteq t) : closure s <= closure t
  证明: closure_le.2 Set.Subset.trans h subset_closure

Depends on / 依赖: Set.Subset.trans, Subset, closure_le, subset_closure
-/
theorem closure_mono ⦃s t : Set R⦄ (h : s subseteq t) : closure s <= closure t :=
closure_le.2 Set.Subset.trans h subset_closure

/--
theorem `closure_eq_of_le` / 定理 `closure_eq_of_le`

English:
theorem closure_eq_of_le
  statement: {s : Set R} {t : NonUnitalSubsemiring R} (h₁ : s subseteq t)
  proof: le_antisymm (closure_le.2 h₁) h₂

中文:
定理 closure_eq_of_le
  结论: {s : Set R} {t : NonUnitalSubsemiring R} (h₁ : s subseteq t)
  证明: le_antisymm (closure_le.2 h₁) h₂

Depends on / 依赖: closure_le, le_antisymm
-/
theorem closure_eq_of_le {s : Set R} {t : NonUnitalSubsemiring R} (h₁ : s subseteq t)
    (h₂ : t <= closure s) : closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/--
lemma `closure_le_centralizer_centralizer` / 引理 `closure_le_centralizer_centralizer`

English:
lemma closure_le_centralizer_centralizer
  given: {R : Type*} [NonUnitalSemiring R] (s : Set R)
  proof: closure_le.mpr Set.subset_centralizer_centralizer

中文:
引理 closure_le_centralizer_centralizer
  条件: {R : 类型} [NonUnitalSemiring R] (s : Set R)
  证明: closure_le.mpr Set.subset_centralizer_centralizer

Depends on / 依赖: Set.subset_centralizer_centralizer, closure_le, closure_le.mpr, subset_centralizer_centralizer
-/
lemma closure_le_centralizer_centralizer {R : Type*} [NonUnitalSemiring R] (s : Set R) :
    closure s <= centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/--
theorem `isMulCommutative_closure` / 定理 `isMulCommutative_closure`

English:
theorem isMulCommutative_closure
  statement: {R : Type*} [NonUnitalSemiring R] {s : Set R}
  proof: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

中文:
定理 isMulCommutative_closure
  结论: {R : 类型} [NonUnitalSemiring R] {s : Set R}
  证明: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, centralizer_centralizer_comm_of_comm, closure_le_centralizer_centralizer, of_setLike_mul_comm
-/
theorem isMulCommutative_closure {R : Type*} [NonUnitalSemiring R] {s : Set R}
    (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a non-unital commutative
semiring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
/--
Definition of `closureNonUnitalCommSemiringOfComm` / `closureNonUnitalCommSemiringOfComm` 的定义

English:
abbreviation closureNonUnitalCommSemiringOfComm
  signature: {R : Type*} [NonUnitalSemiring R] {s : Set R}
  body: have := isMulCommutative_closure hcomm
  inferInstance

中文:
缩写 closureNonUnitalCommSemiringOfComm
  签名: {R : 类型} [NonUnitalSemiring R] {s : Set R}
  定义体: have := isMulCommutative_closure hcomm
  inferInstance

Depends on / 依赖: isMulCommutative_closure
-/
abbrev closureNonUnitalCommSemiringOfComm {R : Type*} [NonUnitalSemiring R] {s : Set R}
    (hcomm : forall x in s, forall y in s, x * y = y * x) : NonUnitalCommSemiring (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance

/--
Instance `instIsMulCommutative_closure` / 实例 `instIsMulCommutative_closure`

English:
instance instIsMulCommutative_closure
  signature: {S R : Type*} [NonUnitalSemiring R]
  body: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

中文:
实例 instIsMulCommutative_closure
  签名: {S R : 类型} [NonUnitalSemiring R]
  定义体: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

Depends on / 依赖: isMulCommutative_closure, setLike_mul_comm
-/
instance instIsMulCommutative_closure {S R : Type*} [NonUnitalSemiring R]
    [SetLike S R] [MulMemClass S R] (s : S) [IsMulCommutative s] :
    IsMulCommutative (closure (s : Set R)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

variable [NonUnitalNonAssocSemiring S]

/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {f : R ≃+* S} {K : NonUnitalSubsemiring R} {x : S}
  proof: by
  convert! @Set.mem_image_equiv _ _ (↑K) f.toEquiv x

中文:
定理 mem_map_equiv
  条件: {f : R ≃+* S} {K : NonUnitalSubsemiring R} {x : S}
  证明: by
  convert! @Set.mem_image_equiv _ _ (↑K) f.toEquiv x

Depends on / 依赖: Set.mem_image_equiv, convert, f.toEquiv, mem_image_equiv, toEquiv
-/
theorem mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubsemiring R} {x : S} :
    x in K.map (f : R ->ₙ+* S) ↔ f.symm x in K := by
  convert! @Set.mem_image_equiv _ _ (↑K) f.toEquiv x

/--
theorem `map_equiv_eq_comap_symm` / 定理 `map_equiv_eq_comap_symm`

English:
theorem map_equiv_eq_comap_symm
  given: (f : R ≃+* S) (K : NonUnitalSubsemiring R)
  proof: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

中文:
定理 map_equiv_eq_comap_symm
  条件: (f : R ≃+* S) (K : NonUnitalSubsemiring R)
  证明: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubsemiring R) :
    K.map (f : R ->ₙ+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

/--
theorem `comap_equiv_eq_map_symm` / 定理 `comap_equiv_eq_map_symm`

English:
theorem comap_equiv_eq_map_symm
  given: (f : R ≃+* S) (K : NonUnitalSubsemiring S)
  proof: (map_equiv_eq_comap_symm f.symm K).symm

中文:
定理 comap_equiv_eq_map_symm
  条件: (f : R ≃+* S) (K : NonUnitalSubsemiring S)
  证明: (map_equiv_eq_comap_symm f.symm K).symm

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubsemiring S) :
    K.comap (f : R ->ₙ+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end NonUnitalSubsemiring

namespace Subsemigroup

/--
Definition of `nonUnitalSubsemiringClosure` / `nonUnitalSubsemiringClosure` 的定义

English:
definition nonUnitalSubsemiringClosure
  signature: (M : Subsemigroup R)
  body: { AddSubmonoid.closure (M : Set R) with mul_mem' := MulMemClass.mul_mem_add_closure }

中文:
定义 nonUnitalSubsemiringClosure
  签名: (M : Subsemigroup R)
  定义体: { AddSubmonoid.closure (M : Set R) with mul_mem' := MulMemClass.mul_mem_add_closure }

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure, MulMemClass, MulMemClass.mul_mem_add_closure, closure, mul_mem, mul_mem_add_closure
-/
def nonUnitalSubsemiringClosure (M : Subsemigroup R) : NonUnitalSubsemiring R :=
  { AddSubmonoid.closure (M : Set R) with mul_mem' := MulMemClass.mul_mem_add_closure }

/--
theorem `nonUnitalSubsemiringClosure_coe` / 定理 `nonUnitalSubsemiringClosure_coe`

English:
theorem nonUnitalSubsemiringClosure_coe
  proof: rfl

中文:
定理 nonUnitalSubsemiringClosure_coe
  证明: rfl
-/
theorem nonUnitalSubsemiringClosure_coe :
    (M.nonUnitalSubsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl

/--
theorem `nonUnitalSubsemiringClosure_toAddSubmonoid` / 定理 `nonUnitalSubsemiringClosure_toAddSubmonoid`

English:
theorem nonUnitalSubsemiringClosure_toAddSubmonoid
  proof: rfl

中文:
定理 nonUnitalSubsemiringClosure_toAddSubmonoid
  证明: rfl
-/
theorem nonUnitalSubsemiringClosure_toAddSubmonoid :
    M.nonUnitalSubsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl

/--
theorem `nonUnitalSubsemiringClosure_eq_closure` / 定理 `nonUnitalSubsemiringClosure_eq_closure`

English:
theorem nonUnitalSubsemiringClosure_eq_closure
  proof: by
  ext
  refine ⟨fun hx => ?_,
    fun hx => (NonUnitalSubsemiring.mem_closure.mp hx) M.nonUnitalSubsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

中文:
定理 nonUnitalSubsemiringClosure_eq_closure
  证明: by
  ext
  refine ⟨fun hx => ?_,
    fun hx => (NonUnitalSubsemiring.mem_closure.mp hx) M.nonUnitalSubsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_closure.mp, H1.toAddSubmonoid, M.nonUnitalSubsemiringClosure, NonUnitalSubsemiring, NonUnitalSubsemiring.mem_closure.mp, mem_closure, nonUnitalSubsemiringClosure, toAddSubmonoid
-/
theorem nonUnitalSubsemiringClosure_eq_closure :
    M.nonUnitalSubsemiringClosure = NonUnitalSubsemiring.closure (M : Set R) := by
  ext
  refine ⟨fun hx => ?_,
    fun hx => (NonUnitalSubsemiring.mem_closure.mp hx) M.nonUnitalSubsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

end Subsemigroup

namespace NonUnitalSubsemiring

@[simp]
/--
theorem `closure_subsemigroup_closure` / 定理 `closure_subsemigroup_closure`

English:
theorem closure_subsemigroup_closure
  given: (s : Set R)
  statement: closure ↑(Subsemigroup.closure s) = closure s
  proof: le_antisymm
    (closure_le.mpr fun _ hy =>
      (Subsemigroup.mem_closure.mp hy) (closure s).toSubsemigroup subset_closure)
    (closure_mono Subsemigroup.subset_closure)

中文:
定理 closure_subsemigroup_closure
  条件: (s : Set R)
  结论: closure ↑(Subsemigroup.closure s) = closure s
  证明: le_antisymm
    (closure_le.mpr fun _ hy =>
      (Subsemigroup.mem_closure.mp hy) (closure s).toSubsemigroup subset_closure)
    (closure_mono Subsemigroup.subset_closure)

Depends on / 依赖: Subsemigroup, Subsemigroup.mem_closure.mp, Subsemigroup.subset_closure, closure, closure_le, closure_le.mpr, closure_mono, le_antisymm, mem_closure, subset_closure, toSubsemigroup
-/
theorem closure_subsemigroup_closure (s : Set R) : closure ↑(Subsemigroup.closure s) = closure s :=
  le_antisymm
    (closure_le.mpr fun _ hy =>
      (Subsemigroup.mem_closure.mp hy) (closure s).toSubsemigroup subset_closure)
    (closure_mono Subsemigroup.subset_closure)

/--
theorem `coe_closure_eq` / 定理 `coe_closure_eq`

English:
theorem coe_closure_eq
  given: (s : Set R)
  proof: by
  simp [← Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid,
    Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]

中文:
定理 coe_closure_eq
  条件: (s : Set R)
  证明: by
  simp [← Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid,
    Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]

Depends on / 依赖: Subsemigroup, Subsemigroup.nonUnitalSubsemiringClosure_eq_closure, Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid, nonUnitalSubsemiringClosure_eq_closure, nonUnitalSubsemiringClosure_toAddSubmonoid
-/
theorem coe_closure_eq (s : Set R) :
    (closure s : Set R) = AddSubmonoid.closure (Subsemigroup.closure s : Set R) := by
  simp [← Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid,
    Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]

/--
theorem `mem_closure_iff` / 定理 `mem_closure_iff`

English:
theorem mem_closure_iff
  given: {s : Set R} {x}
  proof: Set.ext_iff.mp (coe_closure_eq s) x

@[simp]

中文:
定理 mem_closure_iff
  条件: {s : Set R} {x}
  证明: Set.ext_iff.mp (coe_closure_eq s) x

@[simp]

Depends on / 依赖: Set.ext_iff.mp, coe_closure_eq, ext_iff
-/
theorem mem_closure_iff {s : Set R} {x} :
    x in closure s ↔ x in AddSubmonoid.closure (Subsemigroup.closure s : Set R) :=
  Set.ext_iff.mp (coe_closure_eq s) x

@[simp]
/--
theorem `closure_addSubmonoid_closure` / 定理 `closure_addSubmonoid_closure`

English:
theorem closure_addSubmonoid_closure
  given: {s : Set R}
  proof: by
  ext x
  refine ⟨fun hx => ?_, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => ?_
  refine (Subsemigroup.mem_closure.mp hy) H.toSubsemigroup fun z hz => ?_
 

中文:
定理 closure_addSubmonoid_closure
  条件: {s : Set R}
  证明: by
  ext x
  refine ⟨fun hx => ?_, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => ?_
  refine (Subsemigroup.mem_closure.mp hy) H.toSubsemigroup fun z hz => ?_
 

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_closure.mp, AddSubmonoid.subset_closure, H.toAddSubmonoid, H.toSubsemigroup, Subsemigroup, Subsemigroup.mem_closure.mp, closure_mono, mem_closure, mem_closure_iff, mem_closure_iff.mp, subset_closure, toAddSubmonoid, toSubsemigroup
-/
theorem closure_addSubmonoid_closure {s : Set R} :
    closure ↑(AddSubmonoid.closure s) = closure s := by
  ext x
  refine ⟨fun hx => ?_, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => ?_
  refine (Subsemigroup.mem_closure.mp hy) H.toSubsemigroup fun z hz => ?_
  exact (AddSubmonoid.mem_closure.mp hz) H.toAddSubmonoid fun w hw => J hw

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_elim]
/--
theorem `closure_induction` / 定理 `closure_induction`

English:
theorem closure_induction
  statement: {s : Set R} {p : (x : R) -> x in closure s -> Prop}
  proof: let K : NonUnitalSubsemiring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, 

中文:
定理 closure_induction
  结论: {s : Set R} {p : (x : R) -> x in closure s -> 命题}
  证明: let K : NonUnitalSubsemiring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, 

Depends on / 依赖: NonUnitalSubsemiring, add_mem, carrier, closure_le, mul_mem, subset_closure, zero_mem
-/
theorem closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop}
    (mem : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    {x} (hx : x in closure s) : p x hx :=
  let K : NonUnitalSubsemiring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (t := K)

/-- An induction principle for closure membership for predicates with two arguments. -/
@[elab_as_elim]
/--
theorem `closure_induction₂` / 定理 `closure_induction₂`

English:
theorem closure_induction₂
  statement: {s : Set R} {p : (x y : R) -> x in closure s -> y in closure s -> Prop}
  proof: by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ h _ hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
 

中文:
定理 closure_induction₂
  结论: {s : Set R} {p : (x y : R) -> x in closure s -> y in closure s -> 命题}
  证明: by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ h _ hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
 

Depends on / 依赖: add_left, add_right, closure_induction, mem_mem, mul_left, mul_right, zero_left, zero_right
-/
theorem closure_induction₂ {s : Set R} {p : (x y : R) -> x in closure s -> y in closure s -> Prop}
    (mem_mem : forall (x) (hx : x in s) (y) (hy : y in s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : forall x hx, p 0 x (zero_mem _) hx) (zero_right : forall x hx, p x 0 hx (zero_mem _))
    (add_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x + y) z (add_mem hx hy) hz)
    (add_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y + z) hx (add_mem hy hz))
    (mul_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x * y) z (mul_mem hx hy) hz)
    (mul_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y * z) hx (mul_mem hy hz))
    {x y : R} (hx : x in closure s) (hy : y in closure s) :
    p x y hx hy := by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ h _ hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | zero => exact zero_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

variable (R) in
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (@closure R _) (↑) where
  body: closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

中文:
定义 gi
  签名: : GaloisInsertion (@closure R _) (↑) where
  定义体: closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
-/
protected def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]

/-- Closure of a non-unital subsemiring `S` equals `S`. -/
@[simp]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  given: (s : NonUnitalSubsemiring R)
  statement: closure (s : Set R) = s
  proof: (NonUnitalSubsemiring.gi R).l_u_eq s

@[simp]

中文:
定理 closure_eq
  条件: (s : NonUnitalSubsemiring R)
  结论: closure (s : Set R) = s
  证明: (NonUnitalSubsemiring.gi R).l_u_eq s

@[simp]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.gi, l_u_eq
-/
theorem closure_eq (s : NonUnitalSubsemiring R) : closure (s : Set R) = s :=
  (NonUnitalSubsemiring.gi R).l_u_eq s

@[simp]
/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure (∅ : Set R) = ⊥
  proof: (NonUnitalSubsemiring.gi R).gc.l_bot

@[simp]

中文:
定理 closure_empty
  结论: closure (∅ : Set R) = ⊥
  证明: (NonUnitalSubsemiring.gi R).gc.l_bot

@[simp]

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.gi, gc.l_bot, l_bot
-/
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (NonUnitalSubsemiring.gi R).gc.l_bot

@[simp]
/--
theorem `closure_univ` / 定理 `closure_univ`

English:
theorem closure_univ
  statement: closure (Set.univ : Set R) = ⊤
  proof: @coe_top R _ ▸ closure_eq ⊤

中文:
定理 closure_univ
  结论: closure (Set.univ : Set R) = ⊤
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
  proof: (NonUnitalSubsemiring.gi R).gc.l_sup

中文:
定理 closure_union
  条件: (s t : Set R)
  结论: closure (s union t) = closure s ⊔ closure t
  证明: (NonUnitalSubsemiring.gi R).gc.l_sup

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.gi, gc.l_sup, l_sup
-/
theorem closure_union (s t : Set R) : closure (s union t) = closure s ⊔ closure t :=
  (NonUnitalSubsemiring.gi R).gc.l_sup

/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: {ι} (s : ι -> Set R)
  statement: closure (⋃ i, s i) = ⨆ i, closure (s i)
  proof: (NonUnitalSubsemiring.gi R).gc.l_iSup

中文:
定理 closure_iUnion
  条件: {ι} (s : ι -> Set R)
  结论: closure (⋃ i, s i) = ⨆ i, closure (s i)
  证明: (NonUnitalSubsemiring.gi R).gc.l_iSup

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.gi, gc.l_iSup, l_iSup
-/
theorem closure_iUnion {ι} (s : ι -> Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (NonUnitalSubsemiring.gi R).gc.l_iSup

/--
theorem `closure_sUnion` / 定理 `closure_sUnion`

English:
theorem closure_sUnion
  given: (s : Set (Set R))
  statement: closure (⋃₀ s) = ⨆ t in s, closure t
  proof: (NonUnitalSubsemiring.gi R).gc.l_sSup

中文:
定理 closure_sUnion
  条件: (s : Set (Set R))
  结论: closure (⋃₀ s) = ⨆ t in s, closure t
  证明: (NonUnitalSubsemiring.gi R).gc.l_sSup

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.gi, gc.l_sSup, l_sSup
-/
theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t in s, closure t :=
  (NonUnitalSubsemiring.gi R).gc.l_sSup

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (s t : NonUnitalSubsemiring R) (f : F)
  proof: @GaloisConnection.l_sup _ _ s t _ _ _ _ (gc_map_comap f)

中文:
定理 map_sup
  条件: (s t : NonUnitalSubsemiring R) (f : F)
  证明: @GaloisConnection.l_sup _ _ s t _ _ _ _ (gc_map_comap f)

Depends on / 依赖: GaloisConnection, GaloisConnection.l_sup, gc_map_comap, l_sup
-/
theorem map_sup (s t : NonUnitalSubsemiring R) (f : F) :
    (map f (s ⊔ t) : NonUnitalSubsemiring S) = map f s ⊔ map f t :=
  @GaloisConnection.l_sup _ _ s t _ _ _ _ (gc_map_comap f)

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : F) (s : ι -> NonUnitalSubsemiring R)
  proof: @GaloisConnection.l_iSup _ _ _ _ _ _ _ (gc_map_comap f) s

中文:
定理 map_iSup
  条件: {ι : Sort*} (f : F) (s : ι -> NonUnitalSubsemiring R)
  证明: @GaloisConnection.l_iSup _ _ _ _ _ _ _ (gc_map_comap f) s

Depends on / 依赖: GaloisConnection, GaloisConnection.l_iSup, gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : F) (s : ι -> NonUnitalSubsemiring R) :
    (map f (iSup s) : NonUnitalSubsemiring S) = ⨆ i, map f (s i) :=
  @GaloisConnection.l_iSup _ _ _ _ _ _ _ (gc_map_comap f) s

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (s t : NonUnitalSubsemiring R) (f : F) (hf : Function.Injective f)
  proof: SetLike.coe_injective (Set.image_inter hf)

中文:
定理 map_inf
  条件: (s t : NonUnitalSubsemiring R) (f : F) (hf : Function.Injective f)
  证明: SetLike.coe_injective (Set.image_inter hf)

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (s t : NonUnitalSubsemiring R) (f : F) (hf : Function.Injective f) :
    (map f (s ⊓ t) : NonUnitalSubsemiring S) = map f s ⊓ map f t :=
  SetLike.coe_injective (Set.image_inter hf)

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
  结论: {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
    (s : ι -> NonUnitalSubsemiring R) :
    (map f (iInf s) : NonUnitalSubsemiring S) = ⨅ i, map f (s i) := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (s t : NonUnitalSubsemiring S) (f : F)
  proof: @GaloisConnection.u_inf _ _ s t _ _ _ _ (gc_map_comap f)

中文:
定理 comap_inf
  条件: (s t : NonUnitalSubsemiring S) (f : F)
  证明: @GaloisConnection.u_inf _ _ s t _ _ _ _ (gc_map_comap f)

Depends on / 依赖: GaloisConnection, GaloisConnection.u_inf, gc_map_comap, u_inf
-/
theorem comap_inf (s t : NonUnitalSubsemiring S) (f : F) :
    (comap f (s ⊓ t) : NonUnitalSubsemiring R) = comap f s ⊓ comap f t :=
  @GaloisConnection.u_inf _ _ s t _ _ _ _ (gc_map_comap f)

/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : F) (s : ι -> NonUnitalSubsemiring S)
  proof: @GaloisConnection.u_iInf _ _ _ _ _ _ _ (gc_map_comap f) s

@[simp]

中文:
定理 comap_iInf
  条件: {ι : Sort*} (f : F) (s : ι -> NonUnitalSubsemiring S)
  证明: @GaloisConnection.u_iInf _ _ _ _ _ _ _ (gc_map_comap f) s

@[simp]

Depends on / 依赖: GaloisConnection, GaloisConnection.u_iInf, gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : F) (s : ι -> NonUnitalSubsemiring S) :
    (comap f (iInf s) : NonUnitalSubsemiring R) = ⨅ i, comap f (s i) :=
  @GaloisConnection.u_iInf _ _ _ _ _ _ _ (gc_map_comap f) s

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : F)
  statement: map f (⊥ : NonUnitalSubsemiring R) = (⊥ : NonUnitalSubsemiring S)
  proof: (gc_map_comap f).l_bot

@[simp]

中文:
定理 map_bot
  条件: (f : F)
  结论: map f (⊥ : NonUnitalSubsemiring R) = (⊥ : NonUnitalSubsemiring S)
  证明: (gc_map_comap f).l_bot

@[simp]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : F) : map f (⊥ : NonUnitalSubsemiring R) = (⊥ : NonUnitalSubsemiring S) :=
  (gc_map_comap f).l_bot

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : F)
  statement: comap f (⊤ : NonUnitalSubsemiring S) = (⊤ : NonUnitalSubsemiring R)
  proof: (gc_map_comap f).u_top

中文:
定理 comap_top
  条件: (f : F)
  结论: comap f (⊤ : NonUnitalSubsemiring S) = (⊤ : NonUnitalSubsemiring R)
  证明: (gc_map_comap f).u_top

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top (f : F) : comap f (⊤ : NonUnitalSubsemiring S) = (⊤ : NonUnitalSubsemiring R) :=
  (gc_map_comap f).u_top

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S)
  body: { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := (s : Set R) ×ˢ (t : Set S) }

@[norm_cast]

中文:
定义 prod
  签名: (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S)
  定义体: { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := (s : Set R) ×ˢ (t : Set S) }

@[norm_cast]

Depends on / 依赖: carrier, s.toAddSubmonoid.prod, s.toSubsemigroup.prod, t.toAddSubmonoid, t.toSubsemigroup, toAddSubmonoid, toSubsemigroup
-/
def prod (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : NonUnitalSubsemiring (R × S) :=
  { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := (s : Set R) ×ˢ (t : Set S) }

@[norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S)
  proof: rfl

中文:
定理 coe_prod
  条件: (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S)
  证明: rfl
-/
theorem coe_prod (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl

/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} {p : R × S}
  proof: Iff.rfl

@[gcongr, mono]

中文:
定理 mem_prod
  条件: {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} {p : R × S}
  证明: Iff.rfl

@[gcongr, mono]

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} {p : R × S} :
    p in s.prod t ↔ p.1 in s ∧ p.2 in t :=
  Iff.rfl

@[gcongr, mono]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: ⦃s₁ s₂
  statement: NonUnitalSubsemiring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubsemiring S⦄
  proof: Set.prod_mono hs ht

中文:
定理 prod_mono
  条件: ⦃s₁ s₂
  结论: NonUnitalSubsemiring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubsemiring S⦄
  证明: Set.prod_mono hs ht

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono ⦃s₁ s₂ : NonUnitalSubsemiring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubsemiring S⦄
    (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂ :=
  Set.prod_mono hs ht

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  given: (s : NonUnitalSubsemiring R)
  proof: prod_mono (le_refl s)

中文:
定理 prod_mono_right
  条件: (s : NonUnitalSubsemiring R)
  证明: prod_mono (le_refl s)

Depends on / 依赖: le_refl, prod_mono
-/
theorem prod_mono_right (s : NonUnitalSubsemiring R) :
    Monotone fun t : NonUnitalSubsemiring S => s.prod t :=
  prod_mono (le_refl s)

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  given: (t : NonUnitalSubsemiring S)
  proof: fun _ _ hs => prod_mono hs (le_refl t)

中文:
定理 prod_mono_left
  条件: (t : NonUnitalSubsemiring S)
  证明: fun _ _ hs => prod_mono hs (le_refl t)

Depends on / 依赖: le_refl, prod_mono
-/
theorem prod_mono_left (t : NonUnitalSubsemiring S) :
    Monotone fun s : NonUnitalSubsemiring R => s.prod t := fun _ _ hs => prod_mono hs (le_refl t)

/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  given: (s : NonUnitalSubsemiring R)
  proof: ext fun x => by simp [mem_prod]

中文:
定理 prod_top
  条件: (s : NonUnitalSubsemiring R)
  证明: ext fun x => by simp [mem_prod]

Depends on / 依赖: mem_prod
-/
theorem prod_top (s : NonUnitalSubsemiring R) :
    s.prod (⊤ : NonUnitalSubsemiring S) = s.comap (NonUnitalRingHom.fst R S) :=
  ext fun x => by simp [mem_prod]

/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  given: (s : NonUnitalSubsemiring S)
  proof: ext fun x => by simp [mem_prod]

@[simp]

中文:
定理 top_prod
  条件: (s : NonUnitalSubsemiring S)
  证明: ext fun x => by simp [mem_prod]

@[simp]

Depends on / 依赖: mem_prod
-/
theorem top_prod (s : NonUnitalSubsemiring S) :
    (⊤ : NonUnitalSubsemiring R).prod s = s.comap (NonUnitalRingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
/--
theorem `top_prod_top` / 定理 `top_prod_top`

English:
theorem top_prod_top
  statement: (⊤ : NonUnitalSubsemiring R).prod (⊤ : NonUnitalSubsemiring S) = ⊤
  proof: (top_prod _).trans comap_top _

中文:
定理 top_prod_top
  结论: (⊤ : NonUnitalSubsemiring R).prod (⊤ : NonUnitalSubsemiring S) = ⊤
  证明: (top_prod _).trans comap_top _

Depends on / 依赖: comap_top, top_prod
-/
theorem top_prod_top : (⊤ : NonUnitalSubsemiring R).prod (⊤ : NonUnitalSubsemiring S) = ⊤ :=
(top_prod _).trans comap_top _

/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  statement: center (R × S) = prod (center R) (center S)
  proof: SetLike.coe_injective Set.center_prod

中文:
定理 center_prod
  结论: center (R × S) = prod (center R) (center S)
  证明: SetLike.coe_injective Set.center_prod
-/
protected theorem center_prod : center (R × S) = prod (center R) (center S) :=
  SetLike.coe_injective Set.center_prod

/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S)
  body: { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 prodEquiv
  签名: (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S)
  定义体: { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: Equiv.Set.prod, map_add, map_mul
-/
def prodEquiv (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/--
theorem `mem_iSup_of_directed` / 定理 `mem_iSup_of_directed`

English:
theorem mem_iSup_of_directed
  statement: {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubsemiring R}
  proof: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : NonUnitalSubsemiring R :=
    NonUnitalSubsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubsemigroup) (Subsemigroup.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i 

中文:
定理 mem_iSup_of_directed
  结论: {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubsemiring R}
  证明: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : NonUnitalSubsemiring R :=
    NonUnitalSubsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubsemigroup) (Subsemigroup.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i 

Depends on / 依赖: AddSubmonoid, AddSubmonoid.coe_iSup_of_directed, NonUnitalSubsemiring, NonUnitalSubsemiring.mk, Set.mem_iUnion, Subsemigroup, Subsemigroup.coe_iSup_of_directed, coe_iSup_of_directed, iSup_le, le_iSup, mem_iUnion, toAddSubmonoid, toSubsemigroup
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubsemiring R}
    (hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exists i, x in S i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : NonUnitalSubsemiring R :=
    NonUnitalSubsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubsemigroup) (Subsemigroup.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U] using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  statement: {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubsemiring R}
  proof: Set.ext fun x => by simp [mem_iSup_of_directed hS]

中文:
定理 coe_iSup_of_directed
  结论: {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubsemiring R}
  证明: Set.ext fun x => by simp [mem_iSup_of_directed hS]

Depends on / 依赖: Set.ext, mem_iSup_of_directed
-/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubsemiring R}
    (hS : Directed (· <= ·) S) : ((⨆ i, S i : NonUnitalSubsemiring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]

/--
theorem `mem_sSup_of_directedOn` / 定理 `mem_sSup_of_directedOn`

English:
theorem mem_sSup_of_directedOn
  statement: {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
  proof: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

中文:
定理 mem_sSup_of_directedOn
  结论: {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
  证明: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

Depends on / 依赖: Nonempty, Sne.to_subtype, Subtype, Subtype.exists, directed_val, exists_prop, hS.directed_val, mem_iSup_of_directed, sSup_eq_iSup, to_subtype
-/
theorem mem_sSup_of_directedOn {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) {x : R} : x in sSup S ↔ exists s in S, x in s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

/--
theorem `coe_sSup_of_directedOn` / 定理 `coe_sSup_of_directedOn`

English:
theorem coe_sSup_of_directedOn
  statement: {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
  proof: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

中文:
定理 coe_sSup_of_directedOn
  结论: {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
  证明: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

Depends on / 依赖: Set.ext, mem_sSup_of_directedOn
-/
theorem coe_sSup_of_directedOn {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) : (↑(sSup S) : Set R) = ⋃ s in S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

/--
theorem `isMulCommutative_iSup` / 定理 `isMulCommutative_iSup`

English:
theorem isMulCommutative_iSup
  statement: {ι : Sort*} [Nonempty ι]
  proof: by
  refine .of_setLike_mul_comm ?_
  simp_rw [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion,
    SetLike.mem_coe, forall_exists_index]
  intro a i ha b j hb
  obtain ⟨k, hik, hjk⟩ := dir i j
  exact setLike_mul_comm (hik ha) (hjk hb)

中文:
定理 isMulCommutative_iSup
  结论: {ι : Sort*} [Nonempty ι]
  证明: by
  refine .of_setLike_mul_comm ?_
  simp_rw [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion,
    SetLike.mem_coe, forall_exists_index]
  intro a i ha b j hb
  obtain ⟨k, hik, hjk⟩ := dir i j
  exact setLike_mul_comm (hik ha) (hjk hb)

Depends on / 依赖: Set.mem_iUnion, SetLike, SetLike.mem_coe, coe_iSup_of_directed, forall_exists_index, mem_coe, mem_iUnion, of_setLike_mul_comm, setLike_mul_comm, simp_rw
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι]
    {S : ι -> NonUnitalSubsemiring R} [hS : forall i, IsMulCommutative (S i)]
    (dir : Directed (· <= ·) S) : IsMulCommutative (⨆ i, S i : NonUnitalSubsemiring R) := by
  refine .of_setLike_mul_comm ?_
  simp_rw [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion,
    SetLike.mem_coe, forall_exists_index]
  intro a i ha b j hb
  obtain ⟨k, hik, hjk⟩ := dir i j
  exact setLike_mul_comm (hik ha) (hjk hb)

/--
Instance `instIsMulCommutative_iSup` / 实例 `instIsMulCommutative_iSup`

English:
instance instIsMulCommutative_iSup
  signature: {ι : Type*} [Nonempty ι] [Preorder ι]
  body: NonUnitalSubsemiring.isMulCommutative_iSup S.monotone.directed_le

中文:
实例 instIsMulCommutative_iSup
  签名: {ι : 类型} [Nonempty ι] [Preorder ι]
  定义体: NonUnitalSubsemiring.isMulCommutative_iSup S.monotone.directed_le

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.isMulCommutative_iSup, S.monotone.directed_le, directed_le, isMulCommutative_iSup, monotone
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι]
    [IsDirectedOrder ι] {S : ι ->o NonUnitalSubsemiring R} [hS : forall i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubsemiring R) :=
  NonUnitalSubsemiring.isMulCommutative_iSup S.monotone.directed_le

end NonUnitalSubsemiring

namespace NonUnitalRingHom

variable {F : Type*} [FunLike F R S]

/--
theorem `eq_of_eqOn_stop` / 定理 `eq_of_eqOn_stop`

English:
theorem eq_of_eqOn_stop
  statement: {f g : F}
  proof: DFunLike.ext _ _ fun _ => h trivial

中文:
定理 eq_of_eqOn_stop
  结论: {f g : F}
  证明: DFunLike.ext _ _ fun _ => h trivial

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem eq_of_eqOn_stop {f g : F}
    (h : Set.EqOn (f : R -> S) (g : R -> S) (⊤ : NonUnitalSubsemiring R)) : f = g :=
  DFunLike.ext _ _ fun _ => h trivial

variable [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring T]
  [NonUnitalRingHomClass F R S]
  {S' : Type*} [SetLike S' S] [NonUnitalSubsemiringClass S' S]
  {s : NonUnitalSubsemiring R}

open NonUnitalSubsemiringClass NonUnitalSubsemiring

/--
Definition of `srangeRestrict` / `srangeRestrict` 的定义

English:
definition srangeRestrict
  signature: (f : F)
  body: codRestrict f (srange f) (mem_srange_self f)

@[simp]

中文:
定义 srangeRestrict
  签名: (f : F)
  定义体: codRestrict f (srange f) (mem_srange_self f)

@[simp]

Depends on / 依赖: codRestrict, mem_srange_self, srange
-/
def srangeRestrict (f : F) : R ->ₙ+* (srange f : NonUnitalSubsemiring S) :=
  codRestrict f (srange f) (mem_srange_self f)

@[simp]
/--
theorem `coe_srangeRestrict` / 定理 `coe_srangeRestrict`

English:
theorem coe_srangeRestrict
  given: (f : F) (x : R)
  statement: (srangeRestrict f x : S) = f x
  proof: rfl

中文:
定理 coe_srangeRestrict
  条件: (f : F) (x : R)
  结论: (srangeRestrict f x : S) = f x
  证明: rfl
-/
theorem coe_srangeRestrict (f : F) (x : R) : (srangeRestrict f x : S) = f x :=
  rfl

/--
theorem `srangeRestrict_surjective` / 定理 `srangeRestrict_surjective`

English:
theorem srangeRestrict_surjective
  given: (f : F)
  proof: fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_srange.mp hy
  ⟨x, Subtype.ext hx⟩

中文:
定理 srangeRestrict_surjective
  条件: (f : F)
  证明: fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_srange.mp hy
  ⟨x, Subtype.ext hx⟩

Depends on / 依赖: Subtype, Subtype.ext, mem_srange, mem_srange.mp
-/
theorem srangeRestrict_surjective (f : F) :
    Function.Surjective (srangeRestrict f : R -> (srange f : NonUnitalSubsemiring S)) :=
  fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_srange.mp hy
  ⟨x, Subtype.ext hx⟩

/--
theorem `srange_eq_top_iff_surjective` / 定理 `srange_eq_top_iff_surjective`

English:
theorem srange_eq_top_iff_surjective
  given: {f : F}
  proof: SetLike.ext'_iff.trans Iff.trans (by rw [coe_srange, coe_top]) Set.range_eq_univ

中文:
定理 srange_eq_top_iff_surjective
  条件: {f : F}
  证明: SetLike.ext'_iff.trans Iff.trans (by rw [coe_srange, coe_top]) Set.range_eq_univ

Depends on / 依赖: Iff.trans, Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, coe_srange, coe_top, range_eq_univ
-/
theorem srange_eq_top_iff_surjective {f : F} :
    srange f = (⊤ : NonUnitalSubsemiring S) ↔ Function.Surjective (f : R -> S) :=
SetLike.ext'_iff.trans Iff.trans (by rw [coe_srange, coe_top]) Set.range_eq_univ

/-- The range of a surjective non-unital ring homomorphism is the whole of the codomain. -/
@[simp]
/--
theorem `srange_eq_top_of_surjective` / 定理 `srange_eq_top_of_surjective`

English:
theorem srange_eq_top_of_surjective
  given: (f : F) (hf : Function.Surjective (f : R -> S))
  proof: srange_eq_top_iff_surjective.2 hf

中文:
定理 srange_eq_top_of_surjective
  条件: (f : F) (hf : Function.Surjective (f : R -> S))
  证明: srange_eq_top_iff_surjective.2 hf

Depends on / 依赖: srange_eq_top_iff_surjective
-/
theorem srange_eq_top_of_surjective (f : F) (hf : Function.Surjective (f : R -> S)) :
    srange f = (⊤ : NonUnitalSubsemiring S) :=
  srange_eq_top_iff_surjective.2 hf

/--
theorem `eqOn_sclosure` / 定理 `eqOn_sclosure`

English:
theorem eqOn_sclosure
  given: {f g : F} {s : Set R} (h : Set.EqOn (f : R -> S) (g : R -> S) s)
  proof: show closure s <= eqSlocus f g from closure_le.2 h

中文:
定理 eqOn_sclosure
  条件: {f g : F} {s : Set R} (h : Set.EqOn (f : R -> S) (g : R -> S) s)
  证明: show closure s <= eqSlocus f g from closure_le.2 h

Depends on / 依赖: closure, closure_le, eqSlocus
-/
theorem eqOn_sclosure {f g : F} {s : Set R} (h : Set.EqOn (f : R -> S) (g : R -> S) s) :
    Set.EqOn f g (closure s) :=
  show closure s <= eqSlocus f g from closure_le.2 h

/--
theorem `eq_of_eqOn_sdense` / 定理 `eq_of_eqOn_sdense`

English:
theorem eq_of_eqOn_sdense
  statement: {s : Set R} (hs : closure s = ⊤) {f g : F}
  proof: eq_of_eqOn_stop hs ▸ eqOn_sclosure h

中文:
定理 eq_of_eqOn_sdense
  结论: {s : Set R} (hs : closure s = ⊤) {f g : F}
  证明: eq_of_eqOn_stop hs ▸ eqOn_sclosure h

Depends on / 依赖: eqOn_sclosure, eq_of_eqOn_stop
-/
theorem eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : F}
    (h : s.EqOn (f : R -> S) (g : R -> S)) : f = g :=
eq_of_eqOn_stop hs ▸ eqOn_sclosure h

/--
theorem `sclosure_preimage_le` / 定理 `sclosure_preimage_le`

English:
theorem sclosure_preimage_le
  given: (f : F) (s : Set S)
  proof: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 sclosure_preimage_le
  条件: (f : F) (s : Set S)
  证明: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem sclosure_preimage_le (f : F) (s : Set S) :
    closure ((f : R -> S) ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

/--
theorem `map_sclosure` / 定理 `map_sclosure`

English:
theorem map_sclosure
  given: (f : F) (s : Set R)
  statement: (closure s).map f = closure ((f : R -> S) '' s)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubsemiring.gi S).gc
    (NonUnitalSubsemiring.gi R).gc fun _ => rfl

中文:
定理 map_sclosure
  条件: (f : F) (s : Set R)
  结论: (closure s).map f = closure ((f : R -> S) '' s)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubsemiring.gi S).gc
    (NonUnitalSubsemiring.gi R).gc fun _ => rfl

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.gi, Set.image_preimage.l_comm_of_u_comm, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_sclosure (f : F) (s : Set R) : (closure s).map f = closure ((f : R -> S) '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubsemiring.gi S).gc
    (NonUnitalSubsemiring.gi R).gc fun _ => rfl

end NonUnitalRingHom

namespace NonUnitalSubsemiring

open NonUnitalRingHom NonUnitalSubsemiringClass

@[simp]
/--
theorem `srange_subtype` / 定理 `srange_subtype`

English:
theorem srange_subtype
  given: (s : NonUnitalSubsemiring R)
  statement: NonUnitalRingHom.srange (subtype s) = s
  proof: SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

中文:
定理 srange_subtype
  条件: (s : NonUnitalSubsemiring R)
  结论: NonUnitalRingHom.srange (subtype s) = s
  证明: SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

Depends on / 依赖: SetLike, SetLike.coe_injective, Subtype, Subtype.range_coe, coe_injective, coe_srange, range_coe
-/
theorem srange_subtype (s : NonUnitalSubsemiring R) : NonUnitalRingHom.srange (subtype s) = s :=
SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

variable [NonUnitalNonAssocSemiring S]

@[simp]
/--
theorem `range_fst` / 定理 `range_fst`

English:
theorem range_fst
  statement: NonUnitalRingHom.srange (fst R S) = ⊤
  proof: NonUnitalRingHom.srange_eq_top_of_surjective (fst R S) Prod.fst_surjective

@[simp]

中文:
定理 range_fst
  结论: NonUnitalRingHom.srange (fst R S) = ⊤
  证明: NonUnitalRingHom.srange_eq_top_of_surjective (fst R S) Prod.fst_surjective

@[simp]

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.srange_eq_top_of_surjective, Prod.fst_surjective, fst_surjective, srange_eq_top_of_surjective
-/
theorem range_fst : NonUnitalRingHom.srange (fst R S) = ⊤ :=
  NonUnitalRingHom.srange_eq_top_of_surjective (fst R S) Prod.fst_surjective

@[simp]
/--
theorem `range_snd` / 定理 `range_snd`

English:
theorem range_snd
  statement: NonUnitalRingHom.srange (snd R S) = ⊤
  proof: NonUnitalRingHom.srange_eq_top_of_surjective (snd R S) Prod.snd_surjective

中文:
定理 range_snd
  结论: NonUnitalRingHom.srange (snd R S) = ⊤
  证明: NonUnitalRingHom.srange_eq_top_of_surjective (snd R S) Prod.snd_surjective

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.srange_eq_top_of_surjective, Prod.snd_surjective, snd_surjective, srange_eq_top_of_surjective
-/
theorem range_snd : NonUnitalRingHom.srange (snd R S) = ⊤ :=
NonUnitalRingHom.srange_eq_top_of_surjective (snd R S) Prod.snd_surjective

end NonUnitalSubsemiring

namespace RingEquiv

open NonUnitalRingHom NonUnitalSubsemiringClass

variable {s t : NonUnitalSubsemiring R}
variable [NonUnitalNonAssocSemiring S] {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]

/--
Definition of `nonUnitalSubsemiringCongr` / `nonUnitalSubsemiringCongr` 的定义

English:
definition nonUnitalSubsemiringCongr
  signature: (h : s = t)
  body: { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 nonUnitalSubsemiringCongr
  签名: (h : s = t)
  定义体: { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: Equiv.setCongr, congr_arg, map_add, map_mul, setCongr
-/
def nonUnitalSubsemiringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/--
Definition of `sofLeftInverse'` / `sofLeftInverse'` 的定义

English:
definition sofLeftInverse'
  signature: {g : S -> R} {f : F} (h : Function.LeftInverse g f)
  body: { srangeRestrict f with
    toFun := srangeRestrict f
    invFun := fun x => g (subtype (srange f) x)
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]

中文:
定义 sofLeftInverse'
  签名: {g : S -> R} {f : F} (h : Function.LeftInverse g f)
  定义体: { srangeRestrict f with
    toFun := srangeRestrict f
    invFun := fun x => g (subtype (srange f) x)
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.mem_srange.mp, Subtype, Subtype.ext, invFun, left_inv, mem_srange, right_inv, srange, srangeRestrict, subtype, x.prop
-/
def sofLeftInverse' {g : S -> R} {f : F} (h : Function.LeftInverse g f) : R ≃+* srange f :=
  { srangeRestrict f with
    toFun := srangeRestrict f
    invFun := fun x => g (subtype (srange f) x)
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/--
theorem `sofLeftInverse'_apply` / 定理 `sofLeftInverse'_apply`

English:
theorem sofLeftInverse'_apply
  given: {g : S -> R} {f : F} (h : Function.LeftInverse g f) (x : R)
  proof: rfl

@[simp]

中文:
定理 sofLeftInverse'_apply
  条件: {g : S -> R} {f : F} (h : Function.LeftInverse g f) (x : R)
  证明: rfl

@[simp]
-/
theorem sofLeftInverse'_apply {g : S -> R} {f : F} (h : Function.LeftInverse g f) (x : R) :
    ↑(sofLeftInverse' h x) = f x :=
  rfl

@[simp]
/--
theorem `sofLeftInverse'_symm_apply` / 定理 `sofLeftInverse'_symm_apply`

English:
theorem sofLeftInverse'_symm_apply
  statement: {g : S -> R} {f : F} (h : Function.LeftInverse g f)
  proof: rfl

中文:
定理 sofLeftInverse'_symm_apply
  结论: {g : S -> R} {f : F} (h : Function.LeftInverse g f)
  证明: rfl
-/
theorem sofLeftInverse'_symm_apply {g : S -> R} {f : F} (h : Function.LeftInverse g f)
    (x : srange f) : (sofLeftInverse' h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of non-unital semirings and a non-unital subsemiring
`s` of `R`, `nonUnitalSubsemiringMap e s` is the induced equivalence between `s` and
`s.map e` -/
@[simps!]
/--
Definition of `nonUnitalSubsemiringMap` / `nonUnitalSubsemiringMap` 的定义

English:
definition nonUnitalSubsemiringMap
  signature: (e : R ≃+* S) (s : NonUnitalSubsemiring R)
  body: { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid,
    e.toMulEquiv.subsemigroupMap s.toSubsemigroup with }

中文:
定义 nonUnitalSubsemiringMap
  签名: (e : R ≃+* S) (s : NonUnitalSubsemiring R)
  定义体: { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid,
    e.toMulEquiv.subsemigroupMap s.toSubsemigroup with }

Depends on / 依赖: addSubmonoidMap, e.toAddEquiv.addSubmonoidMap, e.toMulEquiv.subsemigroupMap, s.toAddSubmonoid, s.toSubsemigroup, subsemigroupMap, toAddEquiv, toAddSubmonoid, toMulEquiv, toSubsemigroup
-/
def nonUnitalSubsemiringMap (e : R ≃+* S) (s : NonUnitalSubsemiring R) :
    s ≃+* NonUnitalSubsemiring.map e.toNonUnitalRingHom s :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid,
    e.toMulEquiv.subsemigroupMap s.toSubsemigroup with }

end RingEquiv
