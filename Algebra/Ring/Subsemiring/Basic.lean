/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Ring.Action.Subobjects
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.GroupTheory.Submonoid.Centralizer
public import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
public import Mathlib.Algebra.Module.Defs

/-!
# Bundled subsemirings

We define some standard constructions on bundled subsemirings: `CompleteLattice` structure,
subsemiring `map`, `comap` and range (`rangeS`) of a `RingHom` etc.
-/

@[expose] public section


universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

section SubsemiringClass

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

/--
Instance `instCharZero` / 实例 `instCharZero`

English:
instance instCharZero
  signature: [CharZero R]
  body: ⟨Function.Injective.of_comp (f := Subtype.val) (g := Nat.cast (R := s)) Nat.cast_injective⟩

中文:
实例 instCharZero
  签名: [CharZero R]
  定义体: ⟨Function.Injective.of_comp (f := Subtype.val) (g := Nat.cast (R := s)) Nat.cast_injective⟩

Depends on / 依赖: Function, Function.Injective.of_comp, Injective, Nat.cast, Nat.cast_injective, Subtype, Subtype.val, cast_injective, of_comp
-/
instance instCharZero [CharZero R] : CharZero s :=
  ⟨Function.Injective.of_comp (f := Subtype.val) (g := Nat.cast (R := s)) Nat.cast_injective⟩

end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiring S] [NonAssocSemiring T]

namespace Subsemiring

variable (s : Subsemiring R)

@[gcongr, mono]
/--
theorem `toSubmonoid_strictMono` / 定理 `toSubmonoid_strictMono`

English:
theorem toSubmonoid_strictMono
  statement: StrictMono (toSubmonoid : Subsemiring R -> Submonoid R)
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toSubmonoid_strictMono
  结论: StrictMono (toSubmonoid : Subsemiring R -> Submonoid R)
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subsemiring R -> Submonoid R) :=
  fun _ _ => id

@[gcongr, mono]
/--
theorem `toSubmonoid_mono` / 定理 `toSubmonoid_mono`

English:
theorem toSubmonoid_mono
  statement: Monotone (toSubmonoid : Subsemiring R -> Submonoid R)
  proof: toSubmonoid_strictMono.monotone

@[gcongr, mono]

中文:
定理 toSubmonoid_mono
  结论: Monotone (toSubmonoid : Subsemiring R -> Submonoid R)
  证明: toSubmonoid_strictMono.monotone

@[gcongr, mono]

Depends on / 依赖: monotone, toSubmonoid_strictMono, toSubmonoid_strictMono.monotone
-/
theorem toSubmonoid_mono : Monotone (toSubmonoid : Subsemiring R -> Submonoid R) :=
  toSubmonoid_strictMono.monotone

@[gcongr, mono]
/--
theorem `toAddSubmonoid_strictMono` / 定理 `toAddSubmonoid_strictMono`

English:
theorem toAddSubmonoid_strictMono
  statement: StrictMono (toAddSubmonoid : Subsemiring R -> AddSubmonoid R)
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toAddSubmonoid_strictMono
  结论: StrictMono (toAddSubmonoid : Subsemiring R -> AddSubmonoid R)
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Subsemiring R -> AddSubmonoid R) :=
  fun _ _ => id

@[gcongr, mono]
/--
theorem `toAddSubmonoid_mono` / 定理 `toAddSubmonoid_mono`

English:
theorem toAddSubmonoid_mono
  statement: Monotone (toAddSubmonoid : Subsemiring R -> AddSubmonoid R)
  proof: toAddSubmonoid_strictMono.monotone

中文:
定理 toAddSubmonoid_mono
  结论: Monotone (toAddSubmonoid : Subsemiring R -> AddSubmonoid R)
  证明: toAddSubmonoid_strictMono.monotone

Depends on / 依赖: monotone, toAddSubmonoid_strictMono, toAddSubmonoid_strictMono.monotone
-/
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Subsemiring R -> AddSubmonoid R) :=
  toAddSubmonoid_strictMono.monotone

/-- Product of a list of elements in a `Subsemiring` is in the `Subsemiring`. -/
nonrec theorem list_prod_mem {R : Type*} [Semiring R] (s : Subsemiring R) {l : List R} :
    (forall x in l, x in s) -> l.prod in s :=
  list_prod_mem

/--
theorem `list_sum_mem` / 定理 `list_sum_mem`

English:
theorem list_sum_mem
  given: {l : List R}
  statement: (forall x in l, x in s) -> l.sum in s
  proof: list_sum_mem

中文:
定理 list_sum_mem
  条件: {l : List R}
  结论: (对任意 x in l, x in s) -> l.sum in s
  证明: list_sum_mem
-/
protected theorem list_sum_mem {l : List R} : (forall x in l, x in s) -> l.sum in s :=
  list_sum_mem

/--
theorem `multiset_prod_mem` / 定理 `multiset_prod_mem`

English:
theorem multiset_prod_mem
  given: {R} [CommSemiring R] (s : Subsemiring R) (m : Multiset R)
  proof: multiset_prod_mem m

中文:
定理 multiset_prod_mem
  条件: {R} [CommSemiring R] (s : Subsemiring R) (m : Multiset R)
  证明: multiset_prod_mem m
-/
protected theorem multiset_prod_mem {R} [CommSemiring R] (s : Subsemiring R) (m : Multiset R) :
    (forall a in m, a in s) -> m.prod in s :=
  multiset_prod_mem m

/--
theorem `multiset_sum_mem` / 定理 `multiset_sum_mem`

English:
theorem multiset_sum_mem
  given: (m : Multiset R)
  statement: (forall a in m, a in s) -> m.sum in s
  proof: multiset_sum_mem m

中文:
定理 multiset_sum_mem
  条件: (m : Multiset R)
  结论: (对任意 a in m, a in s) -> m.sum in s
  证明: multiset_sum_mem m

Depends on / 依赖: hom.toAlgebra, toAlgebra, toStalk
-/
protected theorem multiset_sum_mem (m : Multiset R) : (forall a in m, a in s) -> m.sum in s :=
  multiset_sum_mem m

/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  statement: {R : Type*} [CommSemiring R] (s : Subsemiring R) {ι : Type*}
  proof: prod_mem h

中文:
定理 prod_mem
  结论: {R : 类型} [CommSemiring R] (s : Subsemiring R) {ι : 类型}
  证明: prod_mem h

Depends on / 依赖: compHom, toStalk
-/
protected theorem prod_mem {R : Type*} [CommSemiring R] (s : Subsemiring R) {ι : Type*}
    {t : Finset ι} {f : ι -> R} (h : forall c in t, f c in s) : (∏ i in t, f i) in s :=
  prod_mem h

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  statement: (s : Subsemiring R) {ι : Type*} {t : Finset ι} {f : ι -> R}
  proof: sum_mem h

中文:
定理 sum_mem
  结论: (s : Subsemiring R) {ι : 类型} {t : Finset ι} {f : ι -> R}
  证明: sum_mem h
-/
protected theorem sum_mem (s : Subsemiring R) {ι : Type*} {t : Finset ι} {f : ι -> R}
    (h : forall c in t, f c in s) : (∑ i in t, f i) in s :=
  sum_mem h

/-- The ring equiv between the top element of `Subsemiring R` and `R`. -/
@[simps]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : Subsemiring R) ≃+* R where
  body: r
  invFun r := ⟨r, Subsemiring.mem_top r⟩
  map_mul' := (⊤ : Subsemiring R).coe_mul
  map_add' := (⊤ : Subsemiring R).coe_add

中文:
定义 topEquiv
  签名: : (⊤ : Subsemiring R) ≃+* R where
  定义体: r
  invFun r := ⟨r, Subsemiring.mem_top r⟩
  map_mul' := (⊤ : Subsemiring R).coe_mul
  map_add' := (⊤ : Subsemiring R).coe_add

Depends on / 依赖: of_algebraMap_smul
-/
def topEquiv : (⊤ : Subsemiring R) ≃+* R where
  toFun r := r
  invFun r := ⟨r, Subsemiring.mem_top r⟩
  map_mul' := (⊤ : Subsemiring R).coe_mul
  map_add' := (⊤ : Subsemiring R).coe_add

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
@[simps coe toSubmonoid]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : R ->+* S) (s : Subsemiring S)
  body: { s.toSubmonoid.comap (f : R ->* S), s.toAddSubmonoid.comap (f : R ->+ S) with carrier := f ⁻¹' s }

@[simp]

中文:
定义 comap
  签名: (f : R ->+* S) (s : Subsemiring S)
  定义体: { s.toSubmonoid.comap (f : R ->* S), s.toAddSubmonoid.comap (f : R ->+ S) with carrier := f ⁻¹' s }

@[simp]

Depends on / 依赖: carrier, s.toAddSubmonoid.comap, s.toSubmonoid.comap, toAddSubmonoid, toSubmonoid
-/
def comap (f : R ->+* S) (s : Subsemiring S) : Subsemiring R :=
  { s.toSubmonoid.comap (f : R ->* S), s.toAddSubmonoid.comap (f : R ->+ S) with carrier := f ⁻¹' s }

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {s : Subsemiring S} {f : R ->+* S} {x : R}
  statement: x in s.comap f ↔ f x in s
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {s : Subsemiring S} {f : R ->+* S} {x : R}
  结论: x in s.comap f ↔ f x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, module, modulePresheafStalkIso, toAddEquiv, toAddEquiv.symm.module
-/
theorem mem_comap {s : Subsemiring S} {f : R ->+* S} {x : R} : x in s.comap f ↔ f x in s :=
  Iff.rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (s : Subsemiring T) (g : S ->+* T) (f : R ->+* S)
  proof: rfl

中文:
定理 comap_comap
  条件: (s : Subsemiring T) (g : S ->+* T) (f : R ->+* S)
  证明: rfl
-/
theorem comap_comap (s : Subsemiring T) (g : S ->+* T) (f : R ->+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
@[simps coe toSubmonoid]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S) (s : Subsemiring R)
  body: { s.toSubmonoid.map (f : R ->* S), s.toAddSubmonoid.map (f : R ->+ S) with carrier := f '' s }

@[simp]

中文:
定义 map
  签名: (f : R ->+* S) (s : Subsemiring R)
  定义体: { s.toSubmonoid.map (f : R ->* S), s.toAddSubmonoid.map (f : R ->+ S) with carrier := f '' s }

@[simp]

Depends on / 依赖: carrier, s.toAddSubmonoid.map, s.toSubmonoid.map, toAddSubmonoid, toSubmonoid
-/
def map (f : R ->+* S) (s : Subsemiring R) : Subsemiring S :=
  { s.toSubmonoid.map (f : R ->* S), s.toAddSubmonoid.map (f : R ->+ S) with carrier := f '' s }

@[simp]
/--
lemma `mem_map` / 引理 `mem_map`

English:
lemma mem_map
  given: {f : R ->+* S} {s : Subsemiring R} {y : S}
  statement: y in s.map f ↔ exists x in s, f x = y
  proof: Iff.rfl

@[simp]

中文:
引理 mem_map
  条件: {f : R ->+* S} {s : Subsemiring R} {y : S}
  结论: y in s.map f ↔ 存在 x in s, f x = y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_map {f : R ->+* S} {s : Subsemiring R} {y : S} : y in s.map f ↔ exists x in s, f x = y := Iff.rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: s.map (RingHom.id R) = s
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  结论: s.map (RingHom.id R) = s
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
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
  given: {f : R ->+* S} {s : Subsemiring R} {t : Subsemiring S}
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {f : R ->+* S} {s : Subsemiring R} {t : Subsemiring S}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le_iff_le_comap {f : R ->+* S} {s : Subsemiring R} {t : Subsemiring S} :
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
  签名: (f : R ->+* S) (hf : Function.Injective f)
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
  条件: (f : R ->+* S) (hf : Function.Injective f) (x : s)
  证明: rfl
-/
theorem coe_equivMapOfInjective_apply (f : R ->+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subsemiring

namespace RingHom

variable (g : S ->+* T) (f : R ->+* S)

/-- The range of a ring homomorphism is a subsemiring. See Note [range copy pattern]. -/
@[simps! coe toSubmonoid]
/--
Definition of `rangeS` / `rangeS` 的定义

English:
definition rangeS
  signature: : Subsemiring S
  body: ((⊤ : Subsemiring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]

中文:
定义 rangeS
  签名: : Subsemiring S
  定义体: ((⊤ : Subsemiring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]

Depends on / 依赖: Set.image_univ.symm, Set.range, Subsemiring, image_univ
-/
def rangeS : Subsemiring S :=
  ((⊤ : Subsemiring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
/--
theorem `mem_rangeS` / 定理 `mem_rangeS`

English:
theorem mem_rangeS
  given: {f : R ->+* S} {y : S}
  statement: y in f.rangeS ↔ exists x, f x = y
  proof: Iff.rfl

中文:
定理 mem_rangeS
  条件: {f : R ->+* S} {y : S}
  结论: y in f.rangeS ↔ 存在 x, f x = y
  证明: Iff.rfl

Depends on / 依赖: Category, Category.assoc, Iff.rfl
-/
theorem mem_rangeS {f : R ->+* S} {y : S} : y in f.rangeS ↔ exists x, f x = y :=
  Iff.rfl

/--
theorem `rangeS_eq_map` / 定理 `rangeS_eq_map`

English:
theorem rangeS_eq_map
  given: (f : R ->+* S)
  statement: f.rangeS = (⊤ : Subsemiring R).map f
  proof: by
  ext
  simp

中文:
定理 rangeS_eq_map
  条件: (f : R ->+* S)
  结论: f.rangeS = (⊤ : Subsemiring R).map f
  证明: by
  ext
  simp
-/
theorem rangeS_eq_map (f : R ->+* S) : f.rangeS = (⊤ : Subsemiring R).map f := by
  ext
  simp

/--
theorem `mem_rangeS_self` / 定理 `mem_rangeS_self`

English:
theorem mem_rangeS_self
  given: (f : R ->+* S) (x : R)
  statement: f x in f.rangeS
  proof: mem_rangeS.mpr ⟨x, rfl⟩

中文:
定理 mem_rangeS_self
  条件: (f : R ->+* S) (x : R)
  结论: f x in f.rangeS
  证明: mem_rangeS.mpr ⟨x, rfl⟩

Depends on / 依赖: isIso_hom, mem_rangeS, mem_rangeS.mpr
-/
theorem mem_rangeS_self (f : R ->+* S) (x : R) : f x in f.rangeS :=
  mem_rangeS.mpr ⟨x, rfl⟩

/--
theorem `map_rangeS` / 定理 `map_rangeS`

English:
theorem map_rangeS
  statement: f.rangeS.map g = (g.comp f).rangeS
  proof: by
  simpa only [rangeS_eq_map] using (⊤ : Subsemiring R).map_map g f

中文:
定理 map_rangeS
  结论: f.rangeS.map g = (g.comp f).rangeS
  证明: by
  simpa only [rangeS_eq_map] using (⊤ : Subsemiring R).map_map g f

Depends on / 依赖: Subsemiring, isIso_inv, map_map, rangeS_eq_map
-/
theorem map_rangeS : f.rangeS.map g = (g.comp f).rangeS := by
  simpa only [rangeS_eq_map] using (⊤ : Subsemiring R).map_map g f

variable {f} in
/--
theorem `rangeS_eq_top` / 定理 `rangeS_eq_top`

English:
theorem rangeS_eq_top
  statement: f.rangeS = ⊤ ↔ Function.Surjective f
  proof: by
  simp [← Set.range_eq_univ, SetLike.ext'_iff]

中文:
定理 rangeS_eq_top
  结论: f.rangeS = ⊤ ↔ Function.Surjective f
  证明: by
  simp [← Set.range_eq_univ, SetLike.ext'_iff]

Depends on / 依赖: Set.range_eq_univ, SetLike, SetLike.ext, _iff, range_eq_univ
-/
theorem rangeS_eq_top : f.rangeS = ⊤ ↔ Function.Surjective f := by
  simp [← Set.range_eq_univ, SetLike.ext'_iff]

/--
Instance `fintypeRangeS` / 实例 `fintypeRangeS`

English:
instance fintypeRangeS
  signature: [Fintype R] [DecidableEq S] (f : R ->+* S)
  body: Set.fintypeRange f

中文:
实例 fintypeRangeS
  签名: [Fintype R] [DecidableEq S] (f : R ->+* S)
  定义体: Set.fintypeRange f

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeRangeS [Fintype R] [DecidableEq S] (f : R ->+* S) : Fintype (rangeS f) :=
  Set.fintypeRange f

end RingHom

namespace Subsemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Subsemiring R)
  body: ⟨(Nat.castRingHom R).rangeS⟩

中文:
实例 :
  签名: Bot (Subsemiring R)
  定义体: ⟨(Nat.castRingHom R).rangeS⟩

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.of_linearEquiv, LocalizedModule, LocalizedModule.mkLinearMap, Nat.castRingHom, PrimeSpectrum, PrimeSpectrum.basicOpen_one, asIdeal, basicOpen_one, castRingHom, convert, instances, mkLinearMap, of_linearEquiv, primeCompl, rangeS, toLinearEquiv, toLinearEquiv.symm, x.asIdeal.primeCompl
-/
instance : Bot (Subsemiring R) :=
  ⟨(Nat.castRingHom R).rangeS⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Subsemiring R)
  body: ⟨⊥⟩

@[norm_cast]

中文:
实例 :
  签名: Inhabited (Subsemiring R)
  定义体: ⟨⊥⟩

@[norm_cast]
-/
instance : Inhabited (Subsemiring R) :=
  ⟨⊥⟩

@[norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : Nat -> R)
  proof: (Nat.castRingHom R).coe_rangeS

中文:
定理 coe_bot
  结论: ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : 自然数 -> R)
  证明: (Nat.castRingHom R).coe_rangeS

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.of_linearEquiv, Limits, Limits.colimit.isColimit, Limits.colimit.isoColimitCocone, Limits.isColimitOfPreserves, ModuleCat, Nat.castRingHom, OpenNhds, OpenNhds.inclusion, Presheaf, TopCat, TopCat.Presheaf.stalk, addCommGroupIsoToAddEquiv, addCommGroupIsoToAddEquiv.eq_symm_apply, asIdeal, castRingHom, coe_rangeS, colimit, convert
-/
theorem coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : Nat -> R) :=
  (Nat.castRingHom R).coe_rangeS

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : R}
  statement: x in (⊥ : Subsemiring R) ↔ exists n : Nat, ↑n = x
  proof: RingHom.mem_rangeS

中文:
定理 mem_bot
  条件: {x : R}
  结论: x in (⊥ : Subsemiring R) ↔ 存在 n : 自然数, ↑n = x
  证明: RingHom.mem_rangeS

Depends on / 依赖: RingHom, RingHom.mem_rangeS, mem_rangeS
-/
theorem mem_bot {x : R} : x in (⊥ : Subsemiring R) ↔ exists n : Nat, ↑n = x :=
  RingHom.mem_rangeS

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Subsemiring R)
  body: ⟨fun s =>
    Subsemiring.mk' (⋂ t in s, ↑t) (⨅ t in s, Subsemiring.toSubmonoid t) (by simp)
      (⨅ t in s, Subsemiring.toAddSubmonoid t)
      (by simp)⟩

@[simp, norm_cast]

中文:
实例 :
  签名: InfSet (Subsemiring R)
  定义体: ⟨fun s =>
    Subsemiring.mk' (⋂ t in s, ↑t) (⨅ t in s, Subsemiring.toSubmonoid t) (by simp)
      (⨅ t in s, Subsemiring.toAddSubmonoid t)
      (by simp)⟩

@[simp, norm_cast]

Depends on / 依赖: Subsemiring, Subsemiring.mk, Subsemiring.toAddSubmonoid, Subsemiring.toSubmonoid, toAddSubmonoid, toSubmonoid
-/
instance : InfSet (Subsemiring R) :=
  ⟨fun s =>
    Subsemiring.mk' (⋂ t in s, ↑t) (⨅ t in s, Subsemiring.toSubmonoid t) (by simp)
      (⨅ t in s, Subsemiring.toAddSubmonoid t)
      (by simp)⟩

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (Subsemiring R))
  statement: ((sInf S : Subsemiring R) : Set R) = ⋂ s in S, ↑s
  proof: rfl

@[simp]

中文:
定理 coe_sInf
  条件: (S : Set (Subsemiring R))
  结论: ((sInf S : Subsemiring R) : Set R) = ⋂ s in S, ↑s
  证明: rfl

@[simp]
-/
theorem coe_sInf (S : Set (Subsemiring R)) : ((sInf S : Subsemiring R) : Set R) = ⋂ s in S, ↑s :=
  rfl

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (Subsemiring R)} {x : R}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: Set.mem_iInter₂

@[simp, norm_cast]

中文:
定理 mem_sInf
  条件: {S : Set (Subsemiring R)} {x : R}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: Set.mem_iInter₂

@[simp, norm_cast]

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {S : Set (Subsemiring R)} {x : R} : x in sInf S ↔ forall p in S, x in p :=
  Set.mem_iInter₂

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> Subsemiring R}
  statement: (↑(⨅ i, S i) : Set R) = ⋂ i, S i
  proof: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : Sort*} {S : ι -> Subsemiring R}
  结论: (↑(⨅ i, S i) : Set R) = ⋂ i, S i
  证明: by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]

Depends on / 依赖: Set.biInter_range, biInter_range, coe_sInf
-/
theorem coe_iInf {ι : Sort*} {S : ι -> Subsemiring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> Subsemiring R} {x : R}
  statement: x in ⨅ i, S i ↔ forall i, x in S i
  proof: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

中文:
定理 mem_iInf
  条件: {ι : Sort*} {S : ι -> Subsemiring R} {x : R}
  结论: x in ⨅ i, S i ↔ 对任意 i, x in S i
  证明: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> Subsemiring R} {x : R} : x in ⨅ i, S i ↔ forall i, x in S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/--
theorem `sInf_toSubmonoid` / 定理 `sInf_toSubmonoid`

English:
theorem sInf_toSubmonoid
  given: (s : Set (Subsemiring R))
  proof: mk'_toSubmonoid _ _

@[simp]

中文:
定理 sInf_toSubmonoid
  条件: (s : Set (Subsemiring R))
  证明: mk'_toSubmonoid _ _

@[simp]

Depends on / 依赖: _toSubmonoid
-/
theorem sInf_toSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toSubmonoid = ⨅ t in s, Subsemiring.toSubmonoid t :=
  mk'_toSubmonoid _ _

@[simp]
/--
theorem `sInf_toAddSubmonoid` / 定理 `sInf_toAddSubmonoid`

English:
theorem sInf_toAddSubmonoid
  given: (s : Set (Subsemiring R))
  proof: mk'_toAddSubmonoid _ _

中文:
定理 sInf_toAddSubmonoid
  条件: (s : Set (Subsemiring R))
  证明: mk'_toAddSubmonoid _ _

Depends on / 依赖: _toAddSubmonoid
-/
theorem sInf_toAddSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toAddSubmonoid = ⨅ t in s, Subsemiring.toAddSubmonoid t :=
  mk'_toAddSubmonoid _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subsemiring R)
  body: { completeLatticeOfInf (Subsemiring R) fun _ =>
      IsGLB.of_image
        (fun {s t : Subsemiring R} => show (s : Set R) subseteq t ↔ s <= t from SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ natCast_mem s n


中文:
实例 :
  签名: CompleteLattice (Subsemiring R)
  定义体: { completeLatticeOfInf (Subsemiring R) fun _ =>
      IsGLB.of_image
        (fun {s t : Subsemiring R} => show (s : Set R) subseteq t ↔ s <= t from SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ natCast_mem s n


Depends on / 依赖: And.left, And.right, IsGLB.of_image, SetLike, SetLike.coe_subset_coe, Subsemiring, bot_le, coe_subset_coe, completeLatticeOfInf, inf_le_left, inf_le_right, isGLB_biInf, le_inf, le_top, mem_bot, mem_top, natCast_mem, of_image, subseteq
-/
instance : CompleteLattice (Subsemiring R) :=
  { completeLatticeOfInf (Subsemiring R) fun _ =>
      IsGLB.of_image
        (fun {s t : Subsemiring R} => show (s : Set R) subseteq t ↔ s <= t from SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ natCast_mem s n
    top := ⊤
    le_top := fun _ _ _ => mem_top _
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

/--
theorem `eq_top_iff'` / 定理 `eq_top_iff'`

English:
theorem eq_top_iff'
  given: (A : Subsemiring R)
  statement: A = ⊤ ↔ forall x : R, x in A
  proof: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

中文:
定理 eq_top_iff'
  条件: (A : Subsemiring R)
  结论: A = ⊤ ↔ 对任意 x : R, x in A
  证明: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

Depends on / 依赖: eq_top_iff, eq_top_iff.trans, mem_top
-/
theorem eq_top_iff' (A : Subsemiring R) : A = ⊤ ↔ forall x : R, x in A :=
eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

section NonAssocSemiring

variable (R)

/-- The center of a non-associative semiring `R` is the set of elements that commute and associate
with everything in `R` -/
@[simps coe toSubmonoid]
/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : Subsemiring R
  body: { NonUnitalSubsemiring.center R with
    one_mem' := Set.one_mem_center }

中文:
定义 center
  签名: : Subsemiring R
  定义体: { NonUnitalSubsemiring.center R with
    one_mem' := Set.one_mem_center }

Depends on / 依赖: NonUnitalSubsemiring, NonUnitalSubsemiring.center, Set.one_mem_center, center, one_mem, one_mem_center
-/
def center : Subsemiring R :=
  { NonUnitalSubsemiring.center R with
    one_mem' := Set.one_mem_center }

/--
Definition of `center.commSemiring'` / `center.commSemiring'` 的定义

English:
abbreviation center.commSemiring'
  signature: : CommSemiring (center R)
  body: { Submonoid.center.commMonoid', (center R).toNonAssocSemiring with }

中文:
缩写 center.commSemiring'
  签名: : CommSemiring (center R)
  定义体: { Submonoid.center.commMonoid', (center R).toNonAssocSemiring with }

Depends on / 依赖: Submonoid, Submonoid.center.commMonoid, center, commMonoid, toNonAssocSemiring
-/
abbrev center.commSemiring' : CommSemiring (center R) :=
  { Submonoid.center.commMonoid', (center R).toNonAssocSemiring with }

variable {R}

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

end NonAssocSemiring

section Semiring

/--
Instance `center.commSemiring` / 实例 `center.commSemiring`

English:
instance center.commSemiring
  signature: {R} [Semiring R]
  body: (center R).toSemiring
__ : CommMonoid (center R) := inferInstanceAs CommMonoid (Submonoid.center R)

中文:
实例 center.commSemiring
  签名: {R} [Semiring R]
  定义体: (center R).toSemiring
__ : CommMonoid (center R) := inferInstanceAs CommMonoid (Submonoid.center R)

Depends on / 依赖: center, toSemiring
-/
instance center.commSemiring {R} [Semiring R] : CommSemiring (center R) where
  __ := (center R).toSemiring
__ : CommMonoid (center R) := inferInstanceAs CommMonoid (Submonoid.center R)

-- no instance diamond, unlike the primed version
example {R} [Semiring R] :
    center.commSemiring.toSemiring = Subsemiring.toSemiring (center R) := by
  with_reducible_and_instances rfl

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {R} [Semiring R] {z : R}
  statement: z in center R ↔ forall g, g * z = z * g
  proof: Subsemigroup.mem_center_iff

中文:
定理 mem_center_iff
  条件: {R} [Semiring R] {z : R}
  结论: z in center R ↔ 对任意 g, g * z = z * g
  证明: Subsemigroup.mem_center_iff

Depends on / 依赖: Subsemigroup, Subsemigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {R} [Semiring R] {z : R} : z in center R ↔ forall g, g * z = z * g :=
  Subsemigroup.mem_center_iff

/--
Instance `decidableMemCenter` / 实例 `decidableMemCenter`

English:
instance decidableMemCenter
  signature: {R} [Semiring R] [DecidableEq R] [Fintype R]
  body: fun _ => decidable_of_iff' _ mem_center_iff

@[simp]

中文:
实例 decidableMemCenter
  签名: {R} [Semiring R] [DecidableEq R] [Fintype R]
  定义体: fun _ => decidable_of_iff' _ mem_center_iff

@[simp]

Depends on / 依赖: decidable_of_iff, mem_center_iff
-/
instance decidableMemCenter {R} [Semiring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· in center R) := fun _ => decidable_of_iff' _ mem_center_iff

@[simp]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  given: (R) [CommSemiring R]
  statement: center R = ⊤
  proof: SetLike.coe_injective (Set.center_eq_univ R)

中文:
定理 center_eq_top
  条件: (R) [CommSemiring R]
  结论: center R = ⊤
  证明: SetLike.coe_injective (Set.center_eq_univ R)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top (R) [CommSemiring R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

end Semiring

section Centralizer

/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: {R} [Semiring R] (s : Set R)
  body: { Submonoid.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]

中文:
定义 centralizer
  签名: {R} [Semiring R] (s : Set R)
  定义体: { Submonoid.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]

Depends on / 依赖: Set.add_mem_centralizer, Set.zero_mem_centralizer, Submonoid, Submonoid.centralizer, add_mem, add_mem_centralizer, carrier, centralizer, s.centralizer, zero_mem, zero_mem_centralizer
-/
def centralizer {R} [Semiring R] (s : Set R) : Subsemiring R :=
  { Submonoid.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  given: {R} [Semiring R] (s : Set R)
  statement: (centralizer s : Set R) = s.centralizer
  proof: rfl

中文:
定理 coe_centralizer
  条件: {R} [Semiring R] (s : Set R)
  结论: (centralizer s : Set R) = s.centralizer
  证明: rfl
-/
theorem coe_centralizer {R} [Semiring R] (s : Set R) : (centralizer s : Set R) = s.centralizer :=
  rfl

/--
theorem `centralizer_toSubmonoid` / 定理 `centralizer_toSubmonoid`

English:
theorem centralizer_toSubmonoid
  given: {R} [Semiring R] (s : Set R)
  proof: rfl

中文:
定理 centralizer_toSubmonoid
  条件: {R} [Semiring R] (s : Set R)
  证明: rfl
-/
theorem centralizer_toSubmonoid {R} [Semiring R] (s : Set R) :
    (centralizer s).toSubmonoid = Submonoid.centralizer s :=
  rfl

/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {R} [Semiring R] {s : Set R} {z : R}
  proof: Iff.rfl

中文:
定理 mem_centralizer_iff
  条件: {R} [Semiring R] {s : Set R} {z : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_centralizer_iff {R} [Semiring R] {s : Set R} {z : R} :
    z in centralizer s ↔ forall g in s, g * z = z * g :=
  Iff.rfl

/--
theorem `center_le_centralizer` / 定理 `center_le_centralizer`

English:
theorem center_le_centralizer
  given: {R} [Semiring R] (s)
  statement: center R <= centralizer s
  proof: s.center_subset_centralizer

中文:
定理 center_le_centralizer
  条件: {R} [Semiring R] (s)
  结论: center R <= centralizer s
  证明: s.center_subset_centralizer

Depends on / 依赖: center_subset_centralizer, s.center_subset_centralizer
-/
theorem center_le_centralizer {R} [Semiring R] (s) : center R <= centralizer s :=
  s.center_subset_centralizer

/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: {R} [Semiring R] (s t : Set R) (h : s subseteq t)
  statement: centralizer t <= centralizer s
  proof: Set.centralizer_subset h

@[simp]

中文:
定理 centralizer_le
  条件: {R} [Semiring R] (s t : Set R) (h : s subseteq t)
  结论: centralizer t <= centralizer s
  证明: Set.centralizer_subset h

@[simp]

Depends on / 依赖: Set.centralizer_subset, centralizer_subset
-/
theorem centralizer_le {R} [Semiring R] (s t : Set R) (h : s subseteq t) : centralizer t <= centralizer s :=
  Set.centralizer_subset h

@[simp]
/--
theorem `centralizer_eq_top_iff_subset` / 定理 `centralizer_eq_top_iff_subset`

English:
theorem centralizer_eq_top_iff_subset
  given: {R} [Semiring R] {s : Set R}
  proof: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]

中文:
定理 centralizer_eq_top_iff_subset
  条件: {R} [Semiring R] {s : Set R}
  证明: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]

Depends on / 依赖: Set.centralizer_eq_top_iff_subset, SetLike, SetLike.ext, _iff, _iff.trans, centralizer_eq_top_iff_subset
-/
theorem centralizer_eq_top_iff_subset {R} [Semiring R] {s : Set R} :
    centralizer s = ⊤ ↔ s subseteq center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  given: {R} [Semiring R]
  statement: centralizer Set.univ = center R
  proof: SetLike.ext' (Set.centralizer_univ R)

中文:
定理 centralizer_univ
  条件: {R} [Semiring R]
  结论: centralizer Set.univ = center R
  证明: SetLike.ext' (Set.centralizer_univ R)

Depends on / 依赖: Set.centralizer_univ, SetLike, SetLike.ext, centralizer_univ
-/
theorem centralizer_univ {R} [Semiring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

/--
lemma `le_centralizer_centralizer` / 引理 `le_centralizer_centralizer`

English:
lemma le_centralizer_centralizer
  given: {R} [Semiring R] {s : Subsemiring R}
  proof: Set.subset_centralizer_centralizer

@[simp]

中文:
引理 le_centralizer_centralizer
  条件: {R} [Semiring R] {s : Subsemiring R}
  证明: Set.subset_centralizer_centralizer

@[simp]

Depends on / 依赖: Set.subset_centralizer_centralizer, subset_centralizer_centralizer
-/
lemma le_centralizer_centralizer {R} [Semiring R] {s : Subsemiring R} :
    s <= centralizer (centralizer (s : Set R)) :=
  Set.subset_centralizer_centralizer

@[simp]
/--
lemma `centralizer_centralizer_centralizer` / 引理 `centralizer_centralizer_centralizer`

English:
lemma centralizer_centralizer_centralizer
  given: {R} [Semiring R] {s : Set R}
  proof: by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

中文:
引理 centralizer_centralizer_centralizer
  条件: {R} [Semiring R] {s : Set R}
  证明: by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

Depends on / 依赖: Set.centralizer_centralizer_centralizer, SetLike, SetLike.coe_injective, centralizer_centralizer_centralizer, coe_centralizer, coe_injective
-/
lemma centralizer_centralizer_centralizer {R} [Semiring R] {s : Set R} :
    centralizer s.centralizer.centralizer = centralizer s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

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
def closure (s : Set R) : Subsemiring R :=
  sInf { S | s subseteq S }

/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {x : R} {s : Set R}
  statement: x in closure s ↔ forall S : Subsemiring R, s subseteq S -> x in S
  proof: mem_sInf

中文:
定理 mem_closure
  条件: {x : R} {s : Set R}
  结论: x in closure s ↔ 对任意 S : Subsemiring R, s subseteq S -> x in S
  证明: mem_sInf

Depends on / 依赖: mem_sInf
-/
theorem mem_closure {x : R} {s : Set R} : x in closure s ↔ forall S : Subsemiring R, s subseteq S -> x in S :=
  mem_sInf

/-- The subsemiring generated by a set includes the set. -/
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

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
/--
theorem `closure_le` / 定理 `closure_le`

English:
theorem closure_le
  given: {s : Set R} {t : Subsemiring R}
  statement: closure s <= t ↔ s subseteq t
  proof: ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

中文:
定理 closure_le
  条件: {s : Set R} {t : Subsemiring R}
  结论: closure s <= t ↔ s subseteq t
  证明: ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

Depends on / 依赖: Set.Subset.trans, Subset, sInf_le, subset_closure
-/
theorem closure_le {s : Set R} {t : Subsemiring R} : closure s <= t ↔ s subseteq t :=
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
  given: {s : Set R} {t : Subsemiring R} (h₁ : s subseteq t) (h₂ : t <= closure s)
  proof: le_antisymm (closure_le.2 h₁) h₂

中文:
定理 closure_eq_of_le
  条件: {s : Set R} {t : Subsemiring R} (h₁ : s subseteq t) (h₂ : t <= closure s)
  证明: le_antisymm (closure_le.2 h₁) h₂

Depends on / 依赖: closure_le, le_antisymm
-/
theorem closure_eq_of_le {s : Set R} {t : Subsemiring R} (h₁ : s subseteq t) (h₂ : t <= closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {f : R ≃+* S} {K : Subsemiring R} {x : S}
  proof: by
  convert! @Set.mem_image_equiv _ _ (↑K) f.toEquiv x using 1

中文:
定理 mem_map_equiv
  条件: {f : R ≃+* S} {K : Subsemiring R} {x : S}
  证明: by
  convert! @Set.mem_image_equiv _ _ (↑K) f.toEquiv x using 1

Depends on / 依赖: Set.mem_image_equiv, convert, f.toEquiv, mem_image_equiv, toEquiv
-/
theorem mem_map_equiv {f : R ≃+* S} {K : Subsemiring R} {x : S} :
    x in K.map (f : R ->+* S) ↔ f.symm x in K := by
  convert! @Set.mem_image_equiv _ _ (↑K) f.toEquiv x using 1

/--
theorem `map_equiv_eq_comap_symm` / 定理 `map_equiv_eq_comap_symm`

English:
theorem map_equiv_eq_comap_symm
  given: (f : R ≃+* S) (K : Subsemiring R)
  proof: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

中文:
定理 map_equiv_eq_comap_symm
  条件: (f : R ≃+* S) (K : Subsemiring R)
  证明: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, isLocalHom_of_isIso, toEquiv
-/
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subsemiring R) :
    K.map (f : R ->+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

/--
theorem `comap_equiv_eq_map_symm` / 定理 `comap_equiv_eq_map_symm`

English:
theorem comap_equiv_eq_map_symm
  given: (f : R ≃+* S) (K : Subsemiring S)
  proof: (map_equiv_eq_comap_symm f.symm K).symm

中文:
定理 comap_equiv_eq_map_symm
  条件: (f : R ≃+* S) (K : Subsemiring S)
  证明: (map_equiv_eq_comap_symm f.symm K).symm

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subsemiring S) :
    K.comap (f : R ->+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subsemiring

namespace Submonoid

/--
Definition of `subsemiringClosure` / `subsemiringClosure` 的定义

English:
definition subsemiringClosure
  signature: (M : Submonoid R)
  body: { AddSubmonoid.closure (M : Set R) with
    one_mem' := AddSubmonoid.mem_closure.mpr fun _ hy => hy M.one_mem
    mul_mem' := MulMemClass.mul_mem_add_closure }

中文:
定义 subsemiringClosure
  签名: (M : Submonoid R)
  定义体: { AddSubmonoid.closure (M : Set R) with
    one_mem' := AddSubmonoid.mem_closure.mpr fun _ hy => hy M.one_mem
    mul_mem' := MulMemClass.mul_mem_add_closure }

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure, AddSubmonoid.mem_closure.mpr, M.one_mem, MulMemClass, MulMemClass.mul_mem_add_closure, closure, mem_closure, mul_mem, mul_mem_add_closure, one_mem
-/
def subsemiringClosure (M : Submonoid R) : Subsemiring R :=
  { AddSubmonoid.closure (M : Set R) with
    one_mem' := AddSubmonoid.mem_closure.mpr fun _ hy => hy M.one_mem
    mul_mem' := MulMemClass.mul_mem_add_closure }

/--
theorem `subsemiringClosure_coe` / 定理 `subsemiringClosure_coe`

English:
theorem subsemiringClosure_coe
  proof: rfl

中文:
定理 subsemiringClosure_coe
  证明: rfl
-/
theorem subsemiringClosure_coe :
    (M.subsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl

/--
theorem `subsemiringClosure_mem` / 定理 `subsemiringClosure_mem`

English:
theorem subsemiringClosure_mem
  given: {x : R}
  proof: Iff.rfl

中文:
定理 subsemiringClosure_mem
  条件: {x : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem subsemiringClosure_mem {x : R} :
    x in M.subsemiringClosure ↔ x in AddSubmonoid.closure (M : Set R) :=
  Iff.rfl

/--
theorem `subsemiringClosure_toAddSubmonoid` / 定理 `subsemiringClosure_toAddSubmonoid`

English:
theorem subsemiringClosure_toAddSubmonoid
  proof: rfl

中文:
定理 subsemiringClosure_toAddSubmonoid
  证明: rfl
-/
theorem subsemiringClosure_toAddSubmonoid :
    M.subsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl

/--
lemma `subsemiringClosure_toNonUnitalSubsemiring` / 引理 `subsemiringClosure_toNonUnitalSubsemiring`

English:
lemma subsemiringClosure_toNonUnitalSubsemiring
  given: (M : Submonoid R)
  proof: by
  refine Eq.symm (NonUnitalSubsemiring.closure_eq_of_le ?_ fun _ hx => ?_)
  · simp [Submonoid.subsemiringClosure_coe]
  · simp only [Subsemiring.mem_toNonUnitalSubsemiring, subsemiringClosure_mem] at hx
    induction hx using AddSubmonoid.closure_induction <;> aesop

中文:
引理 subsemiringClosure_toNonUnitalSubsemiring
  条件: (M : Submonoid R)
  证明: by
  refine Eq.symm (NonUnitalSubsemiring.closure_eq_of_le ?_ fun _ hx => ?_)
  · simp [Submonoid.subsemiringClosure_coe]
  · simp only [Subsemiring.mem_toNonUnitalSubsemiring, subsemiringClosure_mem] at hx
    induction hx using AddSubmonoid.closure_induction <;> aesop
-/
@[simp] lemma subsemiringClosure_toNonUnitalSubsemiring (M : Submonoid R) :
    M.subsemiringClosure.toNonUnitalSubsemiring = .closure M := by
  refine Eq.symm (NonUnitalSubsemiring.closure_eq_of_le ?_ fun _ hx => ?_)
  · simp [Submonoid.subsemiringClosure_coe]
  · simp only [Subsemiring.mem_toNonUnitalSubsemiring, subsemiringClosure_mem] at hx
    induction hx using AddSubmonoid.closure_induction <;> aesop

/--
theorem `subsemiringClosure_eq_closure` / 定理 `subsemiringClosure_eq_closure`

English:
theorem subsemiringClosure_eq_closure
  statement: M.subsemiringClosure = Subsemiring.closure (M : Set R)
  proof: by
  ext
  refine
    ⟨fun hx => ?_, fun hx =>
      (Subsemiring.mem_closure.mp hx) M.subsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

中文:
定理 subsemiringClosure_eq_closure
  结论: M.subsemiringClosure = Subsemiring.closure (M : Set R)
  证明: by
  ext
  refine
    ⟨fun hx => ?_, fun hx =>
      (Subsemiring.mem_closure.mp hx) M.subsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_closure.mp, H1.toAddSubmonoid, M.subsemiringClosure, Subsemiring, Subsemiring.mem_closure.mp, mem_closure, subsemiringClosure, toAddSubmonoid
-/
theorem subsemiringClosure_eq_closure : M.subsemiringClosure = Subsemiring.closure (M : Set R) := by
  ext
  refine
    ⟨fun hx => ?_, fun hx =>
      (Subsemiring.mem_closure.mp hx) M.subsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

end Submonoid

namespace Subsemiring

@[simp]
/--
theorem `closure_submonoid_closure` / 定理 `closure_submonoid_closure`

English:
theorem closure_submonoid_closure
  given: (s : Set R)
  statement: closure ↑(Submonoid.closure s) = closure s
  proof: le_antisymm
    (closure_le.mpr fun _ hy =>
      (Submonoid.mem_closure.mp hy) (closure s).toSubmonoid subset_closure)
    (closure_mono Submonoid.subset_closure)

中文:
定理 closure_submonoid_closure
  条件: (s : Set R)
  结论: closure ↑(Submonoid.closure s) = closure s
  证明: le_antisymm
    (closure_le.mpr fun _ hy =>
      (Submonoid.mem_closure.mp hy) (closure s).toSubmonoid subset_closure)
    (closure_mono Submonoid.subset_closure)

Depends on / 依赖: Submonoid, Submonoid.mem_closure.mp, Submonoid.subset_closure, closure, closure_le, closure_le.mpr, closure_mono, le_antisymm, mem_closure, subset_closure, toSubmonoid
-/
theorem closure_submonoid_closure (s : Set R) : closure ↑(Submonoid.closure s) = closure s :=
  le_antisymm
    (closure_le.mpr fun _ hy =>
      (Submonoid.mem_closure.mp hy) (closure s).toSubmonoid subset_closure)
    (closure_mono Submonoid.subset_closure)

/--
theorem `coe_closure_eq` / 定理 `coe_closure_eq`

English:
theorem coe_closure_eq
  given: (s : Set R)
  proof: by
  simp [← Submonoid.subsemiringClosure_toAddSubmonoid, Submonoid.subsemiringClosure_eq_closure]

中文:
定理 coe_closure_eq
  条件: (s : Set R)
  证明: by
  simp [← Submonoid.subsemiringClosure_toAddSubmonoid, Submonoid.subsemiringClosure_eq_closure]

Depends on / 依赖: Submonoid, Submonoid.subsemiringClosure_eq_closure, Submonoid.subsemiringClosure_toAddSubmonoid, subsemiringClosure_eq_closure, subsemiringClosure_toAddSubmonoid
-/
theorem coe_closure_eq (s : Set R) :
    (closure s : Set R) = AddSubmonoid.closure (Submonoid.closure s : Set R) := by
  simp [← Submonoid.subsemiringClosure_toAddSubmonoid, Submonoid.subsemiringClosure_eq_closure]

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
    x in closure s ↔ x in AddSubmonoid.closure (Submonoid.closure s : Set R) :=
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
  refine (Submonoid.mem_closure.mp hy) H.toSubmonoid fun z hz => ?_
  exact

中文:
定理 closure_addSubmonoid_closure
  条件: {s : Set R}
  证明: by
  ext x
  refine ⟨fun hx => ?_, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => ?_
  refine (Submonoid.mem_closure.mp hy) H.toSubmonoid fun z hz => ?_
  exact

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_closure.mp, AddSubmonoid.subset_closure, H.toAddSubmonoid, H.toSubmonoid, Submonoid, Submonoid.mem_closure.mp, closure_mono, mem_closure, mem_closure_iff, mem_closure_iff.mp, subset_closure, toAddSubmonoid, toSubmonoid
-/
theorem closure_addSubmonoid_closure {s : Set R} :
    closure ↑(AddSubmonoid.closure s) = closure s := by
  ext x
  refine ⟨fun hx => ?_, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => ?_
  refine (Submonoid.mem_closure.mp hy) H.toSubmonoid fun z hz => ?_
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
  proof: let K : Subsemiring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      one_mem' := ⟨_, one⟩
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨s

中文:
定理 closure_induction
  结论: {s : Set R} {p : (x : R) -> x in closure s -> 命题}
  证明: let K : Subsemiring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      one_mem' := ⟨_, one⟩
      zero_mem' := ⟨_, zero⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨s

Depends on / 依赖: Subsemiring, add_mem, carrier, closure_le, mul_mem, one_mem, subset_closure, zero_mem
-/
theorem closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop}
    (mem : forall (x) (hx : x in s), p x (subset_closure hx))
    (zero : p 0 (zero_mem _)) (one : p 1 (one_mem _))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    {x} (hx : x in closure s) : p x hx :=
  let K : Subsemiring R :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      one_mem' := ⟨_, one⟩
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
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | one => exact one_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => ex

中文:
定理 closure_induction₂
  结论: {s : Set R} {p : (x y : R) -> x in closure s -> y in closure s -> 命题}
  证明: by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | one => exact one_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => ex

Depends on / 依赖: add_left, add_right, closure_induction, mem_mem, mul_left, mul_right, one_left, one_right, zero_left, zero_right
-/
theorem closure_induction₂ {s : Set R} {p : (x y : R) -> x in closure s -> y in closure s -> Prop}
    (mem_mem : forall (x) (y) (hx : x in s) (hy : y in s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : forall x hx, p 0 x (zero_mem _) hx) (zero_right : forall x hx, p x 0 hx (zero_mem _))
    (one_left : forall x hx, p 1 x (one_mem _) hx) (one_right : forall x hx, p x 1 hx (one_mem _))
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
  | zero => exact zero_right x hx
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

/--
theorem `mem_closure_iff_exists_list` / 定理 `mem_closure_iff_exists_list`

English:
theorem mem_closure_iff_exists_list
  given: {R} [Semiring R] {s : Set R} {x}
  proof: by
  constructor
  · intro hx
    rw [mem_closure_iff] at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      suffices exists t : List R, (forall y in t, y in s) ∧ t.prod = x from
        let ⟨t, ht1, ht2⟩ := this
        ⟨[t], List.forall_mem_singleton.2 ht1, by
  

中文:
定理 mem_closure_iff_exists_list
  条件: {R} [Semiring R] {s : Set R} {x}
  证明: by
  constructor
  · intro hx
    rw [mem_closure_iff] at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      suffices exists t : List R, (forall y in t, y in s) ∧ t.prod = x from
        let ⟨t, ht1, ht2⟩ := this
        ⟨[t], List.forall_mem_singleton.2 ht1, by
  

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_induction, List.forall_mem_nil, List.forall_mem_singleton, List.map_singleton, List.prod_singleton, List.sum_singleton, Submonoid, Submonoid.closure_induction, closure_induction, forall_mem_nil, forall_mem_singleton, map_singleton, mem_closure_iff, prod_singleton, sum_singleton, t.prod
-/
theorem mem_closure_iff_exists_list {R} [Semiring R] {s : Set R} {x} :
    x in closure s ↔ exists L : List (List R), (forall t in L, forall y in t, y in s) ∧ (L.map List.prod).sum = x := by
  constructor
  · intro hx
    rw [mem_closure_iff] at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      suffices exists t : List R, (forall y in t, y in s) ∧ t.prod = x from
        let ⟨t, ht1, ht2⟩ := this
        ⟨[t], List.forall_mem_singleton.2 ht1, by
          rw [List.map_singleton]; rw [List.sum_singleton]; rw [ht2]⟩
      induction hx using Submonoid.closure_induction with
      | mem x hx => exact ⟨[x], List.forall_mem_singleton.2 hx, List.prod_singleton⟩
      | one => exact ⟨[], List.forall_mem_nil _, rfl⟩
      | mul x y _ _ ht hu =>
        obtain ⟨⟨t, ht1, ht2⟩, ⟨u, hu1, hu2⟩⟩ := And.intro ht hu
        exact ⟨t ++ u, List.forall_mem_append.2 ⟨ht1, hu1⟩, by rw [List.prod_append, ht2, hu2]⟩
    | zero => exact ⟨[], List.forall_mem_nil _, rfl⟩
    | add x y _ _ hL hM =>
      obtain ⟨⟨L, HL1, HL2⟩, ⟨M, HM1, HM2⟩⟩ := And.intro hL hM
      exact ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
        rw [List.map_append]; rw [List.sum_append]; rw [HL2]; rw [HM2]⟩
  · rintro ⟨L, HL1, rfl⟩
    exact
      list_sum_mem fun r hr =>
        let ⟨t, ht1, ht2⟩ := List.mem_map.1 hr
ht2 ▸ list_prod_mem _ fun y hy => subset_closure HL1 t ht1 y hy

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

/-- Closure of a subsemiring `S` equals `S`. -/
@[simp]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  given: (s : Subsemiring R)
  statement: closure (s : Set R) = s
  proof: (Subsemiring.gi R).l_u_eq s

@[simp]

中文:
定理 closure_eq
  条件: (s : Subsemiring R)
  结论: closure (s : Set R) = s
  证明: (Subsemiring.gi R).l_u_eq s

@[simp]

Depends on / 依赖: Subsemiring, Subsemiring.gi, l_u_eq
-/
theorem closure_eq (s : Subsemiring R) : closure (s : Set R) = s :=
  (Subsemiring.gi R).l_u_eq s

@[simp]
/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure (∅ : Set R) = ⊥
  proof: (Subsemiring.gi R).gc.l_bot

@[simp]

中文:
定理 closure_empty
  结论: closure (∅ : Set R) = ⊥
  证明: (Subsemiring.gi R).gc.l_bot

@[simp]

Depends on / 依赖: Subsemiring, Subsemiring.gi, gc.l_bot, l_bot
-/
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subsemiring.gi R).gc.l_bot

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
  proof: (Subsemiring.gi R).gc.l_sup

中文:
定理 closure_union
  条件: (s t : Set R)
  结论: closure (s union t) = closure s ⊔ closure t
  证明: (Subsemiring.gi R).gc.l_sup

Depends on / 依赖: Subsemiring, Subsemiring.gi, gc.l_sup, l_sup
-/
theorem closure_union (s t : Set R) : closure (s union t) = closure s ⊔ closure t :=
  (Subsemiring.gi R).gc.l_sup

/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: {ι} (s : ι -> Set R)
  statement: closure (⋃ i, s i) = ⨆ i, closure (s i)
  proof: (Subsemiring.gi R).gc.l_iSup

中文:
定理 closure_iUnion
  条件: {ι} (s : ι -> Set R)
  结论: closure (⋃ i, s i) = ⨆ i, closure (s i)
  证明: (Subsemiring.gi R).gc.l_iSup

Depends on / 依赖: Subsemiring, Subsemiring.gi, gc.l_iSup, l_iSup
-/
theorem closure_iUnion {ι} (s : ι -> Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemiring.gi R).gc.l_iSup

/--
theorem `closure_sUnion` / 定理 `closure_sUnion`

English:
theorem closure_sUnion
  given: (s : Set (Set R))
  statement: closure (⋃₀ s) = ⨆ t in s, closure t
  proof: (Subsemiring.gi R).gc.l_sSup

@[simp]

中文:
定理 closure_sUnion
  条件: (s : Set (Set R))
  结论: closure (⋃₀ s) = ⨆ t in s, closure t
  证明: (Subsemiring.gi R).gc.l_sSup

@[simp]

Depends on / 依赖: Subsemiring, Subsemiring.gi, gc.l_sSup, l_sSup
-/
theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t in s, closure t :=
  (Subsemiring.gi R).gc.l_sSup

@[simp]
/--
theorem `closure_singleton_natCast` / 定理 `closure_singleton_natCast`

English:
theorem closure_singleton_natCast
  given: (n : Nat)
  statement: closure {(n : R)} = ⊥
  proof: bot_unique closure_le.2 Set.singleton_subset_iff.mpr natCast_mem _ _

@[simp]

中文:
定理 closure_singleton_natCast
  条件: (n : 自然数)
  结论: closure {(n : R)} = ⊥
  证明: bot_unique closure_le.2 Set.singleton_subset_iff.mpr natCast_mem _ _

@[simp]

Depends on / 依赖: Set.singleton_subset_iff.mpr, bot_unique, closure_le, natCast_mem, singleton_subset_iff
-/
theorem closure_singleton_natCast (n : Nat) : closure {(n : R)} = ⊥ :=
bot_unique closure_le.2 Set.singleton_subset_iff.mpr natCast_mem _ _

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
theorem `closure_insert_natCast` / 定理 `closure_insert_natCast`

English:
theorem closure_insert_natCast
  given: (n : Nat) (s : Set R)
  statement: closure (insert (n : R) s) = closure s
  proof: by
  rw [Set.insert_eq]; rw [closure_union]
  simp

@[simp]

中文:
定理 closure_insert_natCast
  条件: (n : 自然数) (s : Set R)
  结论: closure (insert (n : R) s) = closure s
  证明: by
  rw [Set.insert_eq]; rw [closure_union]
  simp

@[simp]

Depends on / 依赖: Set.insert_eq, closure_union, insert_eq
-/
theorem closure_insert_natCast (n : Nat) (s : Set R) : closure (insert (n : R) s) = closure s := by
  rw [Set.insert_eq]; rw [closure_union]
  simp

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
  条件: (s : Set R)
  结论: closure (insert 0 s) = closure s
  证明: mod_cast closure_insert_natCast 0 s

@[simp]

Depends on / 依赖: closure_insert_natCast, mod_cast
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
  条件: (s : Set R)
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
  given: (s t : Subsemiring R) (f : R ->+* S)
  statement: (s ⊔ t).map f = s.map f ⊔ t.map f
  proof: (gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (s t : Subsemiring R) (f : R ->+* S)
  结论: (s ⊔ t).map f = s.map f ⊔ t.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (s t : Subsemiring R) (f : R ->+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : R ->+* S) (s : ι -> Subsemiring R)
  proof: (gc_map_comap f).l_iSup

中文:
定理 map_iSup
  条件: {ι : Sort*} (f : R ->+* S) (s : ι -> Subsemiring R)
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : R ->+* S) (s : ι -> Subsemiring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (s t : Subsemiring R) (f : R ->+* S) (hf : Function.Injective f)
  proof: SetLike.coe_injective (Set.image_inter hf)

中文:
定理 map_inf
  条件: (s t : Subsemiring R) (f : R ->+* S) (hf : Function.Injective f)
  证明: SetLike.coe_injective (Set.image_inter hf)

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (s t : Subsemiring R) (f : R ->+* S) (hf : Function.Injective f) :
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
  结论: {ι : Sort*} [Nonempty ι] (f : R ->+* S) (hf : Function.Injective f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : R ->+* S) (hf : Function.Injective f)
    (s : ι -> Subsemiring R) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (s t : Subsemiring S) (f : R ->+* S)
  statement: (s ⊓ t).comap f = s.comap f ⊓ t.comap f
  proof: (gc_map_comap f).u_inf

中文:
定理 comap_inf
  条件: (s t : Subsemiring S) (f : R ->+* S)
  结论: (s ⊓ t).comap f = s.comap f ⊓ t.comap f
  证明: (gc_map_comap f).u_inf

Depends on / 依赖: gc_map_comap, u_inf
-/
theorem comap_inf (s t : Subsemiring S) (f : R ->+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : R ->+* S) (s : ι -> Subsemiring S)
  proof: (gc_map_comap f).u_iInf

@[simp]

中文:
定理 comap_iInf
  条件: {ι : Sort*} (f : R ->+* S) (s : ι -> Subsemiring S)
  证明: (gc_map_comap f).u_iInf

@[simp]

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : R ->+* S) (s : ι -> Subsemiring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : R ->+* S)
  statement: (⊥ : Subsemiring R).map f = ⊥
  proof: (gc_map_comap f).l_bot

@[simp]

中文:
定理 map_bot
  条件: (f : R ->+* S)
  结论: (⊥ : Subsemiring R).map f = ⊥
  证明: (gc_map_comap f).l_bot

@[simp]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : R ->+* S) : (⊥ : Subsemiring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : R ->+* S)
  statement: (⊤ : Subsemiring S).comap f = ⊤
  proof: (gc_map_comap f).u_top

中文:
定理 comap_top
  条件: (f : R ->+* S)
  结论: (⊤ : Subsemiring S).comap f = ⊤
  证明: (gc_map_comap f).u_top

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top (f : R ->+* S) : (⊤ : Subsemiring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (s : Subsemiring R) (t : Subsemiring S)
  body: { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := s ×ˢ t }

@[norm_cast]

中文:
定义 prod
  签名: (s : Subsemiring R) (t : Subsemiring S)
  定义体: { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := s ×ˢ t }

@[norm_cast]

Depends on / 依赖: carrier, s.toAddSubmonoid.prod, s.toSubmonoid.prod, t.toAddSubmonoid, t.toSubmonoid, toAddSubmonoid, toSubmonoid
-/
def prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := s ×ˢ t }

@[norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : Subsemiring R) (t : Subsemiring S)
  proof: rfl

中文:
定理 coe_prod
  条件: (s : Subsemiring R) (t : Subsemiring S)
  证明: rfl
-/
theorem coe_prod (s : Subsemiring R) (t : Subsemiring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl

/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : Subsemiring R} {t : Subsemiring S} {p : R × S}
  proof: Iff.rfl

@[gcongr, mono]

中文:
定理 mem_prod
  条件: {s : Subsemiring R} {t : Subsemiring S} {p : R × S}
  证明: Iff.rfl

@[gcongr, mono]

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : Subsemiring R} {t : Subsemiring S} {p : R × S} :
    p in s.prod t ↔ p.1 in s ∧ p.2 in t :=
  Iff.rfl

@[gcongr, mono]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: ⦃s₁ s₂
  statement: Subsemiring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ <= t₂) :
  proof: Set.prod_mono hs ht

中文:
定理 prod_mono
  条件: ⦃s₁ s₂
  结论: Subsemiring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ <= t₂) :
  证明: Set.prod_mono hs ht

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ <= t₂) :
    s₁.prod t₁ <= s₂.prod t₂ :=
  Set.prod_mono hs ht

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  given: (s : Subsemiring R)
  statement: Monotone fun t : Subsemiring S => s.prod t
  proof: prod_mono (le_refl s)

中文:
定理 prod_mono_right
  条件: (s : Subsemiring R)
  结论: Monotone fun t : Subsemiring S => s.prod t
  证明: prod_mono (le_refl s)

Depends on / 依赖: le_refl, prod_mono
-/
theorem prod_mono_right (s : Subsemiring R) : Monotone fun t : Subsemiring S => s.prod t :=
  prod_mono (le_refl s)

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  given: (t : Subsemiring S)
  statement: Monotone fun s : Subsemiring R => s.prod t
  proof: fun _ _ hs => prod_mono hs (le_refl t)

中文:
定理 prod_mono_left
  条件: (t : Subsemiring S)
  结论: Monotone fun s : Subsemiring R => s.prod t
  证明: fun _ _ hs => prod_mono hs (le_refl t)

Depends on / 依赖: le_refl, prod_mono
-/
theorem prod_mono_left (t : Subsemiring S) : Monotone fun s : Subsemiring R => s.prod t :=
  fun _ _ hs => prod_mono hs (le_refl t)

/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  given: (s : Subsemiring R)
  statement: s.prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S)
  proof: ext fun x => by simp [mem_prod]

中文:
定理 prod_top
  条件: (s : Subsemiring R)
  结论: s.prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S)
  证明: ext fun x => by simp [mem_prod]

Depends on / 依赖: mem_prod
-/
theorem prod_top (s : Subsemiring R) : s.prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by simp [mem_prod]

/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  given: (s : Subsemiring S)
  statement: (⊤ : Subsemiring R).prod s = s.comap (RingHom.snd R S)
  proof: ext fun x => by simp [mem_prod]

@[simp]

中文:
定理 top_prod
  条件: (s : Subsemiring S)
  结论: (⊤ : Subsemiring R).prod s = s.comap (RingHom.snd R S)
  证明: ext fun x => by simp [mem_prod]

@[simp]

Depends on / 依赖: mem_prod
-/
theorem top_prod (s : Subsemiring S) : (⊤ : Subsemiring R).prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
/--
theorem `top_prod_top` / 定理 `top_prod_top`

English:
theorem top_prod_top
  statement: (⊤ : Subsemiring R).prod (⊤ : Subsemiring S) = ⊤
  proof: (top_prod _).trans comap_top _

@[simp]

中文:
定理 top_prod_top
  结论: (⊤ : Subsemiring R).prod (⊤ : Subsemiring S) = ⊤
  证明: (top_prod _).trans comap_top _

@[simp]

Depends on / 依赖: comap_top, top_prod
-/
theorem top_prod_top : (⊤ : Subsemiring R).prod (⊤ : Subsemiring S) = ⊤ :=
(top_prod _).trans comap_top _

@[simp]
/--
theorem `_root_.RingHom.rangeS_prodMap` / 定理 `_root_.RingHom.rangeS_prodMap`

English:
theorem _root_.RingHom.rangeS_prodMap
  given: (f : R ->+* S) (g : S ->+* T)
  proof: SetLike.coe_injective Set.range_prodMap

中文:
定理 _root_.RingHom.rangeS_prodMap
  条件: (f : R ->+* S) (g : S ->+* T)
  证明: SetLike.coe_injective Set.range_prodMap

Depends on / 依赖: Set.range_prodMap, SetLike, SetLike.coe_injective, coe_injective, range_prodMap
-/
theorem _root_.RingHom.rangeS_prodMap (f : R ->+* S) (g : S ->+* T) :
    (f.prodMap g).rangeS = Subsemiring.prod f.rangeS g.rangeS :=
  SetLike.coe_injective Set.range_prodMap

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
  signature: (s : Subsemiring R) (t : Subsemiring S)
  body: { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 prodEquiv
  签名: (s : Subsemiring R) (t : Subsemiring S)
  定义体: { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: Equiv.Set.prod, map_add, map_mul
-/
def prodEquiv (s : Subsemiring R) (t : Subsemiring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/--
theorem `mem_iSup_of_directed` / 定理 `mem_iSup_of_directed`

English:
theorem mem_iSup_of_directed
  statement: {ι} [hι : Nonempty ι] {S : ι -> Subsemiring R} (hS : Directed (· <= ·) S)
  proof: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubmonoid) (Submonoid.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U] using 

中文:
定理 mem_iSup_of_directed
  结论: {ι} [hι : Nonempty ι] {S : ι -> Subsemiring R} (hS : Directed (· <= ·) S)
  证明: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubmonoid) (Submonoid.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U] using 

Depends on / 依赖: AddSubmonoid, AddSubmonoid.coe_iSup_of_directed, Set.mem_iUnion, Submonoid, Submonoid.coe_iSup_of_directed, Subsemiring, Subsemiring.mk, coe_iSup_of_directed, iSup_le, le_iSup, mem_iUnion, toAddSubmonoid, toSubmonoid
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subsemiring R} (hS : Directed (· <= ·) S)
    {x : R} : (x in ⨆ i, S i) ↔ exists i, x in S i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubmonoid) (Submonoid.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i <= U by simpa [U] using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  statement: {ι} [hι : Nonempty ι] {S : ι -> Subsemiring R}
  proof: Set.ext fun x => by simp [mem_iSup_of_directed hS]

中文:
定理 coe_iSup_of_directed
  结论: {ι} [hι : Nonempty ι] {S : ι -> Subsemiring R}
  证明: Set.ext fun x => by simp [mem_iSup_of_directed hS]

Depends on / 依赖: Set.ext, mem_iSup_of_directed
-/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subsemiring R}
    (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subsemiring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]

/--
theorem `mem_sSup_of_directedOn` / 定理 `mem_sSup_of_directedOn`

English:
theorem mem_sSup_of_directedOn
  statement: {S : Set (Subsemiring R)} (Sne : S.Nonempty)
  proof: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

中文:
定理 mem_sSup_of_directedOn
  结论: {S : Set (Subsemiring R)} (Sne : S.Nonempty)
  证明: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

Depends on / 依赖: Nonempty, SetCoe, SetCoe.exists, Sne.to_subtype, directed_val, exists_prop, hS.directed_val, mem_iSup_of_directed, sSup_eq_iSup, to_subtype
-/
theorem mem_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) {x : R} : x in sSup S ↔ exists s in S, x in s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

/--
theorem `coe_sSup_of_directedOn` / 定理 `coe_sSup_of_directedOn`

English:
theorem coe_sSup_of_directedOn
  statement: {S : Set (Subsemiring R)} (Sne : S.Nonempty)
  proof: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

中文:
定理 coe_sSup_of_directedOn
  结论: {S : Set (Subsemiring R)} (Sne : S.Nonempty)
  证明: Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

Depends on / 依赖: Set.ext, mem_sSup_of_directedOn
-/
theorem coe_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) : (↑(sSup S) : Set R) = ⋃ s in S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

/--
theorem `isMulCommutative_iSup` / 定理 `isMulCommutative_iSup`

English:
theorem isMulCommutative_iSup
  statement: {ι : Sort*} [Nonempty ι]
  proof: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using! Subsemigroup.isMulCommutative_iSup dir

中文:
定理 isMulCommutative_iSup
  结论: {ι : Sort*} [Nonempty ι]
  证明: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using! Subsemigroup.isMulCommutative_iSup dir

Depends on / 依赖: SetLike, SetLike.mem_coe, Subsemigroup, Subsemigroup.coe_iSup_of_directed, Subsemigroup.isMulCommutative_iSup, coe_iSup_of_directed, isMulCommutative_iSup, isMulCommutative_iff, mem_coe
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι]
    {S : ι -> Subsemiring R} [hS : forall i, IsMulCommutative (S i)]
    (dir : Directed (· <= ·) S) : IsMulCommutative (⨆ i, S i : Subsemiring R) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using! Subsemigroup.isMulCommutative_iSup dir

/--
Instance `instIsMulCommutative_iSup` / 实例 `instIsMulCommutative_iSup`

English:
instance instIsMulCommutative_iSup
  signature: {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
  body: isMulCommutative_iSup S.monotone.directed_le

中文:
实例 instIsMulCommutative_iSup
  签名: {ι : 类型} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
  定义体: isMulCommutative_iSup S.monotone.directed_le

Depends on / 依赖: S.monotone.directed_le, directed_le, isMulCommutative_iSup, monotone
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι ->o Subsemiring R} [hS : forall i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subsemiring R) :=
  isMulCommutative_iSup S.monotone.directed_le

end Subsemiring

namespace RingHom

variable {s : Subsemiring R}
variable {σR σS : Type*}
variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

open Subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
@[implicit_reducible]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : R ->+* S) (s : σS) (h : forall x, f x in s)
  body: { (f : R ->* S).codRestrict s h, (f : R ->+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }

@[simp]

中文:
定义 codRestrict
  签名: (f : R ->+* S) (s : σS) (h : 对任意 x, f x in s)
  定义体: { (f : R ->* S).codRestrict s h, (f : R ->+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }

@[simp]

Depends on / 依赖: codRestrict
-/
def codRestrict (f : R ->+* S) (s : σS) (h : forall x, f x in s) : R ->+* s :=
  { (f : R ->* S).codRestrict s h, (f : R ->+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }

@[simp]
/--
theorem `codRestrict_apply` / 定理 `codRestrict_apply`

English:
theorem codRestrict_apply
  given: (f : R ->+* S) (s : σS) (h : forall x, f x in s) (x : R)
  proof: rfl

中文:
定理 codRestrict_apply
  条件: (f : R ->+* S) (s : σS) (h : 对任意 x, f x in s) (x : R)
  证明: rfl
-/
theorem codRestrict_apply (f : R ->+* S) (s : σS) (h : forall x, f x in s) (x : R) :
    (f.codRestrict s h x : S) = f x :=
  rfl

/--
theorem `injective_codRestrict` / 定理 `injective_codRestrict`

English:
theorem injective_codRestrict
  given: {f : R ->+* S} {s : σS} {h : forall x, f x in s}
  proof: Set.injective_codRestrict h

中文:
定理 injective_codRestrict
  条件: {f : R ->+* S} {s : σS} {h : 对任意 x, f x in s}
  证明: Set.injective_codRestrict h

Depends on / 依赖: Set.injective_codRestrict, injective_codRestrict
-/
theorem injective_codRestrict {f : R ->+* S} {s : σS} {h : forall x, f x in s} :
    Function.Injective (f.codRestrict s h) ↔ Function.Injective f :=
  Set.injective_codRestrict h

/--
theorem `rangeS_codRestrict` / 定理 `rangeS_codRestrict`

English:
theorem rangeS_codRestrict
  given: {f : R ->+* S} {s : σS} {h : forall x, f x in s}
  proof: SetLike.coe_injective Set.range_codRestrict h

中文:
定理 rangeS_codRestrict
  条件: {f : R ->+* S} {s : σS} {h : 对任意 x, f x in s}
  证明: SetLike.coe_injective Set.range_codRestrict h

Depends on / 依赖: Set.range_codRestrict, SetLike, SetLike.coe_injective, coe_injective, range_codRestrict
-/
theorem rangeS_codRestrict {f : R ->+* S} {s : σS} {h : forall x, f x in s} :
    rangeS (codRestrict f s h) = Subsemiring.comap (SubsemiringClass.subtype s) f.rangeS :=
SetLike.coe_injective Set.range_codRestrict h

/--
theorem `surjective_codRestrict` / 定理 `surjective_codRestrict`

English:
theorem surjective_codRestrict
  given: {f : R ->+* S} {s : σS} {h : forall x, f x in s}
  proof: (Set.surjective_codRestrict h).trans .symm SetLike.coe_set_eq.symm

中文:
定理 surjective_codRestrict
  条件: {f : R ->+* S} {s : σS} {h : 对任意 x, f x in s}
  证明: (Set.surjective_codRestrict h).trans .symm SetLike.coe_set_eq.symm

Depends on / 依赖: Set.surjective_codRestrict, SetLike, SetLike.coe_set_eq.symm, coe_set_eq, surjective_codRestrict
-/
theorem surjective_codRestrict {f : R ->+* S} {s : σS} {h : forall x, f x in s} :
    Function.Surjective (codRestrict f s h) ↔ f.rangeS = ofClass s :=
(Set.surjective_codRestrict h).trans .symm SetLike.coe_set_eq.symm

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', f x in s)
  body: (f.domRestrict s').codRestrict s fun x => h x x.2

@[simp]

中文:
定义 restrict
  签名: (f : R ->+* S) (s' : σR) (s : σS) (h : 对任意 x in s', f x in s)
  定义体: (f.domRestrict s').codRestrict s fun x => h x x.2

@[simp]

Depends on / 依赖: codRestrict, domRestrict, f.domRestrict
-/
def restrict (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', f x in s) : s' ->+* s :=
  (f.domRestrict s').codRestrict s fun x => h x x.2

@[simp]
/--
theorem `coe_restrict_apply` / 定理 `coe_restrict_apply`

English:
theorem coe_restrict_apply
  given: (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', f x in s) (x : s')
  proof: rfl

@[simp]

中文:
定理 coe_restrict_apply
  条件: (f : R ->+* S) (s' : σR) (s : σS) (h : 对任意 x in s', f x in s) (x : s')
  证明: rfl

@[simp]
-/
theorem coe_restrict_apply (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', f x in s) (x : s') :
    (f.restrict s' s h x : S) = f x :=
  rfl

@[simp]
/--
theorem `comp_restrict` / 定理 `comp_restrict`

English:
theorem comp_restrict
  given: (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', f x in s)
  proof: rfl

@[simp]

中文:
定理 comp_restrict
  条件: (f : R ->+* S) (s' : σR) (s : σS) (h : 对任意 x in s', f x in s)
  证明: rfl

@[simp]
-/
theorem comp_restrict (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', f x in s) :
    (SubsemiringClass.subtype s).comp (f.restrict s' s h) = f.comp (SubsemiringClass.subtype s') :=
  rfl

@[simp]
/--
theorem `domRestrict_comp_codRestrict` / 定理 `domRestrict_comp_codRestrict`

English:
theorem domRestrict_comp_codRestrict
  statement: (g : S ->+* T) (f : R ->+* S) (p : Subsemiring S)
  proof: rfl

中文:
定理 domRestrict_comp_codRestrict
  结论: (g : S ->+* T) (f : R ->+* S) (p : Subsemiring S)
  证明: rfl
-/
theorem domRestrict_comp_codRestrict (g : S ->+* T) (f : R ->+* S) (p : Subsemiring S)
    (h : forall c, f c in p) :
    (g.domRestrict p).comp (f.codRestrict p h) = g.comp f :=
  rfl

/--
Definition of `rangeSRestrict` / `rangeSRestrict` 的定义

English:
definition rangeSRestrict
  signature: (f : R ->+* S)
  body: f.codRestrict (R := R) (S := S) (σS := Subsemiring S) f.rangeS f.mem_rangeS_self

@[simp]

中文:
定义 rangeSRestrict
  签名: (f : R ->+* S)
  定义体: f.codRestrict (R := R) (S := S) (σS := Subsemiring S) f.rangeS f.mem_rangeS_self

@[simp]

Depends on / 依赖: Subsemiring, codRestrict, f.codRestrict, f.mem_rangeS_self, f.rangeS, mem_rangeS_self, rangeS
-/
def rangeSRestrict (f : R ->+* S) : R ->+* f.rangeS :=
  f.codRestrict (R := R) (S := S) (σS := Subsemiring S) f.rangeS f.mem_rangeS_self

@[simp]
/--
theorem `coe_rangeSRestrict` / 定理 `coe_rangeSRestrict`

English:
theorem coe_rangeSRestrict
  given: (f : R ->+* S) (x : R)
  statement: (f.rangeSRestrict x : S) = f x
  proof: rfl

中文:
定理 coe_rangeSRestrict
  条件: (f : R ->+* S) (x : R)
  结论: (f.rangeSRestrict x : S) = f x
  证明: rfl
-/
theorem coe_rangeSRestrict (f : R ->+* S) (x : R) : (f.rangeSRestrict x : S) = f x :=
  rfl

/--
theorem `rangeSRestrict_surjective` / 定理 `rangeSRestrict_surjective`

English:
theorem rangeSRestrict_surjective
  given: (f : R ->+* S)
  statement: Function.Surjective f.rangeSRestrict
  proof: fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_rangeS.mp hy
  ⟨x, Subtype.ext hx⟩

中文:
定理 rangeSRestrict_surjective
  条件: (f : R ->+* S)
  结论: Function.Surjective f.rangeSRestrict
  证明: fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_rangeS.mp hy
  ⟨x, Subtype.ext hx⟩

Depends on / 依赖: Subtype, Subtype.ext, mem_rangeS, mem_rangeS.mp
-/
theorem rangeSRestrict_surjective (f : R ->+* S) : Function.Surjective f.rangeSRestrict :=
  fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_rangeS.mp hy
  ⟨x, Subtype.ext hx⟩

/--
theorem `rangeS_top_iff_surjective` / 定理 `rangeS_top_iff_surjective`

English:
theorem rangeS_top_iff_surjective
  given: {f : R ->+* S}
  proof: SetLike.ext'_iff.trans Iff.trans (by rw [coe_rangeS, coe_top]) Set.range_eq_univ

中文:
定理 rangeS_top_iff_surjective
  条件: {f : R ->+* S}
  证明: SetLike.ext'_iff.trans Iff.trans (by rw [coe_rangeS, coe_top]) Set.range_eq_univ

Depends on / 依赖: Iff.trans, Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, coe_rangeS, coe_top, range_eq_univ
-/
theorem rangeS_top_iff_surjective {f : R ->+* S} :
    f.rangeS = (⊤ : Subsemiring S) ↔ Function.Surjective f :=
SetLike.ext'_iff.trans Iff.trans (by rw [coe_rangeS, coe_top]) Set.range_eq_univ

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
/--
theorem `rangeS_top_of_surjective` / 定理 `rangeS_top_of_surjective`

English:
theorem rangeS_top_of_surjective
  given: (f : R ->+* S) (hf : Function.Surjective f)
  proof: rangeS_top_iff_surjective.2 hf

中文:
定理 rangeS_top_of_surjective
  条件: (f : R ->+* S) (hf : Function.Surjective f)
  证明: rangeS_top_iff_surjective.2 hf

Depends on / 依赖: rangeS_top_iff_surjective
-/
theorem rangeS_top_of_surjective (f : R ->+* S) (hf : Function.Surjective f) :
    f.rangeS = (⊤ : Subsemiring S) :=
  rangeS_top_iff_surjective.2 hf

/--
theorem `eqOn_sclosure` / 定理 `eqOn_sclosure`

English:
theorem eqOn_sclosure
  given: {f g : R ->+* S} {s : Set R} (h : Set.EqOn f g s)
  statement: Set.EqOn f g (closure s)
  proof: show closure s <= f.eqLocusS g from closure_le.2 h

中文:
定理 eqOn_sclosure
  条件: {f g : R ->+* S} {s : Set R} (h : Set.EqOn f g s)
  结论: Set.EqOn f g (closure s)
  证明: show closure s <= f.eqLocusS g from closure_le.2 h

Depends on / 依赖: closure, closure_le, eqLocusS, f.eqLocusS
-/
theorem eqOn_sclosure {f g : R ->+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s <= f.eqLocusS g from closure_le.2 h

/--
theorem `eq_of_eqOn_stop` / 定理 `eq_of_eqOn_stop`

English:
theorem eq_of_eqOn_stop
  given: {f g : R ->+* S} (h : Set.EqOn f g (⊤ : Subsemiring R))
  statement: f = g
  proof: ext fun _ => h (mem_top _)

中文:
定理 eq_of_eqOn_stop
  条件: {f g : R ->+* S} (h : Set.EqOn f g (⊤ : Subsemiring R))
  结论: f = g
  证明: ext fun _ => h (mem_top _)

Depends on / 依赖: mem_top
-/
theorem eq_of_eqOn_stop {f g : R ->+* S} (h : Set.EqOn f g (⊤ : Subsemiring R)) : f = g :=
  ext fun _ => h (mem_top _)

/--
theorem `eq_of_eqOn_sdense` / 定理 `eq_of_eqOn_sdense`

English:
theorem eq_of_eqOn_sdense
  given: {s : Set R} (hs : closure s = ⊤) {f g : R ->+* S} (h : s.EqOn f g)
  proof: eq_of_eqOn_stop hs ▸ eqOn_sclosure h

中文:
定理 eq_of_eqOn_sdense
  条件: {s : Set R} (hs : closure s = ⊤) {f g : R ->+* S} (h : s.EqOn f g)
  证明: eq_of_eqOn_stop hs ▸ eqOn_sclosure h

Depends on / 依赖: eqOn_sclosure, eq_of_eqOn_stop
-/
theorem eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : R ->+* S} (h : s.EqOn f g) :
    f = g :=
eq_of_eqOn_stop hs ▸ eqOn_sclosure h

/--
theorem `sclosure_preimage_le` / 定理 `sclosure_preimage_le`

English:
theorem sclosure_preimage_le
  given: (f : R ->+* S) (s : Set S)
  statement: closure (f ⁻¹' s) <= (closure s).comap f
  proof: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 sclosure_preimage_le
  条件: (f : R ->+* S) (s : Set S)
  结论: closure (f ⁻¹' s) <= (closure s).comap f
  证明: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem sclosure_preimage_le (f : R ->+* S) (s : Set S) : closure (f ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

/--
theorem `map_closureS` / 定理 `map_closureS`

English:
theorem map_closureS
  given: (f : R ->+* S) (s : Set R)
  statement: (closure s).map f = closure (f '' s)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subsemiring.gi S).gc (Subsemiring.gi R).gc
    fun _ => coe_comap _ _

@[simp]

中文:
定理 map_closureS
  条件: (f : R ->+* S) (s : Set R)
  结论: (closure s).map f = closure (f '' s)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subsemiring.gi S).gc (Subsemiring.gi R).gc
    fun _ => coe_comap _ _

@[simp]

Depends on / 依赖: Set.image_preimage.l_comm_of_u_comm, Subsemiring, Subsemiring.gi, coe_comap, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_closureS (f : R ->+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subsemiring.gi S).gc (Subsemiring.gi R).gc
    fun _ => coe_comap _ _

@[simp]
/--
theorem `domRestrict_comp_rangeSRestrict` / 定理 `domRestrict_comp_rangeSRestrict`

English:
theorem domRestrict_comp_rangeSRestrict
  given: (g : S ->+* T) (f : R ->+* S)
  proof: rfl

中文:
定理 domRestrict_comp_rangeSRestrict
  条件: (g : S ->+* T) (f : R ->+* S)
  证明: rfl
-/
theorem domRestrict_comp_rangeSRestrict (g : S ->+* T) (f : R ->+* S) :
    (g.domRestrict f.rangeS).comp (f.rangeSRestrict) = g.comp f :=
  rfl

end RingHom

namespace Subsemiring

open RingHom

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : Subsemiring R} (h : S <= T)
  body: S.subtype.codRestrict _ fun x => h x.2

中文:
定义 inclusion
  签名: {S T : Subsemiring R} (h : S <= T)
  定义体: S.subtype.codRestrict _ fun x => h x.2

Depends on / 依赖: S.subtype.codRestrict, codRestrict, subtype
-/
def inclusion {S T : Subsemiring R} (h : S <= T) : S ->+* T :=
  S.subtype.codRestrict _ fun x => h x.2

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {S T : Subsemiring R} (h : S <= T)
  proof: Set.inclusion_injective h

@[simp]

中文:
定理 inclusion_injective
  条件: {S T : Subsemiring R} (h : S <= T)
  证明: Set.inclusion_injective h

@[simp]

Depends on / 依赖: Set.inclusion_injective, inclusion_injective
-/
theorem inclusion_injective {S T : Subsemiring R} (h : S <= T) :
    Function.Injective (inclusion h) := Set.inclusion_injective h

@[simp]
/--
theorem `rangeS_subtype` / 定理 `rangeS_subtype`

English:
theorem rangeS_subtype
  given: (s : Subsemiring R)
  statement: s.subtype.rangeS = s
  proof: SetLike.coe_injective (coe_rangeS _).trans Subtype.range_coe

@[simp]

中文:
定理 rangeS_subtype
  条件: (s : Subsemiring R)
  结论: s.subtype.rangeS = s
  证明: SetLike.coe_injective (coe_rangeS _).trans Subtype.range_coe

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, Subtype, Subtype.range_coe, coe_injective, coe_rangeS, range_coe
-/
theorem rangeS_subtype (s : Subsemiring R) : s.subtype.rangeS = s :=
SetLike.coe_injective (coe_rangeS _).trans Subtype.range_coe

@[simp]
/--
theorem `range_fst` / 定理 `range_fst`

English:
theorem range_fst
  statement: (fst R S).rangeS = ⊤
  proof: (fst R S).rangeS_top_of_surjective Prod.fst_surjective

@[simp]

中文:
定理 range_fst
  结论: (fst R S).rangeS = ⊤
  证明: (fst R S).rangeS_top_of_surjective Prod.fst_surjective

@[simp]

Depends on / 依赖: Prod.fst_surjective, fst_surjective, rangeS_top_of_surjective
-/
theorem range_fst : (fst R S).rangeS = ⊤ :=
(fst R S).rangeS_top_of_surjective Prod.fst_surjective

@[simp]
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
  given: (s : Subsemiring R) (t : Subsemiring S)
  proof: le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ <= s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t <= s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <

中文:
定理 prod_bot_sup_bot_prod
  条件: (s : Subsemiring R) (t : Subsemiring S)
  证明: le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ <= s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t <= s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <

Depends on / 依赖: Prod.fst_mul_snd, SetLike, SetLike.mem_coe, bot_le, fst_mul_snd, le_antisymm, le_sup_left, le_sup_right, mem_coe, mul_mem, one_mem, prod_mono_left, prod_mono_right, s.prod, sup_le
-/
theorem prod_bot_sup_bot_prod (s : Subsemiring R) (t : Subsemiring S) :
    s.prod ⊥ ⊔ prod ⊥ t = s.prod t :=
  le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ <= s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t <= s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subsemiring

namespace RingEquiv

variable {s t : Subsemiring R}

/--
Definition of `subsemiringCongr` / `subsemiringCongr` 的定义

English:
definition subsemiringCongr
  signature: (h : s = t)
  body: { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 subsemiringCongr
  签名: (h : s = t)
  定义体: { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: Equiv.setCongr, congr_arg, map_add, map_mul, setCongr
-/
def subsemiringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/--
Definition of `ofLeftInverseS` / `ofLeftInverseS` 的定义

English:
definition ofLeftInverseS
  signature: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f)
  body: { f.rangeSRestrict with
    toFun := fun x => f.rangeSRestrict x
    invFun := fun x => (g ∘ f.rangeS.subtype) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext by
        let ⟨x', hx'⟩ := RingHom.mem_rangeS.mp x.prop
        simp [← hx', h x'] }

@[simp]

中文:
定义 ofLeftInverseS
  签名: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f)
  定义体: { f.rangeSRestrict with
    toFun := fun x => f.rangeSRestrict x
    invFun := fun x => (g ∘ f.rangeS.subtype) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext by
        let ⟨x', hx'⟩ := RingHom.mem_rangeS.mp x.prop
        simp [← hx', h x'] }

@[simp]

Depends on / 依赖: RingHom, RingHom.mem_rangeS.mp, Subtype, Subtype.ext, f.rangeS.subtype, f.rangeSRestrict, invFun, left_inv, mem_rangeS, rangeS, rangeSRestrict, right_inv, subtype, x.prop
-/
def ofLeftInverseS {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) : R ≃+* f.rangeS :=
  { f.rangeSRestrict with
    toFun := fun x => f.rangeSRestrict x
    invFun := fun x => (g ∘ f.rangeS.subtype) x
    left_inv := h
    right_inv := fun x =>
Subtype.ext by
        let ⟨x', hx'⟩ := RingHom.mem_rangeS.mp x.prop
        simp [← hx', h x'] }

@[simp]
/--
theorem `ofLeftInverseS_apply` / 定理 `ofLeftInverseS_apply`

English:
theorem ofLeftInverseS_apply
  given: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) (x : R)
  proof: rfl

@[simp]

中文:
定理 ofLeftInverseS_apply
  条件: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) (x : R)
  证明: rfl

@[simp]
-/
theorem ofLeftInverseS_apply {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverseS h x) = f x :=
  rfl

@[simp]
/--
theorem `ofLeftInverseS_symm_apply` / 定理 `ofLeftInverseS_symm_apply`

English:
theorem ofLeftInverseS_symm_apply
  statement: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f)
  proof: rfl

中文:
定理 ofLeftInverseS_symm_apply
  结论: {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f)
  证明: rfl
-/
theorem ofLeftInverseS_symm_apply {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f)
    (x : f.rangeS) : (ofLeftInverseS h).symm x = g x :=
  rfl

/--
Definition of `subsemiringMap` / `subsemiringMap` 的定义

English:
definition subsemiringMap
  signature: (e : R ≃+* S) (s : Subsemiring R)
  body: { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }

@[simp]

中文:
定义 subsemiringMap
  签名: (e : R ≃+* S) (s : Subsemiring R)
  定义体: { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }

@[simp]

Depends on / 依赖: addSubmonoidMap, e.toAddEquiv.addSubmonoidMap, e.toMulEquiv.submonoidMap, s.toAddSubmonoid, s.toSubmonoid, submonoidMap, toAddEquiv, toAddSubmonoid, toMulEquiv, toSubmonoid
-/
def subsemiringMap (e : R ≃+* S) (s : Subsemiring R) : s ≃+* s.map (e : R ->+* S) :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }

@[simp]
/--
theorem `subsemiringMap_apply_coe` / 定理 `subsemiringMap_apply_coe`

English:
theorem subsemiringMap_apply_coe
  given: (e : R ≃+* S) (s : Subsemiring R) (x : s)
  proof: rfl

@[simp]

中文:
定理 subsemiringMap_apply_coe
  条件: (e : R ≃+* S) (s : Subsemiring R) (x : s)
  证明: rfl

@[simp]
-/
theorem subsemiringMap_apply_coe (e : R ≃+* S) (s : Subsemiring R) (x : s) :
    ((subsemiringMap e s) x : S) = e x :=
  rfl

@[simp]
/--
theorem `subsemiringMap_symm_apply_coe` / 定理 `subsemiringMap_symm_apply_coe`

English:
theorem subsemiringMap_symm_apply_coe
  given: (e : R ≃+* S) (s : Subsemiring R) (x : s.map e.toRingHom)
  proof: rfl

中文:
定理 subsemiringMap_symm_apply_coe
  条件: (e : R ≃+* S) (s : Subsemiring R) (x : s.map e.toRingHom)
  证明: rfl
-/
theorem subsemiringMap_symm_apply_coe (e : R ≃+* S) (s : Subsemiring R) (x : s.map e.toRingHom) :
    ((subsemiringMap e s).symm x : R) = e.symm x :=
  rfl

end RingEquiv

/-! ### Actions by `Subsemiring`s

These are just copies of the definitions about `Submonoid` starting from `Submonoid.mulAction`.
The only new result is `Subsemiring.module`.

When `R` is commutative, `Algebra.ofSubsemiring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subsemiring

variable {R' α β : Type*}

variable {S' : Type*} [SetLike S' R'] (s : S)

section NonAssocSemiring

variable [NonAssocSemiring R']

/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [SMul R' α] (S : Subsemiring R')
  body: inferInstance

中文:
实例 smul
  签名: [SMul R' α] (S : Subsemiring R')
  定义体: inferInstance
-/
instance smul [SMul R' α] (S : Subsemiring R') : SMul S α :=
  inferInstance

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: [SMul R' α] {S : Subsemiring R'} (g : S) (m : α)
  statement: g • m = (g : R') • m
  proof: rfl

中文:
定理 smul_def
  条件: [SMul R' α] {S : Subsemiring R'} (g : S) (m : α)
  结论: g • m = (g : R') • m
  证明: rfl
-/
theorem smul_def [SMul R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m :=
  rfl

/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: [SMul R' β] [SMul α β] [SMulCommClass R' α β] (S : Subsemiring R')
  body: inferInstance

中文:
实例 smulCommClass_left
  签名: [SMul R' β] [SMul α β] [SMulCommClass R' α β] (S : Subsemiring R')
  定义体: inferInstance
-/
instance smulCommClass_left [SMul R' β] [SMul α β] [SMulCommClass R' α β] (S : Subsemiring R') :
    SMulCommClass S α β :=
  inferInstance

/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: [SMul α β] [SMul R' β] [SMulCommClass α R' β] (S : Subsemiring R')
  body: inferInstance

中文:
实例 smulCommClass_right
  签名: [SMul α β] [SMul R' β] [SMulCommClass α R' β] (S : Subsemiring R')
  定义体: inferInstance
-/
instance smulCommClass_right [SMul α β] [SMul R' β] [SMulCommClass α R' β] (S : Subsemiring R') :
    SMulCommClass α S β :=
  inferInstance

instance {R M : Type*} [Semiring R] [MulAction R M] :
    SMulCommClass R (Subsemiring.center R) M :=
inferInstanceAs SMulCommClass R (Submonoid.center R) M

instance {R M : Type*} [Semiring R] [MulAction R M] :
    SMulCommClass (Subsemiring.center R) R M :=
inferInstanceAs SMulCommClass (Submonoid.center R) R M

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul α β] [SMul R' α] [SMul R' β] [IsScalarTower R' α β]
  body: inferInstance

中文:
实例 isScalarTower
  签名: [SMul α β] [SMul R' α] [SMul R' β] [IsScalarTower R' α β]
  定义体: inferInstance
-/
instance isScalarTower [SMul α β] [SMul R' α] [SMul R' β] [IsScalarTower R' α β]
    (S : Subsemiring R') :
    IsScalarTower S α β :=
  inferInstance

instance (priority := low) {M' α : Type*} [SMul M' α] {S' : Type*}
    [SetLike S' M'] (s : S') [FaithfulSMul M' α] : FaithfulSMul s α :=
⟨fun h => Subtype.ext eq_of_smul_eq_smul h⟩

/--
Instance `faithfulSMul` / 实例 `faithfulSMul`

English:
instance faithfulSMul
  signature: [SMul R' α] [FaithfulSMul R' α] (S : Subsemiring R')
  body: inferInstance

中文:
实例 faithfulSMul
  签名: [SMul R' α] [FaithfulSMul R' α] (S : Subsemiring R')
  定义体: inferInstance
-/
instance faithfulSMul [SMul R' α] [FaithfulSMul R' α] (S : Subsemiring R') : FaithfulSMul S α :=
  inferInstance

instance (priority := low) {S' : Type*} [SetLike S' R'] [SubsemiringClass S' R'] (s : S')
    [Zero α] [SMulWithZero R' α] : SMulWithZero s α where
  smul_zero r := smul_zero (r : R')
  zero_smul := zero_smul R'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] [SMulWithZero R' α] (S
  body: inferInstance

中文:
实例 [Zero
  签名: α] [SMulWithZero R' α] (S
  定义体: inferInstance

Depends on / 依赖: RationalMap, RationalMap.comp_def, comp_def, g.toRationalMap_representative, infer_instance, toRationalMap_representative
-/
instance [Zero α] [SMulWithZero R' α] (S : Subsemiring R') : SMulWithZero S α :=
  inferInstance

end NonAssocSemiring

variable [Semiring R']

/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: [MulAction R' α] (S : Subsemiring R')
  body: inferInstance

中文:
实例 mulAction
  签名: [MulAction R' α] (S : Subsemiring R')
  定义体: inferInstance
-/
instance mulAction [MulAction R' α] (S : Subsemiring R') : MulAction S α :=
  inferInstance

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [AddMonoid α] [DistribMulAction R' α] (S : Subsemiring R')
  body: inferInstance

中文:
实例 distribMulAction
  签名: [AddMonoid α] [DistribMulAction R' α] (S : Subsemiring R')
  定义体: inferInstance
-/
instance distribMulAction [AddMonoid α] [DistribMulAction R' α] (S : Subsemiring R') :
    DistribMulAction S α :=
  inferInstance

/--
Instance `mulDistribMulAction` / 实例 `mulDistribMulAction`

English:
instance mulDistribMulAction
  signature: [Monoid α] [MulDistribMulAction R' α] (S : Subsemiring R')
  body: inferInstance

中文:
实例 mulDistribMulAction
  签名: [Monoid α] [MulDistribMulAction R' α] (S : Subsemiring R')
  定义体: inferInstance
-/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction R' α] (S : Subsemiring R') :
    MulDistribMulAction S α :=
  inferInstance

instance (priority := low) {S' : Type*} [SetLike S' R'] [SubsemiringClass S' R'] (s : S')
    [Zero α] [MulActionWithZero R' α] : MulActionWithZero s α where
  smul_zero r := smul_zero (r : R')
  zero_smul := zero_smul R'

/--
Instance `mulActionWithZero` / 实例 `mulActionWithZero`

English:
instance mulActionWithZero
  signature: [Zero α] [MulActionWithZero R' α] (S : Subsemiring R')
  body: inferInstance

中文:
实例 mulActionWithZero
  签名: [Zero α] [MulActionWithZero R' α] (S : Subsemiring R')
  定义体: inferInstance
-/
instance mulActionWithZero [Zero α] [MulActionWithZero R' α] (S : Subsemiring R') :
    MulActionWithZero S α :=
  inferInstance

instance (priority := low) [AddCommMonoid α] [Module R' α] {S' : Type*} [SetLike S' R']
    [SubsemiringClass S' R'] (s : S') : Module s α where
  toDistribMulAction := inferInstance
  add_smul r₁ r₂ := add_smul (r₁ : R') r₂
  zero_smul := zero_smul R'

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: [AddCommMonoid α] [Module R' α] (S : Subsemiring R')
  body: inferInstance

中文:
实例 module
  签名: [AddCommMonoid α] [Module R' α] (S : Subsemiring R')
  定义体: inferInstance
-/
instance module [AddCommMonoid α] [Module R' α] (S : Subsemiring R') : Module S α :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] [MulSemiringAction R' α] (S
  body: inferInstance

中文:
实例 [Semiring
  签名: α] [MulSemiringAction R' α] (S
  定义体: inferInstance
-/
instance [Semiring α] [MulSemiringAction R' α] (S : Subsemiring R') : MulSemiringAction S α :=
  inferInstance

/--
Instance `center.smulCommClass_left` / 实例 `center.smulCommClass_left`

English:
instance center.smulCommClass_left
  signature: : SMulCommClass (center R') R' R'
  body: Submonoid.center.smulCommClass_left

中文:
实例 center.smulCommClass_left
  签名: : SMulCommClass (center R') R' R'
  定义体: Submonoid.center.smulCommClass_left
-/
instance center.smulCommClass_left : SMulCommClass (center R') R' R' :=
  Submonoid.center.smulCommClass_left

/--
Instance `center.smulCommClass_right` / 实例 `center.smulCommClass_right`

English:
instance center.smulCommClass_right
  signature: : SMulCommClass R' (center R') R'
  body: Submonoid.center.smulCommClass_right

中文:
实例 center.smulCommClass_right
  签名: : SMulCommClass R' (center R') R'
  定义体: Submonoid.center.smulCommClass_right
-/
instance center.smulCommClass_right : SMulCommClass R' (center R') R' :=
  Submonoid.center.smulCommClass_right

/--
lemma `closure_le_centralizer_centralizer` / 引理 `closure_le_centralizer_centralizer`

English:
lemma closure_le_centralizer_centralizer
  given: (s : Set R')
  proof: closure_le.mpr Set.subset_centralizer_centralizer

中文:
引理 closure_le_centralizer_centralizer
  条件: (s : Set R')
  证明: closure_le.mpr Set.subset_centralizer_centralizer

Depends on / 依赖: Set.subset_centralizer_centralizer, closure_le, closure_le.mpr, subset_centralizer_centralizer
-/
lemma closure_le_centralizer_centralizer (s : Set R') :
    closure s <= centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/--
theorem `isMulCommutative_closure` / 定理 `isMulCommutative_closure`

English:
theorem isMulCommutative_closure
  given: {s : Set R'} (hcomm : forall x in s, forall y in s, x * y = y * x)
  proof: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

中文:
定理 isMulCommutative_closure
  条件: {s : Set R'} (hcomm : 对任意 x in s, 对任意 y in s, x * y = y * x)
  证明: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, centralizer_centralizer_comm_of_comm, closure_le_centralizer_centralizer, of_setLike_mul_comm
-/
theorem isMulCommutative_closure {s : Set R'} (hcomm : forall x in s, forall y in s, x * y = y * x) :
    IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a commutative semiring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
/--
Definition of `closureCommSemiringOfComm` / `closureCommSemiringOfComm` 的定义

English:
abbreviation closureCommSemiringOfComm
  signature: {s : Set R'} (hcomm : forall x in s, forall y in s, x * y = y * x)
  body: have := isMulCommutative_closure hcomm
  inferInstance

中文:
缩写 closureCommSemiringOfComm
  签名: {s : Set R'} (hcomm : 对任意 x in s, 对任意 y in s, x * y = y * x)
  定义体: have := isMulCommutative_closure hcomm
  inferInstance

Depends on / 依赖: f.isDominant_toRationalMap_iff, isDominant_toRationalMap_iff, isMulCommutative_closure
-/
abbrev closureCommSemiringOfComm {s : Set R'} (hcomm : forall x in s, forall y in s, x * y = y * x) :
    CommSemiring (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance

/--
Instance `instIsMulCommutative_closure` / 实例 `instIsMulCommutative_closure`

English:
instance instIsMulCommutative_closure
  signature: {S : Type*} [SetLike S R'] [MulMemClass S R'] (s : S)
  body: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

中文:
实例 instIsMulCommutative_closure
  签名: {S : 类型} [SetLike S R'] [MulMemClass S R'] (s : S)
  定义体: isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

Depends on / 依赖: f.representative.isDominant_toRationalMap_iff, f.toRationalMap_representative, isDominant_toRationalMap_iff, isMulCommutative_closure, representative, setLike_mul_comm, toRationalMap_representative
-/
instance instIsMulCommutative_closure {S : Type*} [SetLike S R'] [MulMemClass S R'] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set R')) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

end Subsemiring

end Actions

namespace Subsemiring

/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (f : R ->+* S) (t : Subsemiring S)
  statement: (t.comap f).map f = t ⊓ f.rangeS
  proof: SetLike.coe_injective Set.image_preimage_eq_inter_range

中文:
定理 map_comap_eq
  条件: (f : R ->+* S) (t : Subsemiring S)
  结论: (t.comap f).map f = t ⊓ f.rangeS
  证明: SetLike.coe_injective Set.image_preimage_eq_inter_range

Depends on / 依赖: Set.image_preimage_eq_inter_range, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq_inter_range
-/
theorem map_comap_eq (f : R ->+* S) (t : Subsemiring S) : (t.comap f).map f = t ⊓ f.rangeS :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

/--
theorem `map_comap_eq_self` / 定理 `map_comap_eq_self`

English:
theorem map_comap_eq_self
  proof: by
  simpa only [inf_of_le_left h] using map_comap_eq f t

中文:
定理 map_comap_eq_self
  证明: by
  simpa only [inf_of_le_left h] using map_comap_eq f t

Depends on / 依赖: inf_of_le_left, map_comap_eq
-/
theorem map_comap_eq_self
    {f : R ->+* S} {t : Subsemiring S} (h : t <= f.rangeS) : (t.comap f).map f = t := by
  simpa only [inf_of_le_left h] using map_comap_eq f t

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
    {f : R ->+* S} (hf : Function.Surjective f) (t : Subsemiring S) : (t.comap f).map f = t :=
map_comap_eq_self by simp [hf]

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
    {f : R ->+* S} (hf : Function.Injective f) (s : Subsemiring R) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subsemiring
