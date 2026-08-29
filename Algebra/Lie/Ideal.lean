/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Submodule

/-!
# Lie Ideals

This file defines Lie ideals, which are Lie submodules of a Lie algebra over itself.
They are defined as a special case of `LieSubmodule`, and inherit much of their structure from it.

We also prove some basic properties of Lie ideals, including how they behave under
Lie algebra homomorphisms (`map`, `comap`) and how they relate to the lattice structure
on Lie submodules.

## Main definitions

* `LieIdeal`
* `LieIdeal.map`
* `LieIdeal.comap`

## Tags

Lie algebra, ideal, submodule, Lie submodule
-/

@[expose] public section


universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

section LieIdeal
variable [LieAlgebra R L] [LieModule R L M]

/--
Definition of `LieIdeal` / `LieIdeal` 的定义

English:
abbreviation LieIdeal
  body: LieSubmodule R L L

中文:
缩写 LieIdeal
  定义体: LieSubmodule R L L

Depends on / 依赖: LieSubmodule
-/
abbrev LieIdeal :=
  LieSubmodule R L L

/--
theorem `lie_mem_right` / 定理 `lie_mem_right`

English:
theorem lie_mem_right
  given: (I : LieIdeal R L) (x y : L) (h : y in I)
  statement: ⁅x, y⁆ in I
  proof: I.lie_mem h

中文:
定理 lie_mem_right
  条件: (I : LieIdeal R L) (x y : L) (h : y in I)
  结论: ⁅x, y⁆ in I
  证明: I.lie_mem h

Depends on / 依赖: I.lie_mem, lie_mem
-/
theorem lie_mem_right (I : LieIdeal R L) (x y : L) (h : y in I) : ⁅x, y⁆ in I :=
  I.lie_mem h

/--
theorem `lie_mem_left` / 定理 `lie_mem_left`

English:
theorem lie_mem_left
  given: (I : LieIdeal R L) (x y : L) (h : x in I)
  statement: ⁅x, y⁆ in I
  proof: by
  rw [← lie_skew]; rw [← neg_lie]; apply lie_mem_right; assumption

中文:
定理 lie_mem_left
  条件: (I : LieIdeal R L) (x y : L) (h : x in I)
  结论: ⁅x, y⁆ in I
  证明: by
  rw [← lie_skew]; rw [← neg_lie]; apply lie_mem_right; assumption

Depends on / 依赖: lie_mem_right, lie_skew, neg_lie
-/
theorem lie_mem_left (I : LieIdeal R L) (x y : L) (h : x in I) : ⁅x, y⁆ in I := by
  rw [← lie_skew]; rw [← neg_lie]; apply lie_mem_right; assumption

/--
Definition of `LieIdeal.toLieSubalgebra` / `LieIdeal.toLieSubalgebra` 的定义

English:
definition LieIdeal.toLieSubalgebra
  signature: (I : LieIdeal R L)
  body: { I.toSubmodule with lie_mem' := by intro x y _ hy; apply lie_mem_right; exact hy }

中文:
定义 LieIdeal.toLieSubalgebra
  签名: (I : LieIdeal R L)
  定义体: { I.toSubmodule with lie_mem' := by intro x y _ hy; apply lie_mem_right; exact hy }

Depends on / 依赖: I.toSubmodule, lie_mem, lie_mem_right, toSubmodule
-/
def LieIdeal.toLieSubalgebra (I : LieIdeal R L) : LieSubalgebra R L :=
  { I.toSubmodule with lie_mem' := by intro x y _ hy; apply lie_mem_right; exact hy }

/--
lemma `LieIdeal.mem_toLieSubalgebra` / 引理 `LieIdeal.mem_toLieSubalgebra`

English:
lemma LieIdeal.mem_toLieSubalgebra
  given: (I : LieIdeal R L) (x : L)
  proof: Iff.rfl

中文:
引理 LieIdeal.mem_toLieSubalgebra
  条件: (I : LieIdeal R L) (x : L)
  证明: Iff.rfl
-/
@[simp] lemma LieIdeal.mem_toLieSubalgebra (I : LieIdeal R L) (x : L) :
    x in I.toLieSubalgebra ↔ x in I :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (LieIdeal R L) (LieSubalgebra R L)
  body: ⟨LieIdeal.toLieSubalgebra R L⟩

@[simp]

中文:
实例 :
  签名: Coe (LieIdeal R L) (LieSubalgebra R L)
  定义体: ⟨LieIdeal.toLieSubalgebra R L⟩

@[simp]

Depends on / 依赖: LieIdeal, LieIdeal.toLieSubalgebra, toLieSubalgebra
-/
instance : Coe (LieIdeal R L) (LieSubalgebra R L) :=
  ⟨LieIdeal.toLieSubalgebra R L⟩

@[simp]
/--
theorem `LieIdeal.coe_toLieSubalgebra` / 定理 `LieIdeal.coe_toLieSubalgebra`

English:
theorem LieIdeal.coe_toLieSubalgebra
  given: (I : LieIdeal R L)
  statement: ((I : LieSubalgebra R L) : Set L) = I
  proof: rfl

@[simp]

中文:
定理 LieIdeal.coe_toLieSubalgebra
  条件: (I : LieIdeal R L)
  结论: ((I : LieSubalgebra R L) : Set L) = I
  证明: rfl

@[simp]
-/
theorem LieIdeal.coe_toLieSubalgebra (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Set L) = I :=
  rfl

@[simp]
/--
theorem `LieIdeal.toLieSubalgebra_toSubmodule` / 定理 `LieIdeal.toLieSubalgebra_toSubmodule`

English:
theorem LieIdeal.toLieSubalgebra_toSubmodule
  given: (I : LieIdeal R L)
  proof: rfl

中文:
定理 LieIdeal.toLieSubalgebra_toSubmodule
  条件: (I : LieIdeal R L)
  证明: rfl
-/
theorem LieIdeal.toLieSubalgebra_toSubmodule (I : LieIdeal R L) :
    ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule.toSubmodule I :=
  rfl

/--
Instance `LieIdeal.bracket` / 实例 `LieIdeal.bracket`

English:
instance LieIdeal.bracket
  signature: {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  body: ⁅(x : L), m⁆

中文:
实例 LieIdeal.bracket
  签名: {R L : 类型} [CommRing R] [LieRing L] [LieAlgebra R L]
  定义体: ⁅(x : L), m⁆
-/
instance LieIdeal.bracket {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [Bracket L M] : Bracket I M where
  bracket x m := ⁅(x : L), m⁆

instance (I : LieIdeal R L) : Bracket I I := inferInstance

/--
Instance `LieIdeal.lieRing` / 实例 `LieIdeal.lieRing`

English:
instance LieIdeal.lieRing
  signature: (I : LieIdeal R L)
  body: inferInstanceAs LieRing I.toLieSubalgebra

中文:
实例 LieIdeal.lieRing
  签名: (I : LieIdeal R L)
  定义体: inferInstanceAs LieRing I.toLieSubalgebra

Depends on / 依赖: I.toLieSubalgebra, LieRing, toLieSubalgebra
-/
instance LieIdeal.lieRing (I : LieIdeal R L) : LieRing I :=
inferInstanceAs LieRing I.toLieSubalgebra

/--
Instance `LieIdeal.lieAlgebra` / 实例 `LieIdeal.lieAlgebra`

English:
instance LieIdeal.lieAlgebra
  signature: (I : LieIdeal R L)
  body: inferInstanceAs LieAlgebra R I.toLieSubalgebra

中文:
实例 LieIdeal.lieAlgebra
  签名: (I : LieIdeal R L)
  定义体: inferInstanceAs LieAlgebra R I.toLieSubalgebra

Depends on / 依赖: I.toLieSubalgebra, LieAlgebra, toLieSubalgebra
-/
instance LieIdeal.lieAlgebra (I : LieIdeal R L) : LieAlgebra R I :=
inferInstanceAs LieAlgebra R I.toLieSubalgebra

/--
Instance `LieIdeal.lieRingModule` / 实例 `LieIdeal.lieRingModule`

English:
instance LieIdeal.lieRingModule
  signature: {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  body: inferInstanceAs LieRingModule I.toLieSubalgebra M

@[simp]

中文:
实例 LieIdeal.lieRingModule
  签名: {R L : 类型} [CommRing R] [LieRing L] [LieAlgebra R L]
  定义体: inferInstanceAs LieRingModule I.toLieSubalgebra M

@[simp]

Depends on / 依赖: I.toLieSubalgebra, LieRingModule, toLieSubalgebra
-/
instance LieIdeal.lieRingModule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] : LieRingModule I M :=
inferInstanceAs LieRingModule I.toLieSubalgebra M

@[simp]
/--
theorem `LieIdeal.coe_bracket_of_module` / 定理 `LieIdeal.coe_bracket_of_module`

English:
theorem LieIdeal.coe_bracket_of_module
  statement: {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  proof: LieSubalgebra.coe_bracket_of_module (I : LieSubalgebra R L) x m

中文:
定理 LieIdeal.coe_bracket_of_module
  结论: {R L : 类型} [CommRing R] [LieRing L] [LieAlgebra R L]
  证明: LieSubalgebra.coe_bracket_of_module (I : LieSubalgebra R L) x m

Depends on / 依赖: LieSubalgebra, LieSubalgebra.coe_bracket_of_module, coe_bracket_of_module
-/
theorem LieIdeal.coe_bracket_of_module {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] (x : I) (m : M) :
    ⁅x, m⁆ = ⁅(↑x : L), m⁆ :=
  LieSubalgebra.coe_bracket_of_module (I : LieSubalgebra R L) x m

/--
Instance `LieIdeal.lieModule` / 实例 `LieIdeal.lieModule`

English:
instance LieIdeal.lieModule
  signature: (I : LieIdeal R L)
  body: LieSubalgebra.lieModule (I : LieSubalgebra R L)

中文:
实例 LieIdeal.lieModule
  签名: (I : LieIdeal R L)
  定义体: LieSubalgebra.lieModule (I : LieSubalgebra R L)

Depends on / 依赖: LieSubalgebra, LieSubalgebra.lieModule, lieModule
-/
instance LieIdeal.lieModule (I : LieIdeal R L) : LieModule R I M :=
  LieSubalgebra.lieModule (I : LieSubalgebra R L)

instance (I : LieIdeal R L) : IsLieTower I L M where
  leibniz_lie x y m := leibniz_lie x.val y m

instance (I : LieIdeal R L) : IsLieTower L I M where
  leibniz_lie x y m := leibniz_lie x y.val m

end LieIdeal

namespace LieSubalgebra

variable {L}
variable [LieAlgebra R L]
variable (K : LieSubalgebra R L)

/--
theorem `exists_lieIdeal_coe_eq_iff` / 定理 `exists_lieIdeal_coe_eq_iff`

English:
theorem exists_lieIdeal_coe_eq_iff
  proof: by
  simp only [← toSubmodule_inj, LieIdeal.toLieSubalgebra_toSubmodule,
    Submodule.exists_lieSubmodule_coe_eq_iff L, mem_toSubmodule]

中文:
定理 exists_lieIdeal_coe_eq_iff
  证明: by
  simp only [← toSubmodule_inj, LieIdeal.toLieSubalgebra_toSubmodule,
    Submodule.exists_lieSubmodule_coe_eq_iff L, mem_toSubmodule]

Depends on / 依赖: LieIdeal, LieIdeal.toLieSubalgebra_toSubmodule, Submodule, Submodule.exists_lieSubmodule_coe_eq_iff, exists_lieSubmodule_coe_eq_iff, mem_toSubmodule, toLieSubalgebra_toSubmodule, toSubmodule_inj
-/
theorem exists_lieIdeal_coe_eq_iff :
    (exists I : LieIdeal R L, ↑I = K) ↔ forall x y : L, y in K -> ⁅x, y⁆ in K := by
  simp only [← toSubmodule_inj, LieIdeal.toLieSubalgebra_toSubmodule,
    Submodule.exists_lieSubmodule_coe_eq_iff L, mem_toSubmodule]

/--
theorem `exists_nested_lieIdeal_coe_eq_iff` / 定理 `exists_nested_lieIdeal_coe_eq_iff`

English:
theorem exists_nested_lieIdeal_coe_eq_iff
  given: {K' : LieSubalgebra R L} (h : K <= K')
  proof: by
  simp only [exists_lieIdeal_coe_eq_iff, coe_bracket, mem_ofLe]
  constructor
  · intro h' x y hx hy; exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
  · rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy'; exact h' x y hx hy'

中文:
定理 exists_nested_lieIdeal_coe_eq_iff
  条件: {K' : LieSubalgebra R L} (h : K <= K')
  证明: by
  simp only [exists_lieIdeal_coe_eq_iff, coe_bracket, mem_ofLe]
  constructor
  · intro h' x y hx hy; exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
  · rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy'; exact h' x y hx hy'

Depends on / 依赖: coe_bracket, exists_lieIdeal_coe_eq_iff, mem_ofLe
-/
theorem exists_nested_lieIdeal_coe_eq_iff {K' : LieSubalgebra R L} (h : K <= K') :
    (exists I : LieIdeal R K', ↑I = ofLe h) ↔ forall x y : L, x in K' -> y in K -> ⁅x, y⁆ in K := by
  simp only [exists_lieIdeal_coe_eq_iff, coe_bracket, mem_ofLe]
  constructor
  · intro h' x y hx hy; exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
  · rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy'; exact h' x y hx hy'

end LieSubalgebra

end LieSubmodule

section LieSubmoduleMapAndComap

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}
variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

namespace LieIdeal

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable (f : L ->ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

@[simp]
/--
theorem `top_toLieSubalgebra` / 定理 `top_toLieSubalgebra`

English:
theorem top_toLieSubalgebra
  statement: ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤
  proof: rfl

中文:
定理 top_toLieSubalgebra
  结论: ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤
  证明: rfl
-/
theorem top_toLieSubalgebra : ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤ :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : LieIdeal R L'
  body: LieSubmodule.lieSpan R L' (I : Submodule R L).map (f : L ->ₗ[R] L')

中文:
定义 map
  签名: : LieIdeal R L'
  定义体: LieSubmodule.lieSpan R L' (I : Submodule R L).map (f : L ->ₗ[R] L')

Depends on / 依赖: LieSubmodule, LieSubmodule.lieSpan, Submodule, lieSpan
-/
def map : LieIdeal R L' :=
LieSubmodule.lieSpan R L' (I : Submodule R L).map (f : L ->ₗ[R] L')

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: : LieIdeal R L
  body: { (J : Submodule R L').comap (f : L ->ₗ[R] L') with
    lie_mem := fun {x y} h => by
      suffices ⁅f x, f y⁆ in J by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid, Submodule.mem_comap, LieHom.coe_toLinearMap, LieHom.map_lie,

中文:
定义 comap
  签名: : LieIdeal R L
  定义体: { (J : Submodule R L').comap (f : L ->ₗ[R] L') with
    lie_mem := fun {x y} h => by
      suffices ⁅f x, f y⁆ in J by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid, Submodule.mem_comap, LieHom.coe_toLinearMap, LieHom.map_lie,

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_toSubsemigroup, AddSubsemigroup, AddSubsemigroup.mem_carrier, J.lie_mem, LieHom, LieHom.coe_toLinearMap, LieHom.map_lie, LieSubalgebra, LieSubalgebra.mem_toSubmodule, Submodule, Submodule.mem_comap, Submodule.mem_toAddSubmonoid, coe_toLinearMap, lie_mem, map_lie, mem_carrier, mem_comap, mem_toAddSubmonoid, mem_toSubmodule
-/
def comap : LieIdeal R L :=
  { (J : Submodule R L').comap (f : L ->ₗ[R] L') with
    lie_mem := fun {x y} h => by
      suffices ⁅f x, f y⁆ in J by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid, Submodule.mem_comap, LieHom.coe_toLinearMap, LieHom.map_lie,
          LieSubalgebra.mem_toSubmodule]
        exact this
      apply J.lie_mem h }

@[simp]
/--
theorem `map_toSubmodule` / 定理 `map_toSubmodule`

English:
theorem map_toSubmodule
  given: (h : ↑(map f I) = f '' I)
  proof: by
  rw [SetLike.ext'_iff]; rw [LieSubmodule.coe_toSubmodule]; rw [h]; rw [Submodule.map_coe]; rfl

@[simp]

中文:
定理 map_toSubmodule
  条件: (h : ↑(map f I) = f '' I)
  证明: by
  rw [SetLike.ext'_iff]; rw [LieSubmodule.coe_toSubmodule]; rw [h]; rw [Submodule.map_coe]; rfl

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.coe_toSubmodule, SetLike, SetLike.ext, Submodule, Submodule.map_coe, _iff, coe_toSubmodule, map_coe
-/
theorem map_toSubmodule (h : ↑(map f I) = f '' I) :
    LieSubmodule.toSubmodule (map f I) = (LieSubmodule.toSubmodule I).map (f : L ->ₗ[R] L') := by
  rw [SetLike.ext'_iff]; rw [LieSubmodule.coe_toSubmodule]; rw [h]; rw [Submodule.map_coe]; rfl

@[simp]
/--
theorem `comap_toSubmodule` / 定理 `comap_toSubmodule`

English:
theorem comap_toSubmodule
  proof: rfl

中文:
定理 comap_toSubmodule
  证明: rfl
-/
theorem comap_toSubmodule :
    (LieSubmodule.toSubmodule (comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L ->ₗ[R] L') :=
  rfl

/--
theorem `map_le` / 定理 `map_le`

English:
theorem map_le
  statement: map f I <= J ↔ f '' I subseteq J
  proof: LieSubmodule.lieSpan_le

中文:
定理 map_le
  结论: map f I <= J ↔ f '' I subseteq J
  证明: LieSubmodule.lieSpan_le

Depends on / 依赖: LieSubmodule, LieSubmodule.lieSpan_le, lieSpan_le
-/
theorem map_le : map f I <= J ↔ f '' I subseteq J :=
  LieSubmodule.lieSpan_le

variable {f I I₂ J}

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {x : L} (hx : x in I)
  statement: f x in map f I
  proof: by
  apply LieSubmodule.subset_lieSpan
  use x
  exact ⟨hx, rfl⟩

@[simp]

中文:
定理 mem_map
  条件: {x : L} (hx : x in I)
  结论: f x in map f I
  证明: by
  apply LieSubmodule.subset_lieSpan
  use x
  exact ⟨hx, rfl⟩

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.subset_lieSpan, subset_lieSpan
-/
theorem mem_map {x : L} (hx : x in I) : f x in map f I := by
  apply LieSubmodule.subset_lieSpan
  use x
  exact ⟨hx, rfl⟩

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {x : L}
  statement: x in comap f J ↔ f x in J
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {x : L}
  结论: x in comap f J ↔ f x in J
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {x : L} : x in comap f J ↔ f x in J :=
  Iff.rfl

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  statement: map f I <= J ↔ I <= comap f J
  proof: by
  rw [map_le]
  exact Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  结论: map f I <= J ↔ I <= comap f J
  证明: by
  rw [map_le]
  exact Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff, map_le
-/
theorem map_le_iff_le_comap : map f I <= J ↔ I <= comap f J := by
  rw [map_le]
  exact Set.image_subset_iff

variable (f) in
/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ => map_le_iff_le_comap

@[simp]

中文:
定理 gc_map_comap
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ => map_le_iff_le_comap

@[simp]

Depends on / 依赖: map_le_iff_le_comap
-/
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap

@[simp]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  statement: (I ⊔ I₂).map f = I.map f ⊔ I₂.map f
  proof: (gc_map_comap f).l_sup

中文:
定理 map_sup
  结论: (I ⊔ I₂).map f = I.map f ⊔ I₂.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup : (I ⊔ I₂).map f = I.map f ⊔ I₂.map f :=
  (gc_map_comap f).l_sup

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  statement: map f (comap f J) <= J
  proof: by rw [map_le_iff_le_comap]

中文:
定理 map_comap_le
  结论: map f (comap f J) <= J
  证明: by rw [map_le_iff_le_comap]

Depends on / 依赖: map_le_iff_le_comap
-/
theorem map_comap_le : map f (comap f J) <= J := by rw [map_le_iff_le_comap]

/--
theorem `comap_map_le` / 定理 `comap_map_le`

English:
theorem comap_map_le
  statement: I <= comap f (map f I)
  proof: by rw [← map_le_iff_le_comap]

@[gcongr, mono]

中文:
定理 comap_map_le
  结论: I <= comap f (map f I)
  证明: by rw [← map_le_iff_le_comap]

@[gcongr, mono]

Depends on / 依赖: map_le_iff_le_comap
-/
theorem comap_map_le : I <= comap f (map f I) := by rw [← map_le_iff_le_comap]

@[gcongr, mono]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  statement: Monotone (map f)
  proof: fun I₁ I₂ h => by
  unfold map
  gcongr; exact h

@[gcongr, mono]

中文:
定理 map_mono
  结论: Monotone (map f)
  证明: fun I₁ I₂ h => by
  unfold map
  gcongr; exact h

@[gcongr, mono]
-/
theorem map_mono : Monotone (map f) := fun I₁ I₂ h => by
  unfold map
  gcongr; exact h

@[gcongr, mono]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  statement: Monotone (comap f)
  proof: fun J₁ J₂ h => by
  rw [← SetLike.coe_subset_coe] at h ⊢
  dsimp only [SetLike.coe]
  exact Set.preimage_mono h

中文:
定理 comap_mono
  结论: Monotone (comap f)
  证明: fun J₁ J₂ h => by
  rw [← SetLike.coe_subset_coe] at h ⊢
  dsimp only [SetLike.coe]
  exact Set.preimage_mono h

Depends on / 依赖: Set.preimage_mono, SetLike, SetLike.coe, SetLike.coe_subset_coe, coe_subset_coe, preimage_mono
-/
theorem comap_mono : Monotone (comap f) := fun J₁ J₂ h => by
  rw [← SetLike.coe_subset_coe] at h ⊢
  dsimp only [SetLike.coe]
  exact Set.preimage_mono h

/--
theorem `map_of_image` / 定理 `map_of_image`

English:
theorem map_of_image
  given: (h : f '' I = J)
  statement: I.map f = J
  proof: by
  apply le_antisymm
  · rw [map, LieSubmodule.lieSpan_le, Submodule.map_coe]
    /- I'm uncertain how to best resolve this `erw`.
    ```
    have : (↑(toLieSubalgebra R L I).toSubmodule : Set L) = I := rfl
    rw [this]
    simp [h]
    ```
    works, but still feels awkward. There are missing `

中文:
定理 map_of_image
  条件: (h : f '' I = J)
  结论: I.map f = J
  证明: by
  apply le_antisymm
  · rw [map, LieSubmodule.lieSpan_le, Submodule.map_coe]
    /- I'm uncertain how to best resolve this `erw`.
    ```
    have : (↑(toLieSubalgebra R L I).toSubmodule : Set L) = I := rfl
    rw [this]
    simp [h]
    ```
    works, but still feels awkward. There are missing `

Depends on / 依赖: LieSubmodule, LieSubmodule.lieSpan_le, Submodule, Submodule.map_coe, le_antisymm, lieSpan_le, map_coe
-/
theorem map_of_image (h : f '' I = J) : I.map f = J := by
  apply le_antisymm
  · rw [map, LieSubmodule.lieSpan_le, Submodule.map_coe]
    /- I'm uncertain how to best resolve this `erw`.
    ```
    have : (↑(toLieSubalgebra R L I).toSubmodule : Set L) = I := rfl
    rw [this]
    simp [h]
    ```
    works, but still feels awkward. There are missing `simp` lemmas here.`
    -/
    erw [h]
  · rw [← SetLike.coe_subset_coe, ← h]; exact LieSubmodule.subset_lieSpan

/--
Instance `subsingleton_of_bot` / 实例 `subsingleton_of_bot`

English:
instance subsingleton_of_bot
  signature: : Subsingleton (LieIdeal R (⊥ : LieIdeal R L))
  body: by
  apply subsingleton_of_bot_eq_top
  subsingleton

中文:
实例 subsingleton_of_bot
  签名: : Subsingleton (LieIdeal R (⊥ : LieIdeal R L))
  定义体: by
  apply subsingleton_of_bot_eq_top
  subsingleton

Depends on / 依赖: subsingleton, subsingleton_of_bot_eq_top
-/
instance subsingleton_of_bot : Subsingleton (LieIdeal R (⊥ : LieIdeal R L)) := by
  apply subsingleton_of_bot_eq_top
  subsingleton

end LieIdeal

namespace LieHom
variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable (f : L ->ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: : LieIdeal R L
  body: LieIdeal.comap f ⊥

中文:
定义 ker
  签名: : LieIdeal R L
  定义体: LieIdeal.comap f ⊥

Depends on / 依赖: LieIdeal, LieIdeal.comap
-/
def ker : LieIdeal R L :=
  LieIdeal.comap f ⊥

/--
Definition of `idealRange` / `idealRange` 的定义

English:
definition idealRange
  signature: : LieIdeal R L'
  body: LieSubmodule.lieSpan R L' f.range

中文:
定义 idealRange
  签名: : LieIdeal R L'
  定义体: LieSubmodule.lieSpan R L' f.range

Depends on / 依赖: LieSubmodule, LieSubmodule.lieSpan, f.range, lieSpan
-/
def idealRange : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' f.range

/--
theorem `idealRange_eq_lieSpan_range` / 定理 `idealRange_eq_lieSpan_range`

English:
theorem idealRange_eq_lieSpan_range
  statement: f.idealRange = LieSubmodule.lieSpan R L' f.range
  proof: rfl

中文:
定理 idealRange_eq_lieSpan_range
  结论: f.idealRange = LieSubmodule.lieSpan R L' f.range
  证明: rfl
-/
theorem idealRange_eq_lieSpan_range : f.idealRange = LieSubmodule.lieSpan R L' f.range :=
  rfl

/--
theorem `idealRange_eq_map` / 定理 `idealRange_eq_map`

English:
theorem idealRange_eq_map
  statement: f.idealRange = LieIdeal.map f ⊤
  proof: by
  ext
  simp only [idealRange, range_eq_map]
  rfl

中文:
定理 idealRange_eq_map
  结论: f.idealRange = LieIdeal.map f ⊤
  证明: by
  ext
  simp only [idealRange, range_eq_map]
  rfl

Depends on / 依赖: idealRange, range_eq_map
-/
theorem idealRange_eq_map : f.idealRange = LieIdeal.map f ⊤ := by
  ext
  simp only [idealRange, range_eq_map]
  rfl

/--
Definition of `IsIdealMorphism` / `IsIdealMorphism` 的定义

English:
definition IsIdealMorphism
  signature: : Prop
  body: (f.idealRange : LieSubalgebra R L') = f.range

中文:
定义 IsIdealMorphism
  签名: : 命题
  定义体: (f.idealRange : LieSubalgebra R L') = f.range

Depends on / 依赖: LieSubalgebra, f.idealRange, f.range, idealRange
-/
def IsIdealMorphism : Prop :=
  (f.idealRange : LieSubalgebra R L') = f.range

/--
theorem `isIdealMorphism_def` / 定理 `isIdealMorphism_def`

English:
theorem isIdealMorphism_def
  statement: f.IsIdealMorphism ↔ (f.idealRange : LieSubalgebra R L') = f.range
  proof: Iff.rfl

中文:
定理 isIdealMorphism_def
  结论: f.IsIdealMorphism ↔ (f.idealRange : LieSubalgebra R L') = f.range
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isIdealMorphism_def : f.IsIdealMorphism ↔ (f.idealRange : LieSubalgebra R L') = f.range :=
  Iff.rfl

variable {f} in
/--
theorem `IsIdealMorphism.eq` / 定理 `IsIdealMorphism.eq`

English:
theorem IsIdealMorphism.eq
  given: (hf : f.IsIdealMorphism)
  statement: f.idealRange = f.range
  proof: hf

中文:
定理 IsIdealMorphism.eq
  条件: (hf : f.IsIdealMorphism)
  结论: f.idealRange = f.range
  证明: hf
-/
theorem IsIdealMorphism.eq (hf : f.IsIdealMorphism) : f.idealRange = f.range := hf

/--
theorem `isIdealMorphism_iff` / 定理 `isIdealMorphism_iff`

English:
theorem isIdealMorphism_iff
  statement: f.IsIdealMorphism ↔ forall (x : L') (y : L), exists z : L, ⁅x, f y⁆ = f z
  proof: by
  simp only [isIdealMorphism_def, idealRange_eq_lieSpan_range, ←
    LieSubalgebra.toSubmodule_inj, ← f.range.coe_toSubmodule,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff,
    LieSubalgebra.mem_toSubmodule, mem_range, exists_imp,
    Submodule.exists_lieSub

中文:
定理 isIdealMorphism_iff
  结论: f.IsIdealMorphism ↔ 对任意 (x : L') (y : L), 存在 z : L, ⁅x, f y⁆ = f z
  证明: by
  simp only [isIdealMorphism_def, idealRange_eq_lieSpan_range, ←
    LieSubalgebra.toSubmodule_inj, ← f.range.coe_toSubmodule,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff,
    LieSubalgebra.mem_toSubmodule, mem_range, exists_imp,
    Submodule.exists_lieSub

Depends on / 依赖: LieIdeal, LieIdeal.toLieSubalgebra_toSubmodule, LieSubalgebra, LieSubalgebra.mem_toSubmodule, LieSubalgebra.toSubmodule_inj, LieSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff, Submodule, Submodule.exists_lieSubmodule_coe_eq_iff, coe_lieSpan_submodule_eq_iff, coe_toSubmodule, exists_imp, exists_lieSubmodule_coe_eq_iff, f.range.coe_toSubmodule, hz.symm, idealRange_eq_lieSpan_range, isIdealMorphism_def, mem_range, mem_toSubmodule, toLieSubalgebra_toSubmodule
-/
theorem isIdealMorphism_iff : f.IsIdealMorphism ↔ forall (x : L') (y : L), exists z : L, ⁅x, f y⁆ = f z := by
  simp only [isIdealMorphism_def, idealRange_eq_lieSpan_range, ←
    LieSubalgebra.toSubmodule_inj, ← f.range.coe_toSubmodule,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff,
    LieSubalgebra.mem_toSubmodule, mem_range, exists_imp,
    Submodule.exists_lieSubmodule_coe_eq_iff]
  constructor
  · intro h x y; obtain ⟨z, hz⟩ := h x (f y) y rfl; use z; exact hz.symm
  · intro h x y z hz; obtain ⟨w, hw⟩ := h x z; use w; rw [← hw, hz]

/--
theorem `range_subset_idealRange` / 定理 `range_subset_idealRange`

English:
theorem range_subset_idealRange
  statement: (f.range : Set L') subseteq f.idealRange
  proof: LieSubmodule.subset_lieSpan

中文:
定理 range_subset_idealRange
  结论: (f.range : Set L') subseteq f.idealRange
  证明: LieSubmodule.subset_lieSpan

Depends on / 依赖: LieSubmodule, LieSubmodule.subset_lieSpan, subset_lieSpan
-/
theorem range_subset_idealRange : (f.range : Set L') subseteq f.idealRange :=
  LieSubmodule.subset_lieSpan

/--
theorem `map_le_idealRange` / 定理 `map_le_idealRange`

English:
theorem map_le_idealRange
  statement: I.map f <= f.idealRange
  proof: by
  rw [f.idealRange_eq_map]
  exact LieIdeal.map_mono le_top

中文:
定理 map_le_idealRange
  结论: I.map f <= f.idealRange
  证明: by
  rw [f.idealRange_eq_map]
  exact LieIdeal.map_mono le_top

Depends on / 依赖: LieIdeal, LieIdeal.map_mono, f.idealRange_eq_map, idealRange_eq_map, le_top, map_mono
-/
theorem map_le_idealRange : I.map f <= f.idealRange := by
  rw [f.idealRange_eq_map]
  exact LieIdeal.map_mono le_top

/--
theorem `ker_le_comap` / 定理 `ker_le_comap`

English:
theorem ker_le_comap
  statement: f.ker <= J.comap f
  proof: LieIdeal.comap_mono bot_le

@[simp]

中文:
定理 ker_le_comap
  结论: f.ker <= J.comap f
  证明: LieIdeal.comap_mono bot_le

@[simp]

Depends on / 依赖: LieIdeal, LieIdeal.comap_mono, bot_le, comap_mono
-/
theorem ker_le_comap : f.ker <= J.comap f :=
  LieIdeal.comap_mono bot_le

@[simp]
/--
theorem `ker_toSubmodule` / 定理 `ker_toSubmodule`

English:
theorem ker_toSubmodule
  statement: LieSubmodule.toSubmodule (ker f) = LinearMap.ker (f : L ->ₗ[R] L')
  proof: rfl

中文:
定理 ker_toSubmodule
  结论: LieSubmodule.toSubmodule (ker f) = LinearMap.ker (f : L ->ₗ[R] L')
  证明: rfl
-/
theorem ker_toSubmodule : LieSubmodule.toSubmodule (ker f) = LinearMap.ker (f : L ->ₗ[R] L') :=
  rfl

variable {f} in
@[simp]
/--
theorem `mem_ker` / 定理 `mem_ker`

English:
theorem mem_ker
  given: {x : L}
  statement: x in ker f ↔ f x = 0
  proof: show x in LieSubmodule.toSubmodule (f.ker) ↔ _ by
    simp only [ker_toSubmodule, LinearMap.mem_ker, coe_toLinearMap]

中文:
定理 mem_ker
  条件: {x : L}
  结论: x in ker f ↔ f x = 0
  证明: show x in LieSubmodule.toSubmodule (f.ker) ↔ _ by
    simp only [ker_toSubmodule, LinearMap.mem_ker, coe_toLinearMap]

Depends on / 依赖: LieSubmodule, LieSubmodule.toSubmodule, LinearMap, LinearMap.mem_ker, coe_toLinearMap, f.ker, ker_toSubmodule, mem_ker, toSubmodule
-/
theorem mem_ker {x : L} : x in ker f ↔ f x = 0 :=
  show x in LieSubmodule.toSubmodule (f.ker) ↔ _ by
    simp only [ker_toSubmodule, LinearMap.mem_ker, coe_toLinearMap]

/--
theorem `mem_idealRange` / 定理 `mem_idealRange`

English:
theorem mem_idealRange
  given: (x : L)
  statement: f x in idealRange f
  proof: by
  rw [idealRange_eq_map]
  exact LieIdeal.mem_map (LieSubmodule.mem_top x)

@[simp]

中文:
定理 mem_idealRange
  条件: (x : L)
  结论: f x in idealRange f
  证明: by
  rw [idealRange_eq_map]
  exact LieIdeal.mem_map (LieSubmodule.mem_top x)

@[simp]

Depends on / 依赖: LieIdeal, LieIdeal.mem_map, LieSubmodule, LieSubmodule.mem_top, idealRange_eq_map, mem_map, mem_top
-/
theorem mem_idealRange (x : L) : f x in idealRange f := by
  rw [idealRange_eq_map]
  exact LieIdeal.mem_map (LieSubmodule.mem_top x)

@[simp]
/--
theorem `mem_idealRange_iff` / 定理 `mem_idealRange_iff`

English:
theorem mem_idealRange_iff
  given: (h : IsIdealMorphism f) {y : L'}
  proof: by
  rw [f.isIdealMorphism_def] at h
  rw [← LieSubmodule.mem_coe]; rw [← LieIdeal.coe_toLieSubalgebra]; rw [h]; rw [f.coe_range]; rw [Set.mem_range]

中文:
定理 mem_idealRange_iff
  条件: (h : IsIdealMorphism f) {y : L'}
  证明: by
  rw [f.isIdealMorphism_def] at h
  rw [← LieSubmodule.mem_coe]; rw [← LieIdeal.coe_toLieSubalgebra]; rw [h]; rw [f.coe_range]; rw [Set.mem_range]

Depends on / 依赖: LieIdeal, LieIdeal.coe_toLieSubalgebra, LieSubmodule, LieSubmodule.mem_coe, Set.mem_range, coe_range, coe_toLieSubalgebra, f.coe_range, f.isIdealMorphism_def, isIdealMorphism_def, mem_coe, mem_range
-/
theorem mem_idealRange_iff (h : IsIdealMorphism f) {y : L'} :
    y in idealRange f ↔ exists x : L, f x = y := by
  rw [f.isIdealMorphism_def] at h
  rw [← LieSubmodule.mem_coe]; rw [← LieIdeal.coe_toLieSubalgebra]; rw [h]; rw [f.coe_range]; rw [Set.mem_range]

/--
theorem `le_ker_iff` / 定理 `le_ker_iff`

English:
theorem le_ker_iff
  statement: I <= f.ker ↔ forall x, x in I -> f x = 0
  proof: by
  constructor <;> intro h x hx
  · specialize h hx; rw [mem_ker] at h; exact h
  · rw [mem_ker]; apply h x hx

中文:
定理 le_ker_iff
  结论: I <= f.ker ↔ 对任意 x, x in I -> f x = 0
  证明: by
  constructor <;> intro h x hx
  · specialize h hx; rw [mem_ker] at h; exact h
  · rw [mem_ker]; apply h x hx

Depends on / 依赖: mem_ker, specialize
-/
theorem le_ker_iff : I <= f.ker ↔ forall x, x in I -> f x = 0 := by
  constructor <;> intro h x hx
  · specialize h hx; rw [mem_ker] at h; exact h
  · rw [mem_ker]; apply h x hx

/--
theorem `ker_eq_bot` / 定理 `ker_eq_bot`

English:
theorem ker_eq_bot
  statement: f.ker = ⊥ ↔ Function.Injective f
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [ker_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [LinearMap.ker_eq_bot]; rw [coe_toLinearMap]

@[simp]

中文:
定理 ker_eq_bot
  结论: f.ker = ⊥ ↔ Function.Injective f
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [ker_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [LinearMap.ker_eq_bot]; rw [coe_toLinearMap]

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.bot_toSubmodule, LieSubmodule.toSubmodule_inj, LinearMap, LinearMap.ker_eq_bot, bot_toSubmodule, coe_toLinearMap, ker_eq_bot, ker_toSubmodule, toSubmodule_inj
-/
theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [ker_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [LinearMap.ker_eq_bot]; rw [coe_toLinearMap]

@[simp]
/--
theorem `range_toSubmodule` / 定理 `range_toSubmodule`

English:
theorem range_toSubmodule
  statement: (f.range : Submodule R L') = LinearMap.range (f : L ->ₗ[R] L')
  proof: rfl

中文:
定理 range_toSubmodule
  结论: (f.range : Submodule R L') = LinearMap.range (f : L ->ₗ[R] L')
  证明: rfl
-/
theorem range_toSubmodule : (f.range : Submodule R L') = LinearMap.range (f : L ->ₗ[R] L') :=
  rfl

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  statement: f.range = ⊤ ↔ Function.Surjective f
  proof: by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieSubalgebra.top_toSubmodule]
  exact LinearMap.range_eq_top

@[simp]

中文:
定理 range_eq_top
  结论: f.range = ⊤ ↔ Function.Surjective f
  证明: by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieSubalgebra.top_toSubmodule]
  exact LinearMap.range_eq_top

@[simp]

Depends on / 依赖: LieSubalgebra, LieSubalgebra.toSubmodule_inj, LieSubalgebra.top_toSubmodule, LinearMap, LinearMap.range_eq_top, range_eq_top, range_toSubmodule, toSubmodule_inj, top_toSubmodule
-/
theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieSubalgebra.top_toSubmodule]
  exact LinearMap.range_eq_top

@[simp]
/--
theorem `idealRange_eq_top_of_surjective` / 定理 `idealRange_eq_top_of_surjective`

English:
theorem idealRange_eq_top_of_surjective
  given: (h : Function.Surjective f)
  statement: f.idealRange = ⊤
  proof: by
  rw [← f.range_eq_top] at h
  rw [idealRange_eq_lieSpan_range]; rw [h]; rw [← LieSubalgebra.coe_toSubmodule]; rw [←
    LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.top_toSubmodule]; rw [LieSubalgebra.top_toSubmodule]; rw [LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use ⊤
  exact LieSubmodul

中文:
定理 idealRange_eq_top_of_surjective
  条件: (h : Function.Surjective f)
  结论: f.idealRange = ⊤
  证明: by
  rw [← f.range_eq_top] at h
  rw [idealRange_eq_lieSpan_range]; rw [h]; rw [← LieSubalgebra.coe_toSubmodule]; rw [←
    LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.top_toSubmodule]; rw [LieSubalgebra.top_toSubmodule]; rw [LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use ⊤
  exact LieSubmodul

Depends on / 依赖: LieSubalgebra, LieSubalgebra.coe_toSubmodule, LieSubalgebra.top_toSubmodule, LieSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff, LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule, coe_lieSpan_submodule_eq_iff, coe_toSubmodule, f.range_eq_top, idealRange_eq_lieSpan_range, range_eq_top, toSubmodule_inj, top_toSubmodule
-/
theorem idealRange_eq_top_of_surjective (h : Function.Surjective f) : f.idealRange = ⊤ := by
  rw [← f.range_eq_top] at h
  rw [idealRange_eq_lieSpan_range]; rw [h]; rw [← LieSubalgebra.coe_toSubmodule]; rw [←
    LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.top_toSubmodule]; rw [LieSubalgebra.top_toSubmodule]; rw [LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use ⊤
  exact LieSubmodule.top_toSubmodule

/--
theorem `isIdealMorphism_of_surjective` / 定理 `isIdealMorphism_of_surjective`

English:
theorem isIdealMorphism_of_surjective
  given: (h : Function.Surjective f)
  statement: f.IsIdealMorphism
  proof: by
  rw [isIdealMorphism_def]; rw [f.idealRange_eq_top_of_surjective h]; rw [f.range_eq_top.mpr h]; rw [LieIdeal.top_toLieSubalgebra]

中文:
定理 isIdealMorphism_of_surjective
  条件: (h : Function.Surjective f)
  结论: f.IsIdealMorphism
  证明: by
  rw [isIdealMorphism_def]; rw [f.idealRange_eq_top_of_surjective h]; rw [f.range_eq_top.mpr h]; rw [LieIdeal.top_toLieSubalgebra]

Depends on / 依赖: LieIdeal, LieIdeal.top_toLieSubalgebra, f.idealRange_eq_top_of_surjective, f.range_eq_top.mpr, idealRange_eq_top_of_surjective, isIdealMorphism_def, range_eq_top, top_toLieSubalgebra
-/
theorem isIdealMorphism_of_surjective (h : Function.Surjective f) : f.IsIdealMorphism := by
  rw [isIdealMorphism_def]; rw [f.idealRange_eq_top_of_surjective h]; rw [f.range_eq_top.mpr h]; rw [LieIdeal.top_toLieSubalgebra]

end LieHom

namespace LieIdeal
variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable {f : L ->ₗ⁅R⁆ L'} {I I₂ : LieIdeal R L} {J : LieIdeal R L'}

@[simp]
/--
theorem `map_eq_bot_iff` / 定理 `map_eq_bot_iff`

English:
theorem map_eq_bot_iff
  statement: I.map f = ⊥ ↔ I <= f.ker
  proof: by
  rw [← le_bot_iff]
  exact LieIdeal.map_le_iff_le_comap

中文:
定理 map_eq_bot_iff
  结论: I.map f = ⊥ ↔ I <= f.ker
  证明: by
  rw [← le_bot_iff]
  exact LieIdeal.map_le_iff_le_comap

Depends on / 依赖: LieIdeal, LieIdeal.map_le_iff_le_comap, le_bot_iff, map_le_iff_le_comap
-/
theorem map_eq_bot_iff : I.map f = ⊥ ↔ I <= f.ker := by
  rw [← le_bot_iff]
  exact LieIdeal.map_le_iff_le_comap

/--
theorem `coe_map_of_surjective` / 定理 `coe_map_of_surjective`

English:
theorem coe_map_of_surjective
  given: (h : Function.Surjective f)
  proof: by
  let J : LieIdeal R L' :=
    { (I : Submodule R L).map (f : L ->ₗ[R] L') with
      lie_mem := fun {x y} hy => by
        have hy' : exists x : L, x in I ∧ f x = y := by simpa [hy]
        obtain ⟨z₂, hz₂, rfl⟩ := hy'
        obtain ⟨z₁, rfl⟩ := h x
        simp only [LieHom.coe_toLinearMap, Se

中文:
定理 coe_map_of_surjective
  条件: (h : Function.Surjective f)
  证明: by
  let J : LieIdeal R L' :=
    { (I : Submodule R L).map (f : L ->ₗ[R] L') with
      lie_mem := fun {x y} hy => by
        have hy' : exists x : L, x in I ∧ f x = y := by simpa [hy]
        obtain ⟨z₂, hz₂, rfl⟩ := hy'
        obtain ⟨z₁, rfl⟩ := h x
        simp only [LieHom.coe_toLinearMap, Se

Depends on / 依赖: I.lie_mem, LieHom, LieHom.coe_toLinearMap, LieIdeal, LieSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff, Set.mem_image, SetLike, SetLike.mem_coe, Submodule, Submodule.map_coe, Submodule.mem_carrier, coe_lieSpan_submodule_eq_iff, coe_toLinearMap, f.map_lie, lie_mem, map_coe, map_lie, mem_carrier, mem_coe
-/
theorem coe_map_of_surjective (h : Function.Surjective f) :
    LieSubmodule.toSubmodule (I.map f) = (LieSubmodule.toSubmodule I).map (f : L ->ₗ[R] L') := by
  let J : LieIdeal R L' :=
    { (I : Submodule R L).map (f : L ->ₗ[R] L') with
      lie_mem := fun {x y} hy => by
        have hy' : exists x : L, x in I ∧ f x = y := by simpa [hy]
        obtain ⟨z₂, hz₂, rfl⟩ := hy'
        obtain ⟨z₁, rfl⟩ := h x
        simp only [LieHom.coe_toLinearMap, SetLike.mem_coe, Set.mem_image, Submodule.mem_carrier,
          Submodule.map_coe]
        use ⁅z₁, z₂⁆
        exact ⟨I.lie_mem hz₂, f.map_lie z₁ z₂⟩ }
  rw [map]; rw [toLieSubalgebra_toSubmodule]; rw [LieSubmodule.coe_lieSpan_submodule_eq_iff]
  exact ⟨J, rfl⟩

/--
theorem `mem_map_of_surjective` / 定理 `mem_map_of_surjective`

English:
theorem mem_map_of_surjective
  given: {y : L'} (h₁ : Function.Surjective f) (h₂ : y in I.map f)
  proof: by
  rw [← LieSubmodule.mem_toSubmodule]; rw [coe_map_of_surjective h₁]; rw [Submodule.mem_map] at h₂
  obtain ⟨x, hx, rfl⟩ := h₂
  use ⟨x, hx⟩
  rw [LieHom.coe_toLinearMap]

中文:
定理 mem_map_of_surjective
  条件: {y : L'} (h₁ : Function.Surjective f) (h₂ : y in I.map f)
  证明: by
  rw [← LieSubmodule.mem_toSubmodule]; rw [coe_map_of_surjective h₁]; rw [Submodule.mem_map] at h₂
  obtain ⟨x, hx, rfl⟩ := h₂
  use ⟨x, hx⟩
  rw [LieHom.coe_toLinearMap]

Depends on / 依赖: LieHom, LieHom.coe_toLinearMap, LieSubmodule, LieSubmodule.mem_toSubmodule, Submodule, Submodule.mem_map, coe_map_of_surjective, coe_toLinearMap, mem_map, mem_toSubmodule
-/
theorem mem_map_of_surjective {y : L'} (h₁ : Function.Surjective f) (h₂ : y in I.map f) :
    exists x : I, f x = y := by
  rw [← LieSubmodule.mem_toSubmodule]; rw [coe_map_of_surjective h₁]; rw [Submodule.mem_map] at h₂
  obtain ⟨x, hx, rfl⟩ := h₂
  use ⟨x, hx⟩
  rw [LieHom.coe_toLinearMap]

/--
theorem `bot_of_map_eq_bot` / 定理 `bot_of_map_eq_bot`

English:
theorem bot_of_map_eq_bot
  given: {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥)
  proof: by
  rw [← f.ker_eq_bot]; rw [LieHom.ker] at h₁
  rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [h₁] at h₂
  rw [eq_bot_iff]; exact h₂

中文:
定理 bot_of_map_eq_bot
  条件: {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥)
  证明: by
  rw [← f.ker_eq_bot]; rw [LieHom.ker] at h₁
  rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [h₁] at h₂
  rw [eq_bot_iff]; exact h₂

Depends on / 依赖: LieHom, LieHom.ker, eq_bot_iff, f.ker_eq_bot, ker_eq_bot, map_le_iff_le_comap
-/
theorem bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥) :
    I = ⊥ := by
  rw [← f.ker_eq_bot]; rw [LieHom.ker] at h₁
  rw [eq_bot_iff]; rw [map_le_iff_le_comap]; rw [h₁] at h₂
  rw [eq_bot_iff]; exact h₂

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂)
  body: Submodule.inclusion (show I₁.toSubmodule <= I₂.toSubmodule from h)
  map_lie' := rfl

@[simp]

中文:
定义 inclusion
  签名: {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂)
  定义体: Submodule.inclusion (show I₁.toSubmodule <= I₂.toSubmodule from h)
  map_lie' := rfl

@[simp]

Depends on / 依赖: Submodule, Submodule.inclusion, inclusion, toSubmodule
-/
def inclusion {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) : I₁ ->ₗ⁅R⁆ I₂ where
  __ := Submodule.inclusion (show I₁.toSubmodule <= I₂.toSubmodule from h)
  map_lie' := rfl

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) (x : I₁)
  statement: (inclusion h x : L) = x
  proof: rfl

中文:
定理 coe_inclusion
  条件: {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) (x : I₁)
  结论: (inclusion h x : L) = x
  证明: rfl
-/
theorem coe_inclusion {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) (x : I₁) : (inclusion h x : L) = x :=
  rfl

/--
theorem `inclusion_apply` / 定理 `inclusion_apply`

English:
theorem inclusion_apply
  given: {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) (x : I₁)
  proof: rfl

中文:
定理 inclusion_apply
  条件: {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) (x : I₁)
  证明: rfl
-/
theorem inclusion_apply {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) (x : I₁) :
    inclusion h x = ⟨x.1, h x.2⟩ :=
  rfl

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂)
  proof: fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

中文:
定理 inclusion_injective
  条件: {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂)
  证明: fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

Depends on / 依赖: SetLike, SetLike.coe_eq_coe, Subtype, Subtype.mk_eq_mk, coe_eq_coe, imp_self, inclusion_apply, mk_eq_mk
-/
theorem inclusion_injective {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) :
    Function.Injective (inclusion h) :=
  fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

/--
theorem `map_sup_ker_eq_map` / 定理 `map_sup_ker_eq_map`

English:
theorem map_sup_ker_eq_map
  statement: LieIdeal.map f (I ⊔ f.ker) = LieIdeal.map f I
  proof: by
  refine le_antisymm ?_ (LieIdeal.map_mono le_sup_left)
  apply LieSubmodule.lieSpan_mono
  rintro x ⟨y, hy₁, hy₂⟩
  rw [← hy₂]
  erw [LieSubmodule.mem_sup] at hy₁
  obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁
  rw [← hy]
  rw [map_add]; rw [f.coe_toLinearMap]; rw [LieHom.mem_ker.mp hz₂]; rw [add_zero];

中文:
定理 map_sup_ker_eq_map
  结论: LieIdeal.map f (I ⊔ f.ker) = LieIdeal.map f I
  证明: by
  refine le_antisymm ?_ (LieIdeal.map_mono le_sup_left)
  apply LieSubmodule.lieSpan_mono
  rintro x ⟨y, hy₁, hy₂⟩
  rw [← hy₂]
  erw [LieSubmodule.mem_sup] at hy₁
  obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁
  rw [← hy]
  rw [map_add]; rw [f.coe_toLinearMap]; rw [LieHom.mem_ker.mp hz₂]; rw [add_zero];

Depends on / 依赖: LieHom, LieHom.mem_ker.mp, LieIdeal, LieIdeal.map_mono, LieSubmodule, LieSubmodule.lieSpan_mono, LieSubmodule.mem_sup, add_zero, coe_toLinearMap, f.coe_toLinearMap, le_antisymm, le_sup_left, lieSpan_mono, map_add, map_mono, mem_ker, mem_sup
-/
theorem map_sup_ker_eq_map : LieIdeal.map f (I ⊔ f.ker) = LieIdeal.map f I := by
  refine le_antisymm ?_ (LieIdeal.map_mono le_sup_left)
  apply LieSubmodule.lieSpan_mono
  rintro x ⟨y, hy₁, hy₂⟩
  rw [← hy₂]
  erw [LieSubmodule.mem_sup] at hy₁
  obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁
  rw [← hy]
  rw [map_add]; rw [f.coe_toLinearMap]; rw [LieHom.mem_ker.mp hz₂]; rw [add_zero]; exact ⟨z₁, hz₁, rfl⟩

@[simp]
/--
theorem `map_sup_ker_eq_map'` / 定理 `map_sup_ker_eq_map'`

English:
theorem map_sup_ker_eq_map'
  proof: by
  simpa using map_sup_ker_eq_map (f := f)

@[simp]

中文:
定理 map_sup_ker_eq_map'
  证明: by
  simpa using map_sup_ker_eq_map (f := f)

@[simp]

Depends on / 依赖: map_sup_ker_eq_map
-/
theorem map_sup_ker_eq_map' :
    LieIdeal.map f I ⊔ LieIdeal.map f (LieHom.ker f) = LieIdeal.map f I := by
  simpa using map_sup_ker_eq_map (f := f)

@[simp]
/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (h : f.IsIdealMorphism)
  statement: map f (comap f J) = f.idealRange ⊓ J
  proof: by
  apply le_antisymm
  · rw [le_inf_iff]; exact ⟨f.map_le_idealRange _, map_comap_le⟩
  · rw [f.isIdealMorphism_def] at h
    rw [← SetLike.coe_subset_coe]; rw [LieSubmodule.coe_inf]; rw [← coe_toLieSubalgebra]; rw [h]
    rintro y ⟨⟨x, h₁⟩, h₂⟩; rw [← h₁] at h₂ ⊢; exact mem_map h₂

@[simp]

中文:
定理 map_comap_eq
  条件: (h : f.IsIdealMorphism)
  结论: map f (comap f J) = f.idealRange ⊓ J
  证明: by
  apply le_antisymm
  · rw [le_inf_iff]; exact ⟨f.map_le_idealRange _, map_comap_le⟩
  · rw [f.isIdealMorphism_def] at h
    rw [← SetLike.coe_subset_coe]; rw [LieSubmodule.coe_inf]; rw [← coe_toLieSubalgebra]; rw [h]
    rintro y ⟨⟨x, h₁⟩, h₂⟩; rw [← h₁] at h₂ ⊢; exact mem_map h₂

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.coe_inf, SetLike, SetLike.coe_subset_coe, coe_inf, coe_subset_coe, coe_toLieSubalgebra, f.isIdealMorphism_def, f.map_le_idealRange, isIdealMorphism_def, le_antisymm, le_inf_iff, map_comap_le, map_le_idealRange, mem_map
-/
theorem map_comap_eq (h : f.IsIdealMorphism) : map f (comap f J) = f.idealRange ⊓ J := by
  apply le_antisymm
  · rw [le_inf_iff]; exact ⟨f.map_le_idealRange _, map_comap_le⟩
  · rw [f.isIdealMorphism_def] at h
    rw [← SetLike.coe_subset_coe]; rw [LieSubmodule.coe_inf]; rw [← coe_toLieSubalgebra]; rw [h]
    rintro y ⟨⟨x, h₁⟩, h₂⟩; rw [← h₁] at h₂ ⊢; exact mem_map h₂

@[simp]
/--
theorem `comap_map_eq` / 定理 `comap_map_eq`

English:
theorem comap_map_eq
  given: (h : ↑(map f I) = f '' I)
  statement: comap f (map f I) = I ⊔ f.ker
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [comap_toSubmodule]; rw [I.map_toSubmodule f h]; rw [LieSubmodule.sup_toSubmodule]; rw [f.ker_toSubmodule]; rw [Submodule.comap_map_eq]

中文:
定理 comap_map_eq
  条件: (h : ↑(map f I) = f '' I)
  结论: comap f (map f I) = I ⊔ f.ker
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [comap_toSubmodule]; rw [I.map_toSubmodule f h]; rw [LieSubmodule.sup_toSubmodule]; rw [f.ker_toSubmodule]; rw [Submodule.comap_map_eq]

Depends on / 依赖: I.map_toSubmodule, LieSubmodule, LieSubmodule.sup_toSubmodule, LieSubmodule.toSubmodule_inj, Submodule, Submodule.comap_map_eq, comap_map_eq, comap_toSubmodule, f.ker_toSubmodule, ker_toSubmodule, map_toSubmodule, sup_toSubmodule, toSubmodule_inj
-/
theorem comap_map_eq (h : ↑(map f I) = f '' I) : comap f (map f I) = I ⊔ f.ker := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [comap_toSubmodule]; rw [I.map_toSubmodule f h]; rw [LieSubmodule.sup_toSubmodule]; rw [f.ker_toSubmodule]; rw [Submodule.comap_map_eq]

variable (f I J)

/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : I ->ₗ⁅R⁆ L
  body: (I : LieSubalgebra R L).incl

@[simp]

中文:
定义 incl
  签名: : I ->ₗ⁅R⁆ L
  定义体: (I : LieSubalgebra R L).incl

@[simp]

Depends on / 依赖: LieSubalgebra
-/
def incl : I ->ₗ⁅R⁆ L :=
  (I : LieSubalgebra R L).incl

@[simp]
/--
theorem `incl_range` / 定理 `incl_range`

English:
theorem incl_range
  statement: I.incl.range = I
  proof: (I : LieSubalgebra R L).incl_range

@[simp]

中文:
定理 incl_range
  结论: I.incl.range = I
  证明: (I : LieSubalgebra R L).incl_range

@[simp]

Depends on / 依赖: LieSubalgebra, incl_range
-/
theorem incl_range : I.incl.range = I :=
  (I : LieSubalgebra R L).incl_range

@[simp]
/--
theorem `incl_apply` / 定理 `incl_apply`

English:
theorem incl_apply
  given: (x : I)
  statement: I.incl x = x
  proof: rfl

@[simp]

中文:
定理 incl_apply
  条件: (x : I)
  结论: I.incl x = x
  证明: rfl

@[simp]
-/
theorem incl_apply (x : I) : I.incl x = x :=
  rfl

@[simp]
/--
theorem `incl_coe` / 定理 `incl_coe`

English:
theorem incl_coe
  statement: (I.incl.toLinearMap : I ->ₗ[R] L) = (I : Submodule R L).subtype
  proof: rfl

中文:
定理 incl_coe
  结论: (I.incl.toLinearMap : I ->ₗ[R] L) = (I : Submodule R L).subtype
  证明: rfl
-/
theorem incl_coe : (I.incl.toLinearMap : I ->ₗ[R] L) = (I : Submodule R L).subtype :=
  rfl

/--
lemma `incl_injective` / 引理 `incl_injective`

English:
lemma incl_injective
  given: (I : LieIdeal R L)
  statement: Function.Injective I.incl
  proof: Subtype.val_injective

@[simp]

中文:
引理 incl_injective
  条件: (I : LieIdeal R L)
  结论: Function.Injective I.incl
  证明: Subtype.val_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.val_injective, val_injective
-/
lemma incl_injective (I : LieIdeal R L) : Function.Injective I.incl :=
  Subtype.val_injective

@[simp]
/--
theorem `comap_incl_self` / 定理 `comap_incl_self`

English:
theorem comap_incl_self
  statement: comap I.incl I = ⊤
  proof: by ext; simp

@[simp]

中文:
定理 comap_incl_self
  结论: comap I.incl I = ⊤
  证明: by ext; simp

@[simp]
-/
theorem comap_incl_self : comap I.incl I = ⊤ := by ext; simp

@[simp]
/--
theorem `ker_incl` / 定理 `ker_incl`

English:
theorem ker_incl
  statement: I.incl.ker = ⊥
  proof: by ext; simp

@[simp]

中文:
定理 ker_incl
  结论: I.incl.ker = ⊥
  证明: by ext; simp

@[simp]
-/
theorem ker_incl : I.incl.ker = ⊥ := by ext; simp

@[simp]
/--
theorem `incl_idealRange` / 定理 `incl_idealRange`

English:
theorem incl_idealRange
  statement: I.incl.idealRange = I
  proof: by
  rw [LieHom.idealRange_eq_lieSpan_range]; rw [← LieSubalgebra.coe_toSubmodule]; rw [←
    LieSubmodule.toSubmodule_inj]; rw [incl_range]; rw [toLieSubalgebra_toSubmodule]; rw [LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use I

中文:
定理 incl_idealRange
  结论: I.incl.idealRange = I
  证明: by
  rw [LieHom.idealRange_eq_lieSpan_range]; rw [← LieSubalgebra.coe_toSubmodule]; rw [←
    LieSubmodule.toSubmodule_inj]; rw [incl_range]; rw [toLieSubalgebra_toSubmodule]; rw [LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use I

Depends on / 依赖: LieHom, LieHom.idealRange_eq_lieSpan_range, LieSubalgebra, LieSubalgebra.coe_toSubmodule, LieSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff, LieSubmodule.toSubmodule_inj, Module, Semiring, Semiring.toOppositeModule, coe_lieSpan_submodule_eq_iff, coe_toSubmodule, idealRange_eq_lieSpan_range, incl_range, toLieSubalgebra_toSubmodule, toOppositeModule, toSubmodule_inj
-/
theorem incl_idealRange : I.incl.idealRange = I := by
  rw [LieHom.idealRange_eq_lieSpan_range]; rw [← LieSubalgebra.coe_toSubmodule]; rw [←
    LieSubmodule.toSubmodule_inj]; rw [incl_range]; rw [toLieSubalgebra_toSubmodule]; rw [LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use I

/--
theorem `incl_isIdealMorphism` / 定理 `incl_isIdealMorphism`

English:
theorem incl_isIdealMorphism
  statement: I.incl.IsIdealMorphism
  proof: by
  rw [I.incl.isIdealMorphism_def]; rw [incl_idealRange]
  exact (I : LieSubalgebra R L).incl_range.symm

中文:
定理 incl_isIdealMorphism
  结论: I.incl.IsIdealMorphism
  证明: by
  rw [I.incl.isIdealMorphism_def]; rw [incl_idealRange]
  exact (I : LieSubalgebra R L).incl_range.symm

Depends on / 依赖: I.incl.isIdealMorphism_def, LieSubalgebra, incl_idealRange, incl_range, incl_range.symm, isIdealMorphism_def
-/
theorem incl_isIdealMorphism : I.incl.IsIdealMorphism := by
  rw [I.incl.isIdealMorphism_def]; rw [incl_idealRange]
  exact (I : LieSubalgebra R L).incl_range.symm

variable {I}

/--
theorem `comap_incl_eq_top` / 定理 `comap_incl_eq_top`

English:
theorem comap_incl_eq_top
  statement: I₂.comap I.incl = ⊤ ↔ I <= I₂
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieIdeal.comap_toSubmodule]; rw [LieSubmodule.top_toSubmodule]; rw [incl_coe]
  simp_rw [toLieSubalgebra_toSubmodule]
  rw [Submodule.comap_subtype_eq_top]; rw [LieSubmodule.toSubmodule_le_toSubmodule]

中文:
定理 comap_incl_eq_top
  结论: I₂.comap I.incl = ⊤ ↔ I <= I₂
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieIdeal.comap_toSubmodule]; rw [LieSubmodule.top_toSubmodule]; rw [incl_coe]
  simp_rw [toLieSubalgebra_toSubmodule]
  rw [Submodule.comap_subtype_eq_top]; rw [LieSubmodule.toSubmodule_le_toSubmodule]
-/
@[simp] theorem comap_incl_eq_top : I₂.comap I.incl = ⊤ ↔ I <= I₂ := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieIdeal.comap_toSubmodule]; rw [LieSubmodule.top_toSubmodule]; rw [incl_coe]
  simp_rw [toLieSubalgebra_toSubmodule]
  rw [Submodule.comap_subtype_eq_top]; rw [LieSubmodule.toSubmodule_le_toSubmodule]

/--
theorem `comap_incl_eq_bot` / 定理 `comap_incl_eq_bot`

English:
theorem comap_incl_eq_bot
  statement: I₂.comap I.incl = ⊥ ↔ Disjoint I I₂
  proof: by
  rw [disjoint_iff]; rw [← LieSubmodule.toSubmodule_inj]; rw [LieIdeal.comap_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.inf_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [incl_coe]
  simp_rw [toLieSubalgebra_toSubmodule]
  rw [← Su

中文:
定理 comap_incl_eq_bot
  结论: I₂.comap I.incl = ⊥ ↔ Disjoint I I₂
  证明: by
  rw [disjoint_iff]; rw [← LieSubmodule.toSubmodule_inj]; rw [LieIdeal.comap_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.inf_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [incl_coe]
  simp_rw [toLieSubalgebra_toSubmodule]
  rw [← Su
-/
@[simp] theorem comap_incl_eq_bot : I₂.comap I.incl = ⊥ ↔ Disjoint I I₂ := by
  rw [disjoint_iff]; rw [← LieSubmodule.toSubmodule_inj]; rw [LieIdeal.comap_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.inf_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [incl_coe]
  simp_rw [toLieSubalgebra_toSubmodule]
  rw [← Submodule.disjoint_iff_comap_eq_bot]; rw [disjoint_iff]

end LieIdeal

end LieSubmoduleMapAndComap

section TopEquiv

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L]
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]
variable {R L}
variable [LieAlgebra R L] [LieModule R L M]

/--
Definition of `LieIdeal.topEquiv` / `LieIdeal.topEquiv` 的定义

English:
definition LieIdeal.topEquiv
  signature: : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L
  body: LieSubalgebra.topEquiv

中文:
定义 LieIdeal.topEquiv
  签名: : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L
  定义体: LieSubalgebra.topEquiv

Depends on / 依赖: LieSubalgebra, LieSubalgebra.topEquiv, topEquiv
-/
def LieIdeal.topEquiv : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L :=
  LieSubalgebra.topEquiv

/--
theorem `LieIdeal.topEquiv_apply` / 定理 `LieIdeal.topEquiv_apply`

English:
theorem LieIdeal.topEquiv_apply
  given: (x : (⊤ : LieIdeal R L))
  statement: LieIdeal.topEquiv x = x
  proof: rfl

中文:
定理 LieIdeal.topEquiv_apply
  条件: (x : (⊤ : LieIdeal R L))
  结论: LieIdeal.topEquiv x = x
  证明: rfl
-/
theorem LieIdeal.topEquiv_apply (x : (⊤ : LieIdeal R L)) : LieIdeal.topEquiv x = x :=
  rfl

end TopEquiv
