/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!

# Local rings homomorphisms

We prove basic properties of local rings homomorphisms.

-/

public section

variable {R S T : Type*}
section

variable [Semiring R] [Semiring S] [Semiring T]

@[instance]
/--
theorem `isLocalHom_id` / 定理 `isLocalHom_id`

English:
theorem isLocalHom_id
  given: (R : Type*) [Semiring R]
  statement: IsLocalHom (RingHom.id R) where
  proof: id

中文:
定理 isLocalHom_id
  条件: (R : 类型) [Semiring R]
  结论: IsLocalHom (RingHom.id R) where
  证明: id
-/
theorem isLocalHom_id (R : Type*) [Semiring R] : IsLocalHom (RingHom.id R) where
  map_nonunit _ := id

-- see note [lower instance priority]
@[instance 100]
/--
theorem `isLocalHom_toRingHom` / 定理 `isLocalHom_toRingHom`

English:
theorem isLocalHom_toRingHom
  statement: {F : Type*} [FunLike F R S]
  proof: ⟨IsLocalHom.map_nonunit (f := f)⟩

@[instance]

中文:
定理 isLocalHom_toRingHom
  结论: {F : 类型} [FunLike F R S]
  证明: ⟨IsLocalHom.map_nonunit (f := f)⟩

@[instance]

Depends on / 依赖: IsLocalHom, IsLocalHom.map_nonunit, map_nonunit
-/
theorem isLocalHom_toRingHom {F : Type*} [FunLike F R S]
    [RingHomClass F R S] (f : F) [IsLocalHom f] : IsLocalHom (f : R ->+* S) :=
  ⟨IsLocalHom.map_nonunit (f := f)⟩

@[instance]
/--
theorem `RingHom.isLocalHom_comp` / 定理 `RingHom.isLocalHom_comp`

English:
theorem RingHom.isLocalHom_comp
  statement: (g : S ->+* T) (f : R ->+* S) [IsLocalHom g]
  proof: IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

中文:
定理 RingHom.isLocalHom_comp
  结论: (g : S ->+* T) (f : R ->+* S) [IsLocalHom g]
  证明: IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

Depends on / 依赖: IsLocalHom, IsLocalHom.map_nonunit, map_nonunit
-/
theorem RingHom.isLocalHom_comp (g : S ->+* T) (f : R ->+* S) [IsLocalHom g]
    [IsLocalHom f] : IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

/--
theorem `isLocalHom_of_comp` / 定理 `isLocalHom_of_comp`

English:
theorem isLocalHom_of_comp
  given: (f : R ->+* S) (g : S ->+* T) [IsLocalHom (g.comp f)]
  proof: ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (g.isUnit_map ha)⟩

中文:
定理 isLocalHom_of_comp
  条件: (f : R ->+* S) (g : S ->+* T) [IsLocalHom (g.comp f)]
  证明: ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (g.isUnit_map ha)⟩

Depends on / 依赖: g.comp, g.isUnit_map, isUnit_map, isUnit_map_iff
-/
theorem isLocalHom_of_comp (f : R ->+* S) (g : S ->+* T) [IsLocalHom (g.comp f)] :
    IsLocalHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (g.isUnit_map ha)⟩

/--
theorem `RingHom.domain_isLocalRing` / 定理 `RingHom.domain_isLocalRing`

English:
theorem RingHom.domain_isLocalRing
  given: [IsLocalRing S] (f : R ->+* S) [IsLocalHom f]
  proof: f.domain_nontrivial
  isUnit_or_isUnit_of_add_one {a b} h := Or.imp
    (isUnit_of_map_unit f a) (isUnit_of_map_unit f b)
    (IsLocalRing.isUnit_or_isUnit_of_add_one (by rw [← map_add, h, map_one]))

中文:
定理 RingHom.domain_isLocalRing
  条件: [IsLocalRing S] (f : R ->+* S) [IsLocalHom f]
  证明: f.domain_nontrivial
  isUnit_or_isUnit_of_add_one {a b} h := Or.imp
    (isUnit_of_map_unit f a) (isUnit_of_map_unit f b)
    (IsLocalRing.isUnit_or_isUnit_of_add_one (by rw [← map_add, h, map_one]))

Depends on / 依赖: domain_nontrivial, f.domain_nontrivial
-/
theorem RingHom.domain_isLocalRing [IsLocalRing S] (f : R ->+* S) [IsLocalHom f] :
    IsLocalRing R where
  toNontrivial := f.domain_nontrivial
  isUnit_or_isUnit_of_add_one {a b} h := Or.imp
    (isUnit_of_map_unit f a) (isUnit_of_map_unit f b)
    (IsLocalRing.isUnit_or_isUnit_of_add_one (by rw [← map_add, h, map_one]))

end

section

open IsLocalRing

variable [CommSemiring R] [IsLocalRing R] [CommSemiring S] [IsLocalRing S]

/--
theorem `map_nonunit` / 定理 `map_nonunit`

English:
theorem map_nonunit
  given: (f : R ->+* S) [IsLocalHom f] (a : R) (h : a in maximalIdeal R)
  proof: fun H => h isUnit_of_map_unit f a H

中文:
定理 map_nonunit
  条件: (f : R ->+* S) [IsLocalHom f] (a : R) (h : a in maximalIdeal R)
  证明: fun H => h isUnit_of_map_unit f a H

Depends on / 依赖: isUnit_of_map_unit
-/
theorem map_nonunit (f : R ->+* S) [IsLocalHom f] (a : R) (h : a in maximalIdeal R) :
f a in maximalIdeal S := fun H => h isUnit_of_map_unit f a H

end

namespace IsLocalRing

section

variable [CommSemiring R] [IsLocalRing R] [CommSemiring S] [IsLocalRing S]

/-- A ring homomorphism between local rings is a local ring hom iff it reflects units,
i.e. any preimage of a unit is still a unit. -/
@[stacks 07BJ]
/--
theorem `local_hom_TFAE` / 定理 `local_hom_TFAE`

English:
theorem local_hom_TFAE
  given: (f : R ->+* S)
  proof: by
  tfae_have 1 -> 2
  | _, _, ⟨a, ha, rfl⟩ => map_nonunit f a ha
  tfae_have 2 -> 4 := Set.image_subset_iff.1
  tfae_have 3 ↔ 4 := Ideal.map_le_iff_le_comap
  tfae_have 4 -> 1 := fun h => ⟨fun x => not_imp_not.1 (@h x)⟩
  tfae_have 1 -> 5
  | _ => by ext; exact not_iff_not.2 (isUnit_map_iff f _)
 

中文:
定理 local_hom_TFAE
  条件: (f : R ->+* S)
  证明: by
  tfae_have 1 -> 2
  | _, _, ⟨a, ha, rfl⟩ => map_nonunit f a ha
  tfae_have 2 -> 4 := Set.image_subset_iff.1
  tfae_have 3 ↔ 4 := Ideal.map_le_iff_le_comap
  tfae_have 4 -> 1 := fun h => ⟨fun x => not_imp_not.1 (@h x)⟩
  tfae_have 1 -> 5
  | _ => by ext; exact not_iff_not.2 (isUnit_map_iff f _)
 

Depends on / 依赖: Ideal.map_le_iff_le_comap, Set.image_subset_iff, h.symm, image_subset_iff, isUnit_map_iff, le_of_eq, map_le_iff_le_comap, map_nonunit, not_iff_not, not_imp_not, tfae_finish, tfae_have
-/
theorem local_hom_TFAE (f : R ->+* S) :
    List.TFAE
      [IsLocalHom f, f '' maximalIdeal R subseteq maximalIdeal S,
        (maximalIdeal R).map f <= maximalIdeal S, maximalIdeal R <= (maximalIdeal S).comap f,
        (maximalIdeal S).comap f = maximalIdeal R] := by
  tfae_have 1 -> 2
  | _, _, ⟨a, ha, rfl⟩ => map_nonunit f a ha
  tfae_have 2 -> 4 := Set.image_subset_iff.1
  tfae_have 3 ↔ 4 := Ideal.map_le_iff_le_comap
  tfae_have 4 -> 1 := fun h => ⟨fun x => not_imp_not.1 (@h x)⟩
  tfae_have 1 -> 5
  | _ => by ext; exact not_iff_not.2 (isUnit_map_iff f _)
  tfae_have 5 -> 4 := fun h => le_of_eq h.symm
  tfae_finish

/--
lemma `maximalIdeal_comap` / 引理 `maximalIdeal_comap`

English:
lemma maximalIdeal_comap
  given: (f : R ->+* S) [IsLocalHom f]
  statement: (maximalIdeal S).comap f = maximalIdeal R
  proof: ((local_hom_TFAE _).out 0 4).mp ‹_›

中文:
引理 maximalIdeal_comap
  条件: (f : R ->+* S) [IsLocalHom f]
  结论: (maximalIdeal S).comap f = maximalIdeal R
  证明: ((local_hom_TFAE _).out 0 4).mp ‹_›

Depends on / 依赖: local_hom_TFAE
-/
lemma maximalIdeal_comap (f : R ->+* S) [IsLocalHom f] : (maximalIdeal S).comap f = maximalIdeal R :=
  ((local_hom_TFAE _).out 0 4).mp ‹_›

/--
theorem `map_maximalIdeal_le` / 定理 `map_maximalIdeal_le`

English:
theorem map_maximalIdeal_le
  given: (f : R ->+* S) [IsLocalHom f]
  proof: by
  rw [Ideal.map_le_iff_le_comap]; rw [IsLocalRing.maximalIdeal_comap]

中文:
定理 map_maximalIdeal_le
  条件: (f : R ->+* S) [IsLocalHom f]
  证明: by
  rw [Ideal.map_le_iff_le_comap]; rw [IsLocalRing.maximalIdeal_comap]

Depends on / 依赖: Ideal.map_le_iff_le_comap, IsLocalRing, IsLocalRing.maximalIdeal_comap, map_le_iff_le_comap, maximalIdeal_comap
-/
theorem map_maximalIdeal_le (f : R ->+* S) [IsLocalHom f] :
    (maximalIdeal R).map f <= maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap]; rw [IsLocalRing.maximalIdeal_comap]

/--
theorem `map_maximalIdeal_lt_top` / 定理 `map_maximalIdeal_lt_top`

English:
theorem map_maximalIdeal_lt_top
  given: (f : R ->+* S) [IsLocalHom f]
  statement: (maximalIdeal R).map f < ⊤
  proof: (map_maximalIdeal_le f).trans_lt (maximalIdeal.isMaximal S).lt_top

中文:
定理 map_maximalIdeal_lt_top
  条件: (f : R ->+* S) [IsLocalHom f]
  结论: (maximalIdeal R).map f < ⊤
  证明: (map_maximalIdeal_le f).trans_lt (maximalIdeal.isMaximal S).lt_top

Depends on / 依赖: isMaximal, lt_top, map_maximalIdeal_le, maximalIdeal, maximalIdeal.isMaximal, trans_lt
-/
theorem map_maximalIdeal_lt_top (f : R ->+* S) [IsLocalHom f] : (maximalIdeal R).map f < ⊤ :=
  (map_maximalIdeal_le f).trans_lt (maximalIdeal.isMaximal S).lt_top

end

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  statement: [CommSemiring R] [IsLocalRing R] [Semiring S] [Nontrivial S] (f : R ->+* S)
  proof: of_isUnit_or_isUnit_of_isUnit_add (by
    intro a b hab
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    rw [← map_add] at hab
    exact
      (isUnit_or_isUnit_of_isUnit_add <| IsLocalHom.map_nonunit _ hab).imp f.isUnit_map
        f.isUnit_map)

中文:
定理 of_surjective
  结论: [CommSemiring R] [IsLocalRing R] [Semiring S] [Nontrivial S] (f : R ->+* S)
  证明: of_isUnit_or_isUnit_of_isUnit_add (by
    intro a b hab
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    rw [← map_add] at hab
    exact
      (isUnit_or_isUnit_of_isUnit_add <| IsLocalHom.map_nonunit _ hab).imp f.isUnit_map
        f.isUnit_map)

Depends on / 依赖: IsLocalHom, IsLocalHom.map_nonunit, f.isUnit_map, isUnit_map, isUnit_or_isUnit_of_isUnit_add, map_add, map_nonunit, of_isUnit_or_isUnit_of_isUnit_add
-/
theorem of_surjective [CommSemiring R] [IsLocalRing R] [Semiring S] [Nontrivial S] (f : R ->+* S)
    [IsLocalHom f] (hf : Function.Surjective f) : IsLocalRing S :=
  of_isUnit_or_isUnit_of_isUnit_add (by
    intro a b hab
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    rw [← map_add] at hab
    exact
      (isUnit_or_isUnit_of_isUnit_add <| IsLocalHom.map_nonunit _ hab).imp f.isUnit_map
        f.isUnit_map)

/--
lemma `_root_.IsLocalHom.of_surjective` / 引理 `_root_.IsLocalHom.of_surjective`

English:
lemma _root_.IsLocalHom.of_surjective
  statement: [CommRing R] [CommRing S] [Nontrivial S] [IsLocalRing R]
  proof: by
  have := IsLocalRing.of_surjective' f ‹_›
  refine ((local_hom_TFAE f).out 3 0).mp ?_
  have := Ideal.comap_isMaximal_of_surjective f hf (K := maximalIdeal S)
  exact ((maximal_ideal_unique R).unique (inferInstanceAs (maximalIdeal R).IsMaximal) this).le

alias _root_.Function.Surjective.isLocalH

中文:
引理 _root_.IsLocalHom.of_surjective
  结论: [CommRing R] [CommRing S] [Nontrivial S] [IsLocalRing R]
  证明: by
  have := IsLocalRing.of_surjective' f ‹_›
  refine ((local_hom_TFAE f).out 3 0).mp ?_
  have := Ideal.comap_isMaximal_of_surjective f hf (K := maximalIdeal S)
  exact ((maximal_ideal_unique R).unique (inferInstanceAs (maximalIdeal R).IsMaximal) this).le

alias _root_.Function.Surjective.isLocalH

Depends on / 依赖: Ideal.comap_isMaximal_of_surjective, IsLocalRing, IsLocalRing.of_surjective, IsMaximal, comap_isMaximal_of_surjective, local_hom_TFAE, maximalIdeal, maximal_ideal_unique, of_surjective, unique
-/
lemma _root_.IsLocalHom.of_surjective [CommRing R] [CommRing S] [Nontrivial S] [IsLocalRing R]
    (f : R ->+* S) (hf : Function.Surjective f) :
    IsLocalHom f := by
  have := IsLocalRing.of_surjective' f ‹_›
  refine ((local_hom_TFAE f).out 3 0).mp ?_
  have := Ideal.comap_isMaximal_of_surjective f hf (K := maximalIdeal S)
  exact ((maximal_ideal_unique R).unique (inferInstanceAs (maximalIdeal R).IsMaximal) this).le

alias _root_.Function.Surjective.isLocalHom := _root_.IsLocalHom.of_surjective

/--
theorem `surjective_units_map_of_local_ringHom` / 定理 `surjective_units_map_of_local_ringHom`

English:
theorem surjective_units_map_of_local_ringHom
  statement: [Semiring R] [Semiring S] (f : R ->+* S)
  proof: by
  intro a
  obtain ⟨b, hb⟩ := hf (a : S)
  use (isUnit_of_map_unit f b (by rw [hb]; exact Units.isUnit _)).unit
  ext
  exact hb

中文:
定理 surjective_units_map_of_local_ringHom
  结论: [Semiring R] [Semiring S] (f : R ->+* S)
  证明: by
  intro a
  obtain ⟨b, hb⟩ := hf (a : S)
  use (isUnit_of_map_unit f b (by rw [hb]; exact Units.isUnit _)).unit
  ext
  exact hb

Depends on / 依赖: Units.isUnit, isUnit, isUnit_of_map_unit
-/
theorem surjective_units_map_of_local_ringHom [Semiring R] [Semiring S] (f : R ->+* S)
    (hf : Function.Surjective f) (h : IsLocalHom f) :
    Function.Surjective (Units.map <| f.toMonoidHom) := by
  intro a
  obtain ⟨b, hb⟩ := hf (a : S)
  use (isUnit_of_map_unit f b (by rw [hb]; exact Units.isUnit _)).unit
  ext
  exact hb

-- see Note [lower instance priority]
/-- Every ring hom `f : K →+* R` from a division ring `K` to a nontrivial ring `R` is a
local ring hom. -/
instance (priority := 100) {K R} [DivisionRing K] [CommRing R] [Nontrivial R]
    (f : K ->+* R) : IsLocalHom f where
  map_nonunit r hr := by simpa only [isUnit_iff_ne_zero, ne_eq, map_eq_zero] using hr.ne_zero

/--
lemma `map_maximalIdeal_of_surjective` / 引理 `map_maximalIdeal_of_surjective`

English:
lemma map_maximalIdeal_of_surjective
  statement: [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  proof: by
  let := IsLocalHom.of_surjective f hf
  rw [← maximalIdeal_comap f]; rw [Ideal.map_comap_of_surjective f hf]

@[simp]

中文:
引理 map_maximalIdeal_of_surjective
  结论: [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  证明: by
  let := IsLocalHom.of_surjective f hf
  rw [← maximalIdeal_comap f]; rw [Ideal.map_comap_of_surjective f hf]

@[simp]

Depends on / 依赖: Ideal.map_comap_of_surjective, IsLocalHom, IsLocalHom.of_surjective, map_comap_of_surjective, maximalIdeal_comap, of_surjective
-/
lemma map_maximalIdeal_of_surjective [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R ->+* S) (hf : Function.Surjective f) : (maximalIdeal R).map f = maximalIdeal S := by
  let := IsLocalHom.of_surjective f hf
  rw [← maximalIdeal_comap f]; rw [Ideal.map_comap_of_surjective f hf]

@[simp]
/--
lemma `map_ringEquiv_maximalIdeal` / 引理 `map_ringEquiv_maximalIdeal`

English:
lemma map_ringEquiv_maximalIdeal
  statement: [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  proof: map_maximalIdeal_of_surjective (e : R ->+* S) e.surjective

中文:
引理 map_ringEquiv_maximalIdeal
  结论: [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  证明: map_maximalIdeal_of_surjective (e : R ->+* S) e.surjective

Depends on / 依赖: e.surjective, map_maximalIdeal_of_surjective, surjective
-/
lemma map_ringEquiv_maximalIdeal [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) : (maximalIdeal R).map e = maximalIdeal S :=
  map_maximalIdeal_of_surjective (e : R ->+* S) e.surjective

end IsLocalRing

namespace RingEquiv

/--
theorem `isLocalRing` / 定理 `isLocalRing`

English:
theorem isLocalRing
  statement: {A B : Type*} [CommSemiring A] [IsLocalRing A] [Semiring B]
  proof: haveI := e.symm.toEquiv.nontrivial
  IsLocalRing.of_surjective (e : A ->+* B) e.surjective

中文:
定理 isLocalRing
  结论: {A B : 类型} [CommSemiring A] [IsLocalRing A] [Semiring B]
  证明: haveI := e.symm.toEquiv.nontrivial
  IsLocalRing.of_surjective (e : A ->+* B) e.surjective
-/
protected theorem isLocalRing {A B : Type*} [CommSemiring A] [IsLocalRing A] [Semiring B]
    (e : A ≃+* B) : IsLocalRing B :=
  haveI := e.symm.toEquiv.nontrivial
  IsLocalRing.of_surjective (e : A ->+* B) e.surjective

end RingEquiv

instance {R : Type*} [CommRing R] [IsLocalRing R] {n : Nat} [Nontrivial (ZMod n)] (f : R ->+* ZMod n) :
    IsLocalHom f :=
  (ZMod.ringHom_surjective f).isLocalHom
