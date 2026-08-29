/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Local Ring Properties of Equalizers and Pullbacks

In this file we provide basic lemmas for the equalizers the pullbacks and of ring homomorphisms
and algebra homomorphisms. We show that they preserve the property of being a local ring under
suitable conditions.

## Main definitions

* `RingHom.pullback`: The pullback of two ring homomorphisms `f : R →+* T` and `g : S →+* T`,
  defined as the subring of `R × S` consisting of pairs `(r, s)` such that `f r = g s`.

* `RingHom.pullbackFst`, `RingHom.pullbackSnd`: The canonical projection maps from the
  pullback to `R` and `S`.

## Main results

* `RingHom.isLocalRing_eqLocus`: The equalizer of two ring homomorphisms from a local
  ring is again a local ring.

* `RingHom.isLocalRing_pullback`: The pullback of `f : R →+* T` and `g : S →+* T` is a
  local ring, provided that `R` is a local ring and `g` is a local homomorphism.

-/

@[expose] public section

namespace RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T]

/--
theorem `isLocalRing_eqLocus` / 定理 `isLocalRing_eqLocus`

English:
theorem isLocalRing_eqLocus
  given: [IsLocalRing R] (f g : R ->+* T)
  statement: IsLocalRing (f.eqLocus g)
  proof: (f.eqLocus g).subtype.domain_isLocalRing

中文:
定理 isLocalRing_eqLocus
  条件: [IsLocalRing R] (f g : R ->+* T)
  结论: IsLocalRing (f.eqLocus g)
  证明: (f.eqLocus g).subtype.domain_isLocalRing

Depends on / 依赖: domain_isLocalRing, eqLocus, f.eqLocus, subtype, subtype.domain_isLocalRing
-/
theorem isLocalRing_eqLocus [IsLocalRing R] (f g : R ->+* T) : IsLocalRing (f.eqLocus g) :=
  (f.eqLocus g).subtype.domain_isLocalRing

/--
Definition of `pullback` / `pullback` 的定义

English:
abbreviation pullback
  signature: (f : R ->+* T) (g : S ->+* T)
  body: (f.comp (RingHom.fst R S)).eqLocus g.comp (RingHom.snd R S)

中文:
缩写 pullback
  签名: (f : R ->+* T) (g : S ->+* T)
  定义体: (f.comp (RingHom.fst R S)).eqLocus g.comp (RingHom.snd R S)

Depends on / 依赖: RingHom, RingHom.fst, RingHom.snd, eqLocus, f.comp, g.comp
-/
abbrev pullback (f : R ->+* T) (g : S ->+* T) : Subring (R × S) :=
(f.comp (RingHom.fst R S)).eqLocus g.comp (RingHom.snd R S)

/--
Definition of `pullbackFst` / `pullbackFst` 的定义

English:
abbreviation pullbackFst
  signature: (f : R ->+* T) (g : S ->+* T)
  body: (RingHom.fst R S).comp (RingHom.pullback f g).subtype

中文:
缩写 pullbackFst
  签名: (f : R ->+* T) (g : S ->+* T)
  定义体: (RingHom.fst R S).comp (RingHom.pullback f g).subtype

Depends on / 依赖: RingHom, RingHom.fst, RingHom.pullback, pullback, subtype
-/
abbrev pullbackFst (f : R ->+* T) (g : S ->+* T) : f.pullback g ->+* R :=
  (RingHom.fst R S).comp (RingHom.pullback f g).subtype

/--
Definition of `pullbackSnd` / `pullbackSnd` 的定义

English:
abbreviation pullbackSnd
  signature: (f : R ->+* T) (g : S ->+* T)
  body: (RingHom.snd R S).comp (f.pullback g).subtype

中文:
缩写 pullbackSnd
  签名: (f : R ->+* T) (g : S ->+* T)
  定义体: (RingHom.snd R S).comp (f.pullback g).subtype

Depends on / 依赖: RingHom, RingHom.snd, f.pullback, pullback, subtype
-/
abbrev pullbackSnd (f : R ->+* T) (g : S ->+* T) : f.pullback g ->+* S :=
  (RingHom.snd R S).comp (f.pullback g).subtype

/--
theorem `pullback_comm_sq` / 定理 `pullback_comm_sq`

English:
theorem pullback_comm_sq
  given: (f : R ->+* T) (g : S ->+* T)
  proof: ext fun x => x.prop

中文:
定理 pullback_comm_sq
  条件: (f : R ->+* T) (g : S ->+* T)
  证明: ext fun x => x.prop

Depends on / 依赖: x.prop
-/
theorem pullback_comm_sq (f : R ->+* T) (g : S ->+* T) :
    f.comp (f.pullbackFst g) = g.comp (f.pullbackSnd g) :=
  ext fun x => x.prop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isUnit_pullback_mk_iff` / 定理 `isUnit_pullback_mk_iff`

English:
theorem isUnit_pullback_mk_iff
  given: (f : R ->+* T) (g : S ->+* T) {a : R × S} (a_in : a in f.pullback g)
  proof: by
  rw [isUnit_eqLocus_mk_iff]; rw [Prod.isUnit_iff]

中文:
定理 isUnit_pullback_mk_iff
  条件: (f : R ->+* T) (g : S ->+* T) {a : R × S} (a_in : a in f.pullback g)
  证明: by
  rw [isUnit_eqLocus_mk_iff]; rw [Prod.isUnit_iff]

Depends on / 依赖: Prod.isUnit_iff, isUnit_eqLocus_mk_iff, isUnit_iff
-/
theorem isUnit_pullback_mk_iff (f : R ->+* T) (g : S ->+* T) {a : R × S} (a_in : a in f.pullback g) :
    IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit a.2 := by
  rw [isUnit_eqLocus_mk_iff]; rw [Prod.isUnit_iff]

/--
Instance `isLocalHom_pullbackFst` / 实例 `isLocalHom_pullbackFst`

English:
instance isLocalHom_pullbackFst
  signature: (f : R ->+* T) (g : S ->+* T) [IsLocalHom g]
  body: fun ⟨⟨_, _⟩, h_in⟩ ha =>
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨ha, isUnit_of_map_unit g _ (h_in ▸ ha.map f)⟩

中文:
实例 isLocalHom_pullbackFst
  签名: (f : R ->+* T) (g : S ->+* T) [IsLocalHom g]
  定义体: fun ⟨⟨_, _⟩, h_in⟩ ha =>
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨ha, isUnit_of_map_unit g _ (h_in ▸ ha.map f)⟩

Depends on / 依赖: h_in
-/
instance isLocalHom_pullbackFst (f : R ->+* T) (g : S ->+* T) [IsLocalHom g] :
    IsLocalHom (f.pullbackFst g) where
  map_nonunit := fun ⟨⟨_, _⟩, h_in⟩ ha =>
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨ha, isUnit_of_map_unit g _ (h_in ▸ ha.map f)⟩

/--
Instance `isLocalHom_pullbackSnd` / 实例 `isLocalHom_pullbackSnd`

English:
instance isLocalHom_pullbackSnd
  signature: (f : R ->+* T) (g : S ->+* T) [IsLocalHom f]
  body: fun ⟨⟨_, _⟩, h_in⟩ ha =>
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨isUnit_of_map_unit f _ (h_in.symm ▸ ha.map g), ha⟩

中文:
实例 isLocalHom_pullbackSnd
  签名: (f : R ->+* T) (g : S ->+* T) [IsLocalHom f]
  定义体: fun ⟨⟨_, _⟩, h_in⟩ ha =>
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨isUnit_of_map_unit f _ (h_in.symm ▸ ha.map g), ha⟩

Depends on / 依赖: h_in
-/
instance isLocalHom_pullbackSnd (f : R ->+* T) (g : S ->+* T) [IsLocalHom f] :
    IsLocalHom (f.pullbackSnd g) where
  map_nonunit := fun ⟨⟨_, _⟩, h_in⟩ ha =>
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨isUnit_of_map_unit f _ (h_in.symm ▸ ha.map g), ha⟩

/--
theorem `surjective_pullbackFst_of_surjective` / 定理 `surjective_pullbackFst_of_surjective`

English:
theorem surjective_pullbackFst_of_surjective
  statement: (f : R ->+* T) (g : S ->+* T)
  proof: fun r => by simpa [eq_comm] using h (f r)

中文:
定理 surjective_pullbackFst_of_surjective
  结论: (f : R ->+* T) (g : S ->+* T)
  证明: fun r => by simpa [eq_comm] using h (f r)

Depends on / 依赖: eq_comm
-/
theorem surjective_pullbackFst_of_surjective (f : R ->+* T) (g : S ->+* T)
    (h : Function.Surjective g) : Function.Surjective (f.pullbackFst g) :=
  fun r => by simpa [eq_comm] using h (f r)

/--
theorem `surjective_pullbackSnd_of_surjective` / 定理 `surjective_pullbackSnd_of_surjective`

English:
theorem surjective_pullbackSnd_of_surjective
  statement: (f : R ->+* T) (g : S ->+* T)
  proof: fun s => by simpa [eq_comm] using h (g s)

中文:
定理 surjective_pullbackSnd_of_surjective
  结论: (f : R ->+* T) (g : S ->+* T)
  证明: fun s => by simpa [eq_comm] using h (g s)

Depends on / 依赖: eq_comm
-/
theorem surjective_pullbackSnd_of_surjective (f : R ->+* T) (g : S ->+* T)
    (h : Function.Surjective f) : Function.Surjective (f.pullbackSnd g) :=
  fun s => by simpa [eq_comm] using h (g s)

/--
theorem `map_pullbackSnd_ker_pullbackFst_eq` / 定理 `map_pullbackSnd_ker_pullbackFst_eq`

English:
theorem map_pullbackSnd_ker_pullbackFst_eq
  given: (f : R ->+* T) (g : S ->+* T)
  proof: by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro ⟨⟨_, _⟩, h⟩
    simp at h ⊢; grind
  · intro s hs
    exact Ideal.mem_map_of_mem (f.pullbackSnd g) (x := ⟨(0, s), by simpa using hs.symm⟩)
      (I := RingHom.ker (f.pullbackFst g)) (by simp)

中文:
定理 map_pullbackSnd_ker_pullbackFst_eq
  条件: (f : R ->+* T) (g : S ->+* T)
  证明: by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro ⟨⟨_, _⟩, h⟩
    simp at h ⊢; grind
  · intro s hs
    exact Ideal.mem_map_of_mem (f.pullbackSnd g) (x := ⟨(0, s), by simpa using hs.symm⟩)
      (I := RingHom.ker (f.pullbackFst g)) (by simp)

Depends on / 依赖: Ideal.map_le_iff_le_comap, Ideal.mem_map_of_mem, RingHom, RingHom.ker, f.pullbackFst, f.pullbackSnd, hs.symm, le_antisymm, map_le_iff_le_comap, mem_map_of_mem, pullbackFst, pullbackSnd
-/
theorem map_pullbackSnd_ker_pullbackFst_eq (f : R ->+* T) (g : S ->+* T) :
    Ideal.map (f.pullbackSnd g) (RingHom.ker (f.pullbackFst g)) = RingHom.ker g := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro ⟨⟨_, _⟩, h⟩
    simp at h ⊢; grind
  · intro s hs
    exact Ideal.mem_map_of_mem (f.pullbackSnd g) (x := ⟨(0, s), by simpa using hs.symm⟩)
      (I := RingHom.ker (f.pullbackFst g)) (by simp)

/--
theorem `isLocalRing_pullback` / 定理 `isLocalRing_pullback`

English:
theorem isLocalRing_pullback
  given: [IsLocalRing R] (f : R ->+* T) (g : S ->+* T) [IsLocalHom g]
  proof: (f.pullbackFst g).domain_isLocalRing

中文:
定理 isLocalRing_pullback
  条件: [IsLocalRing R] (f : R ->+* T) (g : S ->+* T) [IsLocalHom g]
  证明: (f.pullbackFst g).domain_isLocalRing

Depends on / 依赖: domain_isLocalRing, f.pullbackFst, pullbackFst
-/
theorem isLocalRing_pullback [IsLocalRing R] (f : R ->+* T) (g : S ->+* T) [IsLocalHom g] :
    IsLocalRing (f.pullback g) := (f.pullbackFst g).domain_isLocalRing

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommSemiring R]

section Semiring

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/--
Definition of `pullback` / `pullback` 的定义

English:
abbreviation pullback
  signature: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  body: equalizer
  (f.comp (fst R A B)) (g.comp (snd R A B))

中文:
缩写 pullback
  签名: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  定义体: equalizer
  (f.comp (fst R A B)) (g.comp (snd R A B))

Depends on / 依赖: equalizer
-/
abbrev pullback (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) : Subalgebra R (A × B) := equalizer
  (f.comp (fst R A B)) (g.comp (snd R A B))

/--
Definition of `pullbackFst` / `pullbackFst` 的定义

English:
abbreviation pullbackFst
  signature: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  body: (fst R A B).comp (pullback f g).val

中文:
缩写 pullbackFst
  签名: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  定义体: (fst R A B).comp (pullback f g).val

Depends on / 依赖: pullback
-/
abbrev pullbackFst (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) : pullback f g ->ₐ[R] A :=
  (fst R A B).comp (pullback f g).val

/--
Definition of `pullbackSnd` / `pullbackSnd` 的定义

English:
abbreviation pullbackSnd
  signature: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  body: (snd R A B).comp (pullback f g).val

中文:
缩写 pullbackSnd
  签名: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  定义体: (snd R A B).comp (pullback f g).val

Depends on / 依赖: pullback
-/
abbrev pullbackSnd (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) : pullback f g ->ₐ[R] B :=
  (snd R A B).comp (pullback f g).val

/--
theorem `pullback_comm_sq` / 定理 `pullback_comm_sq`

English:
theorem pullback_comm_sq
  given: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  proof: AlgHom.ext fun x => x.prop

中文:
定理 pullback_comm_sq
  条件: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  证明: AlgHom.ext fun x => x.prop

Depends on / 依赖: AlgHom, AlgHom.ext, x.prop
-/
theorem pullback_comm_sq (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) :
    f.comp (pullbackFst f g) = g.comp (pullbackSnd f g) :=
  AlgHom.ext fun x => x.prop

end Semiring

section Ring

variable [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Semiring C] [Algebra R C]

/--
theorem `isUnit_pullback_mk_iff` / 定理 `isUnit_pullback_mk_iff`

English:
theorem isUnit_pullback_mk_iff
  statement: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) {a : A × B}
  proof: RingHom.isUnit_pullback_mk_iff (f : A ->+* C) (g : B ->+* C) a_in

中文:
定理 isUnit_pullback_mk_iff
  结论: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) {a : A × B}
  证明: RingHom.isUnit_pullback_mk_iff (f : A ->+* C) (g : B ->+* C) a_in

Depends on / 依赖: RingHom, RingHom.isUnit_pullback_mk_iff, a_in, isUnit_pullback_mk_iff
-/
theorem isUnit_pullback_mk_iff (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) {a : A × B}
    (a_in : a in f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pullback g) ↔
      IsUnit a.1 ∧ IsUnit a.2 :=
  RingHom.isUnit_pullback_mk_iff (f : A ->+* C) (g : B ->+* C) a_in

/--
theorem `surjective_pullbackFst_of_surjective` / 定理 `surjective_pullbackFst_of_surjective`

English:
theorem surjective_pullbackFst_of_surjective
  statement: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  proof: RingHom.surjective_pullbackFst_of_surjective (f : A ->+* C) (g : B ->+* C) h

中文:
定理 surjective_pullbackFst_of_surjective
  结论: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  证明: RingHom.surjective_pullbackFst_of_surjective (f : A ->+* C) (g : B ->+* C) h

Depends on / 依赖: RingHom, RingHom.surjective_pullbackFst_of_surjective, surjective_pullbackFst_of_surjective
-/
theorem surjective_pullbackFst_of_surjective (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
    (h : Function.Surjective g) : Function.Surjective (pullbackFst f g) :=
  RingHom.surjective_pullbackFst_of_surjective (f : A ->+* C) (g : B ->+* C) h

/--
theorem `surjective_pullbackSnd_of_surjective` / 定理 `surjective_pullbackSnd_of_surjective`

English:
theorem surjective_pullbackSnd_of_surjective
  statement: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  proof: RingHom.surjective_pullbackSnd_of_surjective (f : A ->+* C) (g : B ->+* C) h

中文:
定理 surjective_pullbackSnd_of_surjective
  结论: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  证明: RingHom.surjective_pullbackSnd_of_surjective (f : A ->+* C) (g : B ->+* C) h

Depends on / 依赖: RingHom, RingHom.surjective_pullbackSnd_of_surjective, surjective_pullbackSnd_of_surjective
-/
theorem surjective_pullbackSnd_of_surjective (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
    (h : Function.Surjective f) : Function.Surjective (pullbackSnd f g) :=
  RingHom.surjective_pullbackSnd_of_surjective (f : A ->+* C) (g : B ->+* C) h

/--
theorem `isLocalRing_pullback` / 定理 `isLocalRing_pullback`

English:
theorem isLocalRing_pullback
  statement: [IsLocalRing A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  proof: RingHom.isLocalRing_pullback (f : A ->+* C) (g : B ->+* C)

中文:
定理 isLocalRing_pullback
  结论: [IsLocalRing A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  证明: RingHom.isLocalRing_pullback (f : A ->+* C) (g : B ->+* C)

Depends on / 依赖: RingHom, RingHom.isLocalRing_pullback, isLocalRing_pullback
-/
theorem isLocalRing_pullback [IsLocalRing A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
    [IsLocalHom g] : IsLocalRing (f.pullback g) :=
  RingHom.isLocalRing_pullback (f : A ->+* C) (g : B ->+* C)

end Ring

end AlgHom
