/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Order.CompleteSublattice
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Isotypic modules and isotypic components

## Main definitions

* `IsIsotypicOfType R M S` means that all simple submodules of the `R`-module `M`
  are isomorphic to `S`. Such a module `M` is isomorphic to a finsupp over `S`,
  see `IsIsotypicOfType.linearEquiv_finsupp`.

* `IsIsotypic R M` means that all simple submodules of the `R`-module `M`
  are isomorphic to each other.

* `isotypicComponent R M S` is the sum of all submodules of `M` isomorphic to `S`.

* `isotypicComponents R M` is the set of all nontrivial isotypic components of `M`
  (where `S` is taken to be simple submodules).

* `Submodule.IsFullyInvariant N` means that the submodule `N` of an `R`-module `M` is mapped into
  itself by all endomorphisms of `M`. The `fullyInvariantSubmodule`s of `M` form a complete
  lattice, which is atomic if `M` is semisimple, in which case the atoms are the isotypic
  components of `M`. A fully invariant submodule of a semiring as a module over itself
  is simply a two-sided ideal, see `isFullyInvariant_iff_isTwoSided`.

* `iSupIndep.ringEquiv`, `iSupIndep.algEquiv`: if `M` is the direct sum of fully invariant
  submodules `Nᵢ`, then `End R M` is isomorphic to `Πᵢ End R Nᵢ`. This can be applied to
  the isotypic components of a semisimple module `M`, yielding `IsSemisimpleModule.endAlgEquiv`.

## Keywords

isotypic component, fully invariant submodule

-/

@[expose] public section

universe u

variable (R₀ R : Type*) (M : Type u) (N S : Type*) [CommSemiring R₀]
  [Ring R] [Algebra R₀ R] [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup S] [Module R M] [Module R N] [Module R S]

/--
Definition of `IsIsotypicOfType` / `IsIsotypicOfType` 的定义

English:
definition IsIsotypicOfType
  signature: : Prop
  body: forall (m : Submodule R M) [IsSimpleModule R m], Nonempty (m ≃ₗ[R] S)

中文:
定义 IsIsotypicOfType
  签名: : 命题
  定义体: forall (m : Submodule R M) [IsSimpleModule R m], Nonempty (m ≃ₗ[R] S)

Depends on / 依赖: IsSimpleModule, Nonempty, Submodule
-/
def IsIsotypicOfType : Prop := forall (m : Submodule R M) [IsSimpleModule R m], Nonempty (m ≃ₗ[R] S)

/--
Definition of `IsIsotypic` / `IsIsotypic` 的定义

English:
definition IsIsotypic
  signature: : Prop
  body: forall (m : Submodule R M) [IsSimpleModule R m], IsIsotypicOfType R M m

中文:
定义 IsIsotypic
  签名: : 命题
  定义体: forall (m : Submodule R M) [IsSimpleModule R m], IsIsotypicOfType R M m

Depends on / 依赖: IsIsotypicOfType, IsSimpleModule, Submodule
-/
def IsIsotypic : Prop := forall (m : Submodule R M) [IsSimpleModule R m], IsIsotypicOfType R M m

variable {R M S} in
/--
theorem `IsIsotypicOfType.isIsotypic` / 定理 `IsIsotypicOfType.isIsotypic`

English:
theorem IsIsotypicOfType.isIsotypic
  given: (h : IsIsotypicOfType R M S)
  statement: IsIsotypic R M
  proof: fun m _ m' _ => ⟨(h m').some.trans (h m).some.symm⟩

@[nontriviality]

中文:
定理 IsIsotypicOfType.isIsotypic
  条件: (h : IsIsotypicOfType R M S)
  结论: IsIsotypic R M
  证明: fun m _ m' _ => ⟨(h m').some.trans (h m).some.symm⟩

@[nontriviality]

Depends on / 依赖: some.symm, some.trans
-/
theorem IsIsotypicOfType.isIsotypic (h : IsIsotypicOfType R M S) : IsIsotypic R M :=
  fun m _ m' _ => ⟨(h m').some.trans (h m).some.symm⟩

@[nontriviality]
/--
theorem `IsIsotypicOfType.of_subsingleton` / 定理 `IsIsotypicOfType.of_subsingleton`

English:
theorem IsIsotypicOfType.of_subsingleton
  given: [Subsingleton M]
  statement: IsIsotypicOfType R M S
  proof: fun S => have := IsSimpleModule.nontrivial R S
    (not_subsingleton _ S.subtype_injective.subsingleton).elim

中文:
定理 IsIsotypicOfType.of_subsingleton
  条件: [Subsingleton M]
  结论: IsIsotypicOfType R M S
  证明: fun S => have := IsSimpleModule.nontrivial R S
    (not_subsingleton _ S.subtype_injective.subsingleton).elim

Depends on / 依赖: IsSimpleModule, IsSimpleModule.nontrivial, S.subtype_injective.subsingleton, nontrivial, not_subsingleton, subsingleton, subtype_injective
-/
theorem IsIsotypicOfType.of_subsingleton [Subsingleton M] : IsIsotypicOfType R M S :=
  fun S => have := IsSimpleModule.nontrivial R S
    (not_subsingleton _ S.subtype_injective.subsingleton).elim

/--
theorem `IsIsotypic.of_subsingleton` / 定理 `IsIsotypic.of_subsingleton`

English:
theorem IsIsotypic.of_subsingleton
  given: [Subsingleton M]
  statement: IsIsotypic R M
  proof: fun S => (IsIsotypicOfType.of_subsingleton R M S).isIsotypic S

中文:
定理 IsIsotypic.of_subsingleton
  条件: [Subsingleton M]
  结论: IsIsotypic R M
  证明: fun S => (IsIsotypicOfType.of_subsingleton R M S).isIsotypic S
-/
@[nontriviality] theorem IsIsotypic.of_subsingleton [Subsingleton M] : IsIsotypic R M :=
  fun S => (IsIsotypicOfType.of_subsingleton R M S).isIsotypic S

/--
theorem `IsIsotypicOfType.of_isSimpleModule` / 定理 `IsIsotypicOfType.of_isSimpleModule`

English:
theorem IsIsotypicOfType.of_isSimpleModule
  given: [IsSimpleModule R M]
  statement: IsIsotypicOfType R M M
  proof: fun S hS => by
    rw [isSimpleModule_iff_isAtom]; rw [isAtom_iff_eq_top] at hS
    exact ⟨.trans (.ofEq _ _ hS) Submodule.topEquiv⟩

中文:
定理 IsIsotypicOfType.of_isSimpleModule
  条件: [IsSimpleModule R M]
  结论: IsIsotypicOfType R M M
  证明: fun S hS => by
    rw [isSimpleModule_iff_isAtom]; rw [isAtom_iff_eq_top] at hS
    exact ⟨.trans (.ofEq _ _ hS) Submodule.topEquiv⟩

Depends on / 依赖: Submodule, Submodule.topEquiv, isAtom_iff_eq_top, isSimpleModule_iff_isAtom, topEquiv
-/
theorem IsIsotypicOfType.of_isSimpleModule [IsSimpleModule R M] : IsIsotypicOfType R M M :=
  fun S hS => by
    rw [isSimpleModule_iff_isAtom]; rw [isAtom_iff_eq_top] at hS
    exact ⟨.trans (.ofEq _ _ hS) Submodule.topEquiv⟩

variable {R}

/--
theorem `IsIsotypic.of_self` / 定理 `IsIsotypic.of_self`

English:
theorem IsIsotypic.of_self
  given: [IsSemisimpleRing R] (h : IsIsotypic R R)
  statement: IsIsotypic R M
  proof: fun m _ m' _ =>
    have ⟨_, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m
    have ⟨_, ⟨e'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m'
    have := IsSimpleModule.congr e.symm
    have := IsSimpleModule.congr e'.symm
⟨e'.trans (h _ _).some.trans e.

中文:
定理 IsIsotypic.of_self
  条件: [IsSemisimpleRing R] (h : IsIsotypic R R)
  结论: IsIsotypic R M
  证明: fun m _ m' _ =>
    have ⟨_, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m
    have ⟨_, ⟨e'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m'
    have := IsSimpleModule.congr e.symm
    have := IsSimpleModule.congr e'.symm
⟨e'.trans (h _ _).some.trans e.

Depends on / 依赖: IsSemisimpleRing, IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule, IsSimpleModule, IsSimpleModule.congr, e.symm, exists_linearEquiv_ideal_of_isSimpleModule, some.trans
-/
theorem IsIsotypic.of_self [IsSemisimpleRing R] (h : IsIsotypic R R) : IsIsotypic R M :=
  fun m _ m' _ =>
    have ⟨_, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m
    have ⟨_, ⟨e'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m'
    have := IsSimpleModule.congr e.symm
    have := IsSimpleModule.congr e'.symm
⟨e'.trans (h _ _).some.trans e.symm⟩

variable {M N S}

/--
theorem `IsIsotypicOfType.of_linearEquiv_type` / 定理 `IsIsotypicOfType.of_linearEquiv_type`

English:
theorem IsIsotypicOfType.of_linearEquiv_type
  given: (h : IsIsotypicOfType R M S) (e : S ≃ₗ[R] N)
  proof: fun m _ => ⟨(h m).some.trans e⟩

中文:
定理 IsIsotypicOfType.of_linearEquiv_type
  条件: (h : IsIsotypicOfType R M S) (e : S ≃ₗ[R] N)
  证明: fun m _ => ⟨(h m).some.trans e⟩

Depends on / 依赖: some.trans
-/
theorem IsIsotypicOfType.of_linearEquiv_type (h : IsIsotypicOfType R M S) (e : S ≃ₗ[R] N) :
    IsIsotypicOfType R M N := fun m _ => ⟨(h m).some.trans e⟩

/--
theorem `IsIsotypicOfType.of_injective` / 定理 `IsIsotypicOfType.of_injective`

English:
theorem IsIsotypicOfType.of_injective
  statement: (h : IsIsotypicOfType R N S) (f : M ->ₗ[R] N)
  proof: fun m =>
  have em := m.equivMapOfInjective f inj
  have := IsSimpleModule.congr em.symm
  ⟨em.trans (h (m.map f)).some⟩

中文:
定理 IsIsotypicOfType.of_injective
  结论: (h : IsIsotypicOfType R N S) (f : M ->ₗ[R] N)
  证明: fun m =>
  have em := m.equivMapOfInjective f inj
  have := IsSimpleModule.congr em.symm
  ⟨em.trans (h (m.map f)).some⟩
-/
theorem IsIsotypicOfType.of_injective (h : IsIsotypicOfType R N S) (f : M ->ₗ[R] N)
    (inj : Function.Injective f) : IsIsotypicOfType R M S := fun m =>
  have em := m.equivMapOfInjective f inj
  have := IsSimpleModule.congr em.symm
  ⟨em.trans (h (m.map f)).some⟩

/--
theorem `IsIsotypic.of_injective` / 定理 `IsIsotypic.of_injective`

English:
theorem IsIsotypic.of_injective
  given: (h : IsIsotypic R N) (f : M ->ₗ[R] N) (inj : Function.Injective f)
  proof: fun m _ =>
  have em := (m.equivMapOfInjective f inj).symm
  have := IsSimpleModule.congr em
  ((h (m.map f)).of_injective f inj).of_linearEquiv_type em

中文:
定理 IsIsotypic.of_injective
  条件: (h : IsIsotypic R N) (f : M ->ₗ[R] N) (inj : Function.Injective f)
  证明: fun m _ =>
  have em := (m.equivMapOfInjective f inj).symm
  have := IsSimpleModule.congr em
  ((h (m.map f)).of_injective f inj).of_linearEquiv_type em
-/
theorem IsIsotypic.of_injective (h : IsIsotypic R N) (f : M ->ₗ[R] N) (inj : Function.Injective f) :
    IsIsotypic R M := fun m _ =>
  have em := (m.equivMapOfInjective f inj).symm
  have := IsSimpleModule.congr em
  ((h (m.map f)).of_injective f inj).of_linearEquiv_type em

/--
theorem `LinearEquiv.isIsotypicOfType_iff` / 定理 `LinearEquiv.isIsotypicOfType_iff`

English:
theorem LinearEquiv.isIsotypicOfType_iff
  given: (e : M ≃ₗ[R] N)
  proof: ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

中文:
定理 LinearEquiv.isIsotypicOfType_iff
  条件: (e : M ≃ₗ[R] N)
  证明: ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

Depends on / 依赖: e.injective, e.symm.injective, injective, of_injective
-/
theorem LinearEquiv.isIsotypicOfType_iff (e : M ≃ₗ[R] N) :
    IsIsotypicOfType R M S ↔ IsIsotypicOfType R N S :=
  ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

/--
theorem `LinearEquiv.isIsotypicOfType_iff_type` / 定理 `LinearEquiv.isIsotypicOfType_iff_type`

English:
theorem LinearEquiv.isIsotypicOfType_iff_type
  given: (e : N ≃ₗ[R] S)
  proof: ⟨(·.of_linearEquiv_type e), (·.of_linearEquiv_type e.symm)⟩

中文:
定理 LinearEquiv.isIsotypicOfType_iff_type
  条件: (e : N ≃ₗ[R] S)
  证明: ⟨(·.of_linearEquiv_type e), (·.of_linearEquiv_type e.symm)⟩

Depends on / 依赖: e.symm, of_linearEquiv_type
-/
theorem LinearEquiv.isIsotypicOfType_iff_type (e : N ≃ₗ[R] S) :
    IsIsotypicOfType R M N ↔ IsIsotypicOfType R M S :=
  ⟨(·.of_linearEquiv_type e), (·.of_linearEquiv_type e.symm)⟩

/--
theorem `LinearEquiv.isIsotypic_iff` / 定理 `LinearEquiv.isIsotypic_iff`

English:
theorem LinearEquiv.isIsotypic_iff
  given: (e : M ≃ₗ[R] N)
  statement: IsIsotypic R M ↔ IsIsotypic R N
  proof: ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

中文:
定理 LinearEquiv.isIsotypic_iff
  条件: (e : M ≃ₗ[R] N)
  结论: IsIsotypic R M ↔ IsIsotypic R N
  证明: ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

Depends on / 依赖: e.injective, e.symm.injective, injective, of_injective
-/
theorem LinearEquiv.isIsotypic_iff (e : M ≃ₗ[R] N) : IsIsotypic R M ↔ IsIsotypic R N :=
  ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIsotypicOfType_submodule_iff` / 定理 `isIsotypicOfType_submodule_iff`

English:
theorem isIsotypicOfType_submodule_iff
  given: {N : Submodule R M}
  proof: by
  rw [Subtype.forall']; rw [← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff]
  exact forall₂_congr fun m _ => ⟨fun ⟨e'⟩ => ⟨(e m).symm.tran

中文:
定理 isIsotypicOfType_submodule_iff
  条件: {N : Submodule R M}
  证明: by
  rw [Subtype.forall']; rw [← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff]
  exact forall₂_congr fun m _ => ⟨fun ⟨e'⟩ => ⟨(e m).symm.tran

Depends on / 依赖: Equiv.coe_fn_mk, MapSubtype, N.subtype_injective, Submodule, Submodule.MapSubtype.orderIso, Submodule.equivMapOfInjective, Subtype, Subtype.forall, coe_fn_mk, equivMapOfInjective, forall_congr_right, isSimpleModule_iff, orderIso, simp_rw, subtype_injective, symm.trans
-/
theorem isIsotypicOfType_submodule_iff {N : Submodule R M} :
    IsIsotypicOfType R N S ↔ forall m <= N, [IsSimpleModule R m] -> Nonempty (m ≃ₗ[R] S) := by
  rw [Subtype.forall']; rw [← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff]
  exact forall₂_congr fun m _ => ⟨fun ⟨e'⟩ => ⟨(e m).symm.trans e'⟩, fun ⟨e'⟩ => ⟨(e m).trans e'⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIsotypic_submodule_iff` / 定理 `isIsotypic_submodule_iff`

English:
theorem isIsotypic_submodule_iff
  given: {N : Submodule R M}
  proof: by
  rw [Subtype.forall']; rw [← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff,
    ← (e _).isIsotypicOfType_iff_type, IsIsotypic]

中文:
定理 isIsotypic_submodule_iff
  条件: {N : Submodule R M}
  证明: by
  rw [Subtype.forall']; rw [← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff,
    ← (e _).isIsotypicOfType_iff_type, IsIsotypic]

Depends on / 依赖: Equiv.coe_fn_mk, IsIsotypic, MapSubtype, N.subtype_injective, Submodule, Submodule.MapSubtype.orderIso, Submodule.equivMapOfInjective, Subtype, Subtype.forall, coe_fn_mk, equivMapOfInjective, forall_congr_right, isIsotypicOfType_iff_type, isSimpleModule_iff, orderIso, simp_rw, subtype_injective
-/
theorem isIsotypic_submodule_iff {N : Submodule R M} :
    IsIsotypic R N ↔ forall m <= N, [IsSimpleModule R m] -> IsIsotypicOfType R N m := by
  rw [Subtype.forall']; rw [← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff,
    ← (e _).isIsotypicOfType_iff_type, IsIsotypic]

section Finsupp

variable [IsSemisimpleModule R M]

/--
theorem `IsIsotypicOfType.linearEquiv_finsupp` / 定理 `IsIsotypicOfType.linearEquiv_finsupp`

English:
theorem IsIsotypicOfType.linearEquiv_finsupp
  given: (h : IsIsotypicOfType R M S)
  proof: by
  have ⟨s, e, _, hs⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R M
  classical exact ⟨s, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun m : s => (h m.1).some)
.trans (finsuppLequivDFinsupp R).symm⟩⟩

中文:
定理 IsIsotypicOfType.linearEquiv_finsupp
  条件: (h : IsIsotypicOfType R M S)
  证明: by
  have ⟨s, e, _, hs⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R M
  classical exact ⟨s, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun m : s => (h m.1).some)
.trans (finsuppLequivDFinsupp R).symm⟩⟩

Depends on / 依赖: DFinsupp, DFinsupp.mapRange.linearEquiv, IsSemisimpleModule, IsSemisimpleModule.exists_linearEquiv_dfinsupp, classical, e.trans, exists_linearEquiv_dfinsupp, finsuppLequivDFinsupp, linearEquiv, mapRange
-/
theorem IsIsotypicOfType.linearEquiv_finsupp (h : IsIsotypicOfType R M S) :
    exists ι : Type u, Nonempty (M ≃ₗ[R] ι ->₀ S) := by
  have ⟨s, e, _, hs⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R M
  classical exact ⟨s, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun m : s => (h m.1).some)
.trans (finsuppLequivDFinsupp R).symm⟩⟩

/--
theorem `IsIsotypic.linearEquiv_finsupp` / 定理 `IsIsotypic.linearEquiv_finsupp`

English:
theorem IsIsotypic.linearEquiv_finsupp
  given: [Nontrivial M] (h : IsIsotypic R M)
  proof: by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨ι, e⟩ := (h S).linearEquiv_finsupp
  exact ⟨ι, (isEmpty_or_nonempty ι).resolve_left fun _ => not_subsingleton _ (e.some.subsingleton),
    S, hS, e⟩

中文:
定理 IsIsotypic.linearEquiv_finsupp
  条件: [Nontrivial M] (h : IsIsotypic R M)
  证明: by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨ι, e⟩ := (h S).linearEquiv_finsupp
  exact ⟨ι, (isEmpty_or_nonempty ι).resolve_left fun _ => not_subsingleton _ (e.some.subsingleton),
    S, hS, e⟩

Depends on / 依赖: IsAtomic, IsAtomic.exists_atom, Submodule, e.some.subsingleton, exists_atom, isEmpty_or_nonempty, isSimpleModule_iff_isAtom, linearEquiv_finsupp, not_subsingleton, resolve_left, subsingleton
-/
theorem IsIsotypic.linearEquiv_finsupp [Nontrivial M] (h : IsIsotypic R M) :
    exists (ι : Type u) (_ : Nonempty ι) (S : Submodule R M),
      IsSimpleModule R S ∧ Nonempty (M ≃ₗ[R] ι ->₀ S) := by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨ι, e⟩ := (h S).linearEquiv_finsupp
  exact ⟨ι, (isEmpty_or_nonempty ι).resolve_left fun _ => not_subsingleton _ (e.some.subsingleton),
    S, hS, e⟩

/--
theorem `IsIsotypicOfType.linearEquiv_fun` / 定理 `IsIsotypicOfType.linearEquiv_fun`

English:
theorem IsIsotypicOfType.linearEquiv_fun
  given: [Module.Finite R M] (h : IsIsotypicOfType R M S)
  proof: by
  have ⟨n, S, e, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  classical exact ⟨n, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun i => (h (S i)).some)
.trans (Finsupp.linearEquivFunOnFinite ..)⟩⟩ .trans (finsuppLequivDFinsupp R).symm

中文:
定理 IsIsotypicOfType.linearEquiv_fun
  条件: [Module.Finite R M] (h : IsIsotypicOfType R M S)
  证明: by
  have ⟨n, S, e, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  classical exact ⟨n, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun i => (h (S i)).some)
.trans (Finsupp.linearEquivFunOnFinite ..)⟩⟩ .trans (finsuppLequivDFinsupp R).symm

Depends on / 依赖: DFinsupp, DFinsupp.mapRange.linearEquiv, Finsupp, Finsupp.linearEquivFunOnFinite, IsSemisimpleModule, IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp, classical, e.trans, exists_linearEquiv_fin_dfinsupp, finsuppLequivDFinsupp, linearEquiv, linearEquivFunOnFinite, mapRange
-/
theorem IsIsotypicOfType.linearEquiv_fun [Module.Finite R M] (h : IsIsotypicOfType R M S) :
    exists n : Nat, Nonempty (M ≃ₗ[R] Fin n -> S) := by
  have ⟨n, S, e, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  classical exact ⟨n, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun i => (h (S i)).some)
.trans (Finsupp.linearEquivFunOnFinite ..)⟩⟩ .trans (finsuppLequivDFinsupp R).symm

/--
theorem `IsIsotypic.linearEquiv_fun` / 定理 `IsIsotypic.linearEquiv_fun`

English:
theorem IsIsotypic.linearEquiv_fun
  given: [Module.Finite R M] [Nontrivial M] (h : IsIsotypic R M)
  proof: by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨n, e⟩ := (h S).linearEquiv_fun
exact ⟨n, neZero_iff.2 by rintro rfl; exact not_subsingleton _ (e.some.subsingleton), S, hS, e⟩

中文:
定理 IsIsotypic.linearEquiv_fun
  条件: [Module.Finite R M] [Nontrivial M] (h : IsIsotypic R M)
  证明: by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨n, e⟩ := (h S).linearEquiv_fun
exact ⟨n, neZero_iff.2 by rintro rfl; exact not_subsingleton _ (e.some.subsingleton), S, hS, e⟩

Depends on / 依赖: IsAtomic, IsAtomic.exists_atom, Submodule, e.some.subsingleton, exists_atom, isSimpleModule_iff_isAtom, linearEquiv_fun, neZero_iff, not_subsingleton, subsingleton
-/
theorem IsIsotypic.linearEquiv_fun [Module.Finite R M] [Nontrivial M] (h : IsIsotypic R M) :
    exists (n : Nat) (_ : NeZero n) (S : Submodule R M),
      IsSimpleModule R S ∧ Nonempty (M ≃ₗ[R] Fin n -> S) := by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨n, e⟩ := (h S).linearEquiv_fun
exact ⟨n, neZero_iff.2 by rintro rfl; exact not_subsingleton _ (e.some.subsingleton), S, hS, e⟩

/--
theorem `IsIsotypic.submodule_linearEquiv_fun` / 定理 `IsIsotypic.submodule_linearEquiv_fun`

English:
theorem IsIsotypic.submodule_linearEquiv_fun
  statement: {m : Submodule R M} [Module.Finite R m] [Nontrivial m]
  proof: have ⟨n, hn, S, _, ⟨e⟩⟩ := h.linearEquiv_fun
  let e' := S.equivMapOfInjective _ m.subtype_injective
⟨n, hn, _, m.map_subtype_le S, .congr e'.symm, ⟨e.trans .piCongrRight fun _ => e'⟩⟩

中文:
定理 IsIsotypic.submodule_linearEquiv_fun
  结论: {m : Submodule R M} [Module.Finite R m] [Nontrivial m]
  证明: have ⟨n, hn, S, _, ⟨e⟩⟩ := h.linearEquiv_fun
  let e' := S.equivMapOfInjective _ m.subtype_injective
⟨n, hn, _, m.map_subtype_le S, .congr e'.symm, ⟨e.trans .piCongrRight fun _ => e'⟩⟩

Depends on / 依赖: S.equivMapOfInjective, e.trans, equivMapOfInjective, h.linearEquiv_fun, linearEquiv_fun, m.map_subtype_le, m.subtype_injective, map_subtype_le, piCongrRight, subtype_injective
-/
theorem IsIsotypic.submodule_linearEquiv_fun {m : Submodule R M} [Module.Finite R m] [Nontrivial m]
    (h : IsIsotypic R m) : exists (n : Nat) (_ : NeZero n) (S : Submodule R M),
      S <= m ∧ IsSimpleModule R S ∧ Nonempty (m ≃ₗ[R] Fin n -> S) :=
  have ⟨n, hn, S, _, ⟨e⟩⟩ := h.linearEquiv_fun
  let e' := S.equivMapOfInjective _ m.subtype_injective
⟨n, hn, _, m.map_subtype_le S, .congr e'.symm, ⟨e.trans .piCongrRight fun _ => e'⟩⟩

end Finsupp

variable (R M S)

/--
Definition of `isotypicComponent` / `isotypicComponent` 的定义

English:
definition isotypicComponent
  signature: : Submodule R M
  body: sSup {m | Nonempty (m ≃ₗ[R] S)}

中文:
定义 isotypicComponent
  签名: : Submodule R M
  定义体: sSup {m | Nonempty (m ≃ₗ[R] S)}

Depends on / 依赖: Nonempty
-/
def isotypicComponent : Submodule R M := sSup {m | Nonempty (m ≃ₗ[R] S)}

/--
Definition of `isotypicComponents` / `isotypicComponents` 的定义

English:
definition isotypicComponents
  signature: : Set (Submodule R M)
  body: { m | exists S : Submodule R M, IsSimpleModule R S ∧ m = isotypicComponent R M S }

中文:
定义 isotypicComponents
  签名: : Set (Submodule R M)
  定义体: { m | exists S : Submodule R M, IsSimpleModule R S ∧ m = isotypicComponent R M S }

Depends on / 依赖: IsSimpleModule, Submodule, isotypicComponent
-/
def isotypicComponents : Set (Submodule R M) :=
  { m | exists S : Submodule R M, IsSimpleModule R S ∧ m = isotypicComponent R M S }

variable {R M}

/--
theorem `Submodule.le_isotypicComponent` / 定理 `Submodule.le_isotypicComponent`

English:
theorem Submodule.le_isotypicComponent
  given: (m : Submodule R M)
  statement: m <= isotypicComponent R M m
  proof: le_sSup ⟨.refl ..⟩

中文:
定理 Submodule.le_isotypicComponent
  条件: (m : Submodule R M)
  结论: m <= isotypicComponent R M m
  证明: le_sSup ⟨.refl ..⟩

Depends on / 依赖: le_sSup
-/
theorem Submodule.le_isotypicComponent (m : Submodule R M) : m <= isotypicComponent R M m :=
  le_sSup ⟨.refl ..⟩

/--
theorem `bot_lt_isotypicComponent` / 定理 `bot_lt_isotypicComponent`

English:
theorem bot_lt_isotypicComponent
  given: (S : Submodule R M) [IsSimpleModule R S]
  proof: (bot_lt_iff_ne_bot.mpr <| (S.nontrivial_iff_ne_bot).mp <| IsSimpleModule.nontrivial R S).trans_le
    S.le_isotypicComponent

中文:
定理 bot_lt_isotypicComponent
  条件: (S : Submodule R M) [IsSimpleModule R S]
  证明: (bot_lt_iff_ne_bot.mpr <| (S.nontrivial_iff_ne_bot).mp <| IsSimpleModule.nontrivial R S).trans_le
    S.le_isotypicComponent

Depends on / 依赖: IsSimpleModule, IsSimpleModule.nontrivial, S.le_isotypicComponent, S.nontrivial_iff_ne_bot, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, le_isotypicComponent, nontrivial, nontrivial_iff_ne_bot, trans_le
-/
theorem bot_lt_isotypicComponent (S : Submodule R M) [IsSimpleModule R S] :
    ⊥ < isotypicComponent R M S :=
  (bot_lt_iff_ne_bot.mpr <| (S.nontrivial_iff_ne_bot).mp <| IsSimpleModule.nontrivial R S).trans_le
    S.le_isotypicComponent

/--
theorem `bot_lt_isotypicComponents` / 定理 `bot_lt_isotypicComponents`

English:
theorem bot_lt_isotypicComponents
  given: {m : Submodule R M} (h : m in isotypicComponents R M)
  statement: ⊥ < m
  proof: by
  obtain ⟨_, _, rfl⟩ := h; exact bot_lt_isotypicComponent ..

中文:
定理 bot_lt_isotypicComponents
  条件: {m : Submodule R M} (h : m in isotypicComponents R M)
  结论: ⊥ < m
  证明: by
  obtain ⟨_, _, rfl⟩ := h; exact bot_lt_isotypicComponent ..

Depends on / 依赖: bot_lt_isotypicComponent
-/
theorem bot_lt_isotypicComponents {m : Submodule R M} (h : m in isotypicComponents R M) : ⊥ < m := by
  obtain ⟨_, _, rfl⟩ := h; exact bot_lt_isotypicComponent ..

instance (c : isotypicComponents R M) : Nontrivial c :=
  Submodule.nontrivial_iff_ne_bot.mpr (bot_lt_isotypicComponents c.2).ne'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSemisimpleModule
  signature: R S] : IsSemisimpleModule R (isotypicComponent R M S)
  body: by
  rw [isotypicComponent]; rw [sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m ⟨e⟩ => ?_
  have := IsSemisimpleModule.congr e
  infer_instance

中文:
实例 [IsSemisimpleModule
  签名: R S] : IsSemisimpleModule R (isotypicComponent R M S)
  定义体: by
  rw [isotypicComponent]; rw [sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m ⟨e⟩ => ?_
  have := IsSemisimpleModule.congr e
  infer_instance

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.congr, infer_instance, isSemisimpleModule_biSup_of_isSemisimpleModule_submodule, isotypicComponent, sSup_eq_iSup
-/
instance [IsSemisimpleModule R S] : IsSemisimpleModule R (isotypicComponent R M S) := by
  rw [isotypicComponent]; rw [sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m ⟨e⟩ => ?_
  have := IsSemisimpleModule.congr e
  infer_instance

instance (c : isotypicComponents R M) : IsSemisimpleModule R c := by
  obtain ⟨c, S, _, rfl⟩ := c; infer_instance

variable {S} in
/--
theorem `LinearEquiv.isotypicComponent_eq` / 定理 `LinearEquiv.isotypicComponent_eq`

English:
theorem LinearEquiv.isotypicComponent_eq
  given: (e : N ≃ₗ[R] S)
  proof: congr_arg sSup Set.ext fun _ => Nonempty.congr (·.trans e) (·.trans e.symm)

中文:
定理 LinearEquiv.isotypicComponent_eq
  条件: (e : N ≃ₗ[R] S)
  证明: congr_arg sSup Set.ext fun _ => Nonempty.congr (·.trans e) (·.trans e.symm)

Depends on / 依赖: Nonempty, Nonempty.congr, Set.ext, congr_arg, e.symm
-/
theorem LinearEquiv.isotypicComponent_eq (e : N ≃ₗ[R] S) :
    isotypicComponent R M N = isotypicComponent R M S :=
congr_arg sSup Set.ext fun _ => Nonempty.congr (·.trans e) (·.trans e.symm)

section SimpleSubmodule

variable (N : Submodule R M) [IsSimpleModule R N] (s : Set (Submodule R M))

open LinearMap in
/--
theorem `Submodule.le_linearEquiv_of_sSup_eq_top` / 定理 `Submodule.le_linearEquiv_of_sSup_eq_top`

English:
theorem Submodule.le_linearEquiv_of_sSup_eq_top
  statement: [IsSemisimpleModule R M]
  proof: by
  have := IsSimpleModule.nontrivial R N
  have ⟨_, compl⟩ := exists_isCompl N
  have ⟨m, hm, ne⟩ := exists_ne_zero_of_sSup_eq_top (ne_zero_of_surjective
    (projectionOnto_surjective compl)) _ hs
  have ⟨S, ⟨e⟩⟩ := linearEquiv_of_ne_zero ne
  exact ⟨m, hm, _, m.map_subtype_le S, ⟨e.trans (S.equi

中文:
定理 Submodule.le_linearEquiv_of_sSup_eq_top
  结论: [IsSemisimpleModule R M]
  证明: by
  have := IsSimpleModule.nontrivial R N
  have ⟨_, compl⟩ := exists_isCompl N
  have ⟨m, hm, ne⟩ := exists_ne_zero_of_sSup_eq_top (ne_zero_of_surjective
    (projectionOnto_surjective compl)) _ hs
  have ⟨S, ⟨e⟩⟩ := linearEquiv_of_ne_zero ne
  exact ⟨m, hm, _, m.map_subtype_le S, ⟨e.trans (S.equi

Depends on / 依赖: IsSimpleModule, IsSimpleModule.nontrivial, S.equivMapOfInjective, e.trans, equivMapOfInjective, exists_isCompl, exists_ne_zero_of_sSup_eq_top, linearEquiv_of_ne_zero, m.map_subtype_le, m.subtype_injective, map_subtype_le, ne_zero_of_surjective, nontrivial, projectionOnto_surjective, subtype_injective
-/
theorem Submodule.le_linearEquiv_of_sSup_eq_top [IsSemisimpleModule R M]
    (hs : sSup s = ⊤) : exists m in s, exists S <= m, Nonempty (N ≃ₗ[R] S) := by
  have := IsSimpleModule.nontrivial R N
  have ⟨_, compl⟩ := exists_isCompl N
  have ⟨m, hm, ne⟩ := exists_ne_zero_of_sSup_eq_top (ne_zero_of_surjective
    (projectionOnto_surjective compl)) _ hs
  have ⟨S, ⟨e⟩⟩ := linearEquiv_of_ne_zero ne
  exact ⟨m, hm, _, m.map_subtype_le S, ⟨e.trans (S.equivMapOfInjective _ m.subtype_injective)⟩⟩

/--
theorem `Submodule.linearEquiv_of_sSup_eq_top` / 定理 `Submodule.linearEquiv_of_sSup_eq_top`

English:
theorem Submodule.linearEquiv_of_sSup_eq_top
  statement: [h : forall m : s, IsSimpleModule R m]
  proof: have := isSemisimpleModule_of_isSemisimpleModule_submodule' (fun _ => inferInstance)
    (sSup_eq_iSup' s ▸ hs)
  have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_sSup_eq_top _ hs
  have := isSimpleModule_iff_isAtom.mp (IsSimpleModule.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| h ⟨m, h

中文:
定理 Submodule.linearEquiv_of_sSup_eq_top
  结论: [h : 对任意 m : s, IsSimpleModule R m]
  证明: have := isSemisimpleModule_of_isSemisimpleModule_submodule' (fun _ => inferInstance)
    (sSup_eq_iSup' s ▸ hs)
  have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_sSup_eq_top _ hs
  have := isSimpleModule_iff_isAtom.mp (IsSimpleModule.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| h ⟨m, h

Depends on / 依赖: IsSimpleModule, IsSimpleModule.congr, N.le_linearEquiv_of_sSup_eq_top, e.symm, e.trans, isSemisimpleModule_of_isSemisimpleModule_submodule, isSimpleModule_iff_isAtom, isSimpleModule_iff_isAtom.mp, le_iff_eq, le_linearEquiv_of_sSup_eq_top, sSup_eq_iSup
-/
theorem Submodule.linearEquiv_of_sSup_eq_top [h : forall m : s, IsSimpleModule R m]
    (hs : sSup s = ⊤) : exists S in s, Nonempty (N ≃ₗ[R] S) :=
  have := isSemisimpleModule_of_isSemisimpleModule_submodule' (fun _ => inferInstance)
    (sSup_eq_iSup' s ▸ hs)
  have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_sSup_eq_top _ hs
  have := isSimpleModule_iff_isAtom.mp (IsSimpleModule.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| h ⟨m, hm⟩).le_iff_eq this.1).mp le
  ⟨m, hm, ⟨e.trans (.ofEq _ _ this)⟩⟩

/--
theorem `Submodule.le_linearEquiv_of_le_sSup` / 定理 `Submodule.le_linearEquiv_of_le_sSup`

English:
theorem Submodule.le_linearEquiv_of_le_sSup
  statement: [hs : forall m : s, IsSemisimpleModule R m]
  proof: by
  rw [sSup_eq_iSup] at hN
  have e := LinearEquiv.ofInjective _ (inclusion_injective hN)
  have := IsSimpleModule.congr e.symm
  have := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm => hs ⟨m, hm⟩
  obtain ⟨_, ⟨m, hm, rfl⟩, S, le, ⟨e'⟩⟩ := LinearMap.range (inclusion hN)
.le_li

中文:
定理 Submodule.le_linearEquiv_of_le_sSup
  结论: [hs : 对任意 m : s, IsSemisimpleModule R m]
  证明: by
  rw [sSup_eq_iSup] at hN
  have e := LinearEquiv.ofInjective _ (inclusion_injective hN)
  have := IsSimpleModule.congr e.symm
  have := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm => hs ⟨m, hm⟩
  obtain ⟨_, ⟨m, hm, rfl⟩, S, le, ⟨e'⟩⟩ := LinearMap.range (inclusion hN)
.le_li

Depends on / 依赖: IsSimpleModule, IsSimpleModule.congr, LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.range, biSup_comap_subtype_eq_top, e.symm, e.trans, equivMapOfInjective, inclusion, inclusion_injective, isSemisimpleModule_biSup_of_isSemisimpleModule_submodule, le_linearEquiv_of_sSup_eq_top, map_le_iff_le_comap, map_le_iff_le_comap.mpr, ofInjective, sSup_eq_iSup, sSup_image, subtype
-/
theorem Submodule.le_linearEquiv_of_le_sSup [hs : forall m : s, IsSemisimpleModule R m]
    (hN : N <= sSup s) : exists m in s, exists S <= m, Nonempty (N ≃ₗ[R] S) := by
  rw [sSup_eq_iSup] at hN
  have e := LinearEquiv.ofInjective _ (inclusion_injective hN)
  have := IsSimpleModule.congr e.symm
  have := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm => hs ⟨m, hm⟩
  obtain ⟨_, ⟨m, hm, rfl⟩, S, le, ⟨e'⟩⟩ := LinearMap.range (inclusion hN)
.le_linearEquiv_of_sSup_eq_top (comap (⨆ i in s, i).subtype '' s) by
    rw [sSup_image]; rw [biSup_comap_subtype_eq_top]
  exact ⟨m, hm, _, map_le_iff_le_comap.mpr le,
    ⟨(e.trans e').trans (equivMapOfInjective _ (subtype_injective _) _)⟩⟩

/--
theorem `Submodule.linearEquiv_of_le_sSup` / 定理 `Submodule.linearEquiv_of_le_sSup`

English:
theorem Submodule.linearEquiv_of_le_sSup
  statement: [simple : forall m : s, IsSimpleModule R m]
  proof: have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_le_sSup _ hs
  have := isSimpleModule_iff_isAtom.mp (.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| simple ⟨m, hm⟩).le_iff_eq this.1).mp le
  ⟨m, hm, ⟨e.trans (.ofEq _ _ this)⟩⟩

中文:
定理 Submodule.linearEquiv_of_le_sSup
  结论: [simple : 对任意 m : s, IsSimpleModule R m]
  证明: have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_le_sSup _ hs
  have := isSimpleModule_iff_isAtom.mp (.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| simple ⟨m, hm⟩).le_iff_eq this.1).mp le
  ⟨m, hm, ⟨e.trans (.ofEq _ _ this)⟩⟩

Depends on / 依赖: N.le_linearEquiv_of_le_sSup, e.symm, e.trans, isSimpleModule_iff_isAtom, isSimpleModule_iff_isAtom.mp, le_iff_eq, le_linearEquiv_of_le_sSup, simple
-/
theorem Submodule.linearEquiv_of_le_sSup [simple : forall m : s, IsSimpleModule R m]
    (hs : N <= sSup s) : exists S in s, Nonempty (N ≃ₗ[R] S) :=
  have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_le_sSup _ hs
  have := isSimpleModule_iff_isAtom.mp (.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| simple ⟨m, hm⟩).le_iff_eq this.1).mp le
  ⟨m, hm, ⟨e.trans (.ofEq _ _ this)⟩⟩

end SimpleSubmodule

section IsSimpleModule

variable (R M) [IsSimpleModule R S]

local instance (m : {m : Submodule R M | Nonempty (m ≃ₗ[R] S)}) : IsSimpleModule R m :=
  .congr m.2.some

/--
theorem `IsIsotypicOfType.isotypicComponent` / 定理 `IsIsotypicOfType.isotypicComponent`

English:
theorem IsIsotypicOfType.isotypicComponent
  proof: isIsotypicOfType_submodule_iff.mpr fun m h _ =>
    have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_le_sSup _ h
    ⟨e'.trans e⟩

中文:
定理 IsIsotypicOfType.isotypicComponent
  证明: isIsotypicOfType_submodule_iff.mpr fun m h _ =>
    have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_le_sSup _ h
    ⟨e'.trans e⟩
-/
protected theorem IsIsotypicOfType.isotypicComponent :
    IsIsotypicOfType R (isotypicComponent R M S) S :=
  isIsotypicOfType_submodule_iff.mpr fun m h _ =>
    have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_le_sSup _ h
    ⟨e'.trans e⟩

/--
theorem `IsIsotypic.isotypicComponent` / 定理 `IsIsotypic.isotypicComponent`

English:
theorem IsIsotypic.isotypicComponent
  statement: IsIsotypic R (isotypicComponent R M S)
  proof: (IsIsotypicOfType.isotypicComponent R M S).isIsotypic

中文:
定理 IsIsotypic.isotypicComponent
  结论: IsIsotypic R (isotypicComponent R M S)
  证明: (IsIsotypicOfType.isotypicComponent R M S).isIsotypic
-/
protected theorem IsIsotypic.isotypicComponent : IsIsotypic R (isotypicComponent R M S) :=
  (IsIsotypicOfType.isotypicComponent R M S).isIsotypic

variable {R M} in
/--
theorem `IsIsotypic.isotypicComponents` / 定理 `IsIsotypic.isotypicComponents`

English:
theorem IsIsotypic.isotypicComponents
  statement: {m : Submodule R M}
  proof: by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

中文:
定理 IsIsotypic.isotypicComponents
  结论: {m : Submodule R M}
  证明: by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _
-/
protected theorem IsIsotypic.isotypicComponents {m : Submodule R M}
    (h : m in isotypicComponents R M) : IsIsotypic R m := by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

variable {R M} in
/--
theorem `eq_isotypicComponent_of_le` / 定理 `eq_isotypicComponent_of_le`

English:
theorem eq_isotypicComponent_of_le
  statement: {S c : Submodule R M} (hc : c in isotypicComponents R M)
  proof: by
  obtain ⟨S', _, rfl⟩ := hc
  have ⟨e⟩ := isIsotypicOfType_submodule_iff.mp (.isotypicComponent R M S') _ le
  exact e.symm.isotypicComponent_eq

中文:
定理 eq_isotypicComponent_of_le
  结论: {S c : Submodule R M} (hc : c in isotypicComponents R M)
  证明: by
  obtain ⟨S', _, rfl⟩ := hc
  have ⟨e⟩ := isIsotypicOfType_submodule_iff.mp (.isotypicComponent R M S') _ le
  exact e.symm.isotypicComponent_eq

Depends on / 依赖: e.symm.isotypicComponent_eq, isIsotypicOfType_submodule_iff, isIsotypicOfType_submodule_iff.mp, isotypicComponent, isotypicComponent_eq
-/
theorem eq_isotypicComponent_of_le {S c : Submodule R M} (hc : c in isotypicComponents R M)
    [IsSimpleModule R S] (le : S <= c) : c = isotypicComponent R M S := by
  obtain ⟨S', _, rfl⟩ := hc
  have ⟨e⟩ := isIsotypicOfType_submodule_iff.mp (.isotypicComponent R M S') _ le
  exact e.symm.isotypicComponent_eq

/--
theorem `sSupIndep_isotypicComponents` / 定理 `sSupIndep_isotypicComponents`

English:
theorem sSupIndep_isotypicComponents
  statement: sSupIndep (isotypicComponents R M)
  proof: fun c hc => disjoint_iff.mpr of_not_not fun ne => by
    set s := isotypicComponents R M \ {c}
    have : IsSemisimpleModule R c := by obtain ⟨S, _, rfl⟩ := hc; infer_instance
    have := IsSemisimpleModule.of_injective _
      (Submodule.inclusion_injective (inf_le_left : c ⊓ sSup s <= c))
    have

中文:
定理 sSupIndep_isotypicComponents
  结论: sSupIndep (isotypicComponents R M)
  证明: fun c hc => disjoint_iff.mpr of_not_not fun ne => by
    set s := isotypicComponents R M \ {c}
    have : IsSemisimpleModule R c := by obtain ⟨S, _, rfl⟩ := hc; infer_instance
    have := IsSemisimpleModule.of_injective _
      (Submodule.inclusion_injective (inf_le_left : c ⊓ sSup s <= c))
    have

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.eq_bot_or_exists_simple_le, IsSemisimpleModule.of_injective, S.le_linearEquiv_, Submodule, Submodule.inclusion_injective, disjoint_iff, disjoint_iff.mpr, eq_bot_or_exists_simple_le, inclusion_injective, inf_le_left, infer_instance, isotypicComponents, le_linearEquiv_, of_injective, of_not_not, resolve_left
-/
theorem sSupIndep_isotypicComponents : sSupIndep (isotypicComponents R M) :=
fun c hc => disjoint_iff.mpr of_not_not fun ne => by
    set s := isotypicComponents R M \ {c}
    have : IsSemisimpleModule R c := by obtain ⟨S, _, rfl⟩ := hc; infer_instance
    have := IsSemisimpleModule.of_injective _
      (Submodule.inclusion_injective (inf_le_left : c ⊓ sSup s <= c))
    have (c : s) : IsSemisimpleModule R c := by obtain ⟨_, ⟨_, _, rfl⟩, _⟩ := c; infer_instance
    have ⟨S, le, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left ne
    have ⟨c', hc', S', le', ⟨e⟩⟩ := S.le_linearEquiv_of_le_sSup _ (le.trans inf_le_right)
    have := IsSimpleModule.congr e.symm
    refine hc'.2 ?_
    rw [eq_isotypicComponent_of_le hc (le.trans inf_le_left)]; rw [eq_isotypicComponent_of_le hc'.1 le']
    exact e.symm.isotypicComponent_eq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherian
  signature: R M] : Finite (isotypicComponents R M)
  body: Set.finite_coe_iff.mpr WellFoundedGT.finite_of_sSupIndep (sSupIndep_isotypicComponents R M)

中文:
实例 [IsNoetherian
  签名: R M] : Finite (isotypicComponents R M)
  定义体: Set.finite_coe_iff.mpr WellFoundedGT.finite_of_sSupIndep (sSupIndep_isotypicComponents R M)

Depends on / 依赖: Set.finite_coe_iff.mpr, WellFoundedGT, WellFoundedGT.finite_of_sSupIndep, finite_coe_iff, finite_of_sSupIndep, sSupIndep_isotypicComponents
-/
instance [IsNoetherian R M] : Finite (isotypicComponents R M) :=
Set.finite_coe_iff.mpr WellFoundedGT.finite_of_sSupIndep (sSupIndep_isotypicComponents R M)

variable {R M S}

/--
theorem `IsIsotypicOfType.of_isotypicComponent_eq_top` / 定理 `IsIsotypicOfType.of_isotypicComponent_eq_top`

English:
theorem IsIsotypicOfType.of_isotypicComponent_eq_top
  given: (h : isotypicComponent R M S = ⊤)
  proof: fun m _ => have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_sSup_eq_top _ h; ⟨e'.trans e⟩

中文:
定理 IsIsotypicOfType.of_isotypicComponent_eq_top
  条件: (h : isotypicComponent R M S = ⊤)
  证明: fun m _ => have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_sSup_eq_top _ h; ⟨e'.trans e⟩

Depends on / 依赖: linearEquiv_of_sSup_eq_top, m.linearEquiv_of_sSup_eq_top
-/
theorem IsIsotypicOfType.of_isotypicComponent_eq_top (h : isotypicComponent R M S = ⊤) :
    IsIsotypicOfType R M S :=
  fun m _ => have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_sSup_eq_top _ h; ⟨e'.trans e⟩

/--
theorem `Submodule.map_le_isotypicComponent` / 定理 `Submodule.map_le_isotypicComponent`

English:
theorem Submodule.map_le_isotypicComponent
  statement: (S : Submodule R M) [IsSimpleModule R S]
  proof: by
  conv_lhs => rw [← S.range_subtype, ← LinearMap.range_comp]
  obtain inj | eq := (f ∘ₗ S.subtype).injective_or_eq_zero
· exact le_sSup ⟨.symm .ofInjective _ inj⟩
  · simp_rw [eq, LinearMap.range_zero, bot_le]

中文:
定理 Submodule.map_le_isotypicComponent
  结论: (S : Submodule R M) [IsSimpleModule R S]
  证明: by
  conv_lhs => rw [← S.range_subtype, ← LinearMap.range_comp]
  obtain inj | eq := (f ∘ₗ S.subtype).injective_or_eq_zero
· exact le_sSup ⟨.symm .ofInjective _ inj⟩
  · simp_rw [eq, LinearMap.range_zero, bot_le]

Depends on / 依赖: LinearMap, LinearMap.range_comp, LinearMap.range_zero, S.range_subtype, S.subtype, bot_le, conv_lhs, injective_or_eq_zero, le_sSup, ofInjective, range_comp, range_subtype, range_zero, simp_rw, subtype
-/
theorem Submodule.map_le_isotypicComponent (S : Submodule R M) [IsSimpleModule R S]
    (f : M ->ₗ[R] N) : S.map f <= isotypicComponent R N S := by
  conv_lhs => rw [← S.range_subtype, ← LinearMap.range_comp]
  obtain inj | eq := (f ∘ₗ S.subtype).injective_or_eq_zero
· exact le_sSup ⟨.symm .ofInjective _ inj⟩
  · simp_rw [eq, LinearMap.range_zero, bot_le]

variable (S) in
/--
theorem `LinearMap.le_comap_isotypicComponent` / 定理 `LinearMap.le_comap_isotypicComponent`

English:
theorem LinearMap.le_comap_isotypicComponent
  given: (f : M ->ₗ[R] N)
  proof: sSup_le fun m ⟨e⟩ => Submodule.map_le_iff_le_comap.mp
    have := IsSimpleModule.congr e
    (m.map_le_isotypicComponent f).trans_eq e.isotypicComponent_eq

中文:
定理 LinearMap.le_comap_isotypicComponent
  条件: (f : M ->ₗ[R] N)
  证明: sSup_le fun m ⟨e⟩ => Submodule.map_le_iff_le_comap.mp
    have := IsSimpleModule.congr e
    (m.map_le_isotypicComponent f).trans_eq e.isotypicComponent_eq

Depends on / 依赖: IsSimpleModule, IsSimpleModule.congr, Submodule, Submodule.map_le_iff_le_comap.mp, e.isotypicComponent_eq, isotypicComponent_eq, m.map_le_isotypicComponent, map_le_iff_le_comap, map_le_isotypicComponent, sSup_le, trans_eq
-/
theorem LinearMap.le_comap_isotypicComponent (f : M ->ₗ[R] N) :
    isotypicComponent R M S <= (isotypicComponent R N S).comap f :=
sSup_le fun m ⟨e⟩ => Submodule.map_le_iff_le_comap.mp
    have := IsSimpleModule.congr e
    (m.map_le_isotypicComponent f).trans_eq e.isotypicComponent_eq

section IsFullyInvariant

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `Submodule.IsFullyInvariant` / `Submodule.IsFullyInvariant` 的定义

English:
definition Submodule.IsFullyInvariant
  signature: (N : Submodule R M)
  body: forall f : Module.End R M, N <= N.comap f

中文:
定义 Submodule.IsFullyInvariant
  签名: (N : Submodule R M)
  定义体: forall f : Module.End R M, N <= N.comap f

Depends on / 依赖: Module, Module.End, N.comap
-/
def Submodule.IsFullyInvariant (N : Submodule R M) : Prop :=
  forall f : Module.End R M, N <= N.comap f

/--
theorem `isFullyInvariant_iff_isTwoSided` / 定理 `isFullyInvariant_iff_isTwoSided`

English:
theorem isFullyInvariant_iff_isTwoSided
  given: {I : Ideal R}
  statement: I.IsFullyInvariant ↔ I.IsTwoSided
  proof: by
  simpa only [Submodule.IsFullyInvariant, ← MulOpposite.opEquiv.trans (RingEquiv.moduleEndSelf R
.toEquiv) |>.forall_congr_right, SetLike.le_def, I.isTwoSided_iff] using! forall_comm

中文:
定理 isFullyInvariant_iff_isTwoSided
  条件: {I : Ideal R}
  结论: I.IsFullyInvariant ↔ I.IsTwoSided
  证明: by
  simpa only [Submodule.IsFullyInvariant, ← MulOpposite.opEquiv.trans (RingEquiv.moduleEndSelf R
.toEquiv) |>.forall_congr_right, SetLike.le_def, I.isTwoSided_iff] using! forall_comm

Depends on / 依赖: I.isTwoSided_iff, IsFullyInvariant, MulOpposite, MulOpposite.opEquiv.trans, RingEquiv, RingEquiv.moduleEndSelf, SetLike, SetLike.le_def, Submodule, Submodule.IsFullyInvariant, forall_comm, forall_congr_right, isTwoSided_iff, le_def, moduleEndSelf, opEquiv, toEquiv
-/
theorem isFullyInvariant_iff_isTwoSided {I : Ideal R} : I.IsFullyInvariant ↔ I.IsTwoSided := by
  simpa only [Submodule.IsFullyInvariant, ← MulOpposite.opEquiv.trans (RingEquiv.moduleEndSelf R
.toEquiv) |>.forall_congr_right, SetLike.le_def, I.isTwoSided_iff] using! forall_comm

variable (R M) in
/--
Definition of `fullyInvariantSubmodule` / `fullyInvariantSubmodule` 的定义

English:
definition fullyInvariantSubmodule
  signature: : CompleteSublattice (Submodule R M)
  body: .mk' { N : Submodule R M | N.IsFullyInvariant }
    (fun _s hs f => sSup_le fun _N hN => (hs hN f).trans <| Submodule.comap_mono <| le_sSup hN)
fun _s hs f => Submodule.map_le_iff_le_comap.mp le_sInf fun _N hN =>
Submodule.map_le_iff_le_comap.mpr (sInf_le hN).trans (hs hN f)

中文:
定义 fullyInvariantSubmodule
  签名: : CompleteSublattice (Submodule R M)
  定义体: .mk' { N : Submodule R M | N.IsFullyInvariant }
    (fun _s hs f => sSup_le fun _N hN => (hs hN f).trans <| Submodule.comap_mono <| le_sSup hN)
fun _s hs f => Submodule.map_le_iff_le_comap.mp le_sInf fun _N hN =>
Submodule.map_le_iff_le_comap.mpr (sInf_le hN).trans (hs hN f)

Depends on / 依赖: IsFullyInvariant, N.IsFullyInvariant, Submodule, Submodule.comap_mono, Submodule.map_le_iff_le_comap.mp, Submodule.map_le_iff_le_comap.mpr, comap_mono, le_sInf, le_sSup, map_le_iff_le_comap, sInf_le, sSup_le
-/
def fullyInvariantSubmodule : CompleteSublattice (Submodule R M) :=
  .mk' { N : Submodule R M | N.IsFullyInvariant }
    (fun _s hs f => sSup_le fun _N hN => (hs hN f).trans <| Submodule.comap_mono <| le_sSup hN)
fun _s hs f => Submodule.map_le_iff_le_comap.mp le_sInf fun _N hN =>
Submodule.map_le_iff_le_comap.mpr (sInf_le hN).trans (hs hN f)

/--
theorem `mem_fullyInvariantSubmodule_iff` / 定理 `mem_fullyInvariantSubmodule_iff`

English:
theorem mem_fullyInvariantSubmodule_iff
  given: {m : Submodule R M}
  proof: Iff.rfl

中文:
定理 mem_fullyInvariantSubmodule_iff
  条件: {m : Submodule R M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_fullyInvariantSubmodule_iff {m : Submodule R M} :
    m in fullyInvariantSubmodule R M ↔ m.IsFullyInvariant := Iff.rfl

end IsFullyInvariant

section Equiv

variable {ι : Type*} [DecidableEq ι] {N : ι -> Submodule R M}
  (ind : iSupIndep N) (iSup_top : ⨆ i, N i = ⊤) (invar : forall i, (N i).IsFullyInvariant)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `iSupIndep.ringEquiv` / `iSupIndep.ringEquiv` 的定义

English:
definition iSupIndep.ringEquiv
  signature: : Module.End R M ≃+* Π i, Module.End R (N i) where
  body: f.restrict (invar i f)
  invFun f := letI e := ind.linearEquiv iSup_top; e ∘ₗ DFinsupp.mapRange.linearMap f ∘ₗ e.symm
  left_inv f := LinearMap.ext fun x => by
    exact Submodule.iSup_induction _ (motive := (_ = f ·)) (iSup_top ▸ Submodule.mem_top (x := x))
      (fun i x h => by simp [ind.linearEq

中文:
定义 iSupIndep.ringEquiv
  签名: : Module.End R M ≃+* Π i, Module.End R (N i) where
  定义体: f.restrict (invar i f)
  invFun f := letI e := ind.linearEquiv iSup_top; e ∘ₗ DFinsupp.mapRange.linearMap f ∘ₗ e.symm
  left_inv f := LinearMap.ext fun x => by
    exact Submodule.iSup_induction _ (motive := (_ = f ·)) (iSup_top ▸ Submodule.mem_top (x := x))
      (fun i x h => by simp [ind.linearEq

Depends on / 依赖: f.restrict, restrict
-/
noncomputable def iSupIndep.ringEquiv : Module.End R M ≃+* Π i, Module.End R (N i) where
  toFun f i := f.restrict (invar i f)
  invFun f := letI e := ind.linearEquiv iSup_top; e ∘ₗ DFinsupp.mapRange.linearMap f ∘ₗ e.symm
  left_inv f := LinearMap.ext fun x => by
    exact Submodule.iSup_induction _ (motive := (_ = f ·)) (iSup_top ▸ Submodule.mem_top (x := x))
      (fun i x h => by simp [ind.linearEquiv_symm_apply _ h]) (by simp)
      fun _ _ h₁ h₂ => by simpa only [map_add] using congr($h₁ + $h₂)
  right_inv f := by ext i x; simp [ind.linearEquiv_symm_apply _ x.2]
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/--
Definition of `iSupIndep.algEquiv` / `iSupIndep.algEquiv` 的定义

English:
definition iSupIndep.algEquiv
  signature: [Module R₀ M] [IsScalarTower R₀ R M]
  body: ind.ringEquiv iSup_top invar
  commutes' _ := rfl

中文:
定义 iSupIndep.algEquiv
  签名: [Module R₀ M] [IsScalarTower R₀ R M]
  定义体: ind.ringEquiv iSup_top invar
  commutes' _ := rfl

Depends on / 依赖: iSup_top, ind.ringEquiv, ringEquiv
-/
noncomputable def iSupIndep.algEquiv [Module R₀ M] [IsScalarTower R₀ R M] :
    Module.End R M ≃ₐ[R₀] Π i, Module.End R (N i) where
  __ := ind.ringEquiv iSup_top invar
  commutes' _ := rfl

end Equiv

variable (R M S) in
/--
theorem `Submodule.IsFullyInvariant.isotypicComponent` / 定理 `Submodule.IsFullyInvariant.isotypicComponent`

English:
theorem Submodule.IsFullyInvariant.isotypicComponent
  proof: LinearMap.le_comap_isotypicComponent S

中文:
定理 Submodule.IsFullyInvariant.isotypicComponent
  证明: LinearMap.le_comap_isotypicComponent S
-/
protected theorem Submodule.IsFullyInvariant.isotypicComponent :
    (isotypicComponent R M S).IsFullyInvariant :=
  LinearMap.le_comap_isotypicComponent S

/--
theorem `Submodule.IsFullyInvariant.of_mem_isotypicComponents` / 定理 `Submodule.IsFullyInvariant.of_mem_isotypicComponents`

English:
theorem Submodule.IsFullyInvariant.of_mem_isotypicComponents
  statement: {m : Submodule R M}
  proof: by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

中文:
定理 Submodule.IsFullyInvariant.of_mem_isotypicComponents
  结论: {m : Submodule R M}
  证明: by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

Depends on / 依赖: isotypicComponent
-/
theorem Submodule.IsFullyInvariant.of_mem_isotypicComponents {m : Submodule R M}
    (h : m in isotypicComponents R M) : m.IsFullyInvariant := by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

variable (R M) in
/--
Definition of `GaloisCoinsertion.setIsotypicComponents` / `GaloisCoinsertion.setIsotypicComponents` 的定义

English:
definition GaloisCoinsertion.setIsotypicComponents
  signature: :
  body: GaloisConnection.toGaloisCoinsertion (fun _ _ => iSup₂_le_iff) fun s c hc => of_not_not fun hcs =>
(bot_lt_isotypicComponents c.2).ne' (sSupIndep_isotypicComponents R M c.2).eq_bot_of_le
hc.trans by
      simp_rw [CompleteSublattice.coe_iSup, iSup₂_le_iff]
      exact fun c hc => le_sSup ⟨c.2, Subty

中文:
定义 GaloisCoinsertion.setIsotypicComponents
  签名: :
  定义体: GaloisConnection.toGaloisCoinsertion (fun _ _ => iSup₂_le_iff) fun s c hc => of_not_not fun hcs =>
(bot_lt_isotypicComponents c.2).ne' (sSupIndep_isotypicComponents R M c.2).eq_bot_of_le
hc.trans by
      simp_rw [CompleteSublattice.coe_iSup, iSup₂_le_iff]
      exact fun c hc => le_sSup ⟨c.2, Subty

Depends on / 依赖: fullyInvariantSubmodule, isotypicComponents
-/
def GaloisCoinsertion.setIsotypicComponents :
    GaloisCoinsertion (α := Set (isotypicComponents R M)) (β := fullyInvariantSubmodule R M)
      (fun s => ⨆ c in s, ⟨c, .of_mem_isotypicComponents c.2⟩) fun m => {c | c.1 <= m} :=
  GaloisConnection.toGaloisCoinsertion (fun _ _ => iSup₂_le_iff) fun s c hc => of_not_not fun hcs =>
(bot_lt_isotypicComponents c.2).ne' (sSupIndep_isotypicComponents R M c.2).eq_bot_of_le
hc.trans by
      simp_rw [CompleteSublattice.coe_iSup, iSup₂_le_iff]
      exact fun c hc => le_sSup ⟨c.2, Subtype.coe_ne_coe.mpr (ne_of_mem_of_not_mem hc hcs)⟩

/--
theorem `le_isotypicComponent_iff` / 定理 `le_isotypicComponent_iff`

English:
theorem le_isotypicComponent_iff
  given: [IsSemisimpleModule R M] {m : Submodule R M}
  proof: .of_injective (.isotypicComponent R M S) _ (Submodule.inclusion_injective h)
  mpr h := (IsSemisimpleModule.sSup_simples_le m).ge.trans
    (sSup_le_sSup fun S ⟨_, le⟩ => isIsotypicOfType_submodule_iff.mp h S le)

中文:
定理 le_isotypicComponent_iff
  条件: [IsSemisimpleModule R M] {m : Submodule R M}
  证明: .of_injective (.isotypicComponent R M S) _ (Submodule.inclusion_injective h)
  mpr h := (IsSemisimpleModule.sSup_simples_le m).ge.trans
    (sSup_le_sSup fun S ⟨_, le⟩ => isIsotypicOfType_submodule_iff.mp h S le)

Depends on / 依赖: Submodule, Submodule.inclusion_injective, inclusion_injective, isotypicComponent, of_injective
-/
theorem le_isotypicComponent_iff [IsSemisimpleModule R M] {m : Submodule R M} :
    m <= isotypicComponent R M S ↔ IsIsotypicOfType R m S where
  mp h := .of_injective (.isotypicComponent R M S) _ (Submodule.inclusion_injective h)
  mpr h := (IsSemisimpleModule.sSup_simples_le m).ge.trans
    (sSup_le_sSup fun S ⟨_, le⟩ => isIsotypicOfType_submodule_iff.mp h S le)

/--
theorem `isotypicComponent_eq_top_iff` / 定理 `isotypicComponent_eq_top_iff`

English:
theorem isotypicComponent_eq_top_iff
  given: [IsSemisimpleModule R M]
  proof: by
  rw [← top_le_iff]; rw [le_isotypicComponent_iff]; rw [Submodule.topEquiv.isIsotypicOfType_iff]

中文:
定理 isotypicComponent_eq_top_iff
  条件: [IsSemisimpleModule R M]
  证明: by
  rw [← top_le_iff]; rw [le_isotypicComponent_iff]; rw [Submodule.topEquiv.isIsotypicOfType_iff]

Depends on / 依赖: Submodule, Submodule.topEquiv.isIsotypicOfType_iff, isIsotypicOfType_iff, le_isotypicComponent_iff, topEquiv, top_le_iff
-/
theorem isotypicComponent_eq_top_iff [IsSemisimpleModule R M] :
    isotypicComponent R M S = ⊤ ↔ IsIsotypicOfType R M S := by
  rw [← top_le_iff]; rw [le_isotypicComponent_iff]; rw [Submodule.topEquiv.isIsotypicOfType_iff]

open IsSemisimpleModule in
/--
theorem `isFullyInvariant_iff_le_imp_isotypicComponent_le` / 定理 `isFullyInvariant_iff_le_imp_isotypicComponent_le`

English:
theorem isFullyInvariant_iff_le_imp_isotypicComponent_le
  statement: [IsSemisimpleModule R M]
  proof: sSup_le fun S' ⟨e⟩ => by
    have ⟨p, eq⟩ := extension_property _ S.subtype_injective (S'.subtype ∘ₗ e.symm)
    refine le_trans ?_ (Submodule.map_le_iff_le_comap.mpr (le.trans (h p)))
    rw [← S.range_subtype]; rw [← LinearMap.range_comp]; rw [eq]; rw [e.symm.range_comp]; rw [S'.range_subtype]
mpr

中文:
定理 isFullyInvariant_iff_le_imp_isotypicComponent_le
  结论: [IsSemisimpleModule R M]
  证明: sSup_le fun S' ⟨e⟩ => by
    have ⟨p, eq⟩ := extension_property _ S.subtype_injective (S'.subtype ∘ₗ e.symm)
    refine le_trans ?_ (Submodule.map_le_iff_le_comap.mpr (le.trans (h p)))
    rw [← S.range_subtype]; rw [← LinearMap.range_comp]; rw [eq]; rw [e.symm.range_comp]; rw [S'.range_subtype]
mpr

Depends on / 依赖: LinearMap, LinearMap.range_comp, S.map_le_isotypicComponent, S.range_subtype, S.subtype_injective, Submodule, Submodule.map_le_iff_le_comap.mp, Submodule.map_le_iff_le_comap.mpr, e.symm, e.symm.range_comp, extension_property, ge.trans, le.trans, le_trans, map_le_iff_le_comap, map_le_isotypicComponent, range_comp, range_subtype, sSup_le, sSup_simples_le
-/
theorem isFullyInvariant_iff_le_imp_isotypicComponent_le [IsSemisimpleModule R M]
    {m : Submodule R M} :
    m.IsFullyInvariant ↔ forall S <= m, [IsSimpleModule R S] -> isotypicComponent R M S <= m where
  mp h S le _ := sSup_le fun S' ⟨e⟩ => by
    have ⟨p, eq⟩ := extension_property _ S.subtype_injective (S'.subtype ∘ₗ e.symm)
    refine le_trans ?_ (Submodule.map_le_iff_le_comap.mpr (le.trans (h p)))
    rw [← S.range_subtype]; rw [← LinearMap.range_comp]; rw [eq]; rw [e.symm.range_comp]; rw [S'.range_subtype]
mpr h f := (sSup_simples_le m).ge.trans sSup_le fun S ⟨_, le⟩ =>
    Submodule.map_le_iff_le_comap.mp ((S.map_le_isotypicComponent f).trans (h S le))

/--
theorem `eq_isotypicComponent_iff` / 定理 `eq_isotypicComponent_iff`

English:
theorem eq_isotypicComponent_iff
  given: [IsSemisimpleModule R M] {m : Submodule R M} (ne : m != ⊥)
  proof: by rintro rfl; exact ⟨.isotypicComponent R M S, .isotypicComponent R M S⟩
mpr := fun ⟨iso, invar⟩ => (le_isotypicComponent_iff.mpr iso).antisymm
    have ⟨S', le, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le m).resolve_left ne
    (isIsotypicOfType_submodule_iff.mp iso S' le).some.symm.isoty

中文:
定理 eq_isotypicComponent_iff
  条件: [IsSemisimpleModule R M] {m : Submodule R M} (ne : m != ⊥)
  证明: by rintro rfl; exact ⟨.isotypicComponent R M S, .isotypicComponent R M S⟩
mpr := fun ⟨iso, invar⟩ => (le_isotypicComponent_iff.mpr iso).antisymm
    have ⟨S', le, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le m).resolve_left ne
    (isIsotypicOfType_submodule_iff.mp iso S' le).some.symm.isoty

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.eq_bot_or_exists_simple_le, antisymm, eq_bot_or_exists_simple_le, isFullyInvariant_iff_le_imp_isotypicComponent_le, isFullyInvariant_iff_le_imp_isotypicComponent_le.mp, isIsotypicOfType_submodule_iff, isIsotypicOfType_submodule_iff.mp, isotypicComponent, isotypicComponent_eq, le_isotypicComponent_iff, le_isotypicComponent_iff.mpr, resolve_left, some.symm.isotypicComponent_eq.trans_le, trans_le
-/
theorem eq_isotypicComponent_iff [IsSemisimpleModule R M] {m : Submodule R M} (ne : m != ⊥) :
    m = isotypicComponent R M S ↔ IsIsotypicOfType R m S ∧ m.IsFullyInvariant where
  mp := by rintro rfl; exact ⟨.isotypicComponent R M S, .isotypicComponent R M S⟩
mpr := fun ⟨iso, invar⟩ => (le_isotypicComponent_iff.mpr iso).antisymm
    have ⟨S', le, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le m).resolve_left ne
    (isIsotypicOfType_submodule_iff.mp iso S' le).some.symm.isotypicComponent_eq.trans_le
      (isFullyInvariant_iff_le_imp_isotypicComponent_le.mp invar _ le)

end IsSimpleModule

variable [IsSemisimpleModule R M]

open IsSemisimpleModule

/--
theorem `isIsotypic_iff_isFullyInvariant_imp_bot_or_top` / 定理 `isIsotypic_iff_isFullyInvariant_imp_bot_or_top`

English:
theorem isIsotypic_iff_isFullyInvariant_imp_bot_or_top
  proof: (eq_bot_or_exists_simple_le N).imp_right fun ⟨S, le, _⟩ => top_unique
    (isotypicComponent_eq_top_iff.mpr (h S)).ge.trans
    ((isFullyInvariant_iff_le_imp_isotypicComponent_le.mp hN) _ le)
mpr h S _ := isotypicComponent_eq_top_iff.mp
    (h _ (.isotypicComponent R M S)).resolve_left (bot_lt_isoty

中文:
定理 isIsotypic_iff_isFullyInvariant_imp_bot_or_top
  证明: (eq_bot_or_exists_simple_le N).imp_right fun ⟨S, le, _⟩ => top_unique
    (isotypicComponent_eq_top_iff.mpr (h S)).ge.trans
    ((isFullyInvariant_iff_le_imp_isotypicComponent_le.mp hN) _ le)
mpr h S _ := isotypicComponent_eq_top_iff.mp
    (h _ (.isotypicComponent R M S)).resolve_left (bot_lt_isoty

Depends on / 依赖: eq_bot_or_exists_simple_le, imp_right, top_unique
-/
theorem isIsotypic_iff_isFullyInvariant_imp_bot_or_top :
    IsIsotypic R M ↔ forall N : Submodule R M, N.IsFullyInvariant -> N = ⊥ ∨ N = ⊤ where
mp h N hN := (eq_bot_or_exists_simple_le N).imp_right fun ⟨S, le, _⟩ => top_unique
    (isotypicComponent_eq_top_iff.mpr (h S)).ge.trans
    ((isFullyInvariant_iff_le_imp_isotypicComponent_le.mp hN) _ le)
mpr h S _ := isotypicComponent_eq_top_iff.mp
    (h _ (.isotypicComponent R M S)).resolve_left (bot_lt_isotypicComponent S).ne'

/--
theorem `mem_isotypicComponents_iff` / 定理 `mem_isotypicComponents_iff`

English:
theorem mem_isotypicComponents_iff
  given: {m : Submodule R M}
  proof: by rintro ⟨S, _, rfl⟩; exact ⟨.isotypicComponent R M S,
    .isotypicComponent R M S, (bot_lt_isotypicComponent S).ne'⟩
  mpr := fun ⟨iso, invar, ne⟩ =>
    have ⟨S, le, simple⟩ := (eq_bot_or_exists_simple_le m).resolve_left ne
    ⟨S, simple, (eq_isotypicComponent_iff ne).mpr ⟨isIsotypic_submodule_

中文:
定理 mem_isotypicComponents_iff
  条件: {m : Submodule R M}
  证明: by rintro ⟨S, _, rfl⟩; exact ⟨.isotypicComponent R M S,
    .isotypicComponent R M S, (bot_lt_isotypicComponent S).ne'⟩
  mpr := fun ⟨iso, invar, ne⟩ =>
    have ⟨S, le, simple⟩ := (eq_bot_or_exists_simple_le m).resolve_left ne
    ⟨S, simple, (eq_isotypicComponent_iff ne).mpr ⟨isIsotypic_submodule_

Depends on / 依赖: bot_lt_isotypicComponent, eq_bot_or_exists_simple_le, eq_isotypicComponent_iff, isIsotypic_submodule_iff, isIsotypic_submodule_iff.mp, isotypicComponent, resolve_left, simple
-/
theorem mem_isotypicComponents_iff {m : Submodule R M} :
    m in isotypicComponents R M ↔ IsIsotypic R m ∧ m.IsFullyInvariant ∧ m != ⊥ where
  mp := by rintro ⟨S, _, rfl⟩; exact ⟨.isotypicComponent R M S,
    .isotypicComponent R M S, (bot_lt_isotypicComponent S).ne'⟩
  mpr := fun ⟨iso, invar, ne⟩ =>
    have ⟨S, le, simple⟩ := (eq_bot_or_exists_simple_le m).resolve_left ne
    ⟨S, simple, (eq_isotypicComponent_iff ne).mpr ⟨isIsotypic_submodule_iff.mp iso S le, invar⟩⟩

/--
Definition of `OrderIso.setIsotypicComponents` / `OrderIso.setIsotypicComponents` 的定义

English:
definition OrderIso.setIsotypicComponents
  signature: :
  body: ⨆ c in s, ⟨c, .of_mem_isotypicComponents c.2⟩
  invFun m := { c | c.1 <= m }
  left_inv := (GaloisCoinsertion.setIsotypicComponents R M).u_l_eq
right_inv m := (iSup₂_le fun _ => by exact id).antisymm (sSup_simples_le m.1).ge.trans
sSup_le fun S ⟨simple, le⟩ => S.le_isotypicComponent.trans by
    let

中文:
定义 OrderIso.setIsotypicComponents
  签名: :
  定义体: ⨆ c in s, ⟨c, .of_mem_isotypicComponents c.2⟩
  invFun m := { c | c.1 <= m }
  left_inv := (GaloisCoinsertion.setIsotypicComponents R M).u_l_eq
right_inv m := (iSup₂_le fun _ => by exact id).antisymm (sSup_simples_le m.1).ge.trans
sSup_le fun S ⟨simple, le⟩ => S.le_isotypicComponent.trans by
    let
-/
@[simps] def OrderIso.setIsotypicComponents :
    Set (isotypicComponents R M) ≃o fullyInvariantSubmodule R M where
  toFun s := ⨆ c in s, ⟨c, .of_mem_isotypicComponents c.2⟩
  invFun m := { c | c.1 <= m }
  left_inv := (GaloisCoinsertion.setIsotypicComponents R M).u_l_eq
right_inv m := (iSup₂_le fun _ => by exact id).antisymm (sSup_simples_le m.1).ge.trans
sSup_le fun S ⟨simple, le⟩ => S.le_isotypicComponent.trans by
    let c : isotypicComponents R M := ⟨_, S, simple, rfl⟩
    simp_rw [← show c.1 = isotypicComponent R M S from rfl, CompleteSublattice.coe_iSup]
    exact le_biSup _ (isFullyInvariant_iff_le_imp_isotypicComponent_le.mp m.2 _ le)
  map_rel_iff' := (GaloisCoinsertion.setIsotypicComponents R M).l_le_l_iff

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isFullyInvariant_iff_sSup_isotypicComponents` / 定理 `isFullyInvariant_iff_sSup_isotypicComponents`

English:
theorem isFullyInvariant_iff_sSup_isotypicComponents
  given: {m : Submodule R M}
  proof: by
  refine ⟨fun h => ⟨OrderIso.setIsotypicComponents.symm ⟨m, h⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rintro _ ⟨c, _, rfl⟩; exact c.2
  · convert! Subtype.ext_iff.mp (OrderIso.setIsotypicComponents.right_inv ⟨m, h⟩).symm
    simp [sSup_image, OrderIso.setIsotypicComponents, OrderIso.symm]
  · rintro ⟨_, hs, rfl⟩
  

中文:
定理 isFullyInvariant_iff_sSup_isotypicComponents
  条件: {m : Submodule R M}
  证明: by
  refine ⟨fun h => ⟨OrderIso.setIsotypicComponents.symm ⟨m, h⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rintro _ ⟨c, _, rfl⟩; exact c.2
  · convert! Subtype.ext_iff.mp (OrderIso.setIsotypicComponents.right_inv ⟨m, h⟩).symm
    simp [sSup_image, OrderIso.setIsotypicComponents, OrderIso.symm]
  · rintro ⟨_, hs, rfl⟩
  

Depends on / 依赖: OrderIso, OrderIso.setIsotypicComponents, OrderIso.setIsotypicComponents.right_inv, OrderIso.setIsotypicComponents.symm, OrderIso.symm, Subtype, Subtype.ext_iff.mp, convert, ext_iff, fullyInvariantSubmodule, of_mem_isotypicComponents, right_inv, sSupClosed, sSup_image, setIsotypicComponents
-/
theorem isFullyInvariant_iff_sSup_isotypicComponents {m : Submodule R M} :
    m.IsFullyInvariant ↔ exists s subseteq isotypicComponents R M, m = sSup s := by
  refine ⟨fun h => ⟨OrderIso.setIsotypicComponents.symm ⟨m, h⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rintro _ ⟨c, _, rfl⟩; exact c.2
  · convert! Subtype.ext_iff.mp (OrderIso.setIsotypicComponents.right_inv ⟨m, h⟩).symm
    simp [sSup_image, OrderIso.setIsotypicComponents, OrderIso.symm]
  · rintro ⟨_, hs, rfl⟩
    exact (fullyInvariantSubmodule R M).sSupClosed fun _ h => .of_mem_isotypicComponents (hs h)

variable (R M) in
/--
theorem `sSup_isotypicComponents` / 定理 `sSup_isotypicComponents`

English:
theorem sSup_isotypicComponents
  statement: sSup (isotypicComponents R M) = ⊤
  proof: have ⟨_, h, eq⟩ := isFullyInvariant_iff_sSup_isotypicComponents.mp
    (fullyInvariantSubmodule R M).top_mem
top_unique eq.le.trans (sSup_le_sSup h)

中文:
定理 sSup_isotypicComponents
  结论: sSup (isotypicComponents R M) = ⊤
  证明: have ⟨_, h, eq⟩ := isFullyInvariant_iff_sSup_isotypicComponents.mp
    (fullyInvariantSubmodule R M).top_mem
top_unique eq.le.trans (sSup_le_sSup h)

Depends on / 依赖: eq.le.trans, fullyInvariantSubmodule, isFullyInvariant_iff_sSup_isotypicComponents, isFullyInvariant_iff_sSup_isotypicComponents.mp, sSup_le_sSup, top_mem, top_unique
-/
theorem sSup_isotypicComponents : sSup (isotypicComponents R M) = ⊤ :=
  have ⟨_, h, eq⟩ := isFullyInvariant_iff_sSup_isotypicComponents.mp
    (fullyInvariantSubmodule R M).top_mem
top_unique eq.le.trans (sSup_le_sSup h)

namespace IsSemisimpleModule

variable (R M) [Module R₀ M] [IsScalarTower R₀ R M] [DecidableEq (isotypicComponents R M)]

/--
Definition of `endAlgEquiv` / `endAlgEquiv` 的定义

English:
definition endAlgEquiv
  signature: :
  body: ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).algEquiv R₀
    ((sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M) (.of_mem_isotypicComponents ·.2)

中文:
定义 endAlgEquiv
  签名: :
  定义体: ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).algEquiv R₀
    ((sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M) (.of_mem_isotypicComponents ·.2)

Depends on / 依赖: algEquiv, of_mem_isotypicComponents, sSupIndep_iff, sSupIndep_isotypicComponents, sSup_eq_iSup, sSup_isotypicComponents, symm.trans
-/
noncomputable def endAlgEquiv :
    Module.End R M ≃ₐ[R₀] Π c : isotypicComponents R M, Module.End R c.1 :=
  ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).algEquiv R₀
    ((sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M) (.of_mem_isotypicComponents ·.2)

/--
Definition of `endRingEquiv` / `endRingEquiv` 的定义

English:
definition endRingEquiv
  signature: :
  body: (endAlgEquiv Nat R M).toRingEquiv

中文:
定义 endRingEquiv
  签名: :
  定义体: (endAlgEquiv Nat R M).toRingEquiv

Depends on / 依赖: endAlgEquiv, toRingEquiv
-/
noncomputable def endRingEquiv :
    Module.End R M ≃+* Π c : isotypicComponents R M, Module.End R c.1 :=
  (endAlgEquiv Nat R M).toRingEquiv

end IsSemisimpleModule
