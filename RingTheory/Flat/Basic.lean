/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang, Yongle Hu
-/
module

public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Adjoin.FGBaseChange
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Flat modules

A module `M` over a commutative semiring `R` is *mono-flat* if for all monomorphisms of modules
(i.e., injective linear maps) `N →ₗ[R] P`, the canonical map `N ⊗ M → P ⊗ M` is injective
(cf. [Katsov2004], [KatsovNam2011]).
To show a module is mono-flat, it suffices to check inclusions of finitely generated
submodules `N` into finitely generated modules `P`, and `P` can be further assumed to lie in
the same universe as `R`.

`M` is flat if `· ⊗ M` preserves finite limits (equivalently, pullbacks, or equalizers).
If `R` is a ring, an `R`-module `M` is flat if and only if it is mono-flat, and to show
a module is flat, it suffices to check inclusions of finitely generated ideals into `R`.
See <https://stacks.math.columbia.edu/tag/00HD>.

Currently, `Module.Flat` is defined to be equivalent to mono-flatness over a semiring.
It is left as a TODO item to introduce the genuine flatness over semirings and rename
the current `Module.Flat` to `Module.MonoFlat`.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## Main theorems

* `Module.Flat.of_retract`: retracts of flat modules are flat
* `Module.Flat.of_linearEquiv`: modules linearly equivalent to a flat module are flat
* `Module.Flat.directSum`: arbitrary direct sums of flat modules are flat
* `Module.Flat.of_free`: free modules are flat
* `Module.Flat.of_projective`: projective modules are flat
* `Module.Flat.preserves_injective_linearMap`: If `M` is a flat module then tensoring with `M`
  preserves injectivity of linear maps. This lemma is fully universally polymorphic in all
  arguments, i.e. `R`, `M` and linear maps `N → N'` can all have different universe levels.
* `Module.Flat.iff_rTensor_preserves_injective_linearMap`: a module is flat iff tensoring modules
  in the higher universe preserves injectivity.
* `Module.Flat.lTensor_exact`: If `M` is a flat module then tensoring with `M` is an exact
  functor. This lemma is fully universally polymorphic in all arguments, i.e.
  `R`, `M` and linear maps `N → N' → N''` can all have different universe levels.
* `Module.Flat.iff_lTensor_exact`: a module is flat iff tensoring modules
  in the higher universe is an exact functor.

## TODO

* Generalize flatness to noncommutative semirings.

-/

@[expose] public section

assert_not_exists AddCircle

universe v' u v w

open TensorProduct

namespace Module

open Function (Injective Surjective)

open LinearMap Submodule DirectSum

section Semiring

/-! ### Flatness over a semiring -/

variable {R : Type u} {M : Type v} {N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/--
theorem `_root_.LinearMap.rTensor_injective_of_fg` / 定理 `_root_.LinearMap.rTensor_injective_of_fg`

English:
theorem _root_.LinearMap.rTensor_injective_of_fg
  statement: {f : N ->ₗ[R] P}
  proof: fun x y eq => by
  have ⟨N', Nfg, sub⟩ := Submodule.exists_fg_le_subset_range_rTensor_subtype {x, y} (by simp)
  obtain ⟨x, rfl⟩ := sub (.inl rfl)
  obtain ⟨y, rfl⟩ := sub (.inr rfl)
  simp_rw [← rTensor_comp_apply, show f ∘ₗ N'.subtype = (N'.map f).subtype ∘ₗ f.submoduleMap N'
    from rfl, rTensor

中文:
定理 _root_.LinearMap.rTensor_injective_of_fg
  结论: {f : N ->ₗ[R] P}
  证明: fun x y eq => by
  have ⟨N', Nfg, sub⟩ := Submodule.exists_fg_le_subset_range_rTensor_subtype {x, y} (by simp)
  obtain ⟨x, rfl⟩ := sub (.inl rfl)
  obtain ⟨y, rfl⟩ := sub (.inr rfl)
  simp_rw [← rTensor_comp_apply, show f ∘ₗ N'.subtype = (N'.map f).subtype ∘ₗ f.submoduleMap N'
    from rfl, rTensor

Depends on / 依赖: Nfg.map, Submodule, Submodule.exists_fg_le_subset_range_rTensor_subtype, exists_fg_le_subset_range_rTensor_subtype, exists_rTensor_fg_inclusion_eq, f.submoduleMap, map_le_iff_le_comap, map_le_iff_le_comap.mp, rTensor_comp_apply, simp_rw, submoduleMap, subtype
-/
theorem _root_.LinearMap.rTensor_injective_of_fg {f : N ->ₗ[R] P}
    (h : forall (N' : Submodule R N) (P' : Submodule R P),
      N'.FG -> P'.FG -> forall h : N' <= P'.comap f, Function.Injective ((f.restrict h).rTensor M)) :
    Function.Injective (f.rTensor M) := fun x y eq => by
  have ⟨N', Nfg, sub⟩ := Submodule.exists_fg_le_subset_range_rTensor_subtype {x, y} (by simp)
  obtain ⟨x, rfl⟩ := sub (.inl rfl)
  obtain ⟨y, rfl⟩ := sub (.inr rfl)
  simp_rw [← rTensor_comp_apply, show f ∘ₗ N'.subtype = (N'.map f).subtype ∘ₗ f.submoduleMap N'
    from rfl, rTensor_comp_apply] at eq
  have ⟨P', Pfg, le, eq⟩ := (Nfg.map _).exists_rTensor_fg_inclusion_eq eq
  simp_rw [← rTensor_comp_apply] at eq
  rw [h _ _ Nfg Pfg (map_le_iff_le_comap.mp le) eq]

/--
lemma `_root_.LinearMap.rTensor_injective_iff_subtype` / 引理 `_root_.LinearMap.rTensor_injective_iff_subtype`

English:
lemma _root_.LinearMap.rTensor_injective_iff_subtype
  statement: {f : N ->ₗ[R] P} (hf : Function.Injective f)
  proof: by
  simp_rw [← EquivLike.injective_comp <| (LinearEquiv.ofInjective (e.toLinearMap ∘ₗ f)
    (e.injective.comp hf)).rTensor M, ← EquivLike.comp_injective _ (e.rTensor M),
    ← LinearEquiv.coe_coe, ← coe_comp, LinearEquiv.coe_rTensor, ← rTensor_comp]
  rfl

中文:
引理 _root_.LinearMap.rTensor_injective_iff_subtype
  结论: {f : N ->ₗ[R] P} (hf : Function.Injective f)
  证明: by
  simp_rw [← EquivLike.injective_comp <| (LinearEquiv.ofInjective (e.toLinearMap ∘ₗ f)
    (e.injective.comp hf)).rTensor M, ← EquivLike.comp_injective _ (e.rTensor M),
    ← LinearEquiv.coe_coe, ← coe_comp, LinearEquiv.coe_rTensor, ← rTensor_comp]
  rfl

Depends on / 依赖: EquivLike, EquivLike.comp_injective, EquivLike.injective_comp, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_rTensor, LinearEquiv.ofInjective, coe_coe, coe_comp, coe_rTensor, comp_injective, e.injective.comp, e.rTensor, e.toLinearMap, injective, injective_comp, ofInjective, rTensor, rTensor_comp, simp_rw
-/
lemma _root_.LinearMap.rTensor_injective_iff_subtype {f : N ->ₗ[R] P} (hf : Function.Injective f)
    (e : P ≃ₗ[R] Q) : Function.Injective (f.rTensor M) ↔
      Function.Injective ((range <| e.toLinearMap ∘ₗ f).subtype.rTensor M) := by
  simp_rw [← EquivLike.injective_comp <| (LinearEquiv.ofInjective (e.toLinearMap ∘ₗ f)
    (e.injective.comp hf)).rTensor M, ← EquivLike.comp_injective _ (e.rTensor M),
    ← LinearEquiv.coe_coe, ← coe_comp, LinearEquiv.coe_rTensor, ← rTensor_comp]
  rfl

variable (R M) in
/--
Definition of `Flat` / `Flat` 的定义

English:
class Flat
  parameters: : Prop where
  axioms and operations (1):
    - out(⦃P) : Type u⦄ [AddCommMonoid P] [Module R P] [Module.Finite R P] (N : Submodule R P) : N.FG -> Function.Injective (N.subtype.rTensor M)

中文:
类 Flat
  参数: : 命题 where
  公理与运算 (1 个):
    - out(⦃P) : 类型u⦄ [AddCommMonoid P] [Module R P] [Module.Finite R P] (N : Submodule R P) : N.FG -> Function.Injective (N.subtype.rTensor M)
-/
@[mk_iff] class Flat : Prop where
  out ⦃P : Type u⦄ [AddCommMonoid P] [Module R P] [Module.Finite R P] (N : Submodule R P) : N.FG ->
    Function.Injective (N.subtype.rTensor M)

namespace Flat

/--
theorem `rTensor_preserves_injective_linearMap` / 定理 `rTensor_preserves_injective_linearMap`

English:
theorem rTensor_preserves_injective_linearMap
  statement: [Flat R M] (f : N ->ₗ[R] P)
  proof: by
  refine rTensor_injective_of_fg fun N P Nfg Pfg le => ?_
  rw [← Finite.iff_fg] at Nfg Pfg
  have := Finite.small R P
  let se := (Shrink.linearEquiv R P).symm
  have := Module.Finite.equiv se
  rw [rTensor_injective_iff_subtype (fun _ _ => (Subtype.ext <| hf <| Subtype.ext_iff.mp ·)) se]
  exac

中文:
定理 rTensor_preserves_injective_linearMap
  结论: [Flat R M] (f : N ->ₗ[R] P)
  证明: by
  refine rTensor_injective_of_fg fun N P Nfg Pfg le => ?_
  rw [← Finite.iff_fg] at Nfg Pfg
  have := Finite.small R P
  let se := (Shrink.linearEquiv R P).symm
  have := Module.Finite.equiv se
  rw [rTensor_injective_iff_subtype (fun _ _ => (Subtype.ext <| hf <| Subtype.ext_iff.mp ·)) se]
  exac

Depends on / 依赖: Finite, Finite.iff_fg, Finite.iff_fg.mp, Finite.small, Module, Module.Finite.equiv, Shrink, Shrink.linearEquiv, Subtype, Subtype.ext, Subtype.ext_iff.mp, ext_iff, flat_iff, iff_fg, linearEquiv, rTensor_injective_iff_subtype, rTensor_injective_of_fg
-/
theorem rTensor_preserves_injective_linearMap [Flat R M] (f : N ->ₗ[R] P)
    (hf : Function.Injective f) : Function.Injective (f.rTensor M) := by
  refine rTensor_injective_of_fg fun N P Nfg Pfg le => ?_
  rw [← Finite.iff_fg] at Nfg Pfg
  have := Finite.small R P
  let se := (Shrink.linearEquiv R P).symm
  have := Module.Finite.equiv se
  rw [rTensor_injective_iff_subtype (fun _ _ => (Subtype.ext <| hf <| Subtype.ext_iff.mp ·)) se]
  exact (flat_iff R M).mp ‹_› _ (Finite.iff_fg.mp inferInstance)

/--
theorem `lTensor_preserves_injective_linearMap` / 定理 `lTensor_preserves_injective_linearMap`

English:
theorem lTensor_preserves_injective_linearMap
  statement: [Flat R M] (f : N ->ₗ[R] P)
  proof: (f.lTensor_inj_iff_rTensor_inj M).2 (rTensor_preserves_injective_linearMap f hf)

中文:
定理 lTensor_preserves_injective_linearMap
  结论: [Flat R M] (f : N ->ₗ[R] P)
  证明: (f.lTensor_inj_iff_rTensor_inj M).2 (rTensor_preserves_injective_linearMap f hf)

Depends on / 依赖: f.lTensor_inj_iff_rTensor_inj, lTensor_inj_iff_rTensor_inj, rTensor_preserves_injective_linearMap
-/
theorem lTensor_preserves_injective_linearMap [Flat R M] (f : N ->ₗ[R] P)
    (hf : Function.Injective f) : Function.Injective (f.lTensor M) :=
  (f.lTensor_inj_iff_rTensor_inj M).2 (rTensor_preserves_injective_linearMap f hf)

/--
lemma `iff_rTensor_preserves_injective_linearMapₛ` / 引理 `iff_rTensor_preserves_injective_linearMapₛ`

English:
lemma iff_rTensor_preserves_injective_linearMapₛ
  given: [Small.{v'} R]
  statement: Flat R M ↔
  proof: ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h => ⟨fun P _ _ _ _ _ => by
    have := Finite.small.{v'} R P
    rw [rTensor_injective_iff_subtype Subtype.val_injective (Shrink.linearEquiv R P).symm]
    exact h _ Subtype.val_injective⟩⟩

中文:
引理 iff_rTensor_preserves_injective_linearMapₛ
  条件: [Small.{v'} R]
  结论: Flat R M ↔
  证明: ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h => ⟨fun P _ _ _ _ _ => by
    have := Finite.small.{v'} R P
    rw [rTensor_injective_iff_subtype Subtype.val_injective (Shrink.linearEquiv R P).symm]
    exact h _ Subtype.val_injective⟩⟩

Depends on / 依赖: Finite, Finite.small, Shrink, Shrink.linearEquiv, Subtype, Subtype.val_injective, introv, linearEquiv, rTensor_injective_iff_subtype, rTensor_preserves_injective_linearMap, val_injective
-/
lemma iff_rTensor_preserves_injective_linearMapₛ [Small.{v'} R] : Flat R M ↔
    forall ⦃N N' : Type v'⦄ [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
      (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.rTensor M) :=
  ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h => ⟨fun P _ _ _ _ _ => by
    have := Finite.small.{v'} R P
    rw [rTensor_injective_iff_subtype Subtype.val_injective (Shrink.linearEquiv R P).symm]
    exact h _ Subtype.val_injective⟩⟩

/--
lemma `iff_lTensor_preserves_injective_linearMapₛ` / 引理 `iff_lTensor_preserves_injective_linearMapₛ`

English:
lemma iff_lTensor_preserves_injective_linearMapₛ
  given: [Small.{v'} R]
  statement: Flat R M ↔
  proof: by
  simp_rw [iff_rTensor_preserves_injective_linearMapₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

中文:
引理 iff_lTensor_preserves_injective_linearMapₛ
  条件: [Small.{v'} R]
  结论: Flat R M ↔
  证明: by
  simp_rw [iff_rTensor_preserves_injective_linearMapₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

Depends on / 依赖: LinearMap, LinearMap.lTensor_inj_iff_rTensor_inj, lTensor_inj_iff_rTensor_inj, simp_rw
-/
lemma iff_lTensor_preserves_injective_linearMapₛ [Small.{v'} R] : Flat R M ↔
    forall ⦃N N' : Type v'⦄ [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
      (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMapₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

/--
lemma `iff_rTensor_injectiveₛ` / 引理 `iff_rTensor_injectiveₛ`

English:
lemma iff_rTensor_injectiveₛ
  statement: Flat R M ↔ forall ⦃P : Type u⦄ [AddCommMonoid P] [Module R P]
  proof: ⟨fun _ _ _ _ _ => rTensor_preserves_injective_linearMap _ Subtype.val_injective,
    fun h => ⟨fun _ _ _ _ _ _ => h _⟩⟩

中文:
引理 iff_rTensor_injectiveₛ
  结论: Flat R M ↔ 对任意 ⦃P : 类型u⦄ [AddCommMonoid P] [Module R P]
  证明: ⟨fun _ _ _ _ _ => rTensor_preserves_injective_linearMap _ Subtype.val_injective,
    fun h => ⟨fun _ _ _ _ _ _ => h _⟩⟩

Depends on / 依赖: Subtype, Subtype.val_injective, rTensor_preserves_injective_linearMap, val_injective
-/
lemma iff_rTensor_injectiveₛ : Flat R M ↔ forall ⦃P : Type u⦄ [AddCommMonoid P] [Module R P]
    (N : Submodule R P), Function.Injective (N.subtype.rTensor M) :=
  ⟨fun _ _ _ _ _ => rTensor_preserves_injective_linearMap _ Subtype.val_injective,
    fun h => ⟨fun _ _ _ _ _ _ => h _⟩⟩

/--
lemma `iff_lTensor_injectiveₛ` / 引理 `iff_lTensor_injectiveₛ`

English:
lemma iff_lTensor_injectiveₛ
  statement: Flat R M ↔ forall ⦃P : Type u⦄ [AddCommMonoid P] [Module R P]
  proof: by
  simp_rw [iff_rTensor_injectiveₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

中文:
引理 iff_lTensor_injectiveₛ
  结论: Flat R M ↔ 对任意 ⦃P : 类型u⦄ [AddCommMonoid P] [Module R P]
  证明: by
  simp_rw [iff_rTensor_injectiveₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

Depends on / 依赖: LinearMap, LinearMap.lTensor_inj_iff_rTensor_inj, lTensor_inj_iff_rTensor_inj, simp_rw
-/
lemma iff_lTensor_injectiveₛ : Flat R M ↔ forall ⦃P : Type u⦄ [AddCommMonoid P] [Module R P]
    (N : Submodule R P), Function.Injective (N.subtype.lTensor M) := by
  simp_rw [iff_rTensor_injectiveₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

/--
Instance `instSubalgebraToSubmodule` / 实例 `instSubalgebraToSubmodule`

English:
instance instSubalgebraToSubmodule
  signature: {S : Type v} [Semiring S] [Algebra R S]
  body: ‹Flat R A›

中文:
实例 instSubalgebraToSubmodule
  签名: {S : 类型v} [Semiring S] [Algebra R S]
  定义体: ‹Flat R A›
-/
instance instSubalgebraToSubmodule {S : Type v} [Semiring S] [Algebra R S]
    (A : Subalgebra R S) [Flat R A] : Flat R A.toSubmodule := ‹Flat R A›

/--
Instance `self` / 实例 `self`

English:
instance self
  signature: : Flat R R where
  body: by
    rw [← (TensorProduct.rid R I).symm.injective_comp]; rw [← (TensorProduct.rid R _).comp_injective]
    convert! Subtype.coe_injective using 1
    ext; simp

中文:
实例 self
  签名: : Flat R R where
  定义体: by
    rw [← (TensorProduct.rid R I).symm.injective_comp]; rw [← (TensorProduct.rid R _).comp_injective]
    convert! Subtype.coe_injective using 1
    ext; simp

Depends on / 依赖: Subtype, Subtype.coe_injective, TensorProduct, TensorProduct.rid, coe_injective, comp_injective, convert, injective_comp, symm.injective_comp
-/
instance self : Flat R R where
  out _ _ _ _ I _ := by
    rw [← (TensorProduct.rid R I).symm.injective_comp]; rw [← (TensorProduct.rid R _).comp_injective]
    convert! Subtype.coe_injective using 1
    ext; simp

/--
lemma `of_retract` / 引理 `of_retract`

English:
lemma of_retract
  given: [f : Flat R M] (i : N ->ₗ[R] M) (r : M ->ₗ[R] N) (h : r.comp i = LinearMap.id)
  proof: by
  rw [iff_rTensor_injectiveₛ] at *
  refine fun P _ _ Q => .of_comp (f := lTensor P i) ?_
  rw [← coe_comp]; rw [lTensor_comp_rTensor]; rw [← rTensor_comp_lTensor]; rw [coe_comp]
  refine (f Q).comp (Function.RightInverse.injective (g := lTensor Q r) fun x => ?_)
  simp [← comp_apply, ← lTensor_c

中文:
引理 of_retract
  条件: [f : Flat R M] (i : N ->ₗ[R] M) (r : M ->ₗ[R] N) (h : r.comp i = LinearMap.id)
  证明: by
  rw [iff_rTensor_injectiveₛ] at *
  refine fun P _ _ Q => .of_comp (f := lTensor P i) ?_
  rw [← coe_comp]; rw [lTensor_comp_rTensor]; rw [← rTensor_comp_lTensor]; rw [coe_comp]
  refine (f Q).comp (Function.RightInverse.injective (g := lTensor Q r) fun x => ?_)
  simp [← comp_apply, ← lTensor_c

Depends on / 依赖: Function, Function.RightInverse.injective, RightInverse, coe_comp, comp_apply, injective, lTensor, lTensor_comp, lTensor_comp_rTensor, of_comp, rTensor_comp_lTensor
-/
lemma of_retract [f : Flat R M] (i : N ->ₗ[R] M) (r : M ->ₗ[R] N) (h : r.comp i = LinearMap.id) :
    Flat R N := by
  rw [iff_rTensor_injectiveₛ] at *
  refine fun P _ _ Q => .of_comp (f := lTensor P i) ?_
  rw [← coe_comp]; rw [lTensor_comp_rTensor]; rw [← rTensor_comp_lTensor]; rw [coe_comp]
  refine (f Q).comp (Function.RightInverse.injective (g := lTensor Q r) fun x => ?_)
  simp [← comp_apply, ← lTensor_comp, h]

/--
lemma `of_linearEquiv` / 引理 `of_linearEquiv`

English:
lemma of_linearEquiv
  given: [Flat R M] (e : N ≃ₗ[R] M)
  statement: Flat R N
  proof: of_retract e.toLinearMap e.symm (by simp)

中文:
引理 of_linearEquiv
  条件: [Flat R M] (e : N ≃ₗ[R] M)
  结论: Flat R N
  证明: of_retract e.toLinearMap e.symm (by simp)

Depends on / 依赖: e.symm, e.toLinearMap, of_retract, toLinearMap
-/
lemma of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : Flat R N :=
  of_retract e.toLinearMap e.symm (by simp)

/--
lemma `equiv_iff` / 引理 `equiv_iff`

English:
lemma equiv_iff
  given: (e : M ≃ₗ[R] N)
  statement: Flat R M ↔ Flat R N
  proof: ⟨fun _ => of_linearEquiv e.symm, fun _ => of_linearEquiv e⟩

中文:
引理 equiv_iff
  条件: (e : M ≃ₗ[R] N)
  结论: Flat R M ↔ Flat R N
  证明: ⟨fun _ => of_linearEquiv e.symm, fun _ => of_linearEquiv e⟩

Depends on / 依赖: e.symm, of_linearEquiv
-/
lemma equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N :=
  ⟨fun _ => of_linearEquiv e.symm, fun _ => of_linearEquiv e⟩

/--
Instance `ulift` / 实例 `ulift`

English:
instance ulift
  signature: [Flat R M]
  body: of_linearEquiv ULift.moduleEquiv

中文:
实例 ulift
  签名: [Flat R M]
  定义体: of_linearEquiv ULift.moduleEquiv

Depends on / 依赖: ULift.moduleEquiv, moduleEquiv, of_linearEquiv
-/
instance ulift [Flat R M] : Flat R (ULift.{v'} M) :=
  of_linearEquiv ULift.moduleEquiv

-- Making this an instance causes an infinite sequence `M → ULift M → ULift (ULift M) → ...`.
/--
lemma `of_ulift` / 引理 `of_ulift`

English:
lemma of_ulift
  given: [Flat R (ULift.{v'} M)]
  statement: Flat R M
  proof: of_linearEquiv ULift.moduleEquiv.symm

中文:
引理 of_ulift
  条件: [Flat R (ULift.{v'} M)]
  结论: Flat R M
  证明: of_linearEquiv ULift.moduleEquiv.symm

Depends on / 依赖: ULift.moduleEquiv.symm, moduleEquiv, of_linearEquiv
-/
lemma of_ulift [Flat R (ULift.{v'} M)] : Flat R M :=
  of_linearEquiv ULift.moduleEquiv.symm

/--
Instance `shrink` / 实例 `shrink`

English:
instance shrink
  signature: [Small.{v'} M] [Flat R M]
  body: of_linearEquiv (Shrink.linearEquiv R M)

中文:
实例 shrink
  签名: [Small.{v'} M] [Flat R M]
  定义体: of_linearEquiv (Shrink.linearEquiv R M)

Depends on / 依赖: Shrink, Shrink.linearEquiv, linearEquiv, of_linearEquiv
-/
instance shrink [Small.{v'} M] [Flat R M] : Flat R (Shrink.{v'} M) :=
  of_linearEquiv (Shrink.linearEquiv R M)

-- Making this an instance causes an infinite sequence `M → Shrink M → Shrink (Shrink M) → ...`.
/--
lemma `of_shrink` / 引理 `of_shrink`

English:
lemma of_shrink
  given: [Small.{v'} M] [Flat R (Shrink.{v'} M)]
  statement: Flat R M
  proof: of_linearEquiv (Shrink.linearEquiv R M).symm

中文:
引理 of_shrink
  条件: [Small.{v'} M] [Flat R (Shrink.{v'} M)]
  结论: Flat R M
  证明: of_linearEquiv (Shrink.linearEquiv R M).symm

Depends on / 依赖: Shrink, Shrink.linearEquiv, linearEquiv, of_linearEquiv
-/
lemma of_shrink [Small.{v'} M] [Flat R (Shrink.{v'} M)] : Flat R M :=
  of_linearEquiv (Shrink.linearEquiv R M).symm

section DirectSum

variable {ι : Type v} {M : ι -> Type w} [Π i, AddCommMonoid (M i)] [Π i, Module R (M i)]

/--
theorem `directSum_iff` / 定理 `directSum_iff`

English:
theorem directSum_iff
  statement: Flat R (⨁ i, M i) ↔ forall i, Flat R (M i)
  proof: by
  classical
  simp_rw [iff_rTensor_injectiveₛ, ← EquivLike.comp_injective _ (directSumRight R R _ _),
    ← LinearEquiv.coe_coe, ← coe_comp, directSumRight_comp_rTensor, coe_comp, LinearEquiv.coe_coe,
    EquivLike.injective_comp, lmap_injective]
  constructor <;> (intro h; intros; apply h)

中文:
定理 directSum_iff
  结论: Flat R (⨁ i, M i) ↔ 对任意 i, Flat R (M i)
  证明: by
  classical
  simp_rw [iff_rTensor_injectiveₛ, ← EquivLike.comp_injective _ (directSumRight R R _ _),
    ← LinearEquiv.coe_coe, ← coe_comp, directSumRight_comp_rTensor, coe_comp, LinearEquiv.coe_coe,
    EquivLike.injective_comp, lmap_injective]
  constructor <;> (intro h; intros; apply h)

Depends on / 依赖: EquivLike, EquivLike.comp_injective, EquivLike.injective_comp, LinearEquiv, LinearEquiv.coe_coe, classical, coe_coe, coe_comp, comp_injective, directSumRight, directSumRight_comp_rTensor, injective_comp, intros, lmap_injective, simp_rw
-/
theorem directSum_iff : Flat R (⨁ i, M i) ↔ forall i, Flat R (M i) := by
  classical
  simp_rw [iff_rTensor_injectiveₛ, ← EquivLike.comp_injective _ (directSumRight R R _ _),
    ← LinearEquiv.coe_coe, ← coe_comp, directSumRight_comp_rTensor, coe_comp, LinearEquiv.coe_coe,
    EquivLike.injective_comp, lmap_injective]
  constructor <;> (intro h; intros; apply h)

/--
theorem `dfinsupp_iff` / 定理 `dfinsupp_iff`

English:
theorem dfinsupp_iff
  statement: Flat R (Π₀ i, M i) ↔ forall i, Flat R (M i)
  proof: directSum_iff ..

中文:
定理 dfinsupp_iff
  结论: Flat R (Π₀ i, M i) ↔ 对任意 i, Flat R (M i)
  证明: directSum_iff ..

Depends on / 依赖: directSum_iff
-/
theorem dfinsupp_iff : Flat R (Π₀ i, M i) ↔ forall i, Flat R (M i) := directSum_iff ..

/--
Instance `directSum` / 实例 `directSum`

English:
instance directSum
  signature: [forall i, Flat R (M i)]
  body: directSum_iff.mpr ‹_›

中文:
实例 directSum
  签名: [对任意 i, Flat R (M i)]
  定义体: directSum_iff.mpr ‹_›

Depends on / 依赖: directSum_iff, directSum_iff.mpr
-/
instance directSum [forall i, Flat R (M i)] : Flat R (⨁ i, M i) := directSum_iff.mpr ‹_›

/--
Instance `dfinsupp` / 实例 `dfinsupp`

English:
instance dfinsupp
  signature: [forall i, Flat R (M i)]
  body: dfinsupp_iff.mpr ‹_›

中文:
实例 dfinsupp
  签名: [对任意 i, Flat R (M i)]
  定义体: dfinsupp_iff.mpr ‹_›

Depends on / 依赖: dfinsupp_iff, dfinsupp_iff.mpr
-/
instance dfinsupp [forall i, Flat R (M i)] : Flat R (Π₀ i, M i) := dfinsupp_iff.mpr ‹_›

end DirectSum

/--
Instance `finsupp` / 实例 `finsupp`

English:
instance finsupp
  signature: (ι : Type v)
  body: by
  classical exact of_linearEquiv (finsuppLEquivDirectSum R R ι)

中文:
实例 finsupp
  签名: (ι : 类型v)
  定义体: by
  classical exact of_linearEquiv (finsuppLEquivDirectSum R R ι)

Depends on / 依赖: classical, finsuppLEquivDirectSum, of_linearEquiv
-/
instance finsupp (ι : Type v) : Flat R (ι ->₀ R) := by
  classical exact of_linearEquiv (finsuppLEquivDirectSum R R ι)

/--
Instance `of_projective` / 实例 `of_projective`

English:
instance of_projective
  signature: [Projective R M]
  body: have ⟨e, he⟩ := Module.projective_def'.mp ‹_›
  of_retract _ _ he

中文:
实例 of_projective
  签名: [Projective R M]
  定义体: have ⟨e, he⟩ := Module.projective_def'.mp ‹_›
  of_retract _ _ he

Depends on / 依赖: Module, Module.projective_def, of_retract, projective_def
-/
instance of_projective [Projective R M] : Flat R M :=
  have ⟨e, he⟩ := Module.projective_def'.mp ‹_›
  of_retract _ _ he

/--
Instance `of_free` / 实例 `of_free`

English:
instance of_free
  signature: [Free R M]
  body: inferInstance

中文:
实例 of_free
  签名: [Free R M]
  定义体: inferInstance

Depends on / 依赖: List.cons, Multiseries, basis_hd, basis_tl
-/
instance of_free [Free R M] : Flat R M := inferInstance

instance {S} [CommSemiring S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [Flat S M] [Flat R N] : Flat S (M otimes[R] N) :=
  iff_rTensor_injectiveₛ.mpr fun P _ _ I => by
    let := RestrictScalars.moduleOrig R S P
    change Submodule S (RestrictScalars R S P) at I
    change Function.Injective (rTensor _ I.subtype)
    simpa [AlgebraTensorModule.rTensor_tensor] using!
      rTensor_preserves_injective_linearMap (.restrictScalars R <| I.subtype.rTensor M)
      (rTensor_preserves_injective_linearMap _ I.injective_subtype)

example [Flat R M] [Flat R N] : Flat R (M otimes[R] N) := inferInstance

section Algebra

variable {S : Type*} [Semiring S] [Algebra R S]

/--
theorem `linearIndependent_one_tmul` / 定理 `linearIndependent_one_tmul`

English:
theorem linearIndependent_one_tmul
  statement: [Flat R S] {ι} {v : ι -> M}
  proof: by
  classical rw [LinearIndependent, ← LinearMap.coe_restrictScalars R,
    Finsupp.linearCombination_one_tmul]
  simpa using lTensor_preserves_injective_linearMap _ hv

中文:
定理 linearIndependent_one_tmul
  结论: [Flat R S] {ι} {v : ι -> M}
  证明: by
  classical rw [LinearIndependent, ← LinearMap.coe_restrictScalars R,
    Finsupp.linearCombination_one_tmul]
  simpa using lTensor_preserves_injective_linearMap _ hv

Depends on / 依赖: Finsupp, Finsupp.linearCombination_one_tmul, LinearIndependent, LinearMap, LinearMap.coe_restrictScalars, classical, coe_restrictScalars, lTensor_preserves_injective_linearMap, linearCombination_one_tmul
-/
theorem linearIndependent_one_tmul [Flat R S] {ι} {v : ι -> M}
    (hv : LinearIndependent R v) : LinearIndependent S ((1 : S) otimesₜ[R] v ·) := by
  classical rw [LinearIndependent, ← LinearMap.coe_restrictScalars R,
    Finsupp.linearCombination_one_tmul]
  simpa using lTensor_preserves_injective_linearMap _ hv

variable (R S M)

/--
lemma `tensorProduct_mk_injective` / 引理 `tensorProduct_mk_injective`

English:
lemma tensorProduct_mk_injective
  given: [FaithfulSMul R S] [Flat R M]
  proof: by
  have : TensorProduct.mk R S M 1 =
      (Algebra.linearMap R S).rTensor M ∘ (TensorProduct.lid R M).symm := by ext; simp
  rw [this]
  refine Injective.comp ?_ (LinearEquiv.injective _)
exact Flat.rTensor_preserves_injective_linearMap _ FaithfulSMul.algebraMap_injective R S

中文:
引理 tensorProduct_mk_injective
  条件: [FaithfulSMul R S] [Flat R M]
  证明: by
  have : TensorProduct.mk R S M 1 =
      (Algebra.linearMap R S).rTensor M ∘ (TensorProduct.lid R M).symm := by ext; simp
  rw [this]
  refine Injective.comp ?_ (LinearEquiv.injective _)
exact Flat.rTensor_preserves_injective_linearMap _ FaithfulSMul.algebraMap_injective R S

Depends on / 依赖: Algebra, Algebra.linearMap, FaithfulSMul, FaithfulSMul.algebraMap_injective, Flat.rTensor_preserves_injective_linearMap, Injective, Injective.comp, LinearEquiv, LinearEquiv.injective, TensorProduct, TensorProduct.lid, TensorProduct.mk, algebraMap_injective, injective, linearMap, rTensor, rTensor_preserves_injective_linearMap
-/
lemma tensorProduct_mk_injective [FaithfulSMul R S] [Flat R M] :
    Injective (TensorProduct.mk R S M 1) := by
  have : TensorProduct.mk R S M 1 =
      (Algebra.linearMap R S).rTensor M ∘ (TensorProduct.lid R M).symm := by ext; simp
  rw [this]
  refine Injective.comp ?_ (LinearEquiv.injective _)
exact Flat.rTensor_preserves_injective_linearMap _ FaithfulSMul.algebraMap_injective R S

/--
lemma `_root_.LinearMap.baseChangeHom_injective` / 引理 `_root_.LinearMap.baseChangeHom_injective`

English:
lemma _root_.LinearMap.baseChangeHom_injective
  given: [FaithfulSMul R S] [Flat R N]
  proof: by
  intro f g h
  ext m
simpa using Flat.tensorProduct_mk_injective R N S LinearMap.congr_fun h (1 otimesₜ[R] m)

中文:
引理 _root_.LinearMap.baseChangeHom_injective
  条件: [FaithfulSMul R S] [Flat R N]
  证明: by
  intro f g h
  ext m
simpa using Flat.tensorProduct_mk_injective R N S LinearMap.congr_fun h (1 otimesₜ[R] m)

Depends on / 依赖: Flat.tensorProduct_mk_injective, LinearMap, LinearMap.congr_fun, congr_fun, tensorProduct_mk_injective
-/
lemma _root_.LinearMap.baseChangeHom_injective [FaithfulSMul R S] [Flat R N] :
    Injective (LinearMap.baseChangeHom R S M N) := by
  intro f g h
  ext m
simpa using Flat.tensorProduct_mk_injective R N S LinearMap.congr_fun h (1 otimesₜ[R] m)

end Algebra

end Flat

end Semiring

namespace Flat

/-! ### Flatness over a ring -/

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/--
lemma `iff_rTensor_preserves_injective_linearMap'` / 引理 `iff_rTensor_preserves_injective_linearMap'`

English:
lemma iff_rTensor_preserves_injective_linearMap'
  given: [Small.{v'} R]
  statement: Flat R M ↔
  proof: ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h =>
    iff_rTensor_preserves_injective_linearMapₛ.mpr fun P N _ _ _ _ => by
      let := Module.addCommMonoidToAddCommGroup R (M := P)
      let := Module.addCommMonoidToAddCommGroup R (M := N)
      apply h⟩

中文:
引理 iff_rTensor_preserves_injective_linearMap'
  条件: [Small.{v'} R]
  结论: Flat R M ↔
  证明: ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h =>
    iff_rTensor_preserves_injective_linearMapₛ.mpr fun P N _ _ _ _ => by
      let := Module.addCommMonoidToAddCommGroup R (M := P)
      let := Module.addCommMonoidToAddCommGroup R (M := N)
      apply h⟩

Depends on / 依赖: Module, Module.addCommMonoidToAddCommGroup, addCommMonoidToAddCommGroup, introv, rTensor_preserves_injective_linearMap
-/
lemma iff_rTensor_preserves_injective_linearMap' [Small.{v'} R] : Flat R M ↔
    forall ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.rTensor M) :=
  ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h =>
    iff_rTensor_preserves_injective_linearMapₛ.mpr fun P N _ _ _ _ => by
      let := Module.addCommMonoidToAddCommGroup R (M := P)
      let := Module.addCommMonoidToAddCommGroup R (M := N)
      apply h⟩

/--
lemma `iff_rTensor_preserves_injective_linearMap` / 引理 `iff_rTensor_preserves_injective_linearMap`

English:
lemma iff_rTensor_preserves_injective_linearMap
  statement: Flat R M ↔
  proof: iff_rTensor_preserves_injective_linearMap'

中文:
引理 iff_rTensor_preserves_injective_linearMap
  结论: Flat R M ↔
  证明: iff_rTensor_preserves_injective_linearMap'

Depends on / 依赖: iff_rTensor_preserves_injective_linearMap
-/
lemma iff_rTensor_preserves_injective_linearMap : Flat R M ↔
    forall ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.rTensor M) :=
  iff_rTensor_preserves_injective_linearMap'

/--
lemma `iff_lTensor_preserves_injective_linearMap'` / 引理 `iff_lTensor_preserves_injective_linearMap'`

English:
lemma iff_lTensor_preserves_injective_linearMap'
  given: [Small.{v'} R]
  statement: Flat R M ↔
  proof: by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]

中文:
引理 iff_lTensor_preserves_injective_linearMap'
  条件: [Small.{v'} R]
  结论: Flat R M ↔
  证明: by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]

Depends on / 依赖: LinearMap, LinearMap.lTensor_inj_iff_rTensor_inj, iff_rTensor_preserves_injective_linearMap, lTensor_inj_iff_rTensor_inj, simp_rw
-/
lemma iff_lTensor_preserves_injective_linearMap' [Small.{v'} R] : Flat R M ↔
    forall ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]

/--
lemma `iff_lTensor_preserves_injective_linearMap` / 引理 `iff_lTensor_preserves_injective_linearMap`

English:
lemma iff_lTensor_preserves_injective_linearMap
  statement: Flat R M ↔
  proof: iff_lTensor_preserves_injective_linearMap'

中文:
引理 iff_lTensor_preserves_injective_linearMap
  结论: Flat R M ↔
  证明: iff_lTensor_preserves_injective_linearMap'

Depends on / 依赖: iff_lTensor_preserves_injective_linearMap
-/
lemma iff_lTensor_preserves_injective_linearMap : Flat R M ↔
    forall ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.lTensor M) :=
  iff_lTensor_preserves_injective_linearMap'

variable (M) in
/--
lemma `lTensor_exact` / 引理 `lTensor_exact`

English:
lemma lTensor_exact
  given: [Flat R M] ⦃N N' N''
  statement: Type*⦄
  proof: by
  let π : N' ->ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f ->ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  

中文:
引理 lTensor_exact
  条件: [Flat R M] ⦃N N' N''
  结论: 类型⦄
  证明: by
  let π : N' ->ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f ->ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  

Depends on / 依赖: Function, Function.Exact, LinearMap, LinearMap.exact_iff.mp, LinearMap.ker, LinearMap.quotKerEquivRange, LinearMap.range, Submodule, Submodule.mkQ, Submodule.quotEquivOfEq, Submodule.subtype, Subtype, Subtype.val_injective, comp_injective, exact1, exact1.comp_injective, exact_iff, f.lTensor, lTensor, lTensor_comp
-/
lemma lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  let π : N' ->ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f ->ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.lTensor M) (π.lTensor M) by
    rw [show g = ι.comp π from rfl]; rw [lTensor_comp]
    exact exact1.comp_injective _ (lTensor_preserves_injective_linearMap ι <| by
      simpa [ι, -Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.lTensor_exact _ (fun x => by simp [π]) Quotient.mk''_surjective

variable (M) in
/--
lemma `rTensor_exact` / 引理 `rTensor_exact`

English:
lemma rTensor_exact
  given: [Flat R M] ⦃N N' N''
  statement: Type*⦄
  proof: by
  let π : N' ->ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f ->ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  

中文:
引理 rTensor_exact
  条件: [Flat R M] ⦃N N' N''
  结论: 类型⦄
  证明: by
  let π : N' ->ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f ->ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  

Depends on / 依赖: Function, Function.Exact, LinearMap, LinearMap.exact_iff.mp, LinearMap.ker, LinearMap.quotKerEquivRange, LinearMap.range, Submodule, Submodule.mkQ, Submodule.quotEquivOfEq, Submodule.subtype, Subtype, Subtype.val_injective, comp_injective, exact1, exact1.comp_injective, exact_iff, f.rTensor, quotEquivOfEq, quotKerEquivRange
-/
lemma rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.rTensor M) (g.rTensor M) := by
  let π : N' ->ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f ->ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.rTensor M) (π.rTensor M) by
    rw [show g = ι.comp π from rfl]; rw [rTensor_comp]
    exact exact1.comp_injective _ (rTensor_preserves_injective_linearMap ι <| by
      simpa [ι, -Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.rTensor_exact M (fun x => by simp [π]) Quotient.mk''_surjective

/--
theorem `iff_lTensor_exact'` / 定理 `iff_lTensor_exact'`

English:
theorem iff_lTensor_exact'
  given: [Small.{v'} R]
  statement: Flat R M ↔
  proof: by
  refine ⟨fun _ => lTensor_exact _, fun H => iff_lTensor_preserves_injective_linearMap'.mpr
.mp .mpr eq_bot_iff fun N' N'' _ _ _ _ L hL => LinearMap.ker_eq_bot
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x => by
    simp_rw [Set.mem_range, LinearMa

中文:
定理 iff_lTensor_exact'
  条件: [Small.{v'} R]
  结论: Flat R M ↔
  证明: by
  refine ⟨fun _ => lTensor_exact _, fun H => iff_lTensor_preserves_injective_linearMap'.mpr
.mp .mpr eq_bot_iff fun N' N'' _ _ _ _ L hL => LinearMap.ker_eq_bot
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x => by
    simp_rw [Set.mem_range, LinearMa

Depends on / 依赖: Eq.comm, L.map_eq_zero_iff, LinearMap, LinearMap.ker_eq_bot, LinearMap.zero_apply, Set.mem_range, eq_bot_iff, eq_comm, exists_const, iff_lTensor_preserves_injective_linearMap, ker_eq_bot, lTensor_exact, map_eq_zero_iff, mem_range, simp_rw, zero_apply
-/
theorem iff_lTensor_exact' [Small.{v'} R] : Flat R M ↔
    forall ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄,
        Function.Exact f g -> Function.Exact (f.lTensor M) (g.lTensor M) := by
  refine ⟨fun _ => lTensor_exact _, fun H => iff_lTensor_preserves_injective_linearMap'.mpr
.mp .mpr eq_bot_iff fun N' N'' _ _ _ _ L hL => LinearMap.ker_eq_bot
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x => by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (L.map_eq_zero_iff hL).trans eq_comm) x |>.mp hx

/--
theorem `iff_lTensor_exact` / 定理 `iff_lTensor_exact`

English:
theorem iff_lTensor_exact
  statement: Flat R M ↔
  proof: iff_lTensor_exact'

中文:
定理 iff_lTensor_exact
  结论: Flat R M ↔
  证明: iff_lTensor_exact'

Depends on / 依赖: iff_lTensor_exact
-/
theorem iff_lTensor_exact : Flat R M ↔
    forall ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄,
        Function.Exact f g -> Function.Exact (f.lTensor M) (g.lTensor M) :=
  iff_lTensor_exact'

/--
theorem `iff_rTensor_exact'` / 定理 `iff_rTensor_exact'`

English:
theorem iff_rTensor_exact'
  given: [Small.{v'} R]
  statement: Flat R M ↔
  proof: by
  refine ⟨fun _ => rTensor_exact _, fun H => iff_rTensor_preserves_injective_linearMap'.mpr
.mp .mpr eq_bot_iff fun N' N'' _ _ _ _ f hf => LinearMap.ker_eq_bot
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 f (fun x => by
    simp_rw [Set.mem_range, LinearMa

中文:
定理 iff_rTensor_exact'
  条件: [Small.{v'} R]
  结论: Flat R M ↔
  证明: by
  refine ⟨fun _ => rTensor_exact _, fun H => iff_rTensor_preserves_injective_linearMap'.mpr
.mp .mpr eq_bot_iff fun N' N'' _ _ _ _ f hf => LinearMap.ker_eq_bot
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 f (fun x => by
    simp_rw [Set.mem_range, LinearMa

Depends on / 依赖: Eq.comm, LinearMap, LinearMap.ker_eq_bot, LinearMap.zero_apply, Set.mem_range, eq_bot_iff, eq_comm, exists_const, f.map_eq_zero_iff, iff_rTensor_preserves_injective_linearMap, ker_eq_bot, map_eq_zero_iff, mem_range, rTensor_exact, simp_rw, zero_apply
-/
theorem iff_rTensor_exact' [Small.{v'} R] : Flat R M ↔
    forall ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄,
        Function.Exact f g -> Function.Exact (f.rTensor M) (g.rTensor M) := by
  refine ⟨fun _ => rTensor_exact _, fun H => iff_rTensor_preserves_injective_linearMap'.mpr
.mp .mpr eq_bot_iff fun N' N'' _ _ _ _ f hf => LinearMap.ker_eq_bot
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 f (fun x => by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (f.map_eq_zero_iff hf).trans eq_comm) x |>.mp hx

/--
theorem `iff_rTensor_exact` / 定理 `iff_rTensor_exact`

English:
theorem iff_rTensor_exact
  statement: Flat R M ↔
  proof: iff_rTensor_exact'

中文:
定理 iff_rTensor_exact
  结论: Flat R M ↔
  证明: iff_rTensor_exact'

Depends on / 依赖: iff_rTensor_exact
-/
theorem iff_rTensor_exact : Flat R M ↔
    forall ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄,
        Function.Exact f g -> Function.Exact (f.rTensor M) (g.rTensor M) :=
  iff_rTensor_exact'

end Flat

end Module

section Injective

variable {R S A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CommSemiring S] [Algebra S A] [SMulCommClass R S A]

namespace Algebra.TensorProduct

/--
theorem `includeLeft_injective` / 定理 `includeLeft_injective`

English:
theorem includeLeft_injective
  given: [Module.Flat R A] (hb : Function.Injective (algebraMap R B))
  proof: by
  convert!
.comp Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R B) hb
      (_root_.TensorProduct.rid R A).symm.injective
  ext; simp

中文:
定理 includeLeft_injective
  条件: [Module.Flat R A] (hb : Function.Injective (algebraMap R B))
  证明: by
  convert!
.comp Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R B) hb
      (_root_.TensorProduct.rid R A).symm.injective
  ext; simp

Depends on / 依赖: Algebra, Algebra.linearMap, Module, Module.Flat.lTensor_preserves_injective_linearMap, TensorProduct, _root_, _root_.TensorProduct.rid, convert, injective, lTensor_preserves_injective_linearMap, linearMap, symm.injective
-/
theorem includeLeft_injective [Module.Flat R A] (hb : Function.Injective (algebraMap R B)) :
    Function.Injective (includeLeft : A ->ₐ[S] A otimes[R] B) := by
  convert!
.comp Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R B) hb
      (_root_.TensorProduct.rid R A).symm.injective
  ext; simp

/--
theorem `includeRight_injective` / 定理 `includeRight_injective`

English:
theorem includeRight_injective
  given: [Module.Flat R B] (ha : Function.Injective (algebraMap R A))
  proof: by
  convert!
.comp Module.Flat.rTensor_preserves_injective_linearMap (M := B) (Algebra.linearMap R A) ha
      (_root_.TensorProduct.lid R B).symm.injective
  ext; simp

中文:
定理 includeRight_injective
  条件: [Module.Flat R B] (ha : Function.Injective (algebraMap R A))
  证明: by
  convert!
.comp Module.Flat.rTensor_preserves_injective_linearMap (M := B) (Algebra.linearMap R A) ha
      (_root_.TensorProduct.lid R B).symm.injective
  ext; simp

Depends on / 依赖: Algebra, Algebra.linearMap, Module, Module.Flat.rTensor_preserves_injective_linearMap, TensorProduct, _root_, _root_.TensorProduct.lid, convert, injective, linearMap, rTensor_preserves_injective_linearMap, symm.injective
-/
theorem includeRight_injective [Module.Flat R B] (ha : Function.Injective (algebraMap R A)) :
    Function.Injective (includeRight : B ->ₐ[R] A otimes[R] B) := by
  convert!
.comp Module.Flat.rTensor_preserves_injective_linearMap (M := B) (Algebra.linearMap R A) ha
      (_root_.TensorProduct.lid R B).symm.injective
  ext; simp

end Algebra.TensorProduct

variable (A) [Module.Flat R A] {M : Type*} [AddCommMonoid M] [Module R M] (p : Submodule R M)

namespace Submodule

/--
theorem `toBaseChange_injective` / 定理 `toBaseChange_injective`

English:
theorem toBaseChange_injective
  statement: Function.Injective (p.toBaseChange A)
  proof: (p.subtype.baseChange A).injective_rangeRestrict_iff.mpr
    (Module.Flat.lTensor_preserves_injective_linearMap p.subtype (injective_subtype p))

中文:
定理 toBaseChange_injective
  结论: Function.Injective (p.toBaseChange A)
  证明: (p.subtype.baseChange A).injective_rangeRestrict_iff.mpr
    (Module.Flat.lTensor_preserves_injective_linearMap p.subtype (injective_subtype p))

Depends on / 依赖: Module, Module.Flat.lTensor_preserves_injective_linearMap, baseChange, injective_rangeRestrict_iff, injective_rangeRestrict_iff.mpr, injective_subtype, lTensor_preserves_injective_linearMap, p.subtype, p.subtype.baseChange, subtype
-/
theorem toBaseChange_injective : Function.Injective (p.toBaseChange A) :=
  (p.subtype.baseChange A).injective_rangeRestrict_iff.mpr
    (Module.Flat.lTensor_preserves_injective_linearMap p.subtype (injective_subtype p))

/-- `Submodule.toBaseChange` as a `LinearEquiv`. -/
@[simps! apply]
/--
Definition of `toBaseChange.toLinearEquiv` / `toBaseChange.toLinearEquiv` 的定义

English:
definition toBaseChange.toLinearEquiv
  signature: : A otimes[R] ↥p ≃ₗ[A] baseChange A p
  body: .ofBijective (p.toBaseChange A) ⟨p.toBaseChange_injective A, p.toBaseChange_surjective A⟩

@[simp]

中文:
定义 toBaseChange.toLinearEquiv
  签名: : A otimes[R] ↥p ≃ₗ[A] baseChange A p
  定义体: .ofBijective (p.toBaseChange A) ⟨p.toBaseChange_injective A, p.toBaseChange_surjective A⟩

@[simp]

Depends on / 依赖: ofBijective, p.toBaseChange, p.toBaseChange_injective, p.toBaseChange_surjective, toBaseChange, toBaseChange_injective, toBaseChange_surjective
-/
noncomputable def toBaseChange.toLinearEquiv : A otimes[R] ↥p ≃ₗ[A] baseChange A p :=
  .ofBijective (p.toBaseChange A) ⟨p.toBaseChange_injective A, p.toBaseChange_surjective A⟩

@[simp]
/--
theorem `toBaseChange.toLinearEquiv_symm_apply` / 定理 `toBaseChange.toLinearEquiv_symm_apply`

English:
theorem toBaseChange.toLinearEquiv_symm_apply
  given: (a : A) (m : p)
  proof: (toBaseChange.toLinearEquiv A p).symm_apply_apply (a otimesₜ[R] m)

中文:
定理 toBaseChange.toLinearEquiv_symm_apply
  条件: (a : A) (m : p)
  证明: (toBaseChange.toLinearEquiv A p).symm_apply_apply (a otimesₜ[R] m)

Depends on / 依赖: symm_apply_apply, toBaseChange, toBaseChange.toLinearEquiv, toLinearEquiv
-/
theorem toBaseChange.toLinearEquiv_symm_apply (a : A) (m : p) :
    (toBaseChange.toLinearEquiv A p).symm
      ⟨a otimesₜ[R] m, tmul_mem_baseChange_of_mem a m.2⟩ = a otimesₜ[R] m :=
  (toBaseChange.toLinearEquiv A p).symm_apply_apply (a otimesₜ[R] m)

end Submodule

end Injective

section Nontrivial

variable (R : Type*) [CommSemiring R]

namespace TensorProduct

variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/--
theorem `nontrivial_of_linearMap_injective_of_flat_left` / 定理 `nontrivial_of_linearMap_injective_of_flat_left`

English:
theorem nontrivial_of_linearMap_injective_of_flat_left
  statement: (f : R ->ₗ[R] N) (h : Function.Injective f)
  proof: .comp Module.Flat.lTensor_preserves_injective_linearMap (M := M) f h
.nontrivial (TensorProduct.rid R M).symm.injective

中文:
定理 nontrivial_of_linearMap_injective_of_flat_left
  结论: (f : R ->ₗ[R] N) (h : Function.Injective f)
  证明: .comp Module.Flat.lTensor_preserves_injective_linearMap (M := M) f h
.nontrivial (TensorProduct.rid R M).symm.injective

Depends on / 依赖: Module, Module.Flat.lTensor_preserves_injective_linearMap, TensorProduct, TensorProduct.rid, injective, lTensor_preserves_injective_linearMap, nontrivial, symm.injective
-/
theorem nontrivial_of_linearMap_injective_of_flat_left (f : R ->ₗ[R] N) (h : Function.Injective f)
    [Module.Flat R M] [Nontrivial M] : Nontrivial (M otimes[R] N) :=
.comp Module.Flat.lTensor_preserves_injective_linearMap (M := M) f h
.nontrivial (TensorProduct.rid R M).symm.injective

/--
theorem `nontrivial_of_linearMap_injective_of_flat_right` / 定理 `nontrivial_of_linearMap_injective_of_flat_right`

English:
theorem nontrivial_of_linearMap_injective_of_flat_right
  statement: (f : R ->ₗ[R] M) (h : Function.Injective f)
  proof: .comp Module.Flat.rTensor_preserves_injective_linearMap (M := N) f h
.nontrivial (TensorProduct.lid R N).symm.injective

中文:
定理 nontrivial_of_linearMap_injective_of_flat_right
  结论: (f : R ->ₗ[R] M) (h : Function.Injective f)
  证明: .comp Module.Flat.rTensor_preserves_injective_linearMap (M := N) f h
.nontrivial (TensorProduct.lid R N).symm.injective

Depends on / 依赖: Module, Module.Flat.rTensor_preserves_injective_linearMap, TensorProduct, TensorProduct.lid, injective, nontrivial, rTensor_preserves_injective_linearMap, symm.injective
-/
theorem nontrivial_of_linearMap_injective_of_flat_right (f : R ->ₗ[R] M) (h : Function.Injective f)
    [Module.Flat R N] [Nontrivial N] : Nontrivial (M otimes[R] N) :=
.comp Module.Flat.rTensor_preserves_injective_linearMap (M := N) f h
.nontrivial (TensorProduct.lid R N).symm.injective

variable {R M N}
variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/--
lemma `map_injective_of_flat_flat` / 引理 `map_injective_of_flat_flat`

English:
lemma map_injective_of_flat_flat
  proof: by
  rw [← LinearMap.lTensor_comp_rTensor]
  exact (Module.Flat.lTensor_preserves_injective_linearMap g hg).comp
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)

中文:
引理 map_injective_of_flat_flat
  证明: by
  rw [← LinearMap.lTensor_comp_rTensor]
  exact (Module.Flat.lTensor_preserves_injective_linearMap g hg).comp
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)

Depends on / 依赖: LinearMap, LinearMap.lTensor_comp_rTensor, Module, Module.Flat.lTensor_preserves_injective_linearMap, Module.Flat.rTensor_preserves_injective_linearMap, lTensor_comp_rTensor, lTensor_preserves_injective_linearMap, rTensor_preserves_injective_linearMap
-/
lemma map_injective_of_flat_flat
    (f : P ->ₗ[R] M) (g : Q ->ₗ[R] N) [Module.Flat R M] [Module.Flat R Q]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.lTensor_comp_rTensor]
  exact (Module.Flat.lTensor_preserves_injective_linearMap g hg).comp
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)

/--
lemma `map_injective_of_flat_flat'` / 引理 `map_injective_of_flat_flat'`

English:
lemma map_injective_of_flat_flat'
  proof: by
  rw [← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)

中文:
引理 map_injective_of_flat_flat'
  证明: by
  rw [← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)

Depends on / 依赖: LinearMap, LinearMap.rTensor_comp_lTensor, Module, Module.Flat.lTensor_preserves_injective_linearMap, Module.Flat.rTensor_preserves_injective_linearMap, lTensor_preserves_injective_linearMap, rTensor_comp_lTensor, rTensor_preserves_injective_linearMap
-/
lemma map_injective_of_flat_flat'
    (f : P ->ₗ[R] M) (g : Q ->ₗ[R] N) [Module.Flat R P] [Module.Flat R N]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)

variable {ι κ : Type*} {v : ι -> M} {w : κ -> N} {s : Set ι} {t : Set κ}

/--
lemma `_root_.LinearIndependent.tmul_of_flat_left` / 引理 `_root_.LinearIndependent.tmul_of_flat_left`

English:
lemma _root_.LinearIndependent.tmul_of_flat_left
  statement: [Module.Flat R M] (hv : LinearIndependent R v)
  proof: by
  rw [LinearIndependent]
  convert!
    (TensorProduct.map_injective_of_flat_flat _ _ hv hw).comp
      (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

中文:
引理 _root_.LinearIndependent.tmul_of_flat_left
  结论: [Module.Flat R M] (hv : LinearIndependent R v)
  证明: by
  rw [LinearIndependent]
  convert!
    (TensorProduct.map_injective_of_flat_flat _ _ hv hw).comp
      (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_toLinearMap, LinearIndependent, LinearMap, LinearMap.coe_comp, TensorProduct, TensorProduct.map_injective_of_flat_flat, _symm_single_eq_single_one_tmul, coe_comp, coe_toLinearMap, convert, finsuppTensorFinsupp, injective, map_injective_of_flat_flat, symm.injective
-/
lemma _root_.LinearIndependent.tmul_of_flat_left [Module.Flat R M] (hv : LinearIndependent R v)
    (hw : LinearIndependent R w) : LinearIndependent R fun i : ι × κ => v i.1 otimesₜ[R] w i.2 := by
  rw [LinearIndependent]
  convert!
    (TensorProduct.map_injective_of_flat_flat _ _ hv hw).comp
      (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndepOn.tmul_of_isDomain`. -/
nonrec lemma LinearIndepOn.tmul_of_flat_left [Module.Flat R M] (hv : LinearIndepOn R v s)
    (hw : LinearIndepOn R w t) : LinearIndepOn R (fun i : ι × κ => v i.1 otimesₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_flat_left hw).comp _ (Equiv.Set.prod _ _).injective :)

/--
lemma `_root_.LinearIndependent.tmul_of_flat_right` / 引理 `_root_.LinearIndependent.tmul_of_flat_right`

English:
lemma _root_.LinearIndependent.tmul_of_flat_right
  statement: [Module.Flat R N] (hv : LinearIndependent R v)
  proof: (((TensorProduct.comm R N M).toLinearMap.linearIndependent_iff_of_injOn
    (TensorProduct.comm R N M).injective.injOn).mpr
      (hw.tmul_of_flat_left hv)).comp Prod.swap Prod.swap_bijective.injective

中文:
引理 _root_.LinearIndependent.tmul_of_flat_right
  结论: [Module.Flat R N] (hv : LinearIndependent R v)
  证明: (((TensorProduct.comm R N M).toLinearMap.linearIndependent_iff_of_injOn
    (TensorProduct.comm R N M).injective.injOn).mpr
      (hw.tmul_of_flat_left hv)).comp Prod.swap Prod.swap_bijective.injective

Depends on / 依赖: Prod.swap, Prod.swap_bijective.injective, TensorProduct, TensorProduct.comm, hw.tmul_of_flat_left, injective, injective.injOn, linearIndependent_iff_of_injOn, swap_bijective, tmul_of_flat_left, toLinearMap, toLinearMap.linearIndependent_iff_of_injOn
-/
lemma _root_.LinearIndependent.tmul_of_flat_right [Module.Flat R N] (hv : LinearIndependent R v)
    (hw : LinearIndependent R w) : LinearIndependent R fun i : ι × κ => v i.1 otimesₜ[R] w i.2 :=
  (((TensorProduct.comm R N M).toLinearMap.linearIndependent_iff_of_injOn
    (TensorProduct.comm R N M).injective.injOn).mpr
      (hw.tmul_of_flat_left hv)).comp Prod.swap Prod.swap_bijective.injective

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndepOn.tmul_of_isDomain`. -/
nonrec lemma LinearIndepOn.tmul_of_flat_right [Module.Flat R N] (hv : LinearIndepOn R v s)
    (hw : LinearIndepOn R w t) : LinearIndepOn R (fun i : ι × κ => v i.1 otimesₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_flat_right hw).comp _ (Equiv.Set.prod _ _).injective :)

variable (p : Submodule R M) (q : Submodule R N)

/--
theorem `_root_.Module.Flat.tensorProduct_mapIncl_injective_of_right` / 定理 `_root_.Module.Flat.tensorProduct_mapIncl_injective_of_right`

English:
theorem _root_.Module.Flat.tensorProduct_mapIncl_injective_of_right
  proof: TensorProduct.map_injective_of_flat_flat _ _ p.subtype_injective q.subtype_injective

中文:
定理 _root_.Module.Flat.tensorProduct_mapIncl_injective_of_right
  证明: TensorProduct.map_injective_of_flat_flat _ _ p.subtype_injective q.subtype_injective

Depends on / 依赖: TensorProduct, TensorProduct.map_injective_of_flat_flat, map_injective_of_flat_flat, p.subtype_injective, q.subtype_injective, subtype_injective
-/
theorem _root_.Module.Flat.tensorProduct_mapIncl_injective_of_right
    [Module.Flat R M] [Module.Flat R q] : Function.Injective (mapIncl p q) :=
  TensorProduct.map_injective_of_flat_flat _ _ p.subtype_injective q.subtype_injective

/--
theorem `_root_.Module.Flat.tensorProduct_mapIncl_injective_of_left` / 定理 `_root_.Module.Flat.tensorProduct_mapIncl_injective_of_left`

English:
theorem _root_.Module.Flat.tensorProduct_mapIncl_injective_of_left
  proof: TensorProduct.map_injective_of_flat_flat' _ _ p.subtype_injective q.subtype_injective

中文:
定理 _root_.Module.Flat.tensorProduct_mapIncl_injective_of_left
  证明: TensorProduct.map_injective_of_flat_flat' _ _ p.subtype_injective q.subtype_injective

Depends on / 依赖: TensorProduct, TensorProduct.map_injective_of_flat_flat, map_injective_of_flat_flat, p.subtype_injective, q.subtype_injective, subtype_injective
-/
theorem _root_.Module.Flat.tensorProduct_mapIncl_injective_of_left
    [Module.Flat R p] [Module.Flat R N] : Function.Injective (mapIncl p q) :=
  TensorProduct.map_injective_of_flat_flat' _ _ p.subtype_injective q.subtype_injective

end TensorProduct

namespace Algebra.TensorProduct

variable (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/--
theorem `nontrivial_of_algebraMap_injective_of_flat_left` / 定理 `nontrivial_of_algebraMap_injective_of_flat_left`

English:
theorem nontrivial_of_algebraMap_injective_of_flat_left
  statement: (h : Function.Injective (algebraMap R B))
  proof: TensorProduct.nontrivial_of_linearMap_injective_of_flat_left R A B (Algebra.linearMap R B) h

中文:
定理 nontrivial_of_algebraMap_injective_of_flat_left
  结论: (h : Function.Injective (algebraMap R B))
  证明: TensorProduct.nontrivial_of_linearMap_injective_of_flat_left R A B (Algebra.linearMap R B) h

Depends on / 依赖: Algebra, Algebra.linearMap, TensorProduct, TensorProduct.nontrivial_of_linearMap_injective_of_flat_left, linearMap, nontrivial_of_linearMap_injective_of_flat_left
-/
theorem nontrivial_of_algebraMap_injective_of_flat_left (h : Function.Injective (algebraMap R B))
    [Module.Flat R A] [Nontrivial A] : Nontrivial (A otimes[R] B) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_left R A B (Algebra.linearMap R B) h

/--
theorem `nontrivial_of_algebraMap_injective_of_flat_right` / 定理 `nontrivial_of_algebraMap_injective_of_flat_right`

English:
theorem nontrivial_of_algebraMap_injective_of_flat_right
  statement: (h : Function.Injective (algebraMap R A))
  proof: TensorProduct.nontrivial_of_linearMap_injective_of_flat_right R A B (Algebra.linearMap R A) h

中文:
定理 nontrivial_of_algebraMap_injective_of_flat_right
  结论: (h : Function.Injective (algebraMap R A))
  证明: TensorProduct.nontrivial_of_linearMap_injective_of_flat_right R A B (Algebra.linearMap R A) h

Depends on / 依赖: Algebra, Algebra.linearMap, TensorProduct, TensorProduct.nontrivial_of_linearMap_injective_of_flat_right, linearMap, nontrivial_of_linearMap_injective_of_flat_right
-/
theorem nontrivial_of_algebraMap_injective_of_flat_right (h : Function.Injective (algebraMap R A))
    [Module.Flat R B] [Nontrivial B] : Nontrivial (A otimes[R] B) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_right R A B (Algebra.linearMap R A) h

end Algebra.TensorProduct

end Nontrivial

namespace IsTensorProduct

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P] {M₁ M₂ N₁ N₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁] [Module R N₂]
  {f : M₁ ->ₗ[R] M₂ ->ₗ[R] M} {g : N₁ ->ₗ[R] N₂ ->ₗ[R] N}
  (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂)

/--
theorem `map_id_injective_of_flat_left` / 定理 `map_id_injective_of_flat_left`

English:
theorem map_id_injective_of_flat_left
  statement: {g : M₁ ->ₗ[R] N₂ ->ₗ[R] N} (hg : IsTensorProduct g)
  proof: by
  have h : hf.map hg LinearMap.id i = hg.equiv ∘ i.lTensor M₁ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using Module.Flat.lTensor_preserves_injective_linearMap i hi

中文:
定理 map_id_injective_of_flat_left
  结论: {g : M₁ ->ₗ[R] N₂ ->ₗ[R] N} (hg : IsTensorProduct g)
  证明: by
  have h : hf.map hg LinearMap.id i = hg.equiv ∘ i.lTensor M₁ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using Module.Flat.lTensor_preserves_injective_linearMap i hi

Depends on / 依赖: LinearMap, LinearMap.id, Module, Module.Flat.lTensor_preserves_injective_linearMap, hf.equiv.symm, hf.inductionOn, hf.map, hg.equiv, i.lTensor, inductionOn, lTensor, lTensor_preserves_injective_linearMap
-/
theorem map_id_injective_of_flat_left {g : M₁ ->ₗ[R] N₂ ->ₗ[R] N} (hg : IsTensorProduct g)
    (i : M₂ ->ₗ[R] N₂) (hi : Function.Injective i) [Module.Flat R M₁] :
    Function.Injective (hf.map hg LinearMap.id i) := by
  have h : hf.map hg LinearMap.id i = hg.equiv ∘ i.lTensor M₁ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using Module.Flat.lTensor_preserves_injective_linearMap i hi

/--
theorem `map_id_injective_of_flat_right` / 定理 `map_id_injective_of_flat_right`

English:
theorem map_id_injective_of_flat_right
  statement: {g : N₁ ->ₗ[R] M₂ ->ₗ[R] N} (hg : IsTensorProduct g)
  proof: by
  have h : hf.map hg i LinearMap.id = hg.equiv ∘ i.rTensor M₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using Module.Flat.rTensor_preserves_injective_linearMap i hi

中文:
定理 map_id_injective_of_flat_right
  结论: {g : N₁ ->ₗ[R] M₂ ->ₗ[R] N} (hg : IsTensorProduct g)
  证明: by
  have h : hf.map hg i LinearMap.id = hg.equiv ∘ i.rTensor M₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using Module.Flat.rTensor_preserves_injective_linearMap i hi

Depends on / 依赖: LinearMap, LinearMap.id, Module, Module.Flat.rTensor_preserves_injective_linearMap, hf.equiv.symm, hf.inductionOn, hf.map, hg.equiv, i.rTensor, inductionOn, rTensor, rTensor_preserves_injective_linearMap
-/
theorem map_id_injective_of_flat_right {g : N₁ ->ₗ[R] M₂ ->ₗ[R] N} (hg : IsTensorProduct g)
    (i : M₁ ->ₗ[R] N₁) (hi : Function.Injective i) [Module.Flat R M₂] :
    Function.Injective (hf.map hg i LinearMap.id) := by
  have h : hf.map hg i LinearMap.id = hg.equiv ∘ i.rTensor M₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using Module.Flat.rTensor_preserves_injective_linearMap i hi

/--
theorem `map_injective_of_flat_right_left` / 定理 `map_injective_of_flat_right_left`

English:
theorem map_injective_of_flat_right_left
  statement: (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
  proof: by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat i₁ i₂ h₁ h₂

中文:
定理 map_injective_of_flat_right_left
  结论: (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
  证明: by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat i₁ i₂ h₁ h₂

Depends on / 依赖: TensorProduct, TensorProduct.map, hf.equiv.symm, hf.inductionOn, hf.map, hg.equiv, inductionOn, map_injective_of_flat_flat
-/
theorem map_injective_of_flat_right_left (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
    [Module.Flat R M₂] [Module.Flat R N₁] : Function.Injective (hf.map hg i₁ i₂) := by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat i₁ i₂ h₁ h₂

/--
theorem `map_injective_of_flat_left_right` / 定理 `map_injective_of_flat_left_right`

English:
theorem map_injective_of_flat_left_right
  statement: (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
  proof: by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat' i₁ i₂ h₁ h₂

中文:
定理 map_injective_of_flat_left_right
  结论: (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
  证明: by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat' i₁ i₂ h₁ h₂

Depends on / 依赖: TensorProduct, TensorProduct.map, hf.equiv.symm, hf.inductionOn, hf.map, hg.equiv, inductionOn, map_injective_of_flat_flat
-/
theorem map_injective_of_flat_left_right (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
    [Module.Flat R M₁] [Module.Flat R N₂] : Function.Injective (hf.map hg i₁ i₂) := by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x => hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy => by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat' i₁ i₂ h₁ h₂

end IsTensorProduct

section IsSMulRegular

variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Module.Flat R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/--
theorem `IsSMulRegular.of_flat_of_isBaseChange` / 定理 `IsSMulRegular.of_flat_of_isBaseChange`

English:
theorem IsSMulRegular.of_flat_of_isBaseChange
  statement: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {x : R}
  proof: by
  have h := hf.map_id_injective_of_flat_left hf (LinearMap.lsmul R M x) reg
  rwa [hf.map_id_lsmul_eq_lsmul_algebraMap] at h

中文:
定理 IsSMulRegular.of_flat_of_isBaseChange
  结论: {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {x : R}
  证明: by
  have h := hf.map_id_injective_of_flat_left hf (LinearMap.lsmul R M x) reg
  rwa [hf.map_id_lsmul_eq_lsmul_algebraMap] at h

Depends on / 依赖: LinearMap, LinearMap.lsmul, hf.map_id_injective_of_flat_left, hf.map_id_lsmul_eq_lsmul_algebraMap, map_id_injective_of_flat_left, map_id_lsmul_eq_lsmul_algebraMap
-/
theorem IsSMulRegular.of_flat_of_isBaseChange {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {x : R}
    (reg : IsSMulRegular M x) : IsSMulRegular N (algebraMap R S x) := by
  have h := hf.map_id_injective_of_flat_left hf (LinearMap.lsmul R M x) reg
  rwa [hf.map_id_lsmul_eq_lsmul_algebraMap] at h

/--
theorem `IsSMulRegular.of_flat` / 定理 `IsSMulRegular.of_flat`

English:
theorem IsSMulRegular.of_flat
  given: {x : R} (reg : IsSMulRegular R x)
  proof: reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

中文:
定理 IsSMulRegular.of_flat
  条件: {x : R} (reg : IsSMulRegular R x)
  证明: reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

Depends on / 依赖: IsBaseChange, IsBaseChange.linearMap, linearMap, of_flat_of_isBaseChange, reg.of_flat_of_isBaseChange
-/
theorem IsSMulRegular.of_flat {x : R} (reg : IsSMulRegular R x) :
    IsSMulRegular S (algebraMap R S x) :=
  reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

end IsSMulRegular

/--
theorem `IsReduced.tensorProduct_of_flat_of_forall_fg` / 定理 `IsReduced.tensorProduct_of_flat_of_forall_fg`

English:
theorem IsReduced.tensorProduct_of_flat_of_forall_fg
  statement: {R C A : Type*}
  proof: by
  by_contra h_contra
  obtain ⟨x, hx⟩ := exists_isNilpotent_of_not_isReduced h_contra
  obtain ⟨D, hD⟩ := exists_fg_and_mem_baseChange x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id C C) D.val) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val

中文:
定理 IsReduced.tensorProduct_of_flat_of_forall_fg
  结论: {R C A : 类型}
  证明: by
  by_contra h_contra
  obtain ⟨x, hx⟩ := exists_isNilpotent_of_not_isReduced h_contra
  obtain ⟨D, hD⟩ := exists_fg_and_mem_baseChange x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id C C) D.val) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val

Depends on / 依赖: AlgHom, AlgHom.id, Algebra, Algebra.TensorProduct.map, D.val, Function, Function.Injective, Injective, IsNilpotent, IsNilpotent.map_iff, IsReduced, Module, Module.Flat.lTensor_preserves_injective_linearMap, Subtype, Subtype.val_injective, TensorProduct, exists_fg_and_mem_baseChange, exists_isNilpotent_of_not_isReduced, h_contra, h_inj
-/
theorem IsReduced.tensorProduct_of_flat_of_forall_fg {R C A : Type*}
    [CommSemiring R] [CommSemiring C] [Semiring A] [Algebra R A] [Algebra R C] [Module.Flat R C]
    (h : forall B : Subalgebra R A, B.FG -> IsReduced (C otimes[R] B)) :
    IsReduced (C otimes[R] A) := by
  by_contra h_contra
  obtain ⟨x, hx⟩ := exists_isNilpotent_of_not_isReduced h_contra
  obtain ⟨D, hD⟩ := exists_fg_and_mem_baseChange x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id C C) D.val) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨z, rfl⟩ := hD.2
  have h_notReduced : ¬IsReduced (C otimes[R] D) := by
    simp_rw [isReduced_iff, not_forall]
    exact ⟨z, (IsNilpotent.map_iff h_inj).mp hx.right, (by simpa [·] using hx.1)⟩
  tauto
