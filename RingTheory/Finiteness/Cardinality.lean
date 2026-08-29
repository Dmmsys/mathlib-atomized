/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Module.Congruence.Defs
public import Mathlib.LinearAlgebra.Basis.Cardinality
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite modules and types with finitely many elements

This file relates `Module.Finite` and `_root_.Finite`.

-/

@[expose] public section

open Function (Surjective)
open Finsupp

section ModuleAndAlgebra

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

open Module in
/--
theorem `Submodule.fg_iff_exists_fin_linearMap` / 定理 `Submodule.fg_iff_exists_fin_linearMap`

English:
theorem Submodule.fg_iff_exists_fin_linearMap
  given: {N : Submodule R M}
  proof: by
  simp_rw [fg_iff_exists_fin_generating_family, ← ((Pi.basisFun R _).constr Nat).exists_congr_right]
  simp [Basis.constr_range]

中文:
定理 Submodule.fg_iff_exists_fin_linearMap
  条件: {N : Submodule R M}
  证明: by
  simp_rw [fg_iff_exists_fin_generating_family, ← ((Pi.basisFun R _).constr Nat).exists_congr_right]
  simp [Basis.constr_range]

Depends on / 依赖: Basis.constr_range, Pi.basisFun, basisFun, constr, constr_range, exists_congr_right, fg_iff_exists_fin_generating_family, simp_rw
-/
theorem Submodule.fg_iff_exists_fin_linearMap {N : Submodule R M} :
    N.FG ↔ exists (n : Nat) (f : (Fin n -> R) ->ₗ[R] M), LinearMap.range f = N := by
  simp_rw [fg_iff_exists_fin_generating_family, ← ((Pi.basisFun R _).constr Nat).exists_congr_right]
  simp [Basis.constr_range]

/--
theorem `AddSubmonoid.fg_iff_exists_fin_addMonoidHom` / 定理 `AddSubmonoid.fg_iff_exists_fin_addMonoidHom`

English:
theorem AddSubmonoid.fg_iff_exists_fin_addMonoidHom
  statement: {M : Type*} [AddCommMonoid M]
  proof: by
  rw [← S.toNatSubmodule_toAddSubmonoid]; rw [← Submodule.fg_iff_addSubmonoid_fg]; rw [Submodule.fg_iff_exists_fin_linearMap]
  exact exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubmonoid _⟩,
fun ⟨f, hf⟩ => ⟨f.toNatLinearMap, Submodule.toAddSubmonoid_inj.mp
      hf ▸ Line

中文:
定理 AddSubmonoid.fg_iff_exists_fin_addMonoidHom
  结论: {M : 类型} [AddCommMonoid M]
  证明: by
  rw [← S.toNatSubmodule_toAddSubmonoid]; rw [← Submodule.fg_iff_addSubmonoid_fg]; rw [Submodule.fg_iff_exists_fin_linearMap]
  exact exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubmonoid _⟩,
fun ⟨f, hf⟩ => ⟨f.toNatLinearMap, Submodule.toAddSubmonoid_inj.mp
      hf ▸ Line

Depends on / 依赖: LinearMap, LinearMap.range_toAddSubmonoid, S.toNatSubmodule_toAddSubmonoid, Submodule, Submodule.fg_iff_addSubmonoid_fg, Submodule.fg_iff_exists_fin_linearMap, Submodule.toAddSubmonoid_inj.mp, exists_congr, f.toNatLinearMap, fg_iff_addSubmonoid_fg, fg_iff_exists_fin_linearMap, range_toAddSubmonoid, toAddSubmonoid_inj, toNatLinearMap, toNatSubmodule_toAddSubmonoid
-/
theorem AddSubmonoid.fg_iff_exists_fin_addMonoidHom {M : Type*} [AddCommMonoid M]
    {S : AddSubmonoid M} : S.FG ↔ exists (n : Nat) (f : (Fin n -> Nat) ->+ M), AddMonoidHom.mrange f = S := by
  rw [← S.toNatSubmodule_toAddSubmonoid]; rw [← Submodule.fg_iff_addSubmonoid_fg]; rw [Submodule.fg_iff_exists_fin_linearMap]
  exact exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubmonoid _⟩,
fun ⟨f, hf⟩ => ⟨f.toNatLinearMap, Submodule.toAddSubmonoid_inj.mp
      hf ▸ LinearMap.range_toAddSubmonoid _⟩⟩

/--
theorem `AddSubgroup.fg_iff_exists_fin_addMonoidHom` / 定理 `AddSubgroup.fg_iff_exists_fin_addMonoidHom`

English:
theorem AddSubgroup.fg_iff_exists_fin_addMonoidHom
  statement: {M : Type*} [AddCommGroup M]
  proof: by
  rw [← H.toIntSubmodule_toAddSubgroup]; rw [← Submodule.fg_iff_addSubgroup_fg]; rw [Submodule.fg_iff_exists_fin_linearMap]
  refine exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubgroup _⟩,
    fun ⟨f, hf⟩ => ⟨f.toIntLinearMap, Submodule.toAddSubmonoid_inj.mp ?_⟩⟩
  simp [

中文:
定理 AddSubgroup.fg_iff_exists_fin_addMonoidHom
  结论: {M : 类型} [AddCommGroup M]
  证明: by
  rw [← H.toIntSubmodule_toAddSubgroup]; rw [← Submodule.fg_iff_addSubgroup_fg]; rw [Submodule.fg_iff_exists_fin_linearMap]
  refine exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubgroup _⟩,
    fun ⟨f, hf⟩ => ⟨f.toIntLinearMap, Submodule.toAddSubmonoid_inj.mp ?_⟩⟩
  simp [

Depends on / 依赖: H.toIntSubmodule_toAddSubgroup, LinearMap, LinearMap.range_toAddSubgroup, Submodule, Submodule.fg_iff_addSubgroup_fg, Submodule.fg_iff_exists_fin_linearMap, Submodule.toAddSubmonoid_inj.mp, exists_congr, f.toIntLinearMap, fg_iff_addSubgroup_fg, fg_iff_exists_fin_linearMap, range_toAddSubgroup, toAddSubmonoid_inj, toIntLinearMap, toIntSubmodule_toAddSubgroup
-/
theorem AddSubgroup.fg_iff_exists_fin_addMonoidHom {M : Type*} [AddCommGroup M]
    {H : AddSubgroup M} : H.FG ↔ exists (n : Nat) (f : (Fin n -> Int) ->+ M), AddMonoidHom.range f = H := by
  rw [← H.toIntSubmodule_toAddSubgroup]; rw [← Submodule.fg_iff_addSubgroup_fg]; rw [Submodule.fg_iff_exists_fin_linearMap]
  refine exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubgroup _⟩,
    fun ⟨f, hf⟩ => ⟨f.toIntLinearMap, Submodule.toAddSubmonoid_inj.mp ?_⟩⟩
  simp [hf]

namespace Module

namespace Finite

open Submodule Set

/--
lemma `exists_fin'` / 引理 `exists_fin'`

English:
lemma exists_fin'
  given: [Module.Finite R M]
  statement: exists (n : Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
  proof: have ⟨n, f, hf⟩ := (Submodule.fg_iff_exists_fin_linearMap R M).mp fg_top
  ⟨n, f, by rw [← LinearMap.range_eq_top, hf]⟩

中文:
引理 exists_fin'
  条件: [Module.Finite R M]
  结论: 存在 (n : 自然数) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
  证明: have ⟨n, f, hf⟩ := (Submodule.fg_iff_exists_fin_linearMap R M).mp fg_top
  ⟨n, f, by rw [← LinearMap.range_eq_top, hf]⟩

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, Submodule, Submodule.fg_iff_exists_fin_linearMap, fg_iff_exists_fin_linearMap, fg_top, range_eq_top
-/
lemma exists_fin' [Module.Finite R M] : exists (n : Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f :=
  have ⟨n, f, hf⟩ := (Submodule.fg_iff_exists_fin_linearMap R M).mp fg_top
  ⟨n, f, by rw [← LinearMap.range_eq_top, hf]⟩

/--
theorem `exists_fin_quot_equiv` / 定理 `exists_fin_quot_equiv`

English:
theorem exists_fin_quot_equiv
  statement: (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
  proof: let ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n, LinearMap.ker f, ⟨f.quotKerEquivOfSurjective hf⟩⟩

中文:
定理 exists_fin_quot_equiv
  结论: (R M : 类型) [Ring R] [AddCommGroup M] [Module R M]
  证明: let ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n, LinearMap.ker f, ⟨f.quotKerEquivOfSurjective hf⟩⟩

Depends on / 依赖: Finite, LinearMap, LinearMap.ker, Module, Module.Finite.exists_fin, exists_fin, f.quotKerEquivOfSurjective, quotKerEquivOfSurjective
-/
theorem exists_fin_quot_equiv (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
      [Module.Finite R M] :
    exists (n : Nat) (S : Submodule R (Fin n -> R)), Nonempty ((_ ⧸ S) ≃ₗ[R] M) :=
  let ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n, LinearMap.ker f, ⟨f.quotKerEquivOfSurjective hf⟩⟩

variable {M}

/--
lemma `_root_.Module.finite_of_finite` / 引理 `_root_.Module.finite_of_finite`

English:
lemma _root_.Module.finite_of_finite
  given: [Finite R] [Module.Finite R M]
  statement: Finite M
  proof: by
  obtain ⟨n, f, hf⟩ := exists_fin' R M; exact .of_surjective f hf

中文:
引理 _root_.Module.finite_of_finite
  条件: [Finite R] [Module.Finite R M]
  结论: Finite M
  证明: by
  obtain ⟨n, f, hf⟩ := exists_fin' R M; exact .of_surjective f hf

Depends on / 依赖: exists_fin, of_surjective
-/
lemma _root_.Module.finite_of_finite [Finite R] [Module.Finite R M] : Finite M := by
  obtain ⟨n, f, hf⟩ := exists_fin' R M; exact .of_surjective f hf

variable {R}

/--
lemma `_root_.Module.finite_iff_finite` / 引理 `_root_.Module.finite_iff_finite`

English:
lemma _root_.Module.finite_iff_finite
  given: [Finite R]
  statement: Module.Finite R M ↔ Finite M
  proof: ⟨fun _ => finite_of_finite R, fun _ => .of_finite⟩

中文:
引理 _root_.Module.finite_iff_finite
  条件: [Finite R]
  结论: Module.Finite R M ↔ Finite M
  证明: ⟨fun _ => finite_of_finite R, fun _ => .of_finite⟩

Depends on / 依赖: finite_of_finite, of_finite
-/
lemma _root_.Module.finite_iff_finite [Finite R] : Module.Finite R M ↔ Finite M :=
  ⟨fun _ => finite_of_finite R, fun _ => .of_finite⟩

variable (R) in
/--
lemma `_root_.Set.Finite.submoduleSpan` / 引理 `_root_.Set.Finite.submoduleSpan`

English:
lemma _root_.Set.Finite.submoduleSpan
  given: [Finite R] {s : Set M} (hs : s.Finite)
  proof: by
  lift s to Finset M using hs
  rw [Set.Finite]; rw [← Module.finite_iff_finite (R := R)]
  dsimp
  infer_instance

中文:
引理 _root_.Set.Finite.submoduleSpan
  条件: [Finite R] {s : Set M} (hs : s.Finite)
  证明: by
  lift s to Finset M using hs
  rw [Set.Finite]; rw [← Module.finite_iff_finite (R := R)]
  dsimp
  infer_instance

Depends on / 依赖: Finite, Finset, Module, Module.finite_iff_finite, Set.Finite, finite_iff_finite, infer_instance
-/
lemma _root_.Set.Finite.submoduleSpan [Finite R] {s : Set M} (hs : s.Finite) :
    (Submodule.span R s : Set M).Finite := by
  lift s to Finset M using hs
  rw [Set.Finite]; rw [← Module.finite_iff_finite (R := R)]
  dsimp
  infer_instance

/--
lemma `finite_basis` / 引理 `finite_basis`

English:
lemma finite_basis
  statement: [Nontrivial R] {ι} [Module.Finite R M]
  proof: let ⟨s, hs⟩ := ‹Module.Finite R M›
  basis_finite_of_finite_spans s.finite_toSet hs b

中文:
引理 finite_basis
  结论: [Nontrivial R] {ι} [Module.Finite R M]
  证明: let ⟨s, hs⟩ := ‹Module.Finite R M›
  basis_finite_of_finite_spans s.finite_toSet hs b

Depends on / 依赖: Finite, Module, Module.Finite, basis_finite_of_finite_spans, finite_toSet, s.finite_toSet
-/
lemma finite_basis [Nontrivial R] {ι} [Module.Finite R M]
    (b : Basis ι R M) :
    _root_.Finite ι :=
  let ⟨s, hs⟩ := ‹Module.Finite R M›
  basis_finite_of_finite_spans s.finite_toSet hs b

end Finite

variable {R M}
/--
lemma `not_finite_of_infinite_basis` / 引理 `not_finite_of_infinite_basis`

English:
lemma not_finite_of_infinite_basis
  given: [Nontrivial R] {ι} [Infinite ι] (b : Basis ι R M)
  proof: fun _ => (Finite.finite_basis b).not_infinite ‹_›

中文:
引理 not_finite_of_infinite_basis
  条件: [Nontrivial R] {ι} [Infinite ι] (b : Basis ι R M)
  证明: fun _ => (Finite.finite_basis b).not_infinite ‹_›

Depends on / 依赖: Finite, Finite.finite_basis, finite_basis, not_infinite
-/
lemma not_finite_of_infinite_basis [Nontrivial R] {ι} [Infinite ι] (b : Basis ι R M) :
    ¬ Module.Finite R M :=
  fun _ => (Finite.finite_basis b).not_infinite ‹_›

end Module

end ModuleAndAlgebra

namespace Module.Finite

universe u
variable (R : Type u) (M : Type*)

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/--
Definition of `kerRepr` / `kerRepr` 的定义

English:
definition kerRepr
  body: LinearMap.ker (Finite.exists_fin' R M).choose_spec.choose

中文:
定义 kerRepr
  定义体: LinearMap.ker (Finite.exists_fin' R M).choose_spec.choose

Depends on / 依赖: Finite, Finite.exists_fin, LinearMap, LinearMap.ker, choose_spec, choose_spec.choose, exists_fin
-/
noncomputable def kerRepr := LinearMap.ker (Finite.exists_fin' R M).choose_spec.choose

/--
Definition of `repr` / `repr` 的定义

English:
abbreviation repr
  signature: : Type u
  body: _ ⧸ kerRepr R M

中文:
缩写 repr
  签名: : 类型u
  定义体: _ ⧸ kerRepr R M
-/
protected abbrev repr : Type u := _ ⧸ kerRepr R M

/--
Definition of `reprEquiv` / `reprEquiv` 的定义

English:
definition reprEquiv
  signature: : Finite.repr R M ≃ₗ[R] M
  body: LinearMap.quotKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

中文:
定义 reprEquiv
  签名: : Finite.repr R M ≃ₗ[R] M
  定义体: LinearMap.quotKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

Depends on / 依赖: Finite, Finite.exists_fin, LinearMap, LinearMap.quotKerEquivOfSurjective, choose_spec, choose_spec.choose_spec, exists_fin, quotKerEquivOfSurjective
-/
noncomputable def reprEquiv : Finite.repr R M ≃ₗ[R] M :=
  LinearMap.quotKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

end Ring

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M]

/--
Definition of `kerReprₛ` / `kerReprₛ` 的定义

English:
definition kerReprₛ
  body: ModuleCon.ker (Finite.exists_fin' R M).choose_spec.choose.toDistribMulActionHom

中文:
定义 kerReprₛ
  定义体: ModuleCon.ker (Finite.exists_fin' R M).choose_spec.choose.toDistribMulActionHom

Depends on / 依赖: Finite, Finite.exists_fin, ModuleCon, ModuleCon.ker, choose_spec, choose_spec.choose.toDistribMulActionHom, exists_fin, toDistribMulActionHom
-/
noncomputable def kerReprₛ :=
  ModuleCon.ker (Finite.exists_fin' R M).choose_spec.choose.toDistribMulActionHom

/--
Definition of `reprₛ` / `reprₛ` 的定义

English:
abbreviation reprₛ
  signature: : Type u
  body: (kerReprₛ R M).Quotient

中文:
缩写 reprₛ
  签名: : 类型u
  定义体: (kerReprₛ R M).Quotient
-/
protected abbrev reprₛ : Type u := (kerReprₛ R M).Quotient

/--
Definition of `reprEquivₛ` / `reprEquivₛ` 的定义

English:
definition reprEquivₛ
  signature: : Finite.reprₛ R M ≃ₗ[R] M
  body: ModuleCon.quotientKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

中文:
定义 reprEquivₛ
  签名: : Finite.reprₛ R M ≃ₗ[R] M
  定义体: ModuleCon.quotientKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

Depends on / 依赖: Finite, Finite.exists_fin, ModuleCon, ModuleCon.quotientKerEquivOfSurjective, choose_spec, choose_spec.choose_spec, exists_fin, quotientKerEquivOfSurjective
-/
noncomputable def reprEquivₛ : Finite.reprₛ R M ≃ₗ[R] M :=
  ModuleCon.quotientKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

end Semiring

end Module.Finite
