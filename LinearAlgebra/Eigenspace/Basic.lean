/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Tactic.Peel

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvectors, as well as their generalized
counterparts. We follow Axler's approach [axler2024] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`HasEigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

The fact that the eigenvalues are the roots of the minimal polynomial is proved in
`LinearAlgebra.Eigenspace.Minpoly`.

The existence of eigenvalues over an algebraically closed field
(and the fact that the generalized eigenspaces then span) is deferred to
`LinearAlgebra.Eigenspace.IsAlgClosed`.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

@[expose] public section


universe u v w

namespace Module

namespace End

open Module Set

variable {K R : Type v} {V M : Type w} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]

/--
Definition of `genEigenspace` / `genEigenspace` 的定义

English:
definition genEigenspace
  signature: (f : End R M) (μ : R)
  body: ⨆ l : Nat, ⨆ _ : l <= k, LinearMap.ker ((f - μ • 1) ^ l)
  monotone' _ _ hkl := biSup_mono fun _ hi => hi.trans hkl

中文:
定义 genEigenspace
  签名: (f : End R M) (μ : R)
  定义体: ⨆ l : Nat, ⨆ _ : l <= k, LinearMap.ker ((f - μ • 1) ^ l)
  monotone' _ _ hkl := biSup_mono fun _ hi => hi.trans hkl

Depends on / 依赖: LinearMap, LinearMap.ker
-/
def genEigenspace (f : End R M) (μ : R) : Nat∞ ->o Submodule R M where
  toFun k := ⨆ l : Nat, ⨆ _ : l <= k, LinearMap.ker ((f - μ • 1) ^ l)
  monotone' _ _ hkl := biSup_mono fun _ hi => hi.trans hkl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_genEigenspace` / 引理 `mem_genEigenspace`

English:
lemma mem_genEigenspace
  given: {f : End R M} {μ : R} {k : Nat∞} {x : M}
  proof: by
  have : Nonempty {l : Nat // l <= k} := ⟨⟨0, zero_le⟩⟩
  have : Directed (ι := { i : Nat // i <= k }) (· <= ·) fun i => LinearMap.ker ((f - μ • 1) ^ (i : Nat)) :=
    Monotone.directed_le fun m n h => by simpa using (f - μ • 1).iterateKer.monotone h
  simp_rw [genEigenspace, OrderHom.coe_mk, LinearMap.mem_ker, iSup_subtype',
    Submodule.mem_iSup_of_directed _ this, LinearMap.mem_ker, Subtype.exists, exists_prop]

中文:
引理 mem_genEigenspace
  条件: {f : End R M} {μ : R} {k : 自然数∞} {x : M}
  证明: by
  have : Nonempty {l : Nat // l <= k} := ⟨⟨0, zero_le⟩⟩
  have : Directed (ι := { i : Nat // i <= k }) (· <= ·) fun i => LinearMap.ker ((f - μ • 1) ^ (i : Nat)) :=
    Monotone.directed_le fun m n h => by simpa using (f - μ • 1).iterateKer.monotone h
  simp_rw [genEigenspace, OrderHom.coe_mk, LinearMap.mem_ker, iSup_subtype',
    Submodule.mem_iSup_of_directed _ this, LinearMap.mem_ker, Subtype.exists, exists_prop]

Depends on / 依赖: Directed, LinearMap, LinearMap.ker, LinearMap.mem_ker, Monotone, Monotone.directed_le, Nonempty, OrderHom, OrderHom.coe_mk, Submodule, Submodule.mem_iSup_of_directed, Subtype, Subtype.exists, coe_mk, directed_le, exists_prop, genEigenspace, iSup_subtype, iterateKer, iterateKer.monotone
-/
lemma mem_genEigenspace {f : End R M} {μ : R} {k : Nat∞} {x : M} :
    x in f.genEigenspace μ k ↔ exists l : Nat, l <= k ∧ x in LinearMap.ker ((f - μ • 1) ^ l) := by
  have : Nonempty {l : Nat // l <= k} := ⟨⟨0, zero_le⟩⟩
  have : Directed (ι := { i : Nat // i <= k }) (· <= ·) fun i => LinearMap.ker ((f - μ • 1) ^ (i : Nat)) :=
    Monotone.directed_le fun m n h => by simpa using (f - μ • 1).iterateKer.monotone h
  simp_rw [genEigenspace, OrderHom.coe_mk, LinearMap.mem_ker, iSup_subtype',
    Submodule.mem_iSup_of_directed _ this, LinearMap.mem_ker, Subtype.exists, exists_prop]

/--
lemma `genEigenspace_directed` / 引理 `genEigenspace_directed`

English:
lemma genEigenspace_directed
  given: {f : End R M} {μ : R} {k : Nat∞}
  proof: by
  have aux : Monotone ((↑) : {l : Nat // l <= k} -> Nat∞) := fun x y h => by simpa using h
  exact ((genEigenspace f μ).monotone.comp aux).directed_le

中文:
引理 genEigenspace_directed
  条件: {f : End R M} {μ : R} {k : 自然数∞}
  证明: by
  have aux : Monotone ((↑) : {l : Nat // l <= k} -> Nat∞) := fun x y h => by simpa using h
  exact ((genEigenspace f μ).monotone.comp aux).directed_le

Depends on / 依赖: Monotone, directed_le, genEigenspace, monotone, monotone.comp
-/
lemma genEigenspace_directed {f : End R M} {μ : R} {k : Nat∞} :
    Directed (· <= ·) (fun l : {l : Nat // l <= k} => f.genEigenspace μ l) := by
  have aux : Monotone ((↑) : {l : Nat // l <= k} -> Nat∞) := fun x y h => by simpa using h
  exact ((genEigenspace f μ).monotone.comp aux).directed_le

/--
lemma `mem_genEigenspace_nat` / 引理 `mem_genEigenspace_nat`

English:
lemma mem_genEigenspace_nat
  given: {f : End R M} {μ : R} {k : Nat} {x : M}
  proof: by
  rw [mem_genEigenspace]
  constructor
  · rintro ⟨l, hl, hx⟩
    simp only [Nat.cast_le] at hl
    exact (f - μ • 1).iterateKer.monotone hl hx
  · intro hx
    exact ⟨k, le_rfl, hx⟩

中文:
引理 mem_genEigenspace_nat
  条件: {f : End R M} {μ : R} {k : 自然数} {x : M}
  证明: by
  rw [mem_genEigenspace]
  constructor
  · rintro ⟨l, hl, hx⟩
    simp only [Nat.cast_le] at hl
    exact (f - μ • 1).iterateKer.monotone hl hx
  · intro hx
    exact ⟨k, le_rfl, hx⟩

Depends on / 依赖: Nat.cast_le, cast_le, iterateKer, iterateKer.monotone, le_rfl, mem_genEigenspace, monotone
-/
lemma mem_genEigenspace_nat {f : End R M} {μ : R} {k : Nat} {x : M} :
    x in f.genEigenspace μ k ↔ x in LinearMap.ker ((f - μ • 1) ^ k) := by
  rw [mem_genEigenspace]
  constructor
  · rintro ⟨l, hl, hx⟩
    simp only [Nat.cast_le] at hl
    exact (f - μ • 1).iterateKer.monotone hl hx
  · intro hx
    exact ⟨k, le_rfl, hx⟩

/--
lemma `mem_genEigenspace_top` / 引理 `mem_genEigenspace_top`

English:
lemma mem_genEigenspace_top
  given: {f : End R M} {μ : R} {x : M}
  proof: by
  simp [mem_genEigenspace]

中文:
引理 mem_genEigenspace_top
  条件: {f : End R M} {μ : R} {x : M}
  证明: by
  simp [mem_genEigenspace]

Depends on / 依赖: mem_genEigenspace
-/
lemma mem_genEigenspace_top {f : End R M} {μ : R} {x : M} :
    x in f.genEigenspace μ ⊤ ↔ exists k : Nat, x in LinearMap.ker ((f - μ • 1) ^ k) := by
  simp [mem_genEigenspace]

/--
lemma `genEigenspace_nat` / 引理 `genEigenspace_nat`

English:
lemma genEigenspace_nat
  given: {f : End R M} {μ : R} {k : Nat}
  proof: by
  ext; simp [mem_genEigenspace_nat]

中文:
引理 genEigenspace_nat
  条件: {f : End R M} {μ : R} {k : 自然数}
  证明: by
  ext; simp [mem_genEigenspace_nat]

Depends on / 依赖: mem_genEigenspace_nat
-/
lemma genEigenspace_nat {f : End R M} {μ : R} {k : Nat} :
    f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k) := by
  ext; simp [mem_genEigenspace_nat]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `genEigenspace_eq_iSup_genEigenspace_nat` / 引理 `genEigenspace_eq_iSup_genEigenspace_nat`

English:
lemma genEigenspace_eq_iSup_genEigenspace_nat
  given: (f : End R M) (μ : R) (k : Nat∞)
  proof: by
  simp_rw [genEigenspace_nat, genEigenspace, OrderHom.coe_mk, iSup_subtype]

中文:
引理 genEigenspace_eq_iSup_genEigenspace_nat
  条件: (f : End R M) (μ : R) (k : 自然数∞)
  证明: by
  simp_rw [genEigenspace_nat, genEigenspace, OrderHom.coe_mk, iSup_subtype]

Depends on / 依赖: OrderHom, OrderHom.coe_mk, coe_mk, genEigenspace, genEigenspace_nat, iSup_subtype, simp_rw
-/
lemma genEigenspace_eq_iSup_genEigenspace_nat (f : End R M) (μ : R) (k : Nat∞) :
    f.genEigenspace μ k = ⨆ l : {l : Nat // l <= k}, f.genEigenspace μ l := by
  simp_rw [genEigenspace_nat, genEigenspace, OrderHom.coe_mk, iSup_subtype]

/--
lemma `genEigenspace_top` / 引理 `genEigenspace_top`

English:
lemma genEigenspace_top
  given: (f : End R M) (μ : R)
  proof: by
  rw [genEigenspace_eq_iSup_genEigenspace_nat]; rw [iSup_subtype]
  simp only [le_top, iSup_pos]

中文:
引理 genEigenspace_top
  条件: (f : End R M) (μ : R)
  证明: by
  rw [genEigenspace_eq_iSup_genEigenspace_nat]; rw [iSup_subtype]
  simp only [le_top, iSup_pos]

Depends on / 依赖: genEigenspace_eq_iSup_genEigenspace_nat, iSup_pos, iSup_subtype, le_top
-/
lemma genEigenspace_top (f : End R M) (μ : R) :
    f.genEigenspace μ ⊤ = ⨆ k : Nat, f.genEigenspace μ k := by
  rw [genEigenspace_eq_iSup_genEigenspace_nat]; rw [iSup_subtype]
  simp only [le_top, iSup_pos]

/--
lemma `genEigenspace_one` / 引理 `genEigenspace_one`

English:
lemma genEigenspace_one
  given: {f : End R M} {μ : R}
  proof: by
  rw [← Nat.cast_one]; rw [genEigenspace_nat]; rw [pow_one]

@[simp]

中文:
引理 genEigenspace_one
  条件: {f : End R M} {μ : R}
  证明: by
  rw [← Nat.cast_one]; rw [genEigenspace_nat]; rw [pow_one]

@[simp]

Depends on / 依赖: Nat.cast_one, cast_one, genEigenspace_nat, pow_one
-/
lemma genEigenspace_one {f : End R M} {μ : R} :
    f.genEigenspace μ 1 = LinearMap.ker (f - μ • 1) := by
  rw [← Nat.cast_one]; rw [genEigenspace_nat]; rw [pow_one]

@[simp]
/--
lemma `mem_genEigenspace_one` / 引理 `mem_genEigenspace_one`

English:
lemma mem_genEigenspace_one
  given: {f : End R M} {μ : R} {x : M}
  proof: by
  rw [genEigenspace_one]; rw [LinearMap.mem_ker]; rw [LinearMap.sub_apply]; rw [sub_eq_zero]; rw [LinearMap.smul_apply]; rw [Module.End.one_apply]

中文:
引理 mem_genEigenspace_one
  条件: {f : End R M} {μ : R} {x : M}
  证明: by
  rw [genEigenspace_one]; rw [LinearMap.mem_ker]; rw [LinearMap.sub_apply]; rw [sub_eq_zero]; rw [LinearMap.smul_apply]; rw [Module.End.one_apply]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.sub_apply, Module, Module.End.one_apply, genEigenspace_one, mem_ker, one_apply, smul_apply, sub_apply, sub_eq_zero
-/
lemma mem_genEigenspace_one {f : End R M} {μ : R} {x : M} :
    x in f.genEigenspace μ 1 ↔ f x = μ • x := by
  rw [genEigenspace_one]; rw [LinearMap.mem_ker]; rw [LinearMap.sub_apply]; rw [sub_eq_zero]; rw [LinearMap.smul_apply]; rw [Module.End.one_apply]

-- `simp` can prove this using `genEigenspace_zero`
/--
lemma `mem_genEigenspace_zero` / 引理 `mem_genEigenspace_zero`

English:
lemma mem_genEigenspace_zero
  given: {f : End R M} {μ : R} {x : M}
  proof: by
  rw [← Nat.cast_zero]; rw [mem_genEigenspace_nat]; rw [pow_zero]; rw [LinearMap.mem_ker]; rw [Module.End.one_apply]

@[simp]

中文:
引理 mem_genEigenspace_zero
  条件: {f : End R M} {μ : R} {x : M}
  证明: by
  rw [← Nat.cast_zero]; rw [mem_genEigenspace_nat]; rw [pow_zero]; rw [LinearMap.mem_ker]; rw [Module.End.one_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Module, Module.End.one_apply, Nat.cast_zero, cast_zero, mem_genEigenspace_nat, mem_ker, one_apply, pow_zero
-/
lemma mem_genEigenspace_zero {f : End R M} {μ : R} {x : M} :
    x in f.genEigenspace μ 0 ↔ x = 0 := by
  rw [← Nat.cast_zero]; rw [mem_genEigenspace_nat]; rw [pow_zero]; rw [LinearMap.mem_ker]; rw [Module.End.one_apply]

@[simp]
/--
lemma `genEigenspace_zero` / 引理 `genEigenspace_zero`

English:
lemma genEigenspace_zero
  given: {f : End R M} {μ : R}
  proof: by
  ext; apply mem_genEigenspace_zero

@[simp]

中文:
引理 genEigenspace_zero
  条件: {f : End R M} {μ : R}
  证明: by
  ext; apply mem_genEigenspace_zero

@[simp]

Depends on / 依赖: mem_genEigenspace_zero
-/
lemma genEigenspace_zero {f : End R M} {μ : R} :
    f.genEigenspace μ 0 = ⊥ := by
  ext; apply mem_genEigenspace_zero

@[simp]
/--
lemma `genEigenspace_zero_nat` / 引理 `genEigenspace_zero_nat`

English:
lemma genEigenspace_zero_nat
  given: (f : End R M) (k : Nat)
  proof: by
  ext; simp [mem_genEigenspace_nat]

中文:
引理 genEigenspace_zero_nat
  条件: (f : End R M) (k : 自然数)
  证明: by
  ext; simp [mem_genEigenspace_nat]

Depends on / 依赖: mem_genEigenspace_nat
-/
lemma genEigenspace_zero_nat (f : End R M) (k : Nat) :
    f.genEigenspace 0 k = LinearMap.ker (f ^ k) := by
  ext; simp [mem_genEigenspace_nat]

/--
Definition of `HasUnifEigenvector` / `HasUnifEigenvector` 的定义

English:
definition HasUnifEigenvector
  signature: (f : End R M) (μ : R) (k : Nat∞) (x : M)
  body: x in f.genEigenspace μ k ∧ x != 0

中文:
定义 HasUnifEigenvector
  签名: (f : End R M) (μ : R) (k : 自然数∞) (x : M)
  定义体: x in f.genEigenspace μ k ∧ x != 0

Depends on / 依赖: f.genEigenspace, genEigenspace
-/
def HasUnifEigenvector (f : End R M) (μ : R) (k : Nat∞) (x : M) : Prop :=
  x in f.genEigenspace μ k ∧ x != 0

/--
Definition of `HasUnifEigenvalue` / `HasUnifEigenvalue` 的定义

English:
definition HasUnifEigenvalue
  signature: (f : End R M) (μ : R) (k : Nat∞)
  body: f.genEigenspace μ k != ⊥

中文:
定义 HasUnifEigenvalue
  签名: (f : End R M) (μ : R) (k : 自然数∞)
  定义体: f.genEigenspace μ k != ⊥

Depends on / 依赖: f.genEigenspace, genEigenspace
-/
def HasUnifEigenvalue (f : End R M) (μ : R) (k : Nat∞) : Prop :=
  f.genEigenspace μ k != ⊥

/--
Definition of `UnifEigenvalues` / `UnifEigenvalues` 的定义

English:
definition UnifEigenvalues
  signature: (f : End R M) (k : Nat∞)
  body: { μ : R // f.HasUnifEigenvalue μ k }

中文:
定义 UnifEigenvalues
  签名: (f : End R M) (k : 自然数∞)
  定义体: { μ : R // f.HasUnifEigenvalue μ k }

Depends on / 依赖: HasUnifEigenvalue, f.HasUnifEigenvalue
-/
def UnifEigenvalues (f : End R M) (k : Nat∞) : Type _ :=
  { μ : R // f.HasUnifEigenvalue μ k }

/-- The underlying value of a bundled eigenvalue. -/
@[coe]
/--
Definition of `UnifEigenvalues.val` / `UnifEigenvalues.val` 的定义

English:
definition UnifEigenvalues.val
  signature: (f : Module.End R M) (k : Nat∞)
  body: Subtype.val

@[simp]

中文:
定义 UnifEigenvalues.val
  签名: (f : 模.End R M) (k : 自然数∞)
  定义体: Subtype.val

@[simp]

Depends on / 依赖: Subtype, Subtype.val
-/
def UnifEigenvalues.val (f : Module.End R M) (k : Nat∞) : UnifEigenvalues f k -> R := Subtype.val

@[simp]
/--
lemma `UnifEigenvalues.val_mk` / 引理 `UnifEigenvalues.val_mk`

English:
lemma UnifEigenvalues.val_mk
  given: {f : End R M} {μ : R} {k : Nat∞} (h : f.HasUnifEigenvalue μ k)
  proof: rfl

@[simp]

中文:
引理 UnifEigenvalues.val_mk
  条件: {f : End R M} {μ : R} {k : 自然数∞} (h : f.HasUnifEigenvalue μ k)
  证明: rfl

@[simp]
-/
lemma UnifEigenvalues.val_mk {f : End R M} {μ : R} {k : Nat∞} (h : f.HasUnifEigenvalue μ k) :
    UnifEigenvalues.val f k ⟨μ, h⟩ = μ := rfl

@[simp]
/--
lemma `UnifEigenvalues.mk_val` / 引理 `UnifEigenvalues.mk_val`

English:
lemma UnifEigenvalues.mk_val
  given: {f : End R M} {k : Nat∞} (μ : UnifEigenvalues f k)
  proof: rfl

中文:
引理 UnifEigenvalues.mk_val
  条件: {f : End R M} {k : 自然数∞} (μ : UnifEigenvalues f k)
  证明: rfl
-/
lemma UnifEigenvalues.mk_val {f : End R M} {k : Nat∞} (μ : UnifEigenvalues f k) :
    ⟨μ.val, μ.property⟩ = μ := rfl

/--
Instance `UnifEigenvalues.instCoeOut` / 实例 `UnifEigenvalues.instCoeOut`

English:
instance UnifEigenvalues.instCoeOut
  signature: {f : Module.End R M} (k : Nat∞)
  body: UnifEigenvalues.val f k

中文:
实例 UnifEigenvalues.instCoeOut
  签名: {f : 模.End R M} (k : 自然数∞)
  定义体: UnifEigenvalues.val f k

Depends on / 依赖: UnifEigenvalues, UnifEigenvalues.val
-/
instance UnifEigenvalues.instCoeOut {f : Module.End R M} (k : Nat∞) :
    CoeOut (UnifEigenvalues f k) R where
  coe := UnifEigenvalues.val f k

/--
Instance `UnivEigenvalues.instDecidableEq` / 实例 `UnivEigenvalues.instDecidableEq`

English:
instance UnivEigenvalues.instDecidableEq
  signature: [DecidableEq R] (f : Module.End R M) (k : Nat∞)
  body: inferInstanceAs (DecidableEq (Subtype (fun x : R => f.HasUnifEigenvalue x k)))

中文:
实例 UnivEigenvalues.instDecidableEq
  签名: [DecidableEq R] (f : 模.End R M) (k : 自然数∞)
  定义体: inferInstanceAs (DecidableEq (Subtype (fun x : R => f.HasUnifEigenvalue x k)))

Depends on / 依赖: DecidableEq, HasUnifEigenvalue, Subtype, f.HasUnifEigenvalue
-/
instance UnivEigenvalues.instDecidableEq [DecidableEq R] (f : Module.End R M) (k : Nat∞) :
    DecidableEq (UnifEigenvalues f k) :=
  inferInstanceAs (DecidableEq (Subtype (fun x : R => f.HasUnifEigenvalue x k)))

/--
lemma `HasUnifEigenvector.hasUnifEigenvalue` / 引理 `HasUnifEigenvector.hasUnifEigenvalue`

English:
lemma HasUnifEigenvector.hasUnifEigenvalue
  statement: {f : End R M} {μ : R} {k : Nat∞} {x : M}
  proof: by
  rw [HasUnifEigenvalue]; rw [Submodule.ne_bot_iff]
  use x; exact h

中文:
引理 HasUnifEigenvector.hasUnifEigenvalue
  结论: {f : End R M} {μ : R} {k : 自然数∞} {x : M}
  证明: by
  rw [HasUnifEigenvalue]; rw [Submodule.ne_bot_iff]
  use x; exact h

Depends on / 依赖: HasUnifEigenvalue, Submodule, Submodule.ne_bot_iff, ne_bot_iff
-/
lemma HasUnifEigenvector.hasUnifEigenvalue {f : End R M} {μ : R} {k : Nat∞} {x : M}
    (h : f.HasUnifEigenvector μ k x) : f.HasUnifEigenvalue μ k := by
  rw [HasUnifEigenvalue]; rw [Submodule.ne_bot_iff]
  use x; exact h

/--
lemma `HasUnifEigenvector.apply_eq_smul` / 引理 `HasUnifEigenvector.apply_eq_smul`

English:
lemma HasUnifEigenvector.apply_eq_smul
  statement: {f : End R M} {μ : R} {x : M}
  proof: mem_genEigenspace_one.mp hx.1

中文:
引理 HasUnifEigenvector.apply_eq_smul
  结论: {f : End R M} {μ : R} {x : M}
  证明: mem_genEigenspace_one.mp hx.1

Depends on / 依赖: mem_genEigenspace_one, mem_genEigenspace_one.mp
-/
lemma HasUnifEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M}
    (hx : f.HasUnifEigenvector μ 1 x) : f x = μ • x :=
  mem_genEigenspace_one.mp hx.1

/--
lemma `HasUnifEigenvector.pow_apply` / 引理 `HasUnifEigenvector.pow_apply`

English:
lemma HasUnifEigenvector.pow_apply
  statement: {f : End R M} {μ : R} {v : M} (hv : f.HasUnifEigenvector μ 1 v)
  proof: by
  induction n <;> simp [*, pow_succ f, hv.apply_eq_smul, smul_smul, pow_succ' μ]

中文:
引理 HasUnifEigenvector.pow_apply
  结论: {f : End R M} {μ : R} {v : M} (hv : f.HasUnifEigenvector μ 1 v)
  证明: by
  induction n <;> simp [*, pow_succ f, hv.apply_eq_smul, smul_smul, pow_succ' μ]

Depends on / 依赖: apply_eq_smul, hv.apply_eq_smul, pow_succ, smul_smul
-/
lemma HasUnifEigenvector.pow_apply {f : End R M} {μ : R} {v : M} (hv : f.HasUnifEigenvector μ 1 v)
    (n : Nat) : (f ^ n) v = μ ^ n • v := by
  induction n <;> simp [*, pow_succ f, hv.apply_eq_smul, smul_smul, pow_succ' μ]

/--
theorem `HasUnifEigenvalue.exists_hasUnifEigenvector` / 定理 `HasUnifEigenvalue.exists_hasUnifEigenvector`

English:
theorem HasUnifEigenvalue.exists_hasUnifEigenvector
  proof: Submodule.exists_mem_ne_zero_of_ne_bot hμ

中文:
定理 HasUnifEigenvalue.存在_hasUnifEigenvector
  证明: Submodule.exists_mem_ne_zero_of_ne_bot hμ

Depends on / 依赖: Submodule, Submodule.exists_mem_ne_zero_of_ne_bot, exists_mem_ne_zero_of_ne_bot
-/
theorem HasUnifEigenvalue.exists_hasUnifEigenvector
    {f : End R M} {μ : R} {k : Nat∞} (hμ : f.HasUnifEigenvalue μ k) :
    exists v, f.HasUnifEigenvector μ k v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ

/--
lemma `HasUnifEigenvalue.pow` / 引理 `HasUnifEigenvalue.pow`

English:
lemma HasUnifEigenvalue.pow
  given: {f : End R M} {μ : R} (h : f.HasUnifEigenvalue μ 1) (n : Nat)
  proof: by
  rw [HasUnifEigenvalue]; rw [Submodule.ne_bot_iff]
  obtain ⟨m : M, hm⟩ := h.exists_hasUnifEigenvector
  exact ⟨m, by simpa [mem_genEigenspace_one] using hm.pow_apply n, hm.2⟩

中文:
引理 HasUnifEigenvalue.pow
  条件: {f : End R M} {μ : R} (h : f.HasUnifEigenvalue μ 1) (n : 自然数)
  证明: by
  rw [HasUnifEigenvalue]; rw [Submodule.ne_bot_iff]
  obtain ⟨m : M, hm⟩ := h.exists_hasUnifEigenvector
  exact ⟨m, by simpa [mem_genEigenspace_one] using hm.pow_apply n, hm.2⟩

Depends on / 依赖: HasUnifEigenvalue, Submodule, Submodule.ne_bot_iff, exists_hasUnifEigenvector, h.exists_hasUnifEigenvector, hm.pow_apply, mem_genEigenspace_one, ne_bot_iff, pow_apply
-/
lemma HasUnifEigenvalue.pow {f : End R M} {μ : R} (h : f.HasUnifEigenvalue μ 1) (n : Nat) :
    (f ^ n).HasUnifEigenvalue (μ ^ n) 1 := by
  rw [HasUnifEigenvalue]; rw [Submodule.ne_bot_iff]
  obtain ⟨m : M, hm⟩ := h.exists_hasUnifEigenvector
  exact ⟨m, by simpa [mem_genEigenspace_one] using hm.pow_apply n, hm.2⟩

/--
lemma `HasUnifEigenvalue.isNilpotent_of_isNilpotent` / 引理 `HasUnifEigenvalue.isNilpotent_of_isNilpotent`

English:
lemma HasUnifEigenvalue.isNilpotent_of_isNilpotent
  statement: [IsDomain R] [IsTorsionFree R M] {f : End R M}
  proof: by
  obtain ⟨m : M, hm⟩ := hf.exists_hasUnifEigenvector
  obtain ⟨n : Nat, hn : f ^ n = 0⟩ := hfn
  exact ⟨n, by simpa [hn, hm.2, eq_comm (a := (0 : M))] using hm.pow_apply n⟩

中文:
引理 HasUnifEigenvalue.isNilpotent_of_isNilpotent
  结论: [是整环 R] [是无挠 R M] {f : End R M}
  证明: by
  obtain ⟨m : M, hm⟩ := hf.exists_hasUnifEigenvector
  obtain ⟨n : Nat, hn : f ^ n = 0⟩ := hfn
  exact ⟨n, by simpa [hn, hm.2, eq_comm (a := (0 : M))] using hm.pow_apply n⟩

Depends on / 依赖: eq_comm, exists_hasUnifEigenvector, hf.exists_hasUnifEigenvector, hm.pow_apply, pow_apply
-/
lemma HasUnifEigenvalue.isNilpotent_of_isNilpotent [IsDomain R] [IsTorsionFree R M] {f : End R M}
    (hfn : IsNilpotent f) {μ : R} (hf : f.HasUnifEigenvalue μ 1) :
    IsNilpotent μ := by
  obtain ⟨m : M, hm⟩ := hf.exists_hasUnifEigenvector
  obtain ⟨n : Nat, hn : f ^ n = 0⟩ := hfn
  exact ⟨n, by simpa [hn, hm.2, eq_comm (a := (0 : M))] using hm.pow_apply n⟩

/--
lemma `HasUnifEigenvalue.mem_spectrum` / 引理 `HasUnifEigenvalue.mem_spectrum`

English:
lemma HasUnifEigenvalue.mem_spectrum
  given: {f : End R M} {μ : R} (hμ : HasUnifEigenvalue f μ 1)
  proof: by
  refine spectrum.mem_iff.mpr fun h_unit => ?_
  set f' := LinearMap.GeneralLinearGroup.toLinearEquiv h_unit.unit
  rcases hμ.exists_hasUnifEigenvector with ⟨v, hv⟩
  refine hv.2 ((LinearMap.ker_eq_bot'.mp f'.ker) v (?_ : μ • v - f v = 0))
  rw [hv.apply_eq_smul]; rw [sub_self]

中文:
引理 HasUnifEigenvalue.mem_spectrum
  条件: {f : End R M} {μ : R} (hμ : HasUnifEigenvalue f μ 1)
  证明: by
  refine spectrum.mem_iff.mpr fun h_unit => ?_
  set f' := LinearMap.GeneralLinearGroup.toLinearEquiv h_unit.unit
  rcases hμ.exists_hasUnifEigenvector with ⟨v, hv⟩
  refine hv.2 ((LinearMap.ker_eq_bot'.mp f'.ker) v (?_ : μ • v - f v = 0))
  rw [hv.apply_eq_smul]; rw [sub_self]

Depends on / 依赖: GeneralLinearGroup, LinearMap, LinearMap.GeneralLinearGroup.toLinearEquiv, LinearMap.ker_eq_bot, apply_eq_smul, exists_hasUnifEigenvector, h_unit, h_unit.unit, hv.apply_eq_smul, ker_eq_bot, mem_iff, spectrum, spectrum.mem_iff.mpr, sub_self, toLinearEquiv
-/
lemma HasUnifEigenvalue.mem_spectrum {f : End R M} {μ : R} (hμ : HasUnifEigenvalue f μ 1) :
    μ in spectrum R f := by
  refine spectrum.mem_iff.mpr fun h_unit => ?_
  set f' := LinearMap.GeneralLinearGroup.toLinearEquiv h_unit.unit
  rcases hμ.exists_hasUnifEigenvector with ⟨v, hv⟩
  refine hv.2 ((LinearMap.ker_eq_bot'.mp f'.ker) v (?_ : μ • v - f v = 0))
  rw [hv.apply_eq_smul]; rw [sub_self]

/--
lemma `hasUnifEigenvalue_iff_mem_spectrum` / 引理 `hasUnifEigenvalue_iff_mem_spectrum`

English:
lemma hasUnifEigenvalue_iff_mem_spectrum
  given: [FiniteDimensional K V] {f : End K V} {μ : K}
  proof: by
  rw [spectrum.mem_iff]; rw [IsUnit.sub_iff]; rw [LinearMap.isUnit_iff_ker_eq_bot]; rw [HasUnifEigenvalue]; rw [genEigenspace_one]; rw [ne_eq]; rw [not_iff_not]
  simp [Submodule.ext_iff, LinearMap.mem_ker]

alias ⟨_, HasUnifEigenvalue.of_mem_spectrum⟩ := hasUnifEigenvalue_iff_mem_spectrum

中文:
引理 hasUnifEigenvalue_iff_mem_spectrum
  条件: [有限维 K V] {f : End K V} {μ : K}
  证明: by
  rw [spectrum.mem_iff]; rw [IsUnit.sub_iff]; rw [LinearMap.isUnit_iff_ker_eq_bot]; rw [HasUnifEigenvalue]; rw [genEigenspace_one]; rw [ne_eq]; rw [not_iff_not]
  simp [Submodule.ext_iff, LinearMap.mem_ker]

alias ⟨_, HasUnifEigenvalue.of_mem_spectrum⟩ := hasUnifEigenvalue_iff_mem_spectrum

Depends on / 依赖: HasUnifEigenvalue, IsUnit, IsUnit.sub_iff, LinearMap, LinearMap.isUnit_iff_ker_eq_bot, LinearMap.mem_ker, Submodule, Submodule.ext_iff, ext_iff, genEigenspace_one, isUnit_iff_ker_eq_bot, mem_iff, mem_ker, ne_eq, not_iff_not, spectrum, spectrum.mem_iff, sub_iff
-/
lemma hasUnifEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasUnifEigenvalue μ 1 ↔ μ in spectrum K f := by
  rw [spectrum.mem_iff]; rw [IsUnit.sub_iff]; rw [LinearMap.isUnit_iff_ker_eq_bot]; rw [HasUnifEigenvalue]; rw [genEigenspace_one]; rw [ne_eq]; rw [not_iff_not]
  simp [Submodule.ext_iff, LinearMap.mem_ker]

alias ⟨_, HasUnifEigenvalue.of_mem_spectrum⟩ := hasUnifEigenvalue_iff_mem_spectrum

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `genEigenspace_div` / 引理 `genEigenspace_div`

English:
lemma genEigenspace_div
  given: (f : End K V) (a b : K) (hb : b != 0)
  proof: calc
    genEigenspace f (a / b) 1 = genEigenspace f (b⁻¹ * a) 1 := by rw [div_eq_mul_inv, mul_comm]
    _ = LinearMap.ker (f - (b⁻¹ * a) • 1) := by rw [genEigenspace_one]
    _ = LinearMap.ker (f - b⁻¹ • a • 1) := by rw [smul_smul]
    _ = LinearMap.ker (b • (f - b⁻¹ • a • 1)) := by rw [LinearMap.ker_smul _ b hb]
    _ = LinearMap.ker (b • f - a • 1) := by rw [smul_sub, smul_inv_smul₀ hb]

中文:
引理 genEigenspace_div
  条件: (f : End K V) (a b : K) (hb : b != 0)
  证明: calc
    genEigenspace f (a / b) 1 = genEigenspace f (b⁻¹ * a) 1 := by rw [div_eq_mul_inv, mul_comm]
    _ = LinearMap.ker (f - (b⁻¹ * a) • 1) := by rw [genEigenspace_one]
    _ = LinearMap.ker (f - b⁻¹ • a • 1) := by rw [smul_smul]
    _ = LinearMap.ker (b • (f - b⁻¹ • a • 1)) := by rw [LinearMap.ker_smul _ b hb]
    _ = LinearMap.ker (b • f - a • 1) := by rw [smul_sub, smul_inv_smul₀ hb]

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.ker_smul, div_eq_mul_inv, genEigenspace, genEigenspace_one, ker_smul, mul_comm, smul_smul, smul_sub
-/
lemma genEigenspace_div (f : End K V) (a b : K) (hb : b != 0) :
    genEigenspace f (a / b) 1 = LinearMap.ker (b • f - a • 1) :=
  calc
    genEigenspace f (a / b) 1 = genEigenspace f (b⁻¹ * a) 1 := by rw [div_eq_mul_inv, mul_comm]
    _ = LinearMap.ker (f - (b⁻¹ * a) • 1) := by rw [genEigenspace_one]
    _ = LinearMap.ker (f - b⁻¹ • a • 1) := by rw [smul_smul]
    _ = LinearMap.ker (b • (f - b⁻¹ • a • 1)) := by rw [LinearMap.ker_smul _ b hb]
    _ = LinearMap.ker (b • f - a • 1) := by rw [smul_sub, smul_inv_smul₀ hb]

/--
Definition of `genEigenrange` / `genEigenrange` 的定义

English:
definition genEigenrange
  signature: (f : End R M) (μ : R) (k : Nat∞)
  body: ⨅ l : Nat, ⨅ (_ : l <= k), LinearMap.range ((f - μ • 1) ^ l)

中文:
定义 genEigenrange
  签名: (f : End R M) (μ : R) (k : 自然数∞)
  定义体: ⨅ l : Nat, ⨅ (_ : l <= k), LinearMap.range ((f - μ • 1) ^ l)

Depends on / 依赖: LinearMap, LinearMap.range
-/
def genEigenrange (f : End R M) (μ : R) (k : Nat∞) : Submodule R M :=
  ⨅ l : Nat, ⨅ (_ : l <= k), LinearMap.range ((f - μ • 1) ^ l)

/--
lemma `genEigenrange_nat` / 引理 `genEigenrange_nat`

English:
lemma genEigenrange_nat
  given: {f : End R M} {μ : R} {k : Nat}
  proof: by
  ext x
  simp only [genEigenrange, Nat.cast_le, Submodule.mem_iInf, LinearMap.mem_range]
  constructor
  · intro h
    exact h _ le_rfl
  · rintro ⟨x, rfl⟩ i hi
    have : k = i + (k - i) := by lia
    rw [this]; rw [pow_add]
    exact ⟨_, rfl⟩

中文:
引理 genEigenrange_nat
  条件: {f : End R M} {μ : R} {k : 自然数}
  证明: by
  ext x
  simp only [genEigenrange, Nat.cast_le, Submodule.mem_iInf, LinearMap.mem_range]
  constructor
  · intro h
    exact h _ le_rfl
  · rintro ⟨x, rfl⟩ i hi
    have : k = i + (k - i) := by lia
    rw [this]; rw [pow_add]
    exact ⟨_, rfl⟩

Depends on / 依赖: LinearMap, LinearMap.mem_range, Nat.cast_le, Submodule, Submodule.mem_iInf, cast_le, genEigenrange, le_rfl, mem_iInf, mem_range, pow_add
-/
lemma genEigenrange_nat {f : End R M} {μ : R} {k : Nat} :
    f.genEigenrange μ k = LinearMap.range ((f - μ • 1) ^ k) := by
  ext x
  simp only [genEigenrange, Nat.cast_le, Submodule.mem_iInf, LinearMap.mem_range]
  constructor
  · intro h
    exact h _ le_rfl
  · rintro ⟨x, rfl⟩ i hi
    have : k = i + (k - i) := by lia
    rw [this]; rw [pow_add]
    exact ⟨_, rfl⟩

/--
lemma `HasUnifEigenvalue.exp_ne_zero` / 引理 `HasUnifEigenvalue.exp_ne_zero`

English:
lemma HasUnifEigenvalue.exp_ne_zero
  statement: {f : End R M} {μ : R} {k : Nat}
  proof: by
  rintro rfl
  simp [HasUnifEigenvalue, Nat.cast_zero, genEigenspace_zero] at h

中文:
引理 HasUnifEigenvalue.exp_ne_zero
  结论: {f : End R M} {μ : R} {k : 自然数}
  证明: by
  rintro rfl
  simp [HasUnifEigenvalue, Nat.cast_zero, genEigenspace_zero] at h

Depends on / 依赖: HasUnifEigenvalue, Nat.cast_zero, cast_zero, genEigenspace_zero
-/
lemma HasUnifEigenvalue.exp_ne_zero {f : End R M} {μ : R} {k : Nat}
    (h : f.HasUnifEigenvalue μ k) : k != 0 := by
  rintro rfl
  simp [HasUnifEigenvalue, Nat.cast_zero, genEigenspace_zero] at h

/--
Definition of `maxUnifEigenspaceIndex` / `maxUnifEigenspaceIndex` 的定义

English:
definition maxUnifEigenspaceIndex
  signature: (f : End R M) (μ : R)
  body: monotonicSequenceLimitIndex (f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom

中文:
定义 maxUnifEigenspaceIndex
  签名: (f : End R M) (μ : R)
  定义体: monotonicSequenceLimitIndex (f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom

Depends on / 依赖: WithTop, WithTop.coeOrderHom.toOrderHom, coeOrderHom, f.genEigenspace, genEigenspace, monotonicSequenceLimitIndex, toOrderHom
-/
noncomputable def maxUnifEigenspaceIndex (f : End R M) (μ : R) :=
monotonicSequenceLimitIndex (f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom

set_option backward.isDefEq.respectTransparency false in
/--
lemma `genEigenspace_top_eq_maxUnifEigenspaceIndex` / 引理 `genEigenspace_top_eq_maxUnifEigenspaceIndex`

English:
lemma genEigenspace_top_eq_maxUnifEigenspaceIndex
  given: [IsNoetherian R M] (f : End R M) (μ : R)
  proof: by
have := WellFoundedGT.iSup_eq_monotonicSequenceLimit
(f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom
  convert! this using 1
  simp only [genEigenspace, OrderHom.coe_mk, le_top, iSup_pos, OrderHom.comp_coe,
    Function.comp_def]
  rw [iSup_prod']; rw [iSup_subtype']; rw [← sSup_range]; rw [← sSup_range]
  congr 1
  aesop

中文:
引理 genEigenspace_top_eq_maxUnifEigenspaceIndex
  条件: [是Noether R M] (f : End R M) (μ : R)
  证明: by
have := WellFoundedGT.iSup_eq_monotonicSequenceLimit
(f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom
  convert! this using 1
  simp only [genEigenspace, OrderHom.coe_mk, le_top, iSup_pos, OrderHom.comp_coe,
    Function.comp_def]
  rw [iSup_prod']; rw [iSup_subtype']; rw [← sSup_range]; rw [← sSup_range]
  congr 1
  aesop

Depends on / 依赖: Function, Function.comp_def, OrderHom, OrderHom.coe_mk, OrderHom.comp_coe, WellFoundedGT, WellFoundedGT.iSup_eq_monotonicSequenceLimit, WithTop, WithTop.coeOrderHom.toOrderHom, coeOrderHom, coe_mk, comp_coe, comp_def, convert, f.genEigenspace, genEigenspace, iSup_eq_monotonicSequenceLimit, iSup_pos, iSup_prod, iSup_subtype
-/
lemma genEigenspace_top_eq_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M) (μ : R) :
    genEigenspace f μ ⊤ = f.genEigenspace μ (maxUnifEigenspaceIndex f μ) := by
have := WellFoundedGT.iSup_eq_monotonicSequenceLimit
(f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom
  convert! this using 1
  simp only [genEigenspace, OrderHom.coe_mk, le_top, iSup_pos, OrderHom.comp_coe,
    Function.comp_def]
  rw [iSup_prod']; rw [iSup_subtype']; rw [← sSup_range]; rw [← sSup_range]
  congr 1
  aesop

/--
lemma `genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex` / 引理 `genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex`

English:
lemma genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex
  statement: [IsNoetherian R M] (f : End R M)
  proof: by
  rw [← genEigenspace_top_eq_maxUnifEigenspaceIndex]
  exact (f.genEigenspace μ).monotone le_top

中文:
引理 genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex
  结论: [是Noether R M] (f : End R M)
  证明: by
  rw [← genEigenspace_top_eq_maxUnifEigenspaceIndex]
  exact (f.genEigenspace μ).monotone le_top

Depends on / 依赖: f.genEigenspace, genEigenspace, genEigenspace_top_eq_maxUnifEigenspaceIndex, le_top, monotone
-/
lemma genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M)
    (μ : R) (k : Nat∞) :
    f.genEigenspace μ k <= f.genEigenspace μ (maxUnifEigenspaceIndex f μ) := by
  rw [← genEigenspace_top_eq_maxUnifEigenspaceIndex]
  exact (f.genEigenspace μ).monotone le_top

/--
theorem `genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le` / 定理 `genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le`

English:
theorem genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le
  statement: [IsNoetherian R M]
  proof: le_antisymm
    (genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex _ _ _)
    ((f.genEigenspace μ).monotone <| by simpa using hk)

中文:
定理 genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le
  结论: [是Noether R M]
  证明: le_antisymm
    (genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex _ _ _)
    ((f.genEigenspace μ).monotone <| by simpa using hk)

Depends on / 依赖: f.genEigenspace, genEigenspace, genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex, le_antisymm, monotone
-/
theorem genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le [IsNoetherian R M]
    (f : End R M) (μ : R) {k : Nat} (hk : maxUnifEigenspaceIndex f μ <= k) :
    f.genEigenspace μ k = f.genEigenspace μ (maxUnifEigenspaceIndex f μ) :=
  le_antisymm
    (genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex _ _ _)
    ((f.genEigenspace μ).monotone <| by simpa using hk)

/--
lemma `HasUnifEigenvalue.le` / 引理 `HasUnifEigenvalue.le`

English:
lemma HasUnifEigenvalue.le
  statement: {f : End R M} {μ : R} {k m : Nat∞}
  proof: by
  unfold HasUnifEigenvalue at *
  contrapose hk
  rw [← le_bot_iff]; rw [← hk]
  exact (f.genEigenspace _).monotone hm

中文:
引理 HasUnifEigenvalue.le
  结论: {f : End R M} {μ : R} {k m : 自然数∞}
  证明: by
  unfold HasUnifEigenvalue at *
  contrapose hk
  rw [← le_bot_iff]; rw [← hk]
  exact (f.genEigenspace _).monotone hm

Depends on / 依赖: HasUnifEigenvalue, contrapose, f.genEigenspace, genEigenspace, le_bot_iff, monotone
-/
lemma HasUnifEigenvalue.le {f : End R M} {μ : R} {k m : Nat∞}
    (hm : k <= m) (hk : f.HasUnifEigenvalue μ k) :
    f.HasUnifEigenvalue μ m := by
  unfold HasUnifEigenvalue at *
  contrapose hk
  rw [← le_bot_iff]; rw [← hk]
  exact (f.genEigenspace _).monotone hm

/--
lemma `HasUnifEigenvalue.lt` / 引理 `HasUnifEigenvalue.lt`

English:
lemma HasUnifEigenvalue.lt
  statement: {f : End R M} {μ : R} {k m : Nat∞}
  proof: by
  apply HasUnifEigenvalue.le (k := 1) (Order.one_le_iff_pos.mpr hm)
  intro contra; apply hk
  rw [genEigenspace_one]; rw [LinearMap.ker_eq_bot] at contra
  rw [eq_bot_iff]
  intro x hx
  rw [mem_genEigenspace] at hx
  rcases hx with ⟨l, -, hx⟩
  rwa [LinearMap.ker_eq_bot.mpr] at hx
  rw [Module.End.coe_pow (f - μ • 1) l]
  exact Function.Injective.iterate contra l

中文:
引理 HasUnifEigenvalue.lt
  结论: {f : End R M} {μ : R} {k m : 自然数∞}
  证明: by
  apply HasUnifEigenvalue.le (k := 1) (Order.one_le_iff_pos.mpr hm)
  intro contra; apply hk
  rw [genEigenspace_one]; rw [LinearMap.ker_eq_bot] at contra
  rw [eq_bot_iff]
  intro x hx
  rw [mem_genEigenspace] at hx
  rcases hx with ⟨l, -, hx⟩
  rwa [LinearMap.ker_eq_bot.mpr] at hx
  rw [Module.End.coe_pow (f - μ • 1) l]
  exact Function.Injective.iterate contra l

Depends on / 依赖: Function, Function.Injective.iterate, HasUnifEigenvalue, HasUnifEigenvalue.le, Injective, LinearMap, LinearMap.ker_eq_bot, LinearMap.ker_eq_bot.mpr, Module, Module.End.coe_pow, Order.one_le_iff_pos.mpr, coe_pow, contra, eq_bot_iff, genEigenspace_one, iterate, ker_eq_bot, mem_genEigenspace, one_le_iff_pos
-/
lemma HasUnifEigenvalue.lt {f : End R M} {μ : R} {k m : Nat∞}
    (hm : 0 < m) (hk : f.HasUnifEigenvalue μ k) :
    f.HasUnifEigenvalue μ m := by
  apply HasUnifEigenvalue.le (k := 1) (Order.one_le_iff_pos.mpr hm)
  intro contra; apply hk
  rw [genEigenspace_one]; rw [LinearMap.ker_eq_bot] at contra
  rw [eq_bot_iff]
  intro x hx
  rw [mem_genEigenspace] at hx
  rcases hx with ⟨l, -, hx⟩
  rwa [LinearMap.ker_eq_bot.mpr] at hx
  rw [Module.End.coe_pow (f - μ • 1) l]
  exact Function.Injective.iterate contra l

/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
/--
lemma `hasUnifEigenvalue_iff_hasUnifEigenvalue_one` / 引理 `hasUnifEigenvalue_iff_hasUnifEigenvalue_one`

English:
lemma hasUnifEigenvalue_iff_hasUnifEigenvalue_one
  given: {f : End R M} {μ : R} {k : Nat∞} (hk : 0 < k)
  proof: ⟨HasUnifEigenvalue.lt zero_lt_one, HasUnifEigenvalue.lt hk⟩

中文:
引理 hasUnifEigenvalue_iff_hasUnifEigenvalue_one
  条件: {f : End R M} {μ : R} {k : 自然数∞} (hk : 0 < k)
  证明: ⟨HasUnifEigenvalue.lt zero_lt_one, HasUnifEigenvalue.lt hk⟩

Depends on / 依赖: HasUnifEigenvalue, HasUnifEigenvalue.lt, zero_lt_one
-/
lemma hasUnifEigenvalue_iff_hasUnifEigenvalue_one {f : End R M} {μ : R} {k : Nat∞} (hk : 0 < k) :
    f.HasUnifEigenvalue μ k ↔ f.HasUnifEigenvalue μ 1 :=
  ⟨HasUnifEigenvalue.lt zero_lt_one, HasUnifEigenvalue.lt hk⟩

/--
lemma `maxUnifEigenspaceIndex_le_finrank` / 引理 `maxUnifEigenspaceIndex_le_finrank`

English:
lemma maxUnifEigenspaceIndex_le_finrank
  given: [FiniteDimensional K V] (f : End K V) (μ : K)
  proof: by
  apply Nat.sInf_le
  intro n hn
  apply le_antisymm
· exact (f.genEigenspace μ).monotone WithTop.coeOrderHom.monotone hn
  · change (f.genEigenspace μ) n <= (f.genEigenspace μ) (finrank K V)
    rw [genEigenspace_nat]; rw [genEigenspace_nat]
    apply ker_pow_le_ker_pow_finrank

中文:
引理 maxUnifEigenspaceIndex_le_finrank
  条件: [有限维 K V] (f : End K V) (μ : K)
  证明: by
  apply Nat.sInf_le
  intro n hn
  apply le_antisymm
· exact (f.genEigenspace μ).monotone WithTop.coeOrderHom.monotone hn
  · change (f.genEigenspace μ) n <= (f.genEigenspace μ) (finrank K V)
    rw [genEigenspace_nat]; rw [genEigenspace_nat]
    apply ker_pow_le_ker_pow_finrank

Depends on / 依赖: Nat.sInf_le, WithTop, WithTop.coeOrderHom.monotone, coeOrderHom, f.genEigenspace, finrank, genEigenspace, genEigenspace_nat, ker_pow_le_ker_pow_finrank, le_antisymm, monotone, sInf_le
-/
lemma maxUnifEigenspaceIndex_le_finrank [FiniteDimensional K V] (f : End K V) (μ : K) :
    maxUnifEigenspaceIndex f μ <= finrank K V := by
  apply Nat.sInf_le
  intro n hn
  apply le_antisymm
· exact (f.genEigenspace μ).monotone WithTop.coeOrderHom.monotone hn
  · change (f.genEigenspace μ) n <= (f.genEigenspace μ) (finrank K V)
    rw [genEigenspace_nat]; rw [genEigenspace_nat]
    apply ker_pow_le_ker_pow_finrank

/--
lemma `genEigenspace_le_genEigenspace_finrank` / 引理 `genEigenspace_le_genEigenspace_finrank`

English:
lemma genEigenspace_le_genEigenspace_finrank
  statement: [FiniteDimensional K V] (f : End K V)
  proof: by
  calc f.genEigenspace μ k
      <= f.genEigenspace μ ⊤ := (f.genEigenspace _).monotone le_top
    _ <= f.genEigenspace μ (finrank K V) := by
      rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]
exact (f.genEigenspace _).monotone by simpa using maxUnifEigenspaceIndex_le_finrank f μ

中文:
引理 genEigenspace_le_genEigenspace_finrank
  结论: [有限维 K V] (f : End K V)
  证明: by
  calc f.genEigenspace μ k
      <= f.genEigenspace μ ⊤ := (f.genEigenspace _).monotone le_top
    _ <= f.genEigenspace μ (finrank K V) := by
      rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]
exact (f.genEigenspace _).monotone by simpa using maxUnifEigenspaceIndex_le_finrank f μ

Depends on / 依赖: f.genEigenspace, finrank, genEigenspace, genEigenspace_top_eq_maxUnifEigenspaceIndex, le_top, maxUnifEigenspaceIndex_le_finrank, monotone
-/
lemma genEigenspace_le_genEigenspace_finrank [FiniteDimensional K V] (f : End K V)
    (μ : K) (k : Nat∞) : f.genEigenspace μ k <= f.genEigenspace μ (finrank K V) := by
  calc f.genEigenspace μ k
      <= f.genEigenspace μ ⊤ := (f.genEigenspace _).monotone le_top
    _ <= f.genEigenspace μ (finrank K V) := by
      rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]
exact (f.genEigenspace _).monotone by simpa using maxUnifEigenspaceIndex_le_finrank f μ

/--
theorem `genEigenspace_eq_genEigenspace_finrank_of_le` / 定理 `genEigenspace_eq_genEigenspace_finrank_of_le`

English:
theorem genEigenspace_eq_genEigenspace_finrank_of_le
  statement: [FiniteDimensional K V]
  proof: le_antisymm
    (genEigenspace_le_genEigenspace_finrank _ _ _)
    ((f.genEigenspace μ).monotone <| by simpa using hk)

中文:
定理 genEigenspace_eq_genEigenspace_finrank_of_le
  结论: [有限维 K V]
  证明: le_antisymm
    (genEigenspace_le_genEigenspace_finrank _ _ _)
    ((f.genEigenspace μ).monotone <| by simpa using hk)

Depends on / 依赖: f.genEigenspace, genEigenspace, genEigenspace_le_genEigenspace_finrank, le_antisymm, monotone
-/
theorem genEigenspace_eq_genEigenspace_finrank_of_le [FiniteDimensional K V]
    (f : End K V) (μ : K) {k : Nat} (hk : finrank K V <= k) :
    f.genEigenspace μ k = f.genEigenspace μ (finrank K V) :=
  le_antisymm
    (genEigenspace_le_genEigenspace_finrank _ _ _)
    ((f.genEigenspace μ).monotone <| by simpa using hk)

/--
lemma `mapsTo_genEigenspace_of_comm` / 引理 `mapsTo_genEigenspace_of_comm`

English:
lemma mapsTo_genEigenspace_of_comm
  given: {f g : End R M} (h : Commute f g) (μ : R) (k : Nat∞)
  proof: by
  intro x hx
  simp only [SetLike.mem_coe, mem_genEigenspace, LinearMap.mem_ker] at hx ⊢
  rcases hx with ⟨l, hl, hx⟩
  replace h : Commute ((f - μ • (1 : End R M)) ^ l) g :=
    (h.sub_left <| Algebra.commute_algebraMap_left μ g).pow_left l
  use l, hl
  rw [← LinearMap.comp_apply]; rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_eq_comp]; rw [LinearMap.comp_apply]; rw [hx]; rw [map_zero]

中文:
引理 mapsTo_genEigenspace_of_comm
  条件: {f g : End R M} (h : Commute f g) (μ : R) (k : 自然数∞)
  证明: by
  intro x hx
  simp only [SetLike.mem_coe, mem_genEigenspace, LinearMap.mem_ker] at hx ⊢
  rcases hx with ⟨l, hl, hx⟩
  replace h : Commute ((f - μ • (1 : End R M)) ^ l) g :=
    (h.sub_left <| Algebra.commute_algebraMap_left μ g).pow_left l
  use l, hl
  rw [← LinearMap.comp_apply]; rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_eq_comp]; rw [LinearMap.comp_apply]; rw [hx]; rw [map_zero]

Depends on / 依赖: Algebra, Algebra.commute_algebraMap_left, Commute, LinearMap, LinearMap.comp_apply, LinearMap.mem_ker, Module, Module.End.mul_eq_comp, SetLike, SetLike.mem_coe, commute_algebraMap_left, comp_apply, h.eq, h.sub_left, map_zero, mem_coe, mem_genEigenspace, mem_ker, mul_eq_comp, pow_left
-/
lemma mapsTo_genEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) :
    MapsTo g (f.genEigenspace μ k) (f.genEigenspace μ k) := by
  intro x hx
  simp only [SetLike.mem_coe, mem_genEigenspace, LinearMap.mem_ker] at hx ⊢
  rcases hx with ⟨l, hl, hx⟩
  replace h : Commute ((f - μ • (1 : End R M)) ^ l) g :=
    (h.sub_left <| Algebra.commute_algebraMap_left μ g).pow_left l
  use l, hl
  rw [← LinearMap.comp_apply]; rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_eq_comp]; rw [LinearMap.comp_apply]; rw [hx]; rw [map_zero]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isNilpotent_restrict_genEigenspace_nat` / 引理 `isNilpotent_restrict_genEigenspace_nat`

English:
lemma isNilpotent_restrict_genEigenspace_nat
  statement: (f : End R M) (μ : R) (k : Nat)
  proof: by
  use k
  ext ⟨x, hx⟩
  rw [mem_genEigenspace_nat] at hx
  rw [LinearMap.zero_apply]; rw [ZeroMemClass.coe_zero]; rw [ZeroMemClass.coe_eq_zero]; rw [Module.End.pow_restrict]; rw [LinearMap.restrict_apply]
  ext
  simpa

中文:
引理 isNilpotent_restrict_genEigenspace_nat
  结论: (f : End R M) (μ : R) (k : 自然数)
  证明: by
  use k
  ext ⟨x, hx⟩
  rw [mem_genEigenspace_nat] at hx
  rw [LinearMap.zero_apply]; rw [ZeroMemClass.coe_zero]; rw [ZeroMemClass.coe_eq_zero]; rw [Module.End.pow_restrict]; rw [LinearMap.restrict_apply]
  ext
  simpa

Depends on / 依赖: Algebra, Algebra.mul_sub_algebraMap_commutes, IsNilpotent, LinearMap, LinearMap.restrict_apply, LinearMap.zero_apply, Module, Module.End.pow_restrict, ZeroMemClass, ZeroMemClass.coe_eq_zero, ZeroMemClass.coe_zero, coe_eq_zero, coe_zero, mapsTo_genEigenspace_of_comm, mem_genEigenspace_nat, mul_sub_algebraMap_commutes, pow_restrict, restrict, restrict_apply, zero_apply
-/
lemma isNilpotent_restrict_genEigenspace_nat (f : End R M) (μ : R) (k : Nat)
    (h : MapsTo (f - μ • (1 : End R M))
      (f.genEigenspace μ k) (f.genEigenspace μ k) :=
      mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ k) :
    IsNilpotent ((f - μ • 1).restrict h) := by
  use k
  ext ⟨x, hx⟩
  rw [mem_genEigenspace_nat] at hx
  rw [LinearMap.zero_apply]; rw [ZeroMemClass.coe_zero]; rw [ZeroMemClass.coe_eq_zero]; rw [Module.End.pow_restrict]; rw [LinearMap.restrict_apply]
  ext
  simpa

/--
lemma `isNilpotent_restrict_genEigenspace_top` / 引理 `isNilpotent_restrict_genEigenspace_top`

English:
lemma isNilpotent_restrict_genEigenspace_top
  statement: [IsNoetherian R M] (f : End R M) (μ : R)
  proof: by
  apply isNilpotent_restrict_of_le
  on_goal 2 => apply isNilpotent_restrict_genEigenspace_nat f μ (maxUnifEigenspaceIndex f μ)
  rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]

中文:
引理 isNilpotent_restrict_genEigenspace_top
  结论: [是Noether R M] (f : End R M) (μ : R)
  证明: by
  apply isNilpotent_restrict_of_le
  on_goal 2 => apply isNilpotent_restrict_genEigenspace_nat f μ (maxUnifEigenspaceIndex f μ)
  rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]

Depends on / 依赖: Algebra, Algebra.mul_sub_algebraMap_commutes, IsNilpotent, genEigenspace_top_eq_maxUnifEigenspaceIndex, isNilpotent_restrict_genEigenspace_nat, isNilpotent_restrict_of_le, mapsTo_genEigenspace_of_comm, maxUnifEigenspaceIndex, mul_sub_algebraMap_commutes, on_goal, restrict
-/
lemma isNilpotent_restrict_genEigenspace_top [IsNoetherian R M] (f : End R M) (μ : R)
    (h : MapsTo (f - μ • (1 : End R M))
      (f.genEigenspace μ ⊤) (f.genEigenspace μ ⊤) :=
      mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ _) :
    IsNilpotent ((f - μ • 1).restrict h) := by
  apply isNilpotent_restrict_of_le
  on_goal 2 => apply isNilpotent_restrict_genEigenspace_nat f μ (maxUnifEigenspaceIndex f μ)
  rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]

/--
Definition of `eigenspace` / `eigenspace` 的定义

English:
abbreviation eigenspace
  signature: (f : End R M) (μ : R)
  body: f.genEigenspace μ 1

中文:
缩写 eigenspace
  签名: (f : End R M) (μ : R)
  定义体: f.genEigenspace μ 1

Depends on / 依赖: f.genEigenspace, genEigenspace
-/
abbrev eigenspace (f : End R M) (μ : R) : Submodule R M :=
  f.genEigenspace μ 1

/--
lemma `eigenspace_def` / 引理 `eigenspace_def`

English:
lemma eigenspace_def
  given: {f : End R M} {μ : R}
  proof: by
  rw [eigenspace]; rw [genEigenspace_one]

@[simp]

中文:
引理 eigenspace_def
  条件: {f : End R M} {μ : R}
  证明: by
  rw [eigenspace]; rw [genEigenspace_one]

@[simp]

Depends on / 依赖: eigenspace, genEigenspace_one
-/
lemma eigenspace_def {f : End R M} {μ : R} :
    f.eigenspace μ = LinearMap.ker (f - μ • 1) := by
  rw [eigenspace]; rw [genEigenspace_one]

@[simp]
/--
theorem `eigenspace_zero` / 定理 `eigenspace_zero`

English:
theorem eigenspace_zero
  given: (f : End R M)
  statement: f.eigenspace 0 = LinearMap.ker f
  proof: by
  simp only [eigenspace, ← Nat.cast_one (R := Nat∞), genEigenspace_zero_nat, pow_one]

中文:
定理 eigenspace_zero
  条件: (f : End R M)
  结论: f.eigenspace 0 = 线性映射.ker f
  证明: by
  simp only [eigenspace, ← Nat.cast_one (R := Nat∞), genEigenspace_zero_nat, pow_one]

Depends on / 依赖: Nat.cast_one, cast_one, eigenspace, genEigenspace_zero_nat, pow_one
-/
theorem eigenspace_zero (f : End R M) : f.eigenspace 0 = LinearMap.ker f := by
  simp only [eigenspace, ← Nat.cast_one (R := Nat∞), genEigenspace_zero_nat, pow_one]

/--
Definition of `HasEigenvector` / `HasEigenvector` 的定义

English:
abbreviation HasEigenvector
  signature: (f : End R M) (μ : R) (x : M)
  body: HasUnifEigenvector f μ 1 x

中文:
缩写 HasEigenvector
  签名: (f : End R M) (μ : R) (x : M)
  定义体: HasUnifEigenvector f μ 1 x

Depends on / 依赖: HasUnifEigenvector
-/
abbrev HasEigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  HasUnifEigenvector f μ 1 x

/--
lemma `hasEigenvector_iff` / 引理 `hasEigenvector_iff`

English:
lemma hasEigenvector_iff
  given: {f : End R M} {μ : R} {x : M}
  proof: Iff.rfl

中文:
引理 hasEigenvector_iff
  条件: {f : End R M} {μ : R} {x : M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma hasEigenvector_iff {f : End R M} {μ : R} {x : M} :
    f.HasEigenvector μ x ↔ x in f.eigenspace μ ∧ x != 0 := Iff.rfl

/--
Definition of `HasEigenvalue` / `HasEigenvalue` 的定义

English:
abbreviation HasEigenvalue
  signature: (f : End R M) (a : R)
  body: HasUnifEigenvalue f a 1

中文:
缩写 HasEigenvalue
  签名: (f : End R M) (a : R)
  定义体: HasUnifEigenvalue f a 1

Depends on / 依赖: HasUnifEigenvalue
-/
abbrev HasEigenvalue (f : End R M) (a : R) : Prop :=
  HasUnifEigenvalue f a 1

/--
lemma `hasEigenvalue_iff` / 引理 `hasEigenvalue_iff`

English:
lemma hasEigenvalue_iff
  given: {f : End R M} {μ : R}
  proof: Iff.rfl

中文:
引理 hasEigenvalue_iff
  条件: {f : End R M} {μ : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma hasEigenvalue_iff {f : End R M} {μ : R} :
    f.HasEigenvalue μ ↔ f.eigenspace μ != ⊥ := Iff.rfl

/--
Definition of `Eigenvalues` / `Eigenvalues` 的定义

English:
abbreviation Eigenvalues
  signature: (f : End R M)
  body: UnifEigenvalues f 1

@[coe]

中文:
缩写 Eigenvalues
  签名: (f : End R M)
  定义体: UnifEigenvalues f 1

@[coe]

Depends on / 依赖: UnifEigenvalues
-/
abbrev Eigenvalues (f : End R M) : Type _ :=
  UnifEigenvalues f 1

@[coe]
/--
Definition of `Eigenvalues.val` / `Eigenvalues.val` 的定义

English:
abbreviation Eigenvalues.val
  signature: (f : Module.End R M)
  body: UnifEigenvalues.val f 1

@[simp]

中文:
缩写 Eigenvalues.val
  签名: (f : 模.End R M)
  定义体: UnifEigenvalues.val f 1

@[simp]

Depends on / 依赖: UnifEigenvalues, UnifEigenvalues.val
-/
abbrev Eigenvalues.val (f : Module.End R M) : Eigenvalues f -> R := UnifEigenvalues.val f 1

@[simp]
/--
lemma `Eigenvalues.val_mk` / 引理 `Eigenvalues.val_mk`

English:
lemma Eigenvalues.val_mk
  given: {f : End R M} {μ : R} (h : f.HasEigenvalue μ)
  proof: rfl

@[simp]

中文:
引理 Eigenvalues.val_mk
  条件: {f : End R M} {μ : R} (h : f.HasEigenvalue μ)
  证明: rfl

@[simp]
-/
lemma Eigenvalues.val_mk {f : End R M} {μ : R} (h : f.HasEigenvalue μ) :
    Eigenvalues.val f ⟨μ, h⟩ = μ := rfl

@[simp]
/--
lemma `Eigenvalues.mk_val` / 引理 `Eigenvalues.mk_val`

English:
lemma Eigenvalues.mk_val
  given: {f : End R M} (μ : Eigenvalues f)
  statement: ⟨μ.val, μ.property⟩ = μ
  proof: rfl

中文:
引理 Eigenvalues.mk_val
  条件: {f : End R M} (μ : Eigenvalues f)
  结论: ⟨μ.val, μ.property⟩ = μ
  证明: rfl
-/
lemma Eigenvalues.mk_val {f : End R M} (μ : Eigenvalues f) : ⟨μ.val, μ.property⟩ = μ := rfl

/--
theorem `hasEigenvalue_of_hasEigenvector` / 定理 `hasEigenvalue_of_hasEigenvector`

English:
theorem hasEigenvalue_of_hasEigenvector
  given: {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x)
  proof: h.hasUnifEigenvalue

中文:
定理 hasEigenvalue_of_hasEigenvector
  条件: {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x)
  证明: h.hasUnifEigenvalue

Depends on / 依赖: h.hasUnifEigenvalue, hasUnifEigenvalue
-/
theorem hasEigenvalue_of_hasEigenvector {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) :
    HasEigenvalue f μ :=
  h.hasUnifEigenvalue

/--
theorem `mem_eigenspace_iff` / 定理 `mem_eigenspace_iff`

English:
theorem mem_eigenspace_iff
  given: {f : End R M} {μ : R} {x : M}
  statement: x in eigenspace f μ ↔ f x = μ • x
  proof: mem_genEigenspace_one

nonrec

中文:
定理 mem_eigenspace_iff
  条件: {f : End R M} {μ : R} {x : M}
  结论: x in eigenspace f μ ↔ f x = μ • x
  证明: mem_genEigenspace_one

nonrec

Depends on / 依赖: mem_genEigenspace_one
-/
theorem mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x in eigenspace f μ ↔ f x = μ • x :=
  mem_genEigenspace_one

nonrec
/--
theorem `HasEigenvector.apply_eq_smul` / 定理 `HasEigenvector.apply_eq_smul`

English:
theorem HasEigenvector.apply_eq_smul
  given: {f : End R M} {μ : R} {x : M} (hx : f.HasEigenvector μ x)
  proof: hx.apply_eq_smul

nonrec

中文:
定理 HasEigenvector.apply_eq_smul
  条件: {f : End R M} {μ : R} {x : M} (hx : f.HasEigenvector μ x)
  证明: hx.apply_eq_smul

nonrec

Depends on / 依赖: apply_eq_smul, hx.apply_eq_smul
-/
theorem HasEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M} (hx : f.HasEigenvector μ x) :
    f x = μ • x :=
  hx.apply_eq_smul

nonrec
/--
theorem `HasEigenvector.pow_apply` / 定理 `HasEigenvector.pow_apply`

English:
theorem HasEigenvector.pow_apply
  given: {f : End R M} {μ : R} {v : M} (hv : f.HasEigenvector μ v) (n : Nat)
  proof: hv.pow_apply n

中文:
定理 HasEigenvector.pow_apply
  条件: {f : End R M} {μ : R} {v : M} (hv : f.HasEigenvector μ v) (n : 自然数)
  证明: hv.pow_apply n

Depends on / 依赖: hv.pow_apply, pow_apply
-/
theorem HasEigenvector.pow_apply {f : End R M} {μ : R} {v : M} (hv : f.HasEigenvector μ v) (n : Nat) :
    (f ^ n) v = μ ^ n • v :=
  hv.pow_apply n

/--
theorem `HasEigenvalue.exists_hasEigenvector` / 定理 `HasEigenvalue.exists_hasEigenvector`

English:
theorem HasEigenvalue.exists_hasEigenvector
  given: {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ)
  proof: Submodule.exists_mem_ne_zero_of_ne_bot hμ

nonrec

中文:
定理 HasEigenvalue.存在_hasEigenvector
  条件: {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ)
  证明: Submodule.exists_mem_ne_zero_of_ne_bot hμ

nonrec

Depends on / 依赖: Submodule, Submodule.exists_mem_ne_zero_of_ne_bot, exists_mem_ne_zero_of_ne_bot
-/
theorem HasEigenvalue.exists_hasEigenvector {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ) :
    exists v, f.HasEigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ

nonrec
/--
lemma `HasEigenvalue.pow` / 引理 `HasEigenvalue.pow`

English:
lemma HasEigenvalue.pow
  given: {f : End R M} {μ : R} (h : f.HasEigenvalue μ) (n : Nat)
  proof: h.pow n

中文:
引理 HasEigenvalue.pow
  条件: {f : End R M} {μ : R} (h : f.HasEigenvalue μ) (n : 自然数)
  证明: h.pow n

Depends on / 依赖: h.pow
-/
lemma HasEigenvalue.pow {f : End R M} {μ : R} (h : f.HasEigenvalue μ) (n : Nat) :
    (f ^ n).HasEigenvalue (μ ^ n) :=
  h.pow n

/--
theorem `genEigenspace_mem_invtSubmodule` / 定理 `genEigenspace_mem_invtSubmodule`

English:
theorem genEigenspace_mem_invtSubmodule
  given: (f : End R M) (μ : R) (n : Nat∞)
  proof: by
  intro x hx
  simp only [Submodule.mem_comap, mem_genEigenspace, LinearMap.mem_ker] at hx ⊢
  obtain ⟨k, hk, hx⟩ := hx
  refine ⟨k, hk, ?_⟩
  induction k generalizing x
  case zero => simp_all
  case succ k ih =>
    rw [pow_succ]; rw [mul_apply] at hx ⊢
    simpa using ih (le_trans (by simp) hk) hx

中文:
定理 genEigenspace_mem_invtSubmodule
  条件: (f : End R M) (μ : R) (n : 自然数∞)
  证明: by
  intro x hx
  simp only [Submodule.mem_comap, mem_genEigenspace, LinearMap.mem_ker] at hx ⊢
  obtain ⟨k, hk, hx⟩ := hx
  refine ⟨k, hk, ?_⟩
  induction k generalizing x
  case zero => simp_all
  case succ k ih =>
    rw [pow_succ]; rw [mul_apply] at hx ⊢
    simpa using ih (le_trans (by simp) hk) hx

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Submodule, Submodule.mem_comap, generalizing, le_trans, mem_comap, mem_genEigenspace, mem_ker, mul_apply, pow_succ
-/
theorem genEigenspace_mem_invtSubmodule (f : End R M) (μ : R) (n : Nat∞) :
    genEigenspace f μ n in invtSubmodule f := by
  intro x hx
  simp only [Submodule.mem_comap, mem_genEigenspace, LinearMap.mem_ker] at hx ⊢
  obtain ⟨k, hk, hx⟩ := hx
  refine ⟨k, hk, ?_⟩
  induction k generalizing x
  case zero => simp_all
  case succ k ih =>
    rw [pow_succ]; rw [mul_apply] at hx ⊢
    simpa using ih (le_trans (by simp) hk) hx

/--
theorem `eigenspace_mem_invtSubmodule` / 定理 `eigenspace_mem_invtSubmodule`

English:
theorem eigenspace_mem_invtSubmodule
  given: (f : End R M) (μ : R)
  proof: genEigenspace_mem_invtSubmodule f μ 1

中文:
定理 eigenspace_mem_invtSubmodule
  条件: (f : End R M) (μ : R)
  证明: genEigenspace_mem_invtSubmodule f μ 1

Depends on / 依赖: genEigenspace_mem_invtSubmodule
-/
theorem eigenspace_mem_invtSubmodule (f : End R M) (μ : R) :
    eigenspace f μ in invtSubmodule f :=
  genEigenspace_mem_invtSubmodule f μ 1

/--
theorem `restrict_eigenspace` / 定理 `restrict_eigenspace`

English:
theorem restrict_eigenspace
  given: (f : End R M) (μ : R)
  proof: by
  ext x
  exact mem_eigenspace_iff.mp x.2

中文:
定理 restrict_eigenspace
  条件: (f : End R M) (μ : R)
  证明: by
  ext x
  exact mem_eigenspace_iff.mp x.2

Depends on / 依赖: mem_eigenspace_iff, mem_eigenspace_iff.mp
-/
theorem restrict_eigenspace (f : End R M) (μ : R) :
    f.restrict (f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
      (eigenspace_mem_invtSubmodule f μ)) = μ • LinearMap.id := by
  ext x
  exact mem_eigenspace_iff.mp x.2

/-- A nilpotent endomorphism has nilpotent eigenvalues.

See also `LinearMap.isNilpotent_trace_of_isNilpotent`. -/
nonrec
/--
lemma `HasEigenvalue.isNilpotent_of_isNilpotent` / 引理 `HasEigenvalue.isNilpotent_of_isNilpotent`

English:
lemma HasEigenvalue.isNilpotent_of_isNilpotent
  statement: [IsDomain R] [IsTorsionFree R M] {f : End R M}
  proof: hf.isNilpotent_of_isNilpotent hfn

nonrec

中文:
引理 HasEigenvalue.isNilpotent_of_isNilpotent
  结论: [是整环 R] [是无挠 R M] {f : End R M}
  证明: hf.isNilpotent_of_isNilpotent hfn

nonrec

Depends on / 依赖: hf.isNilpotent_of_isNilpotent, isNilpotent_of_isNilpotent
-/
lemma HasEigenvalue.isNilpotent_of_isNilpotent [IsDomain R] [IsTorsionFree R M] {f : End R M}
    (hfn : IsNilpotent f) {μ : R} (hf : f.HasEigenvalue μ) :
    IsNilpotent μ :=
  hf.isNilpotent_of_isNilpotent hfn

nonrec
/--
theorem `HasEigenvalue.mem_spectrum` / 定理 `HasEigenvalue.mem_spectrum`

English:
theorem HasEigenvalue.mem_spectrum
  given: {f : End R M} {μ : R} (hμ : HasEigenvalue f μ)
  proof: hμ.mem_spectrum

中文:
定理 HasEigenvalue.mem_spectrum
  条件: {f : End R M} {μ : R} (hμ : HasEigenvalue f μ)
  证明: hμ.mem_spectrum

Depends on / 依赖: mem_spectrum
-/
theorem HasEigenvalue.mem_spectrum {f : End R M} {μ : R} (hμ : HasEigenvalue f μ) :
    μ in spectrum R f :=
  hμ.mem_spectrum

/--
theorem `hasEigenvalue_iff_mem_spectrum` / 定理 `hasEigenvalue_iff_mem_spectrum`

English:
theorem hasEigenvalue_iff_mem_spectrum
  given: [FiniteDimensional K V] {f : End K V} {μ : K}
  proof: hasUnifEigenvalue_iff_mem_spectrum

alias ⟨_, HasEigenvalue.of_mem_spectrum⟩ := hasEigenvalue_iff_mem_spectrum

中文:
定理 hasEigenvalue_iff_mem_spectrum
  条件: [有限维 K V] {f : End K V} {μ : K}
  证明: hasUnifEigenvalue_iff_mem_spectrum

alias ⟨_, HasEigenvalue.of_mem_spectrum⟩ := hasEigenvalue_iff_mem_spectrum

Depends on / 依赖: hasUnifEigenvalue_iff_mem_spectrum
-/
theorem hasEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasEigenvalue μ ↔ μ in spectrum K f :=
  hasUnifEigenvalue_iff_mem_spectrum

alias ⟨_, HasEigenvalue.of_mem_spectrum⟩ := hasEigenvalue_iff_mem_spectrum

/--
theorem `eigenspace_div` / 定理 `eigenspace_div`

English:
theorem eigenspace_div
  given: (f : End K V) (a b : K) (hb : b != 0)
  proof: genEigenspace_div f a b hb

中文:
定理 eigenspace_div
  条件: (f : End K V) (a b : K) (hb : b != 0)
  证明: genEigenspace_div f a b hb

Depends on / 依赖: genEigenspace_div
-/
theorem eigenspace_div (f : End K V) (a b : K) (hb : b != 0) :
    eigenspace f (a / b) = LinearMap.ker (b • f - algebraMap K (End K V) a) :=
  genEigenspace_div f a b hb

/--
Definition of `HasGenEigenvector` / `HasGenEigenvector` 的定义

English:
abbreviation HasGenEigenvector
  signature: (f : End R M) (μ : R) (k : Nat) (x : M)
  body: HasUnifEigenvector f μ k x

中文:
缩写 HasGenEigenvector
  签名: (f : End R M) (μ : R) (k : 自然数) (x : M)
  定义体: HasUnifEigenvector f μ k x

Depends on / 依赖: HasUnifEigenvector
-/
abbrev HasGenEigenvector (f : End R M) (μ : R) (k : Nat) (x : M) : Prop :=
  HasUnifEigenvector f μ k x

/--
lemma `hasGenEigenvector_iff` / 引理 `hasGenEigenvector_iff`

English:
lemma hasGenEigenvector_iff
  given: {f : End R M} {μ : R} {k : Nat} {x : M}
  proof: Iff.rfl

中文:
引理 hasGenEigenvector_iff
  条件: {f : End R M} {μ : R} {k : 自然数} {x : M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma hasGenEigenvector_iff {f : End R M} {μ : R} {k : Nat} {x : M} :
    f.HasGenEigenvector μ k x ↔ x in f.genEigenspace μ k ∧ x != 0 := Iff.rfl

/--
Definition of `HasGenEigenvalue` / `HasGenEigenvalue` 的定义

English:
abbreviation HasGenEigenvalue
  signature: (f : End R M) (μ : R) (k : Nat)
  body: HasUnifEigenvalue f μ k

中文:
缩写 HasGenEigenvalue
  签名: (f : End R M) (μ : R) (k : 自然数)
  定义体: HasUnifEigenvalue f μ k

Depends on / 依赖: HasUnifEigenvalue
-/
abbrev HasGenEigenvalue (f : End R M) (μ : R) (k : Nat) : Prop :=
  HasUnifEigenvalue f μ k

/--
lemma `hasGenEigenvalue_iff` / 引理 `hasGenEigenvalue_iff`

English:
lemma hasGenEigenvalue_iff
  given: {f : End R M} {μ : R} {k : Nat}
  proof: Iff.rfl

中文:
引理 hasGenEigenvalue_iff
  条件: {f : End R M} {μ : R} {k : 自然数}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma hasGenEigenvalue_iff {f : End R M} {μ : R} {k : Nat} :
    f.HasGenEigenvalue μ k ↔ f.genEigenspace μ k != ⊥ := Iff.rfl

/--
theorem `exp_ne_zero_of_hasGenEigenvalue` / 定理 `exp_ne_zero_of_hasGenEigenvalue`

English:
theorem exp_ne_zero_of_hasGenEigenvalue
  statement: {f : End R M} {μ : R} {k : Nat}
  proof: HasUnifEigenvalue.exp_ne_zero h

中文:
定理 exp_ne_zero_of_hasGenEigenvalue
  结论: {f : End R M} {μ : R} {k : 自然数}
  证明: HasUnifEigenvalue.exp_ne_zero h

Depends on / 依赖: HasUnifEigenvalue, HasUnifEigenvalue.exp_ne_zero, exp_ne_zero
-/
theorem exp_ne_zero_of_hasGenEigenvalue {f : End R M} {μ : R} {k : Nat}
    (h : f.HasGenEigenvalue μ k) : k != 0 :=
  HasUnifEigenvalue.exp_ne_zero h

/--
Definition of `maxGenEigenspace` / `maxGenEigenspace` 的定义

English:
abbreviation maxGenEigenspace
  signature: (f : End R M) (μ : R)
  body: genEigenspace f μ ⊤

中文:
缩写 maxGenEigenspace
  签名: (f : End R M) (μ : R)
  定义体: genEigenspace f μ ⊤

Depends on / 依赖: genEigenspace
-/
abbrev maxGenEigenspace (f : End R M) (μ : R) : Submodule R M :=
  genEigenspace f μ ⊤

/--
lemma `iSup_genEigenspace_eq` / 引理 `iSup_genEigenspace_eq`

English:
lemma iSup_genEigenspace_eq
  given: (f : End R M) (μ : R)
  proof: by
  simp_rw [maxGenEigenspace, genEigenspace_top]

中文:
引理 iSup_genEigenspace_eq
  条件: (f : End R M) (μ : R)
  证明: by
  simp_rw [maxGenEigenspace, genEigenspace_top]

Depends on / 依赖: genEigenspace_top, maxGenEigenspace, simp_rw
-/
lemma iSup_genEigenspace_eq (f : End R M) (μ : R) :
    ⨆ k : Nat, (f.genEigenspace μ) k = f.maxGenEigenspace μ := by
  simp_rw [maxGenEigenspace, genEigenspace_top]

/--
theorem `genEigenspace_le_maximal` / 定理 `genEigenspace_le_maximal`

English:
theorem genEigenspace_le_maximal
  given: (f : End R M) (μ : R) (k : Nat)
  proof: (f.genEigenspace μ).monotone le_top

@[simp]

中文:
定理 genEigenspace_le_maximal
  条件: (f : End R M) (μ : R) (k : 自然数)
  证明: (f.genEigenspace μ).monotone le_top

@[simp]

Depends on / 依赖: f.genEigenspace, genEigenspace, le_top, monotone
-/
theorem genEigenspace_le_maximal (f : End R M) (μ : R) (k : Nat) :
    f.genEigenspace μ k <= f.maxGenEigenspace μ :=
  (f.genEigenspace μ).monotone le_top

@[simp]
/--
theorem `mem_maxGenEigenspace` / 定理 `mem_maxGenEigenspace`

English:
theorem mem_maxGenEigenspace
  given: (f : End R M) (μ : R) (m : M)
  proof: mem_genEigenspace_top

中文:
定理 mem_maxGenEigenspace
  条件: (f : End R M) (μ : R) (m : M)
  证明: mem_genEigenspace_top

Depends on / 依赖: mem_genEigenspace_top
-/
theorem mem_maxGenEigenspace (f : End R M) (μ : R) (m : M) :
    m in f.maxGenEigenspace μ ↔ exists k : Nat, ((f - μ • (1 : End R M)) ^ k) m = 0 :=
  mem_genEigenspace_top

/--
Definition of `maxGenEigenspaceIndex` / `maxGenEigenspaceIndex` 的定义

English:
abbreviation maxGenEigenspaceIndex
  signature: (f : End R M) (μ : R)
  body: maxUnifEigenspaceIndex f μ

中文:
缩写 maxGenEigenspaceIndex
  签名: (f : End R M) (μ : R)
  定义体: maxUnifEigenspaceIndex f μ

Depends on / 依赖: maxUnifEigenspaceIndex
-/
noncomputable abbrev maxGenEigenspaceIndex (f : End R M) (μ : R) :=
  maxUnifEigenspaceIndex f μ

/--
theorem `maxGenEigenspace_eq` / 定理 `maxGenEigenspace_eq`

English:
theorem maxGenEigenspace_eq
  given: [IsNoetherian R M] (f : End R M) (μ : R)
  proof: genEigenspace_top_eq_maxUnifEigenspaceIndex _ _

中文:
定理 maxGenEigenspace_eq
  条件: [是Noether R M] (f : End R M) (μ : R)
  证明: genEigenspace_top_eq_maxUnifEigenspaceIndex _ _

Depends on / 依赖: genEigenspace_top_eq_maxUnifEigenspaceIndex
-/
theorem maxGenEigenspace_eq [IsNoetherian R M] (f : End R M) (μ : R) :
    maxGenEigenspace f μ = f.genEigenspace μ (maxGenEigenspaceIndex f μ) :=
  genEigenspace_top_eq_maxUnifEigenspaceIndex _ _

/--
theorem `maxGenEigenspace_eq_maxGenEigenspace_zero` / 定理 `maxGenEigenspace_eq_maxGenEigenspace_zero`

English:
theorem maxGenEigenspace_eq_maxGenEigenspace_zero
  given: (f : End R M) (μ : R)
  proof: by
  ext; simp

中文:
定理 maxGenEigenspace_eq_maxGenEigenspace_zero
  条件: (f : End R M) (μ : R)
  证明: by
  ext; simp
-/
theorem maxGenEigenspace_eq_maxGenEigenspace_zero (f : End R M) (μ : R) :
    maxGenEigenspace f μ = maxGenEigenspace (f - μ • 1) 0 := by
  ext; simp

/--
theorem `hasGenEigenvalue_of_hasGenEigenvalue_of_le` / 定理 `hasGenEigenvalue_of_hasGenEigenvalue_of_le`

English:
theorem hasGenEigenvalue_of_hasGenEigenvalue_of_le
  statement: {f : End R M} {μ : R} {k : Nat}
  proof: hk.le by simpa using hm

中文:
定理 hasGenEigenvalue_of_hasGenEigenvalue_of_le
  结论: {f : End R M} {μ : R} {k : 自然数}
  证明: hk.le by simpa using hm

Depends on / 依赖: hk.le
-/
theorem hasGenEigenvalue_of_hasGenEigenvalue_of_le {f : End R M} {μ : R} {k : Nat}
    {m : Nat} (hm : k <= m) (hk : f.HasGenEigenvalue μ k) :
    f.HasGenEigenvalue μ m :=
hk.le by simpa using hm

/--
theorem `eigenspace_le_genEigenspace` / 定理 `eigenspace_le_genEigenspace`

English:
theorem eigenspace_le_genEigenspace
  given: {f : End R M} {μ : R} {k : Nat} (hk : 0 < k)
  proof: (f.genEigenspace _).monotone by simpa using Nat.succ_le_of_lt hk

中文:
定理 eigenspace_le_genEigenspace
  条件: {f : End R M} {μ : R} {k : 自然数} (hk : 0 < k)
  证明: (f.genEigenspace _).monotone by simpa using Nat.succ_le_of_lt hk

Depends on / 依赖: Nat.succ_le_of_lt, f.genEigenspace, genEigenspace, monotone, succ_le_of_lt
-/
theorem eigenspace_le_genEigenspace {f : End R M} {μ : R} {k : Nat} (hk : 0 < k) :
    f.eigenspace μ <= f.genEigenspace μ k :=
(f.genEigenspace _).monotone by simpa using Nat.succ_le_of_lt hk

/--
theorem `eigenspace_le_maxGenEigenspace` / 定理 `eigenspace_le_maxGenEigenspace`

English:
theorem eigenspace_le_maxGenEigenspace
  given: {f : End R M} {μ : R}
  proof: (f.genEigenspace _).monotone OrderTop.le_top _

中文:
定理 eigenspace_le_maxGenEigenspace
  条件: {f : End R M} {μ : R}
  证明: (f.genEigenspace _).monotone OrderTop.le_top _

Depends on / 依赖: OrderTop, OrderTop.le_top, f.genEigenspace, genEigenspace, le_top, monotone
-/
theorem eigenspace_le_maxGenEigenspace {f : End R M} {μ : R} :
    f.eigenspace μ <= f.maxGenEigenspace μ :=
(f.genEigenspace _).monotone OrderTop.le_top _

/--
theorem `hasGenEigenvalue_of_hasEigenvalue` / 定理 `hasGenEigenvalue_of_hasEigenvalue`

English:
theorem hasGenEigenvalue_of_hasEigenvalue
  statement: {f : End R M} {μ : R} {k : Nat} (hk : 0 < k)
  proof: hμ.lt by simpa using hk

中文:
定理 hasGenEigenvalue_of_hasEigenvalue
  结论: {f : End R M} {μ : R} {k : 自然数} (hk : 0 < k)
  证明: hμ.lt by simpa using hk
-/
theorem hasGenEigenvalue_of_hasEigenvalue {f : End R M} {μ : R} {k : Nat} (hk : 0 < k)
    (hμ : f.HasEigenvalue μ) : f.HasGenEigenvalue μ k :=
hμ.lt by simpa using hk

/--
theorem `hasEigenvalue_of_hasGenEigenvalue` / 定理 `hasEigenvalue_of_hasGenEigenvalue`

English:
theorem hasEigenvalue_of_hasGenEigenvalue
  statement: {f : End R M} {μ : R} {k : Nat}
  proof: hμ.lt zero_lt_one

中文:
定理 hasEigenvalue_of_hasGenEigenvalue
  结论: {f : End R M} {μ : R} {k : 自然数}
  证明: hμ.lt zero_lt_one

Depends on / 依赖: Subtype, Subtype.ext, star_involutive, zero_lt_one
-/
theorem hasEigenvalue_of_hasGenEigenvalue {f : End R M} {μ : R} {k : Nat}
    (hμ : f.HasGenEigenvalue μ k) : f.HasEigenvalue μ :=
  hμ.lt zero_lt_one

/--
theorem `hasGenEigenvalue_iff_hasEigenvalue` / 定理 `hasGenEigenvalue_iff_hasEigenvalue`

English:
theorem hasGenEigenvalue_iff_hasEigenvalue
  given: {f : End R M} {μ : R} {k : Nat} (hk : 0 < k)
  proof: by
  simp [hk]

中文:
定理 hasGenEigenvalue_iff_hasEigenvalue
  条件: {f : End R M} {μ : R} {k : 自然数} (hk : 0 < k)
  证明: by
  simp [hk]
-/
theorem hasGenEigenvalue_iff_hasEigenvalue {f : End R M} {μ : R} {k : Nat} (hk : 0 < k) :
    f.HasGenEigenvalue μ k ↔ f.HasEigenvalue μ := by
  simp [hk]

/--
theorem `maxGenEigenspace_eq_genEigenspace_finrank` / 定理 `maxGenEigenspace_eq_genEigenspace_finrank`

English:
theorem maxGenEigenspace_eq_genEigenspace_finrank
  proof: by
apply le_antisymm _ (f.genEigenspace μ).monotone le_top
  rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]
  apply genEigenspace_le_genEigenspace_finrank f μ

中文:
定理 maxGenEigenspace_eq_genEigenspace_finrank
  证明: by
apply le_antisymm _ (f.genEigenspace μ).monotone le_top
  rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]
  apply genEigenspace_le_genEigenspace_finrank f μ

Depends on / 依赖: f.genEigenspace, genEigenspace, genEigenspace_le_genEigenspace_finrank, genEigenspace_top_eq_maxUnifEigenspaceIndex, le_antisymm, le_top, monotone
-/
theorem maxGenEigenspace_eq_genEigenspace_finrank
    [FiniteDimensional K V] (f : End K V) (μ : K) :
    f.maxGenEigenspace μ = f.genEigenspace μ (finrank K V) := by
apply le_antisymm _ (f.genEigenspace μ).monotone le_top
  rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]
  apply genEigenspace_le_genEigenspace_finrank f μ

/--
lemma `mapsTo_maxGenEigenspace_of_comm` / 引理 `mapsTo_maxGenEigenspace_of_comm`

English:
lemma mapsTo_maxGenEigenspace_of_comm
  given: {f g : End R M} (h : Commute f g) (μ : R)
  proof: mapsTo_genEigenspace_of_comm h μ ⊤

中文:
引理 mapsTo_maxGenEigenspace_of_comm
  条件: {f g : End R M} (h : Commute f g) (μ : R)
  证明: mapsTo_genEigenspace_of_comm h μ ⊤

Depends on / 依赖: ENNReal, ENNReal.le_rpow_inv_iff, ENNReal.rpow_left_bijective, ENNReal.strictMono_rpow_of_pos, _lim_eq_lintegral_liminf, atTop.liminf, eLpNorm, enorm.pow_const, h_lim, h_pow_liminf, h_rpow, h_rpow_mono, h_rpow_mono.orderIsoOfSurjective, h_rpow_surj, hp_pos, hp_pos.ne.symm, inv_inv, le_rpow_inv_iff, liminf, lintegral_liminf_le
-/
lemma mapsTo_maxGenEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) :
    MapsTo g ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
  mapsTo_genEigenspace_of_comm h μ ⊤

/--
lemma `isNilpotent_restrict_sub_algebraMap` / 引理 `isNilpotent_restrict_sub_algebraMap`

English:
lemma isNilpotent_restrict_sub_algebraMap
  statement: (f : End R M) (μ : R) (k : Nat)
  proof: isNilpotent_restrict_genEigenspace_nat _ _ _

中文:
引理 isNilpotent_restrict_sub_algebraMap
  结论: (f : End R M) (μ : R) (k : 自然数)
  证明: isNilpotent_restrict_genEigenspace_nat _ _ _

Depends on / 依赖: Algebra, Algebra.mul_sub_algebraMap_commutes, IsNilpotent, algebraMap, isNilpotent_restrict_genEigenspace_nat, mapsTo_genEigenspace_of_comm, mul_sub_algebraMap_commutes, restrict
-/
lemma isNilpotent_restrict_sub_algebraMap (f : End R M) (μ : R) (k : Nat)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      (f.genEigenspace μ k) (f.genEigenspace μ k) :=
      mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ k) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) :=
  isNilpotent_restrict_genEigenspace_nat _ _ _

/--
lemma `isNilpotent_restrict_maxGenEigenspace_sub_algebraMap` / 引理 `isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`

English:
lemma isNilpotent_restrict_maxGenEigenspace_sub_algebraMap
  statement: [IsNoetherian R M] (f : End R M) (μ : R)
  proof: by
  apply isNilpotent_restrict_of_le (q := f.genEigenspace μ (maxUnifEigenspaceIndex f μ))
    _ (isNilpotent_restrict_genEigenspace_nat f μ (maxUnifEigenspaceIndex f μ))
  rw [maxGenEigenspace_eq]

中文:
引理 isNilpotent_restrict_maxGenEigenspace_sub_algebraMap
  结论: [是Noether R M] (f : End R M) (μ : R)
  证明: by
  apply isNilpotent_restrict_of_le (q := f.genEigenspace μ (maxUnifEigenspaceIndex f μ))
    _ (isNilpotent_restrict_genEigenspace_nat f μ (maxUnifEigenspaceIndex f μ))
  rw [maxGenEigenspace_eq]

Depends on / 依赖: Algebra, Algebra.mul_sub_algebraMap_commutes, IsNilpotent, algebraMap, f.genEigenspace, genEigenspace, isNilpotent_restrict_genEigenspace_nat, isNilpotent_restrict_of_le, mapsTo_maxGenEigenspace_of_comm, maxGenEigenspace_eq, maxUnifEigenspaceIndex, mul_sub_algebraMap_commutes, restrict
-/
lemma isNilpotent_restrict_maxGenEigenspace_sub_algebraMap [IsNoetherian R M] (f : End R M) (μ : R)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
      mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) := by
  apply isNilpotent_restrict_of_le (q := f.genEigenspace μ (maxUnifEigenspaceIndex f μ))
    _ (isNilpotent_restrict_genEigenspace_nat f μ (maxUnifEigenspaceIndex f μ))
  rw [maxGenEigenspace_eq]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `disjoint_genEigenspace` / 引理 `disjoint_genEigenspace`

English:
lemma disjoint_genEigenspace
  statement: [IsDomain R] [IsTorsionFree R M]
  proof: by
  rw [genEigenspace_eq_iSup_genEigenspace_nat]; rw [genEigenspace_eq_iSup_genEigenspace_nat]
  simp_rw [genEigenspace_directed.disjoint_iSup_left, genEigenspace_directed.disjoint_iSup_right]
  rintro ⟨k, -⟩ ⟨l, -⟩
  nontriviality M
  rw [disjoint_iff]
  set p := f.genEigenspace μ₁ k ⊓ f.genEigenspace μ₂ l
  by_contra hp
  replace hp : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
let f₁ : End R p := (f - algebraMap R (End R M) μ₁).restrict MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₂ l)
let f₂ : End R p := (f - algebraMap R (End R M) μ₂).restrict MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₂ l)
  have : IsNilpotent (f₂ - f₁) := by
    apply Commute.isNilpotent_sub (x := f₂) (y := f₁) _
      (isNilpotent_restrict_of_le inf_le_right _)
      (isNilpotent_restrict_of_le inf_le_left _)
    · ext; simp [f₁, f₂, smul_sub, sub_sub, smul_comm μ₁, add_sub_left_comm]
    · apply mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    · apply isNilpotent_restrict_genEigenspace_nat
    · apply mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    apply isNilpotent_restrict_genEigenspace_nat
  have hf₁₂ : f₂ - f₁ = algebraMap R (End R p) (μ₁ - μ₂) := by ext; simp [f₁, f₂]
  rw [hf₁₂]; rw [IsNilpotent.map_iff (FaithfulSMul.algebraMap_injective R (End R p))]; rw [isNilpotent_iff_eq_zero]; rw [sub_eq_zero] at this
  contradiction

中文:
引理 disjoint_genEigenspace
  结论: [是整环 R] [是无挠 R M]
  证明: by
  rw [genEigenspace_eq_iSup_genEigenspace_nat]; rw [genEigenspace_eq_iSup_genEigenspace_nat]
  simp_rw [genEigenspace_directed.disjoint_iSup_left, genEigenspace_directed.disjoint_iSup_right]
  rintro ⟨k, -⟩ ⟨l, -⟩
  nontriviality M
  rw [disjoint_iff]
  set p := f.genEigenspace μ₁ k ⊓ f.genEigenspace μ₂ l
  by_contra hp
  replace hp : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
let f₁ : End R p := (f - algebraMap R (End R M) μ₁).restrict MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₂ l)
let f₂ : End R p := (f - algebraMap R (End R M) μ₂).restrict MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₂ l)
  have : IsNilpotent (f₂ - f₁) := by
    apply Commute.isNilpotent_sub (x := f₂) (y := f₁) _
      (isNilpotent_restrict_of_le inf_le_right _)
      (isNilpotent_restrict_of_le inf_le_left _)
    · ext; simp [f₁, f₂, smul_sub, sub_sub, smul_comm μ₁, add_sub_left_comm]
    · apply mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    · apply isNilpotent_restrict_genEigenspace_nat
    · apply mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    apply isNilpotent_restrict_genEigenspace_nat
  have hf₁₂ : f₂ - f₁ = algebraMap R (End R p) (μ₁ - μ₂) := by ext; simp [f₁, f₂]
  rw [hf₁₂]; rw [IsNilpotent.map_iff (FaithfulSMul.algebraMap_injective R (End R p))]; rw [isNilpotent_iff_eq_zero]; rw [sub_eq_zero] at this
  contradiction

Depends on / 依赖: Algebra, Algebra.mu, MapsTo, MapsTo.inter_inter, Nontrivial, Submodule, Submodule.nontrivial_iff_ne_bot.mpr, algebraMap, disjoint_iSup_left, disjoint_iSup_right, disjoint_iff, f.genEigenspace, genEigenspace, genEigenspace_directed, genEigenspace_directed.disjoint_iSup_left, genEigenspace_directed.disjoint_iSup_right, genEigenspace_eq_iSup_genEigenspace_nat, inter_inter, mapsTo_genEigenspace_of_comm, nontrivial_iff_ne_bot
-/
lemma disjoint_genEigenspace [IsDomain R] [IsTorsionFree R M]
    (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ != μ₂) (k l : Nat∞) :
    Disjoint (f.genEigenspace μ₁ k) (f.genEigenspace μ₂ l) := by
  rw [genEigenspace_eq_iSup_genEigenspace_nat]; rw [genEigenspace_eq_iSup_genEigenspace_nat]
  simp_rw [genEigenspace_directed.disjoint_iSup_left, genEigenspace_directed.disjoint_iSup_right]
  rintro ⟨k, -⟩ ⟨l, -⟩
  nontriviality M
  rw [disjoint_iff]
  set p := f.genEigenspace μ₁ k ⊓ f.genEigenspace μ₂ l
  by_contra hp
  replace hp : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
let f₁ : End R p := (f - algebraMap R (End R M) μ₁).restrict MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₂ l)
let f₂ : End R p := (f - algebraMap R (End R M) μ₂).restrict MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₂ l)
  have : IsNilpotent (f₂ - f₁) := by
    apply Commute.isNilpotent_sub (x := f₂) (y := f₁) _
      (isNilpotent_restrict_of_le inf_le_right _)
      (isNilpotent_restrict_of_le inf_le_left _)
    · ext; simp [f₁, f₂, smul_sub, sub_sub, smul_comm μ₁, add_sub_left_comm]
    · apply mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    · apply isNilpotent_restrict_genEigenspace_nat
    · apply mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    apply isNilpotent_restrict_genEigenspace_nat
  have hf₁₂ : f₂ - f₁ = algebraMap R (End R p) (μ₁ - μ₂) := by ext; simp [f₁, f₂]
  rw [hf₁₂]; rw [IsNilpotent.map_iff (FaithfulSMul.algebraMap_injective R (End R p))]; rw [isNilpotent_iff_eq_zero]; rw [sub_eq_zero] at this
  contradiction

/--
lemma `injOn_genEigenspace` / 引理 `injOn_genEigenspace`

English:
lemma injOn_genEigenspace
  given: [IsDomain R] [IsTorsionFree R M] (f : End R M) (k : Nat∞)
  proof: by
  rintro μ₁ _ μ₂ hμ₂ hμ₁₂
  by_contra contra
  apply hμ₂
  simpa only [hμ₁₂, disjoint_self] using f.disjoint_genEigenspace contra k k

中文:
引理 injOn_genEigenspace
  条件: [是整环 R] [是无挠 R M] (f : End R M) (k : 自然数∞)
  证明: by
  rintro μ₁ _ μ₂ hμ₂ hμ₁₂
  by_contra contra
  apply hμ₂
  simpa only [hμ₁₂, disjoint_self] using f.disjoint_genEigenspace contra k k

Depends on / 依赖: contra, disjoint_genEigenspace, disjoint_self, f.disjoint_genEigenspace
-/
lemma injOn_genEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) (k : Nat∞) :
    InjOn (f.genEigenspace · k) {μ | f.genEigenspace μ k != ⊥} := by
  rintro μ₁ _ μ₂ hμ₂ hμ₁₂
  by_contra contra
  apply hμ₂
  simpa only [hμ₁₂, disjoint_self] using f.disjoint_genEigenspace contra k k

/--
lemma `injOn_maxGenEigenspace` / 引理 `injOn_maxGenEigenspace`

English:
lemma injOn_maxGenEigenspace
  given: [IsDomain R] [IsTorsionFree R M] (f : End R M)
  proof: injOn_genEigenspace f ⊤

中文:
引理 injOn_maxGenEigenspace
  条件: [是整环 R] [是无挠 R M] (f : End R M)
  证明: injOn_genEigenspace f ⊤

Depends on / 依赖: injOn_genEigenspace
-/
lemma injOn_maxGenEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) :
    InjOn (f.maxGenEigenspace ·) {μ | f.maxGenEigenspace μ != ⊥} :=
  injOn_genEigenspace f ⊤

/--
theorem `independent_genEigenspace` / 定理 `independent_genEigenspace`

English:
theorem independent_genEigenspace
  given: [IsDomain R] [IsTorsionFree R M] (f : End R M) (k : Nat∞)
  proof: by
  classical
  suffices forall μ₁ (s : Finset R), μ₁ ∉ s -> Disjoint (f.genEigenspace μ₁ k)
    (s.sup fun μ => f.genEigenspace μ k) by
    simp_rw [iSupIndep_iff_supIndep,
      Finset.supIndep_iff_disjoint_erase]
    exact fun s μ _ => this _ _ (s.notMem_erase μ)
  intro μ₁ s
  induction s using Finset.induction_on with
  | empty => simp
  | insert μ₂ s _ ih =>
  intro hμ₁₂
  obtain ⟨hμ₁₂ : μ₁ != μ₂, hμ₁ : μ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hμ₁₂
  specialize ih hμ₁
  rw [Finset.sup_insert]; rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe] at hx hx'
  suffices x in genEigenspace f μ₂ k by
    rw [← Submodule.mem_bot (R := R)]; rw [← (f.disjoint_genEigenspace hμ₁₂ k k).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'; clear hx'
  let g := f - μ₂ • 1
  simp_rw [mem_genEigenspace, ← exists_prop] at hy ⊢
  peel hy with l hlk hl
  simp only [LinearMap.mem_ker] at hl
  have hyz : (g ^ l) (y + z) in
      (f.genEigenspace μ₁ k) ⊓ s.sup fun μ => f.genEigenspace μ k := by
    refine ⟨f.mapsTo_genEigenspace_of_comm (g := g ^ l) ?_ μ₁ k hx, ?_⟩
    · exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ l
    · rw [SetLike.mem_coe, map_add, hl, zero_add]
      suffices (s.sup fun μ => f.genEigenspace μ k).map (g ^ l) <=
          s.sup fun μ => f.genEigenspace μ k by exact this (Submodule.mem_map_of_mem hz)
      simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := R), Submodule.map_iSup (ι := _ in s)]
      refine iSup₂_mono fun μ _ => ?_
      rintro - ⟨u, hu, rfl⟩
      refine f.mapsTo_genEigenspace_of_comm ?_ μ k hu
      exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ l
  rwa [ih.eq_bot, Submodule.mem_bot] at hyz

中文:
定理 independent_genEigenspace
  条件: [是整环 R] [是无挠 R M] (f : End R M) (k : 自然数∞)
  证明: by
  classical
  suffices forall μ₁ (s : Finset R), μ₁ ∉ s -> Disjoint (f.genEigenspace μ₁ k)
    (s.sup fun μ => f.genEigenspace μ k) by
    simp_rw [iSupIndep_iff_supIndep,
      Finset.supIndep_iff_disjoint_erase]
    exact fun s μ _ => this _ _ (s.notMem_erase μ)
  intro μ₁ s
  induction s using Finset.induction_on with
  | empty => simp
  | insert μ₂ s _ ih =>
  intro hμ₁₂
  obtain ⟨hμ₁₂ : μ₁ != μ₂, hμ₁ : μ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hμ₁₂
  specialize ih hμ₁
  rw [Finset.sup_insert]; rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe] at hx hx'
  suffices x in genEigenspace f μ₂ k by
    rw [← Submodule.mem_bot (R := R)]; rw [← (f.disjoint_genEigenspace hμ₁₂ k k).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'; clear hx'
  let g := f - μ₂ • 1
  simp_rw [mem_genEigenspace, ← exists_prop] at hy ⊢
  peel hy with l hlk hl
  simp only [LinearMap.mem_ker] at hl
  have hyz : (g ^ l) (y + z) in
      (f.genEigenspace μ₁ k) ⊓ s.sup fun μ => f.genEigenspace μ k := by
    refine ⟨f.mapsTo_genEigenspace_of_comm (g := g ^ l) ?_ μ₁ k hx, ?_⟩
    · exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ l
    · rw [SetLike.mem_coe, map_add, hl, zero_add]
      suffices (s.sup fun μ => f.genEigenspace μ k).map (g ^ l) <=
          s.sup fun μ => f.genEigenspace μ k by exact this (Submodule.mem_map_of_mem hz)
      simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := R), Submodule.map_iSup (ι := _ in s)]
      refine iSup₂_mono fun μ _ => ?_
      rintro - ⟨u, hu, rfl⟩
      refine f.mapsTo_genEigenspace_of_comm ?_ μ k hu
      exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ l
  rwa [ih.eq_bot, Submodule.mem_bot] at hyz

Depends on / 依赖: Disjoint, Finset, Finset.induction_on, Finset.mem_insert, Finset.supIndep_iff_disjoint_erase, Finset.sup_insert, classical, disjoint_iff, f.genEigenspace, genEigenspace, iSupIndep_iff_supIndep, induction_on, insert, mem_insert, notMem_erase, not_or, s.notMem_erase, s.sup, simp_rw, specialize
-/
theorem independent_genEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) (k : Nat∞) :
    iSupIndep (f.genEigenspace · k) := by
  classical
  suffices forall μ₁ (s : Finset R), μ₁ ∉ s -> Disjoint (f.genEigenspace μ₁ k)
    (s.sup fun μ => f.genEigenspace μ k) by
    simp_rw [iSupIndep_iff_supIndep,
      Finset.supIndep_iff_disjoint_erase]
    exact fun s μ _ => this _ _ (s.notMem_erase μ)
  intro μ₁ s
  induction s using Finset.induction_on with
  | empty => simp
  | insert μ₂ s _ ih =>
  intro hμ₁₂
  obtain ⟨hμ₁₂ : μ₁ != μ₂, hμ₁ : μ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hμ₁₂
  specialize ih hμ₁
  rw [Finset.sup_insert]; rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe] at hx hx'
  suffices x in genEigenspace f μ₂ k by
    rw [← Submodule.mem_bot (R := R)]; rw [← (f.disjoint_genEigenspace hμ₁₂ k k).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'; clear hx'
  let g := f - μ₂ • 1
  simp_rw [mem_genEigenspace, ← exists_prop] at hy ⊢
  peel hy with l hlk hl
  simp only [LinearMap.mem_ker] at hl
  have hyz : (g ^ l) (y + z) in
      (f.genEigenspace μ₁ k) ⊓ s.sup fun μ => f.genEigenspace μ k := by
    refine ⟨f.mapsTo_genEigenspace_of_comm (g := g ^ l) ?_ μ₁ k hx, ?_⟩
    · exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ l
    · rw [SetLike.mem_coe, map_add, hl, zero_add]
      suffices (s.sup fun μ => f.genEigenspace μ k).map (g ^ l) <=
          s.sup fun μ => f.genEigenspace μ k by exact this (Submodule.mem_map_of_mem hz)
      simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := R), Submodule.map_iSup (ι := _ in s)]
      refine iSup₂_mono fun μ _ => ?_
      rintro - ⟨u, hu, rfl⟩
      refine f.mapsTo_genEigenspace_of_comm ?_ μ k hu
      exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ l
  rwa [ih.eq_bot, Submodule.mem_bot] at hyz

/--
theorem `independent_maxGenEigenspace` / 定理 `independent_maxGenEigenspace`

English:
theorem independent_maxGenEigenspace
  given: [IsDomain R] [IsTorsionFree R M] (f : End R M)
  proof: by
  apply independent_genEigenspace

中文:
定理 independent_maxGenEigenspace
  条件: [是整环 R] [是无挠 R M] (f : End R M)
  证明: by
  apply independent_genEigenspace

Depends on / 依赖: independent_genEigenspace
-/
theorem independent_maxGenEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) :
    iSupIndep f.maxGenEigenspace := by
  apply independent_genEigenspace

/--
theorem `eigenspaces_iSupIndep` / 定理 `eigenspaces_iSupIndep`

English:
theorem eigenspaces_iSupIndep
  given: [IsDomain R] [IsTorsionFree R M] (f : End R M)
  proof: f.independent_genEigenspace 1

中文:
定理 eigenspaces_iSupIndep
  条件: [是整环 R] [是无挠 R M] (f : End R M)
  证明: f.independent_genEigenspace 1

Depends on / 依赖: f.independent_genEigenspace, independent_genEigenspace
-/
theorem eigenspaces_iSupIndep [IsDomain R] [IsTorsionFree R M] (f : End R M) :
    iSupIndep f.eigenspace :=
  f.independent_genEigenspace 1

/--
theorem `eigenvectors_linearIndependent'` / 定理 `eigenvectors_linearIndependent'`

English:
theorem eigenvectors_linearIndependent'
  statement: {ι : Type*} [IsDomain R] [IsTorsionFree R M]
  proof: .linearIndependent _ f.eigenspaces_iSupIndep.comp hμ
    (fun i => h_eigenvec i |>.left) (fun i => h_eigenvec i |>.right)

中文:
定理 eigenvectors_linearIndependent'
  结论: {ι : 类型} [是整环 R] [是无挠 R M]
  证明: .linearIndependent _ f.eigenspaces_iSupIndep.comp hμ
    (fun i => h_eigenvec i |>.left) (fun i => h_eigenvec i |>.right)

Depends on / 依赖: eigenspaces_iSupIndep, f.eigenspaces_iSupIndep.comp, h_eigenvec, linearIndependent
-/
theorem eigenvectors_linearIndependent' {ι : Type*} [IsDomain R] [IsTorsionFree R M]
    (f : End R M) (μ : ι -> R) (hμ : Function.Injective μ) (v : ι -> M)
    (h_eigenvec : forall i, f.HasEigenvector (μ i) (v i)) : LinearIndependent R v :=
.linearIndependent _ f.eigenspaces_iSupIndep.comp hμ
    (fun i => h_eigenvec i |>.left) (fun i => h_eigenvec i |>.right)

/--
theorem `eigenvectors_linearIndependent` / 定理 `eigenvectors_linearIndependent`

English:
theorem eigenvectors_linearIndependent
  statement: [IsDomain R] [IsTorsionFree R M]
  proof: f.eigenvectors_linearIndependent' (fun μ : μs => μ) Subtype.coe_injective _ h_eigenvec

中文:
定理 eigenvectors_linearIndependent
  结论: [是整环 R] [是无挠 R M]
  证明: f.eigenvectors_linearIndependent' (fun μ : μs => μ) Subtype.coe_injective _ h_eigenvec

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, eigenvectors_linearIndependent, f.eigenvectors_linearIndependent, h_eigenvec
-/
theorem eigenvectors_linearIndependent [IsDomain R] [IsTorsionFree R M]
    (f : End R M) (μs : Set R) (xs : μs -> M)
    (h_eigenvec : forall μ : μs, f.HasEigenvector μ (xs μ)) : LinearIndependent R xs :=
  f.eigenvectors_linearIndependent' (fun μ : μs => μ) Subtype.coe_injective _ h_eigenvec

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `genEigenspace_restrict` / 定理 `genEigenspace_restrict`

English:
theorem genEigenspace_restrict
  statement: (f : End R M) (p : Submodule R M) (k : Nat∞) (μ : R)
  proof: by
  ext x
  suffices forall l : Nat, genEigenspace (LinearMap.restrict f hfp) μ l =
      Submodule.comap p.subtype (f.genEigenspace μ l) by
    simp_rw [mem_genEigenspace, ← mem_genEigenspace_nat, this,
      Submodule.mem_comap, mem_genEigenspace (k := k), mem_genEigenspace_nat]
  intro l
  rw [genEigenspace_nat]; rw [genEigenspace_nat]; rw [← LinearMap.restrict_smul_one μ]; rw [LinearMap.restrict_sub hfp]; rw [Module.End.pow_restrict _]; rw [← LinearMap.ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype p)]; rw [LinearMap.subtype_comp_restrict]; rw [LinearMap.domRestrict]; rw [← LinearMap.ker_comp]

中文:
定理 genEigenspace_restrict
  结论: (f : End R M) (p : 子模 R M) (k : 自然数∞) (μ : R)
  证明: by
  ext x
  suffices forall l : Nat, genEigenspace (LinearMap.restrict f hfp) μ l =
      Submodule.comap p.subtype (f.genEigenspace μ l) by
    simp_rw [mem_genEigenspace, ← mem_genEigenspace_nat, this,
      Submodule.mem_comap, mem_genEigenspace (k := k), mem_genEigenspace_nat]
  intro l
  rw [genEigenspace_nat]; rw [genEigenspace_nat]; rw [← LinearMap.restrict_smul_one μ]; rw [LinearMap.restrict_sub hfp]; rw [Module.End.pow_restrict _]; rw [← LinearMap.ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype p)]; rw [LinearMap.subtype_comp_restrict]; rw [LinearMap.domRestrict]; rw [← LinearMap.ker_comp]

Depends on / 依赖: LinearMap, LinearMap.ker_comp_of_ker_eq_bot, LinearMap.restrict, LinearMap.restrict_smul_one, LinearMap.restrict_sub, Module, Module.End.pow_restrict, Submodule, Submodule.comap, Submodule.ker_subtype, Submodule.mem_comap, f.genEigenspace, genEigenspace, genEigenspace_nat, ker_comp_of_ker_eq_bot, ker_subtype, mem_comap, mem_genEigenspace, mem_genEigenspace_nat, p.subtype
-/
theorem genEigenspace_restrict (f : End R M) (p : Submodule R M) (k : Nat∞) (μ : R)
    (hfp : forall x : M, x in p -> f x in p) :
    genEigenspace (LinearMap.restrict f hfp) μ k =
      Submodule.comap p.subtype (f.genEigenspace μ k) := by
  ext x
  suffices forall l : Nat, genEigenspace (LinearMap.restrict f hfp) μ l =
      Submodule.comap p.subtype (f.genEigenspace μ l) by
    simp_rw [mem_genEigenspace, ← mem_genEigenspace_nat, this,
      Submodule.mem_comap, mem_genEigenspace (k := k), mem_genEigenspace_nat]
  intro l
  rw [genEigenspace_nat]; rw [genEigenspace_nat]; rw [← LinearMap.restrict_smul_one μ]; rw [LinearMap.restrict_sub hfp]; rw [Module.End.pow_restrict _]; rw [← LinearMap.ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype p)]; rw [LinearMap.subtype_comp_restrict]; rw [LinearMap.domRestrict]; rw [← LinearMap.ker_comp]

/--
lemma `_root_.Submodule.inf_genEigenspace` / 引理 `_root_.Submodule.inf_genEigenspace`

English:
lemma _root_.Submodule.inf_genEigenspace
  statement: (f : End R M) (p : Submodule R M) {k : Nat∞} {μ : R}
  proof: by
  rw [f.genEigenspace_restrict _ _ _ hfp]; rw [Submodule.map_comap_eq]; rw [Submodule.range_subtype]

中文:
引理 _root_.子模.inf_genEigenspace
  结论: (f : End R M) (p : 子模 R M) {k : 自然数∞} {μ : R}
  证明: by
  rw [f.genEigenspace_restrict _ _ _ hfp]; rw [Submodule.map_comap_eq]; rw [Submodule.range_subtype]

Depends on / 依赖: Submodule, Submodule.map_comap_eq, Submodule.range_subtype, f.genEigenspace_restrict, genEigenspace_restrict, map_comap_eq, range_subtype
-/
lemma _root_.Submodule.inf_genEigenspace (f : End R M) (p : Submodule R M) {k : Nat∞} {μ : R}
    (hfp : forall x : M, x in p -> f x in p) :
    p ⊓ f.genEigenspace μ k =
      (genEigenspace (LinearMap.restrict f hfp) μ k).map p.subtype := by
  rw [f.genEigenspace_restrict _ _ _ hfp]; rw [Submodule.map_comap_eq]; rw [Submodule.range_subtype]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo` / 引理 `mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo`

English:
lemma mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo
  proof: by
  intro x hx
  simp_rw [SetLike.mem_coe, mem_maxGenEigenspace, ← LinearMap.restrict_smul_one _,
    LinearMap.restrict_sub _, Module.End.pow_restrict _, LinearMap.restrict_apply,
    Submodule.mk_eq_zero, ← mem_maxGenEigenspace] at hx ⊢
  exact h hx

中文:
引理 mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo
  证明: by
  intro x hx
  simp_rw [SetLike.mem_coe, mem_maxGenEigenspace, ← LinearMap.restrict_smul_one _,
    LinearMap.restrict_sub _, Module.End.pow_restrict _, LinearMap.restrict_apply,
    Submodule.mk_eq_zero, ← mem_maxGenEigenspace] at hx ⊢
  exact h hx

Depends on / 依赖: LinearMap, LinearMap.restrict_apply, LinearMap.restrict_smul_one, LinearMap.restrict_sub, Module, Module.End.pow_restrict, SetLike, SetLike.mem_coe, Submodule, Submodule.mk_eq_zero, mem_coe, mem_maxGenEigenspace, mk_eq_zero, pow_restrict, restrict_apply, restrict_smul_one, restrict_sub, simp_rw
-/
lemma mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo
    {p : Submodule R M} (f g : End R M) (hf : MapsTo f p p) (hg : MapsTo g p p) {μ₁ μ₂ : R}
    (h : MapsTo f (g.maxGenEigenspace μ₁) (g.maxGenEigenspace μ₂)) :
    MapsTo (f.restrict hf)
      (maxGenEigenspace (g.restrict hg) μ₁)
      (maxGenEigenspace (g.restrict hg) μ₂) := by
  intro x hx
  simp_rw [SetLike.mem_coe, mem_maxGenEigenspace, ← LinearMap.restrict_smul_one _,
    LinearMap.restrict_sub _, Module.End.pow_restrict _, LinearMap.restrict_apply,
    Submodule.mk_eq_zero, ← mem_maxGenEigenspace] at hx ⊢
  exact h hx

/--
theorem `eigenspace_restrict_le_eigenspace` / 定理 `eigenspace_restrict_le_eigenspace`

English:
theorem eigenspace_restrict_le_eigenspace
  statement: (f : End R M) {p : Submodule R M} (hfp : forall x in p, f x in p)
  proof: by
  rintro a ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx ⊢
  exact congr_arg Subtype.val hx

中文:
定理 eigenspace_restrict_le_eigenspace
  结论: (f : End R M) {p : 子模 R M} (hfp : 对任意 x in p, f x in p)
  证明: by
  rintro a ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx ⊢
  exact congr_arg Subtype.val hx

Depends on / 依赖: LinearMap, LinearMap.restrict_apply, SetLike, SetLike.mem_coe, Subtype, Subtype.val, congr_arg, mem_coe, mem_eigenspace_iff, restrict_apply
-/
theorem eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp : forall x in p, f x in p)
    (μ : R) : (eigenspace (f.restrict hfp) μ).map p.subtype <= f.eigenspace μ := by
  rintro a ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx ⊢
  exact congr_arg Subtype.val hx

/--
theorem `generalized_eigenvec_disjoint_range_ker` / 定理 `generalized_eigenvec_disjoint_range_ker`

English:
theorem generalized_eigenvec_disjoint_range_ker
  given: [FiniteDimensional K V] (f : End K V) (μ : K)
  proof: by
  have h :=
    calc
      Submodule.comap ((f - μ • 1) ^ finrank K V)
        (f.genEigenspace μ (finrank K V)) =
          LinearMap.ker ((f - algebraMap _ _ μ) ^ finrank K V *
            (f - algebraMap K (End K V) μ) ^ finrank K V) := by
              rw [genEigenspace_nat]; rw [← LinearMap.ker_comp]; rfl
      _ = f.genEigenspace μ (finrank K V + finrank K V : Nat) := by
              simp_rw [← pow_add, genEigenspace_nat]; rfl
      _ = f.genEigenspace μ (finrank K V) := by
              rw [genEigenspace_eq_genEigenspace_finrank_of_le]; lia
  rw [disjoint_iff_inf_le]; rw [genEigenrange_nat]; rw [LinearMap.range_eq_map]; rw [Submodule.map_inf_eq_map_inf_comap]; rw [top_inf_eq]; rw [h]; rw [genEigenspace_nat]
  apply Submodule.map_comap_le

中文:
定理 generalized_eigenvec_disjoint_range_ker
  条件: [有限维 K V] (f : End K V) (μ : K)
  证明: by
  have h :=
    calc
      Submodule.comap ((f - μ • 1) ^ finrank K V)
        (f.genEigenspace μ (finrank K V)) =
          LinearMap.ker ((f - algebraMap _ _ μ) ^ finrank K V *
            (f - algebraMap K (End K V) μ) ^ finrank K V) := by
              rw [genEigenspace_nat]; rw [← LinearMap.ker_comp]; rfl
      _ = f.genEigenspace μ (finrank K V + finrank K V : Nat) := by
              simp_rw [← pow_add, genEigenspace_nat]; rfl
      _ = f.genEigenspace μ (finrank K V) := by
              rw [genEigenspace_eq_genEigenspace_finrank_of_le]; lia
  rw [disjoint_iff_inf_le]; rw [genEigenrange_nat]; rw [LinearMap.range_eq_map]; rw [Submodule.map_inf_eq_map_inf_comap]; rw [top_inf_eq]; rw [h]; rw [genEigenspace_nat]
  apply Submodule.map_comap_le

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.ker_comp, Submodule, Submodule.comap, algebraMap, disjoint_iff_inf_le, f.genEigenspace, finrank, genEigen, genEigenspace, genEigenspace_eq_genEigenspace_finrank_of_le, genEigenspace_nat, ker_comp, pow_add, simp_rw
-/
theorem generalized_eigenvec_disjoint_range_ker [FiniteDimensional K V] (f : End K V) (μ : K) :
    Disjoint (f.genEigenrange μ (finrank K V))
      (f.genEigenspace μ (finrank K V)) := by
  have h :=
    calc
      Submodule.comap ((f - μ • 1) ^ finrank K V)
        (f.genEigenspace μ (finrank K V)) =
          LinearMap.ker ((f - algebraMap _ _ μ) ^ finrank K V *
            (f - algebraMap K (End K V) μ) ^ finrank K V) := by
              rw [genEigenspace_nat]; rw [← LinearMap.ker_comp]; rfl
      _ = f.genEigenspace μ (finrank K V + finrank K V : Nat) := by
              simp_rw [← pow_add, genEigenspace_nat]; rfl
      _ = f.genEigenspace μ (finrank K V) := by
              rw [genEigenspace_eq_genEigenspace_finrank_of_le]; lia
  rw [disjoint_iff_inf_le]; rw [genEigenrange_nat]; rw [LinearMap.range_eq_map]; rw [Submodule.map_inf_eq_map_inf_comap]; rw [top_inf_eq]; rw [h]; rw [genEigenspace_nat]
  apply Submodule.map_comap_le

/--
theorem `eigenspace_restrict_eq_bot` / 定理 `eigenspace_restrict_eq_bot`

English:
theorem eigenspace_restrict_eq_bot
  statement: {f : End R M} {p : Submodule R M} (hfp : forall x in p, f x in p)
  proof: by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp.le_bot ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩

中文:
定理 eigenspace_restrict_eq_bot
  结论: {f : End R M} {p : 子模 R M} (hfp : 对任意 x in p, f x in p)
  证明: by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp.le_bot ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩

Depends on / 依赖: eigenspace_restrict_le_eigenspace, eq_bot_iff, le_bot, p.le_bot, x.prop
-/
theorem eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : forall x in p, f x in p)
    {μ : R} (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.restrict hfp) μ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp.le_bot ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩

/--
theorem `pos_finrank_genEigenspace_of_hasEigenvalue` / 定理 `pos_finrank_genEigenspace_of_hasEigenvalue`

English:
theorem pos_finrank_genEigenspace_of_hasEigenvalue
  statement: [FiniteDimensional K V] {f : End K V}
  proof: calc
    0 = finrank K (⊥ : Submodule K V) := by rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ <= finrank K (f.genEigenspace μ k) :=
      Submodule.finrank_mono ((f.genEigenspace μ).monotone (by simpa using Nat.succ_le_of_lt hk))

中文:
定理 pos_finrank_genEigenspace_of_hasEigenvalue
  结论: [有限维 K V] {f : End K V}
  证明: calc
    0 = finrank K (⊥ : Submodule K V) := by rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ <= finrank K (f.genEigenspace μ k) :=
      Submodule.finrank_mono ((f.genEigenspace μ).monotone (by simpa using Nat.succ_le_of_lt hk))

Depends on / 依赖: Nat.succ_le_of_lt, Submodule, Submodule.finrank_lt_finrank_of_lt, Submodule.finrank_mono, bot_lt_iff_ne_bot, eigenspace, f.eigenspace, f.genEigenspace, finrank, finrank_bot, finrank_lt_finrank_of_lt, finrank_mono, genEigenspace, monotone, succ_le_of_lt
-/
theorem pos_finrank_genEigenspace_of_hasEigenvalue [FiniteDimensional K V] {f : End K V}
    {k : Nat} {μ : K} (hx : f.HasEigenvalue μ) (hk : 0 < k) :
    0 < finrank K (f.genEigenspace μ k) :=
  calc
    0 = finrank K (⊥ : Submodule K V) := by rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ <= finrank K (f.genEigenspace μ k) :=
      Submodule.finrank_mono ((f.genEigenspace μ).monotone (by simpa using Nat.succ_le_of_lt hk))

/--
theorem `map_genEigenrange_le` / 定理 `map_genEigenrange_le`

English:
theorem map_genEigenrange_le
  given: {f : End K V} {μ : K} {n : Nat}
  proof: calc
    Submodule.map f (f.genEigenrange μ n) =
      LinearMap.range (f * (f - algebraMap _ _ μ) ^ n) := by
        rw [genEigenrange_nat]; exact (LinearMap.range_comp _ _).symm
    _ = LinearMap.range ((f - algebraMap _ _ μ) ^ n * f) := by
        rw [Algebra.mul_sub_algebraMap_pow_commutes]
    _ = Submodule.map ((f - algebraMap _ _ μ) ^ n) (LinearMap.range f) := LinearMap.range_comp _ _
    _ <= f.genEigenrange μ n := by rw [genEigenrange_nat]; apply LinearMap.map_le_range

中文:
定理 map_genEigenrange_le
  条件: {f : End K V} {μ : K} {n : 自然数}
  证明: calc
    Submodule.map f (f.genEigenrange μ n) =
      LinearMap.range (f * (f - algebraMap _ _ μ) ^ n) := by
        rw [genEigenrange_nat]; exact (LinearMap.range_comp _ _).symm
    _ = LinearMap.range ((f - algebraMap _ _ μ) ^ n * f) := by
        rw [Algebra.mul_sub_algebraMap_pow_commutes]
    _ = Submodule.map ((f - algebraMap _ _ μ) ^ n) (LinearMap.range f) := LinearMap.range_comp _ _
    _ <= f.genEigenrange μ n := by rw [genEigenrange_nat]; apply LinearMap.map_le_range

Depends on / 依赖: Algebra, Algebra.mul_sub_algebraMap_pow_commutes, LinearMap, LinearMap.map_le_range, LinearMap.range, LinearMap.range_comp, Submodule, Submodule.map, algebraMap, f.genEigenrange, genEigenrange, genEigenrange_nat, map_le_range, mul_sub_algebraMap_pow_commutes, range_comp
-/
theorem map_genEigenrange_le {f : End K V} {μ : K} {n : Nat} :
    Submodule.map f (f.genEigenrange μ n) <= f.genEigenrange μ n :=
  calc
    Submodule.map f (f.genEigenrange μ n) =
      LinearMap.range (f * (f - algebraMap _ _ μ) ^ n) := by
        rw [genEigenrange_nat]; exact (LinearMap.range_comp _ _).symm
    _ = LinearMap.range ((f - algebraMap _ _ μ) ^ n * f) := by
        rw [Algebra.mul_sub_algebraMap_pow_commutes]
    _ = Submodule.map ((f - algebraMap _ _ μ) ^ n) (LinearMap.range f) := LinearMap.range_comp _ _
    _ <= f.genEigenrange μ n := by rw [genEigenrange_nat]; apply LinearMap.map_le_range

/--
lemma `genEigenspace_le_smul` / 引理 `genEigenspace_le_smul`

English:
lemma genEigenspace_le_smul
  given: (f : Module.End R M) (μ t : R) (k : Nat∞)
  proof: by
  intro m hm
  simp_rw [mem_genEigenspace, ← exists_prop, LinearMap.mem_ker] at hm ⊢
  peel hm with l hlk hl
  rw [mul_smul]; rw [← smul_sub]; rw [smul_pow]; rw [LinearMap.smul_apply]; rw [hl]; rw [smul_zero]

中文:
引理 genEigenspace_le_smul
  条件: (f : 模.End R M) (μ t : R) (k : 自然数∞)
  证明: by
  intro m hm
  simp_rw [mem_genEigenspace, ← exists_prop, LinearMap.mem_ker] at hm ⊢
  peel hm with l hlk hl
  rw [mul_smul]; rw [← smul_sub]; rw [smul_pow]; rw [LinearMap.smul_apply]; rw [hl]; rw [smul_zero]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, LinearMap.smul_apply, exists_prop, mem_genEigenspace, mem_ker, mul_smul, simp_rw, smul_apply, smul_pow, smul_sub, smul_zero
-/
lemma genEigenspace_le_smul (f : Module.End R M) (μ t : R) (k : Nat∞) :
    (f.genEigenspace μ k) <= (t • f).genEigenspace (t * μ) k := by
  intro m hm
  simp_rw [mem_genEigenspace, ← exists_prop, LinearMap.mem_ker] at hm ⊢
  peel hm with l hlk hl
  rw [mul_smul]; rw [← smul_sub]; rw [smul_pow]; rw [LinearMap.smul_apply]; rw [hl]; rw [smul_zero]

/--
lemma `genEigenspace_inf_le_add` / 引理 `genEigenspace_inf_le_add`

English:
lemma genEigenspace_inf_le_add
  proof: by
  intro m hm
  simp only [Submodule.mem_inf, mem_genEigenspace, LinearMap.mem_ker] at hm ⊢
  obtain ⟨⟨l₁, hlk₁, hl₁⟩, ⟨l₂, hlk₂, hl₂⟩⟩ := hm
  use l₁ + l₂
  have : f₁ + f₂ - (μ₁ + μ₂) • 1 = (f₁ - μ₁ • 1) + (f₂ - μ₂ • 1) := by
    rw [add_smul]; exact add_sub_add_comm f₁ f₂ (μ₁ • 1) (μ₂ • 1)
  replace h : Commute (f₁ - μ₁ • 1) (f₂ - μ₂ • 1) :=
    (h.sub_right <| Algebra.commute_algebraMap_right μ₂ f₁).sub_left
      (Algebra.commute_algebraMap_left μ₁ _)
  rw [this]; rw [h.add_pow']; rw [LinearMap.coe_sum]; rw [Finset.sum_apply]
  constructor
  · simpa only [Nat.cast_add] using add_le_add hlk₁ hlk₂
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij => ?_
  suffices (((f₁ - μ₁ • 1) ^ i) * ((f₂ - μ₂ • 1) ^ j)) m = 0 by
    rw [LinearMap.smul_apply]; rw [this]; rw [smul_zero]
  rw [Finset.mem_antidiagonal] at hij
  obtain hi | hj : l₁ <= i ∨ l₂ <= j := by lia
  · rw [(h.pow_pow i j).eq, Module.End.mul_apply, Module.End.pow_map_zero_of_le hi hl₁, map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hj hl₂, map_zero]

中文:
引理 genEigenspace_inf_le_add
  证明: by
  intro m hm
  simp only [Submodule.mem_inf, mem_genEigenspace, LinearMap.mem_ker] at hm ⊢
  obtain ⟨⟨l₁, hlk₁, hl₁⟩, ⟨l₂, hlk₂, hl₂⟩⟩ := hm
  use l₁ + l₂
  have : f₁ + f₂ - (μ₁ + μ₂) • 1 = (f₁ - μ₁ • 1) + (f₂ - μ₂ • 1) := by
    rw [add_smul]; exact add_sub_add_comm f₁ f₂ (μ₁ • 1) (μ₂ • 1)
  replace h : Commute (f₁ - μ₁ • 1) (f₂ - μ₂ • 1) :=
    (h.sub_right <| Algebra.commute_algebraMap_right μ₂ f₁).sub_left
      (Algebra.commute_algebraMap_left μ₁ _)
  rw [this]; rw [h.add_pow']; rw [LinearMap.coe_sum]; rw [Finset.sum_apply]
  constructor
  · simpa only [Nat.cast_add] using add_le_add hlk₁ hlk₂
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij => ?_
  suffices (((f₁ - μ₁ • 1) ^ i) * ((f₂ - μ₂ • 1) ^ j)) m = 0 by
    rw [LinearMap.smul_apply]; rw [this]; rw [smul_zero]
  rw [Finset.mem_antidiagonal] at hij
  obtain hi | hj : l₁ <= i ∨ l₂ <= j := by lia
  · rw [(h.pow_pow i j).eq, Module.End.mul_apply, Module.End.pow_map_zero_of_le hi hl₁, map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hj hl₂, map_zero]

Depends on / 依赖: Algebra, Algebra.commute_algebraMap_left, Algebra.commute_algebraMap_right, Commute, Finset, Finset.s, LinearMap, LinearMap.coe_sum, LinearMap.mem_ker, Submodule, Submodule.mem_inf, add_pow, add_smul, add_sub_add_comm, coe_sum, commute_algebraMap_left, commute_algebraMap_right, h.add_pow, h.sub_right, mem_genEigenspace
-/
lemma genEigenspace_inf_le_add
    (f₁ f₂ : End R M) (μ₁ μ₂ : R) (k₁ k₂ : Nat∞) (h : Commute f₁ f₂) :
    (f₁.genEigenspace μ₁ k₁) ⊓ (f₂.genEigenspace μ₂ k₂) <=
    (f₁ + f₂).genEigenspace (μ₁ + μ₂) (k₁ + k₂) := by
  intro m hm
  simp only [Submodule.mem_inf, mem_genEigenspace, LinearMap.mem_ker] at hm ⊢
  obtain ⟨⟨l₁, hlk₁, hl₁⟩, ⟨l₂, hlk₂, hl₂⟩⟩ := hm
  use l₁ + l₂
  have : f₁ + f₂ - (μ₁ + μ₂) • 1 = (f₁ - μ₁ • 1) + (f₂ - μ₂ • 1) := by
    rw [add_smul]; exact add_sub_add_comm f₁ f₂ (μ₁ • 1) (μ₂ • 1)
  replace h : Commute (f₁ - μ₁ • 1) (f₂ - μ₂ • 1) :=
    (h.sub_right <| Algebra.commute_algebraMap_right μ₂ f₁).sub_left
      (Algebra.commute_algebraMap_left μ₁ _)
  rw [this]; rw [h.add_pow']; rw [LinearMap.coe_sum]; rw [Finset.sum_apply]
  constructor
  · simpa only [Nat.cast_add] using add_le_add hlk₁ hlk₂
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij => ?_
  suffices (((f₁ - μ₁ • 1) ^ i) * ((f₂ - μ₂ • 1) ^ j)) m = 0 by
    rw [LinearMap.smul_apply]; rw [this]; rw [smul_zero]
  rw [Finset.mem_antidiagonal] at hij
  obtain hi | hj : l₁ <= i ∨ l₂ <= j := by lia
  · rw [(h.pow_pow i j).eq, Module.End.mul_apply, Module.End.pow_map_zero_of_le hi hl₁, map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hj hl₂, map_zero]

/--
lemma `map_smul_of_iInf_genEigenspace_ne_bot` / 引理 `map_smul_of_iInf_genEigenspace_ne_bot`

English:
lemma map_smul_of_iInf_genEigenspace_ne_bot
  statement: [IsDomain R] [IsTorsionFree R M]
  proof: by
  by_contra contra
  let g : L -> Submodule R M := fun x => (f x).genEigenspace (μ x) k
  have : ⨅ x, g x <= g x ⊓ g (t • x) := le_inf_iff.mpr ⟨iInf_le g x, iInf_le g (t • x)⟩
refine h_ne eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (genEigenspace_le_smul (f x) (μ x) t k)
  simp only [g, map_smul]
  exact disjoint_genEigenspace (t • f x) (Ne.symm contra) k k

中文:
引理 map_smul_of_iInf_genEigenspace_ne_bot
  结论: [是整环 R] [是无挠 R M]
  证明: by
  by_contra contra
  let g : L -> Submodule R M := fun x => (f x).genEigenspace (μ x) k
  have : ⨅ x, g x <= g x ⊓ g (t • x) := le_inf_iff.mpr ⟨iInf_le g x, iInf_le g (t • x)⟩
refine h_ne eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (genEigenspace_le_smul (f x) (μ x) t k)
  simp only [g, map_smul]
  exact disjoint_genEigenspace (t • f x) (Ne.symm contra) k k

Depends on / 依赖: Disjoint, Disjoint.mono_left, Ne.symm, Submodule, contra, disjoint_genEigenspace, disjoint_iff_inf_le, disjoint_iff_inf_le.mp, eq_bot_iff, eq_bot_iff.mpr, genEigenspace, genEigenspace_le_smul, h_ne, iInf_le, le_inf_iff, le_inf_iff.mpr, le_trans, map_smul, mono_left
-/
lemma map_smul_of_iInf_genEigenspace_ne_bot [IsDomain R] [IsTorsionFree R M]
    {L F : Type*} [SMul R L] [FunLike F L (End R M)] [MulActionHomClass F R L (End R M)] (f : F)
    (μ : L -> R) (k : Nat∞) (h_ne : ⨅ x, (f x).genEigenspace (μ x) k != ⊥)
    (t : R) (x : L) :
    μ (t • x) = t • μ x := by
  by_contra contra
  let g : L -> Submodule R M := fun x => (f x).genEigenspace (μ x) k
  have : ⨅ x, g x <= g x ⊓ g (t • x) := le_inf_iff.mpr ⟨iInf_le g x, iInf_le g (t • x)⟩
refine h_ne eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (genEigenspace_le_smul (f x) (μ x) t k)
  simp only [g, map_smul]
  exact disjoint_genEigenspace (t • f x) (Ne.symm contra) k k

/--
lemma `map_add_of_iInf_genEigenspace_ne_bot_of_commute` / 引理 `map_add_of_iInf_genEigenspace_ne_bot_of_commute`

English:
lemma map_add_of_iInf_genEigenspace_ne_bot_of_commute
  statement: [IsDomain R] [IsTorsionFree R M]
  proof: by
  by_contra contra
  let g : L -> Submodule R M := fun x => (f x).genEigenspace (μ x) k
  have : ⨅ x, g x <= (g x ⊓ g y) ⊓ g (x + y) :=
    le_inf_iff.mpr ⟨le_inf_iff.mpr ⟨iInf_le g x, iInf_le g y⟩, iInf_le g (x + y)⟩
refine h_ne eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (genEigenspace_inf_le_add (f x) (f y) (μ x) (μ y) k k (h x y))
  simp only [g, map_add]
  exact disjoint_genEigenspace (f x + f y) (Ne.symm contra) _ k

中文:
引理 map_add_of_iInf_genEigenspace_ne_bot_of_commute
  结论: [是整环 R] [是无挠 R M]
  证明: by
  by_contra contra
  let g : L -> Submodule R M := fun x => (f x).genEigenspace (μ x) k
  have : ⨅ x, g x <= (g x ⊓ g y) ⊓ g (x + y) :=
    le_inf_iff.mpr ⟨le_inf_iff.mpr ⟨iInf_le g x, iInf_le g y⟩, iInf_le g (x + y)⟩
refine h_ne eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (genEigenspace_inf_le_add (f x) (f y) (μ x) (μ y) k k (h x y))
  simp only [g, map_add]
  exact disjoint_genEigenspace (f x + f y) (Ne.symm contra) _ k

Depends on / 依赖: Disjoint, Disjoint.mono_left, Ne.symm, Submodule, contra, disjoint_genEigenspace, disjoint_iff_inf_le, disjoint_iff_inf_le.mp, eq_bot_iff, eq_bot_iff.mpr, genEigenspace, genEigenspace_inf_le_add, h_ne, iInf_le, le_inf_iff, le_inf_iff.mpr, le_trans, map_add, mono_left
-/
lemma map_add_of_iInf_genEigenspace_ne_bot_of_commute [IsDomain R] [IsTorsionFree R M]
    {L F : Type*} [Add L] [FunLike F L (End R M)] [AddHomClass F L (End R M)] (f : F)
    (μ : L -> R) (k : Nat∞) (h_ne : ⨅ x, (f x).genEigenspace (μ x) k != ⊥)
    (h : forall x y, Commute (f x) (f y)) (x y : L) :
    μ (x + y) = μ x + μ y := by
  by_contra contra
  let g : L -> Submodule R M := fun x => (f x).genEigenspace (μ x) k
  have : ⨅ x, g x <= (g x ⊓ g y) ⊓ g (x + y) :=
    le_inf_iff.mpr ⟨le_inf_iff.mpr ⟨iInf_le g x, iInf_le g y⟩, iInf_le g (x + y)⟩
refine h_ne eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (genEigenspace_inf_le_add (f x) (f y) (μ x) (μ y) k k (h x y))
  simp only [g, map_add]
  exact disjoint_genEigenspace (f x + f y) (Ne.symm contra) _ k

section Arithmetic

variable {f : End R M} {μ ρ : R}

/--
lemma `hasEigenvalue_neg_iff` / 引理 `hasEigenvalue_neg_iff`

English:
lemma hasEigenvalue_neg_iff
  proof: by
  simp only [hasEigenvalue_iff, eigenspace_def]
  rw [← LinearMap.ker_neg]
  simp [add_comm]

中文:
引理 hasEigenvalue_neg_iff
  证明: by
  simp only [hasEigenvalue_iff, eigenspace_def]
  rw [← LinearMap.ker_neg]
  simp [add_comm]

Depends on / 依赖: LinearMap, LinearMap.ker_neg, add_comm, eigenspace_def, hasEigenvalue_iff, ker_neg
-/
lemma hasEigenvalue_neg_iff :
    HasEigenvalue (-f) μ ↔ HasEigenvalue f (-μ) := by
  simp only [hasEigenvalue_iff, eigenspace_def]
  rw [← LinearMap.ker_neg]
  simp [add_comm]

/--
lemma `hasEigenvalue_add_iff` / 引理 `hasEigenvalue_add_iff`

English:
lemma hasEigenvalue_add_iff
  proof: by
  have aux : f + ρ • .id - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [hasEigenvalue_iff, eigenspace_def, aux]

中文:
引理 hasEigenvalue_add_iff
  证明: by
  have aux : f + ρ • .id - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [hasEigenvalue_iff, eigenspace_def, aux]

Depends on / 依赖: eigenspace_def, hasEigenvalue_iff, module
-/
lemma hasEigenvalue_add_iff :
    HasEigenvalue (f + ρ • .id) μ ↔ HasEigenvalue f (μ - ρ) := by
  have aux : f + ρ • .id - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [hasEigenvalue_iff, eigenspace_def, aux]

/--
lemma `hasEigenvalue_add'_iff` / 引理 `hasEigenvalue_add'_iff`

English:
lemma hasEigenvalue_add'_iff
  proof: by
  have aux : ρ • .id + f - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [hasEigenvalue_iff, eigenspace_def, aux]

中文:
引理 hasEigenvalue_add'_iff
  证明: by
  have aux : ρ • .id + f - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [hasEigenvalue_iff, eigenspace_def, aux]

Depends on / 依赖: eigenspace_def, hasEigenvalue_iff, module
-/
lemma hasEigenvalue_add'_iff :
    HasEigenvalue (ρ • .id + f) μ ↔ HasEigenvalue f (μ - ρ) := by
  have aux : ρ • .id + f - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [hasEigenvalue_iff, eigenspace_def, aux]

/--
lemma `hasEigenvalue_sub_iff` / 引理 `hasEigenvalue_sub_iff`

English:
lemma hasEigenvalue_sub_iff
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [hasEigenvalue_add_iff]; rw [sub_neg_eq_add]

中文:
引理 hasEigenvalue_sub_iff
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [hasEigenvalue_add_iff]; rw [sub_neg_eq_add]

Depends on / 依赖: hasEigenvalue_add_iff, neg_smul, sub_eq_add_neg, sub_neg_eq_add
-/
lemma hasEigenvalue_sub_iff :
    HasEigenvalue (f - ρ • .id) μ ↔ HasEigenvalue f (μ + ρ) := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [hasEigenvalue_add_iff]; rw [sub_neg_eq_add]

/--
lemma `hasEigenvalue_sub'_iff` / 引理 `hasEigenvalue_sub'_iff`

English:
lemma hasEigenvalue_sub'_iff
  proof: by
  rw [sub_eq_add_neg]; rw [hasEigenvalue_add'_iff]; rw [hasEigenvalue_neg_iff]; rw [neg_sub]

中文:
引理 hasEigenvalue_sub'_iff
  证明: by
  rw [sub_eq_add_neg]; rw [hasEigenvalue_add'_iff]; rw [hasEigenvalue_neg_iff]; rw [neg_sub]

Depends on / 依赖: _iff, hasEigenvalue_add, hasEigenvalue_neg_iff, neg_sub, sub_eq_add_neg
-/
lemma hasEigenvalue_sub'_iff :
    HasEigenvalue (ρ • .id - f) μ ↔ HasEigenvalue f (ρ - μ) := by
  rw [sub_eq_add_neg]; rw [hasEigenvalue_add'_iff]; rw [hasEigenvalue_neg_iff]; rw [neg_sub]

end Arithmetic

end End

end Module
