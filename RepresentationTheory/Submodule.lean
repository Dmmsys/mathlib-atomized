/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.RepresentationTheory.Basic

/-!
# Invariant submodules of a group representation

-/

@[expose] public section

open scoped MonoidAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

namespace Representation

/--
Definition of `invtSubmodule` / `invtSubmodule` 的定义

English:
definition invtSubmodule
  signature: : Sublattice (Submodule k V)
  body: ⨅ g, Module.End.invtSubmodule (ρ g)

中文:
定义 invtSubmodule
  签名: : Sublattice (Submodule k V)
  定义体: ⨅ g, Module.End.invtSubmodule (ρ g)

Depends on / 依赖: Module, Module.End.invtSubmodule, invtSubmodule
-/
def invtSubmodule : Sublattice (Submodule k V) :=
  ⨅ g, Module.End.invtSubmodule (ρ g)

/--
lemma `mem_invtSubmodule` / 引理 `mem_invtSubmodule`

English:
lemma mem_invtSubmodule
  given: {p : Submodule k V}
  proof: by
  rw [invtSubmodule]; rw [Sublattice.mem_iInf]

中文:
引理 mem_invtSubmodule
  条件: {p : Submodule k V}
  证明: by
  rw [invtSubmodule]; rw [Sublattice.mem_iInf]

Depends on / 依赖: Sublattice, Sublattice.mem_iInf, invtSubmodule, mem_iInf
-/
lemma mem_invtSubmodule {p : Submodule k V} :
    p in ρ.invtSubmodule ↔ forall g, p in Module.End.invtSubmodule (ρ g) := by
  rw [invtSubmodule]; rw [Sublattice.mem_iInf]

namespace invtSubmodule

/--
lemma `top_mem` / 引理 `top_mem`

English:
lemma top_mem
  statement: ⊤ in ρ.invtSubmodule
  proof: by simp [invtSubmodule]

中文:
引理 top_mem
  结论: ⊤ in ρ.invtSubmodule
  证明: by simp [invtSubmodule]
-/
@[simp] protected lemma top_mem : ⊤ in ρ.invtSubmodule := by simp [invtSubmodule]

/--
lemma `bot_mem` / 引理 `bot_mem`

English:
lemma bot_mem
  statement: ⊥ in ρ.invtSubmodule
  proof: by simp [invtSubmodule]

中文:
引理 bot_mem
  结论: ⊥ in ρ.invtSubmodule
  证明: by simp [invtSubmodule]

Depends on / 依赖: Pi.instFintype, instFintype
-/
@[simp] protected lemma bot_mem : ⊥ in ρ.invtSubmodule := by simp [invtSubmodule]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder ρ.invtSubmodule
  body: ⟨⊤, invtSubmodule.top_mem ρ⟩
  bot := ⟨⊥, invtSubmodule.bot_mem ρ⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

中文:
实例 :
  签名: BoundedOrder ρ.invtSubmodule
  定义体: ⟨⊤, invtSubmodule.top_mem ρ⟩
  bot := ⟨⊥, invtSubmodule.bot_mem ρ⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

Depends on / 依赖: invtSubmodule, invtSubmodule.top_mem, top_mem
-/
instance : BoundedOrder ρ.invtSubmodule where
  top := ⟨⊤, invtSubmodule.top_mem ρ⟩
  bot := ⟨⊥, invtSubmodule.bot_mem ρ⟩
  le_top := fun ⟨p, hp⟩ => by simp
  bot_le := fun ⟨p, hp⟩ => by simp

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: (↑(⊤ : ρ.invtSubmodule) : Submodule k V) = ⊤
  proof: rfl

中文:
引理 coe_top
  结论: (↑(⊤ : ρ.invtSubmodule) : Submodule k V) = ⊤
  证明: rfl
-/
@[simp] protected lemma coe_top : (↑(⊤ : ρ.invtSubmodule) : Submodule k V) = ⊤ := rfl

/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: (↑(⊥ : ρ.invtSubmodule) : Submodule k V) = ⊥
  proof: rfl

中文:
引理 coe_bot
  结论: (↑(⊥ : ρ.invtSubmodule) : Submodule k V) = ⊥
  证明: rfl
-/
@[simp] protected lemma coe_bot : (↑(⊥ : ρ.invtSubmodule) : Submodule k V) = ⊥ := rfl

/--
lemma `nontrivial_iff` / 引理 `nontrivial_iff`

English:
lemma nontrivial_iff
  statement: Nontrivial ρ.invtSubmodule ↔ Nontrivial V
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    infer_instance
  · refine ⟨⊥, ⊤, ?_⟩
    rw [← Subtype.coe_ne_coe]; rw [invtSubmodule.coe_top]; rw [invtSubmodule.coe_bot]
    exact bot_ne_top

中文:
引理 nontrivial_iff
  结论: Nontrivial ρ.invtSubmodule ↔ Nontrivial V
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    infer_instance
  · refine ⟨⊥, ⊤, ?_⟩
    rw [← Subtype.coe_ne_coe]; rw [invtSubmodule.coe_top]; rw [invtSubmodule.coe_bot]
    exact bot_ne_top
-/
protected lemma nontrivial_iff : Nontrivial ρ.invtSubmodule ↔ Nontrivial V := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    infer_instance
  · refine ⟨⊥, ⊤, ?_⟩
    rw [← Subtype.coe_ne_coe]; rw [invtSubmodule.coe_top]; rw [invtSubmodule.coe_bot]
    exact bot_ne_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: V] : Nontrivial ρ.invtSubmodule
  body: (invtSubmodule.nontrivial_iff ρ).mpr inferInstance

中文:
实例 [Nontrivial
  签名: V] : Nontrivial ρ.invtSubmodule
  定义体: (invtSubmodule.nontrivial_iff ρ).mpr inferInstance

Depends on / 依赖: invtSubmodule, invtSubmodule.nontrivial_iff, nontrivial_iff
-/
instance [Nontrivial V] : Nontrivial ρ.invtSubmodule :=
  (invtSubmodule.nontrivial_iff ρ).mpr inferInstance

end invtSubmodule

set_option backward.isDefEq.respectTransparency false in
/--
lemma `asAlgebraHom_mem_of_forall_mem` / 引理 `asAlgebraHom_mem_of_forall_mem`

English:
lemma asAlgebraHom_mem_of_forall_mem
  statement: (p : Submodule k V) (hp : forall g, forall v in p, ρ g v in p)
  proof: by
  apply x.induction_on <;> aesop

中文:
引理 asAlgebraHom_mem_of_forall_mem
  结论: (p : Submodule k V) (hp : 对任意 g, 对任意 v in p, ρ g v in p)
  证明: by
  apply x.induction_on <;> aesop

Depends on / 依赖: induction_on, x.induction_on
-/
lemma asAlgebraHom_mem_of_forall_mem (p : Submodule k V) (hp : forall g, forall v in p, ρ g v in p)
    (v : V) (hv : v in p) (x : k[G]) :
    ρ.asAlgebraHom x v in p := by
  apply x.induction_on <;> aesop

/--
Definition of `mapSubmodule` / `mapSubmodule` 的定义

English:
definition mapSubmodule
  signature: : ρ.invtSubmodule ≃o Submodule k[G] ρ.asModule where
  body: { toAddSubmonoid := (p : Submodule k V).toAddSubmonoid.map ρ.asModuleEquiv.symm
      smul_mem' := by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, forall_exists_index, and_imp,
          forall_apply_eq

中文:
定义 mapSubmodule
  签名: : ρ.invtSubmodule ≃o Submodule k[G] ρ.asModule where
  定义体: { toAddSubmonoid := (p : Submodule k V).toAddSubmonoid.map ρ.asModuleEquiv.symm
      smul_mem' := by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, forall_exists_index, and_imp,
          forall_apply_eq

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_map, AddSubmonoid.mem_toSubsemigroup, AddSubsemigroup, AddSubsemigroup.mem_carrier, Submodule, Submodule.mem_toAddSubmonoid, Submodule.orderIsoMapComap, and_imp, asAlgebraHom_mem_of_forall_mem, asModuleEqu, asModuleEquiv, asModuleEquiv.symm, forall_exists_index, invFun, mem_carrier, mem_invtSubmodule, mem_invtSubmodule.mp, mem_map, mem_toAddSubmonoid
-/
noncomputable def mapSubmodule : ρ.invtSubmodule ≃o Submodule k[G] ρ.asModule where
  toFun p :=
    { toAddSubmonoid := (p : Submodule k V).toAddSubmonoid.map ρ.asModuleEquiv.symm
      smul_mem' := by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        refine fun x v hv => ⟨ρ.asModuleEquiv (x • ρ.asModuleEquiv.symm v), ?_, rfl⟩
        simpa using ρ.asAlgebraHom_mem_of_forall_mem p (ρ.mem_invtSubmodule.mp p.property) v hv x }
  invFun q := ⟨(Submodule.orderIsoMapComap ρ.asModuleEquiv.symm).symm (q.restrictScalars k), by
    rw [invtSubmodule]; rw [Sublattice.mem_iInf]
    intro g v hv
    simp only [Submodule.orderIsoMapComap_symm_apply, Submodule.mem_comap] at hv ⊢
    convert! q.smul_mem (MonoidAlgebra.of k G g) hv using 1
    rw [LinearEquiv.coe_coe]; rw [← asModuleEquiv_symm_map_rho]⟩
  left_inv p := by ext; simp
  right_inv q := by ext; aesop
  map_rel_iff' {p q} :=
    ⟨fun h x hx => by
      suffices ρ.asModuleEquiv.symm x in
        (q : Submodule k V).toAddSubmonoid.map ρ.asModuleEquiv.symm by simpa using this
exact h by simpa using hx,
    fun h x hx => by aesop⟩

end Representation
