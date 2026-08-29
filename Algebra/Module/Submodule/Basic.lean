/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Submodules of a module

This file contains basic results on submodules that require further theory to be defined.
As such it is a good target for organizing and splitting further.

## Tags

submodule, subspace, linear map
-/

@[expose] public section

open Function

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

@[gcongr, mono]
/--
theorem `toAddSubmonoid_strictMono` / 定理 `toAddSubmonoid_strictMono`

English:
theorem toAddSubmonoid_strictMono
  statement: StrictMono (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
  proof: fun _ _ => id

中文:
定理 toAddSubmonoid_strictMono
  结论: StrictMono (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
  证明: fun _ _ => id
-/
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Submodule R M -> AddSubmonoid M) :=
  fun _ _ => id

/--
theorem `toAddSubmonoid_le` / 定理 `toAddSubmonoid_le`

English:
theorem toAddSubmonoid_le
  statement: p.toAddSubmonoid <= q.toAddSubmonoid ↔ p <= q
  proof: Iff.rfl

@[gcongr, mono]

中文:
定理 toAddSubmonoid_le
  结论: p.toAddSubmonoid <= q.toAddSubmonoid ↔ p <= q
  证明: Iff.rfl

@[gcongr, mono]

Depends on / 依赖: Iff.rfl
-/
theorem toAddSubmonoid_le : p.toAddSubmonoid <= q.toAddSubmonoid ↔ p <= q :=
  Iff.rfl

@[gcongr, mono]
/--
theorem `toAddSubmonoid_mono` / 定理 `toAddSubmonoid_mono`

English:
theorem toAddSubmonoid_mono
  statement: Monotone (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
  proof: toAddSubmonoid_strictMono.monotone

@[gcongr, mono]

中文:
定理 toAddSubmonoid_mono
  结论: Monotone (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
  证明: toAddSubmonoid_strictMono.monotone

@[gcongr, mono]

Depends on / 依赖: monotone, toAddSubmonoid_strictMono, toAddSubmonoid_strictMono.monotone
-/
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Submodule R M -> AddSubmonoid M) :=
  toAddSubmonoid_strictMono.monotone

@[gcongr, mono]
/--
theorem `toSubMulAction_strictMono` / 定理 `toSubMulAction_strictMono`

English:
theorem toSubMulAction_strictMono
  proof: fun _ _ => id

@[gcongr, mono]

中文:
定理 toSubMulAction_strictMono
  证明: fun _ _ => id

@[gcongr, mono]
-/
theorem toSubMulAction_strictMono :
    StrictMono (toSubMulAction : Submodule R M -> SubMulAction R M) := fun _ _ => id

@[gcongr, mono]
/--
theorem `toSubMulAction_mono` / 定理 `toSubMulAction_mono`

English:
theorem toSubMulAction_mono
  statement: Monotone (toSubMulAction : Submodule R M -> SubMulAction R M)
  proof: toSubMulAction_strictMono.monotone

中文:
定理 toSubMulAction_mono
  结论: Monotone (toSubMulAction : Submodule R M -> SubMulAction R M)
  证明: toSubMulAction_strictMono.monotone

Depends on / 依赖: monotone, toSubMulAction_strictMono, toSubMulAction_strictMono.monotone
-/
theorem toSubMulAction_mono : Monotone (toSubMulAction : Submodule R M -> SubMulAction R M) :=
  toSubMulAction_strictMono.monotone

end Submodule

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  given: {t : Finset ι} {f : ι -> M}
  statement: (forall c in t, f c in p) -> (∑ i in t, f i) in p
  proof: sum_mem

中文:
定理 sum_mem
  条件: {t : Finset ι} {f : ι -> M}
  结论: (对任意 c in t, f c in p) -> (∑ i in t, f i) in p
  证明: sum_mem
-/
protected theorem sum_mem {t : Finset ι} {f : ι -> M} : (forall c in t, f c in p) -> (∑ i in t, f i) in p :=
  sum_mem

/--
theorem `sum_smul_mem` / 定理 `sum_smul_mem`

English:
theorem sum_smul_mem
  given: {t : Finset ι} {f : ι -> M} (r : ι -> R) (hyp : forall c in t, f c in p)
  proof: sum_mem fun i hi => smul_mem _ _ (hyp i hi)

中文:
定理 sum_smul_mem
  条件: {t : Finset ι} {f : ι -> M} (r : ι -> R) (hyp : 对任意 c in t, f c in p)
  证明: sum_mem fun i hi => smul_mem _ _ (hyp i hi)

Depends on / 依赖: smul_mem, sum_mem
-/
theorem sum_smul_mem {t : Finset ι} {f : ι -> M} (r : ι -> R) (hyp : forall c in t, f c in p) :
    (∑ i in t, r i • f i) in p :=
  sum_mem fun i hi => smul_mem _ _ (hyp i hi)

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [SMul S R] [SMul S M] [IsScalarTower S R M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M]
  body: p.toSubMulAction.isCentralScalar

中文:
实例 isCentralScalar
  签名: [SMul S R] [SMul S M] [IsScalarTower S R M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M]
  定义体: p.toSubMulAction.isCentralScalar

Depends on / 依赖: isCentralScalar, p.toSubMulAction.isCentralScalar, toSubMulAction
-/
instance isCentralScalar [SMul S R] [SMul S M] [IsScalarTower S R M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M]
    [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S p :=
  p.toSubMulAction.isCentralScalar

/--
Instance `instIsTorsionFree` / 实例 `instIsTorsionFree`

English:
instance instIsTorsionFree
  signature: [Module.IsTorsionFree R M]
  body: Subtype.coe_injective.moduleIsTorsionFree _ (by simp)

中文:
实例 instIsTorsionFree
  签名: [Module.IsTorsionFree R M]
  定义体: Subtype.coe_injective.moduleIsTorsionFree _ (by simp)

Depends on / 依赖: Subtype, Subtype.coe_injective.moduleIsTorsionFree, coe_injective, moduleIsTorsionFree
-/
instance instIsTorsionFree [Module.IsTorsionFree R M] : Module.IsTorsionFree R p :=
  Subtype.coe_injective.moduleIsTorsionFree _ (by simp)

section AddAction

/-! ### Additive actions by `Submodule`s
These instances transfer the action by an element `m : M` of an `R`-module `M` written as `m +ᵥ a`
onto the action by an element `s : S` of a submodule `S : Submodule R M` such that
`s +ᵥ a = (s : M) +ᵥ a`.
These instances work particularly well in conjunction with `AddGroup.toAddAction`, enabling
`s +ᵥ m` as an alias for `↑s + m`.
-/


variable {α β : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [VAdd
  signature: M α] : VAdd p α
  body: AddSubmonoid.instVAddSubtypeMem p

中文:
实例 [VAdd
  签名: M α] : VAdd p α
  定义体: AddSubmonoid.instVAddSubtypeMem p

Depends on / 依赖: AddSubmonoid, AddSubmonoid.instVAddSubtypeMem, instVAddSubtypeMem
-/
instance [VAdd M α] : VAdd p α :=
  AddSubmonoid.instVAddSubtypeMem p

/--
Instance `vaddCommClass` / 实例 `vaddCommClass`

English:
instance vaddCommClass
  signature: [VAdd M β] [VAdd α β] [VAddCommClass M α β]
  body: ⟨fun a => vadd_comm (a : M)⟩

中文:
实例 vaddCommClass
  签名: [VAdd M β] [VAdd α β] [VAddCommClass M α β]
  定义体: ⟨fun a => vadd_comm (a : M)⟩

Depends on / 依赖: vadd_comm
-/
instance vaddCommClass [VAdd M β] [VAdd α β] [VAddCommClass M α β] : VAddCommClass p α β :=
  ⟨fun a => vadd_comm (a : M)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [VAdd
  signature: M α] [FaithfulVAdd M α] : FaithfulVAdd p α
  body: ⟨fun h => Subtype.ext eq_of_vadd_eq_vadd h⟩

中文:
实例 [VAdd
  签名: M α] [FaithfulVAdd M α] : FaithfulVAdd p α
  定义体: ⟨fun h => Subtype.ext eq_of_vadd_eq_vadd h⟩

Depends on / 依赖: Subtype, Subtype.ext, eq_of_vadd_eq_vadd
-/
instance [VAdd M α] [FaithfulVAdd M α] : FaithfulVAdd p α :=
⟨fun h => Subtype.ext eq_of_vadd_eq_vadd h⟩

variable {p}

/--
theorem `vadd_def` / 定理 `vadd_def`

English:
theorem vadd_def
  given: [VAdd M α] (g : p) (m : α)
  statement: g +ᵥ m = (g : M) +ᵥ m
  proof: rfl

中文:
定理 vadd_def
  条件: [VAdd M α] (g : p) (m : α)
  结论: g +ᵥ m = (g : M) +ᵥ m
  证明: rfl
-/
theorem vadd_def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : M) +ᵥ m :=
  rfl

end AddAction

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M]
variable {module_M : Module R M}
variable (p p' : Submodule R M)
variable {r : R} {x y : M}


@[gcongr, mono]
/--
theorem `toAddSubgroup_strictMono` / 定理 `toAddSubgroup_strictMono`

English:
theorem toAddSubgroup_strictMono
  statement: StrictMono (toAddSubgroup : Submodule R M -> AddSubgroup M)
  proof: fun _ _ => id

@[gcongr]

中文:
定理 toAddSubgroup_strictMono
  结论: StrictMono (toAddSubgroup : Submodule R M -> AddSubgroup M)
  证明: fun _ _ => id

@[gcongr]
-/
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Submodule R M -> AddSubgroup M) :=
  fun _ _ => id

@[gcongr]
/--
theorem `toAddSubgroup_le` / 定理 `toAddSubgroup_le`

English:
theorem toAddSubgroup_le
  statement: p.toAddSubgroup <= p'.toAddSubgroup ↔ p <= p'
  proof: Iff.rfl

@[mono]

中文:
定理 toAddSubgroup_le
  结论: p.toAddSubgroup <= p'.toAddSubgroup ↔ p <= p'
  证明: Iff.rfl

@[mono]

Depends on / 依赖: Iff.rfl
-/
theorem toAddSubgroup_le : p.toAddSubgroup <= p'.toAddSubgroup ↔ p <= p' :=
  Iff.rfl

@[mono]
/--
theorem `toAddSubgroup_mono` / 定理 `toAddSubgroup_mono`

English:
theorem toAddSubgroup_mono
  statement: Monotone (toAddSubgroup : Submodule R M -> AddSubgroup M)
  proof: toAddSubgroup_strictMono.monotone

@[simp]

中文:
定理 toAddSubgroup_mono
  结论: Monotone (toAddSubgroup : Submodule R M -> AddSubgroup M)
  证明: toAddSubgroup_strictMono.monotone

@[simp]

Depends on / 依赖: monotone, toAddSubgroup_strictMono, toAddSubgroup_strictMono.monotone
-/
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Submodule R M -> AddSubgroup M) :=
  toAddSubgroup_strictMono.monotone

@[simp]
/--
theorem `toAddSubgroup_toAddSubmonoid` / 定理 `toAddSubgroup_toAddSubmonoid`

English:
theorem toAddSubgroup_toAddSubmonoid
  given: (p : Submodule R M)
  proof: rfl

中文:
定理 toAddSubgroup_toAddSubmonoid
  条件: (p : Submodule R M)
  证明: rfl
-/
theorem toAddSubgroup_toAddSubmonoid (p : Submodule R M) :
    p.toAddSubgroup.toAddSubmonoid = p.toAddSubmonoid :=
  rfl

-- See `neg_coe_set`
/--
theorem `neg_coe` / 定理 `neg_coe`

English:
theorem neg_coe
  statement: -(p : Set M) = p
  proof: Set.ext fun _ => p.neg_mem_iff

中文:
定理 neg_coe
  结论: -(p : Set M) = p
  证明: Set.ext fun _ => p.neg_mem_iff

Depends on / 依赖: Set.ext, neg_mem_iff, p.neg_mem_iff
-/
theorem neg_coe : -(p : Set M) = p :=
  Set.ext fun _ => p.neg_mem_iff

end AddCommGroup

section IsDomain

variable [Ring R] [IsDomain R]
variable [AddCommGroup M] [Module R M] {b : ι -> M}

/--
theorem `notMem_of_ortho` / 定理 `notMem_of_ortho`

English:
theorem notMem_of_ortho
  statement: {x : M} {N : Submodule R M}
  proof: by
  intro hx
  simpa using ortho (-1) x hx

中文:
定理 notMem_of_ortho
  结论: {x : M} {N : Submodule R M}
  证明: by
  intro hx
  simpa using ortho (-1) x hx
-/
theorem notMem_of_ortho {x : M} {N : Submodule R M}
    (ortho : forall (c : R), forall y in N, c • x + y = (0 : M) -> c = 0) : x ∉ N := by
  intro hx
  simpa using ortho (-1) x hx

/--
theorem `ne_zero_of_ortho` / 定理 `ne_zero_of_ortho`

English:
theorem ne_zero_of_ortho
  statement: {x : M} {N : Submodule R M}
  proof: mt (fun h => show x in N from h.symm ▸ N.zero_mem) (notMem_of_ortho ortho)

中文:
定理 ne_zero_of_ortho
  结论: {x : M} {N : Submodule R M}
  证明: mt (fun h => show x in N from h.symm ▸ N.zero_mem) (notMem_of_ortho ortho)

Depends on / 依赖: N.zero_mem, h.symm, notMem_of_ortho, zero_mem
-/
theorem ne_zero_of_ortho {x : M} {N : Submodule R M}
    (ortho : forall (c : R), forall y in N, c • x + y = (0 : M) -> c = 0) : x != 0 :=
  mt (fun h => show x in N from h.symm ▸ N.zero_mem) (notMem_of_ortho ortho)

end IsDomain

end Submodule

namespace Submodule

variable [DivisionSemiring S] [Semiring R] [AddCommMonoid M] [Module R M]
variable [SMul S R] [Module S M] [IsScalarTower S R M]
variable (p : Submodule R M) {s : S} {x y : M}

/--
theorem `smul_mem_iff` / 定理 `smul_mem_iff`

English:
theorem smul_mem_iff
  given: (s0 : s != 0)
  statement: s • x in p ↔ x in p
  proof: p.toSubMulAction.smul_mem_iff s0

中文:
定理 smul_mem_iff
  条件: (s0 : s != 0)
  结论: s • x in p ↔ x in p
  证明: p.toSubMulAction.smul_mem_iff s0

Depends on / 依赖: p.toSubMulAction.smul_mem_iff, smul_mem_iff, toSubMulAction
-/
theorem smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p :=
  p.toSubMulAction.smul_mem_iff s0

end Submodule

/--
Definition of `Subspace` / `Subspace` 的定义

English:
abbreviation Subspace
  signature: (R : Type u) (M : Type v) [DivisionRing R] [AddCommGroup M] [Module R M]
  body: Submodule R M

中文:
缩写 Subspace
  签名: (R : 类型u) (M : 类型v) [DivisionRing R] [AddCommGroup M] [Module R M]
  定义体: Submodule R M

Depends on / 依赖: Submodule
-/
abbrev Subspace (R : Type u) (M : Type v) [DivisionRing R] [AddCommGroup M] [Module R M] :=
  Submodule R M
