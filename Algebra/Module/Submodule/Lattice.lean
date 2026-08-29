/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The lattice structure on `Submodule`s

This file defines the lattice structure on submodules, `Submodule.CompleteLattice`, with `⊥`
defined as `{0}` and `⊓` defined as intersection of the underlying carrier.
If `p` and `q` are submodules of a module, `p ≤ q` means that `p ⊆ q`.


## Implementation notes

This structure should match the `AddSubmonoid.CompleteLattice` structure, and we should try
to unify the APIs where possible.

-/

@[expose] public section

universe v

variable {R S M : Type*}

section AddCommMonoid

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMul S R] [IsScalarTower S R M]
variable {p q : Submodule R M}

namespace Submodule

/-!
## Bottom element of a submodule
-/

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Submodule R M)
  body: ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩

中文:
实例 :
  签名: Bot (Submodule R M)
  定义体: ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩

Depends on / 依赖: AddSubmonoid, carrier, smul_mem
-/
instance : Bot (Submodule R M) :=
  ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩

/--
Instance `inhabited'` / 实例 `inhabited'`

English:
instance inhabited'
  signature: : Inhabited (Submodule R M)
  body: ⟨⊥⟩

@[simp]

中文:
实例 inhabited'
  签名: : Inhabited (Submodule R M)
  定义体: ⟨⊥⟩

@[simp]
-/
instance inhabited' : Inhabited (Submodule R M) :=
  ⟨⊥⟩

@[simp]
/--
theorem `bot_coe` / 定理 `bot_coe`

English:
theorem bot_coe
  statement: ((⊥ : Submodule R M) : Set M) = {0}
  proof: rfl

@[simp]

中文:
定理 bot_coe
  结论: ((⊥ : Submodule R M) : Set M) = {0}
  证明: rfl

@[simp]
-/
theorem bot_coe : ((⊥ : Submodule R M) : Set M) = {0} :=
  rfl

@[simp]
/--
theorem `bot_toAddSubmonoid` / 定理 `bot_toAddSubmonoid`

English:
theorem bot_toAddSubmonoid
  statement: (⊥ : Submodule R M).toAddSubmonoid = ⊥
  proof: rfl

@[simp]

中文:
定理 bot_toAddSubmonoid
  结论: (⊥ : Submodule R M).toAddSubmonoid = ⊥
  证明: rfl

@[simp]
-/
theorem bot_toAddSubmonoid : (⊥ : Submodule R M).toAddSubmonoid = ⊥ :=
  rfl

@[simp]
/--
lemma `bot_toAddSubgroup` / 引理 `bot_toAddSubgroup`

English:
lemma bot_toAddSubgroup
  given: {R M} [Ring R] [AddCommGroup M] [Module R M]
  proof: rfl

中文:
引理 bot_toAddSubgroup
  条件: {R M} [Ring R] [AddCommGroup M] [Module R M]
  证明: rfl
-/
lemma bot_toAddSubgroup {R M} [Ring R] [AddCommGroup M] [Module R M] :
    (⊥ : Submodule R M).toAddSubgroup = ⊥ := rfl

variable (R) in
@[simp]
/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : M}
  statement: x in (⊥ : Submodule R M) ↔ x = 0
  proof: Set.mem_singleton_iff

中文:
定理 mem_bot
  条件: {x : M}
  结论: x in (⊥ : Submodule R M) ↔ x = 0
  证明: Set.mem_singleton_iff

Depends on / 依赖: Set.mem_singleton_iff, mem_singleton_iff
-/
theorem mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0 :=
  Set.mem_singleton_iff

/--
lemma `mk_eq_bot` / 引理 `mk_eq_bot`

English:
lemma mk_eq_bot
  given: (carrier : AddSubmonoid M) (smul_mem')
  proof: by simp [← toAddSubmonoid_inj]

中文:
引理 mk_eq_bot
  条件: (carrier : AddSubmonoid M) (smul_mem')
  证明: by simp [← toAddSubmonoid_inj]
-/
@[simp] lemma mk_eq_bot (carrier : AddSubmonoid M) (smul_mem') :
    mk carrier smul_mem' = (⊥ : Submodule R M) ↔ carrier = ⊥ := by simp [← toAddSubmonoid_inj]

/--
Instance `uniqueBot` / 实例 `uniqueBot`

English:
instance uniqueBot
  signature: : Unique (⊥ : Submodule R M)
  body: ⟨inferInstance, fun x => Subtype.ext (mem_bot R).1 x.mem⟩

中文:
实例 uniqueBot
  签名: : Unique (⊥ : Submodule R M)
  定义体: ⟨inferInstance, fun x => Subtype.ext (mem_bot R).1 x.mem⟩

Depends on / 依赖: Subtype, Subtype.ext, mem_bot, x.mem
-/
instance uniqueBot : Unique (⊥ : Submodule R M) :=
⟨inferInstance, fun x => Subtype.ext (mem_bot R).1 x.mem⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (Submodule R M)
  body: by simp +contextual [zero_mem]

中文:
实例 :
  签名: OrderBot (Submodule R M)
  定义体: by simp +contextual [zero_mem]

Depends on / 依赖: contextual, zero_mem
-/
instance : OrderBot (Submodule R M) where
  bot_le p x := by simp +contextual [zero_mem]

/--
theorem `eq_bot_iff` / 定理 `eq_bot_iff`

English:
theorem eq_bot_iff
  given: (p : Submodule R M)
  statement: p = ⊥ ↔ forall x in p, x = (0 : M)
  proof: ⟨fun h => h.symm ▸ fun _ hx => (mem_bot R).mp hx,
    fun h => eq_bot_iff.mpr fun x hx => (mem_bot R).mpr (h x hx)⟩

@[ext high]

中文:
定理 eq_bot_iff
  条件: (p : Submodule R M)
  结论: p = ⊥ ↔ 对任意 x in p, x = (0 : M)
  证明: ⟨fun h => h.symm ▸ fun _ hx => (mem_bot R).mp hx,
    fun h => eq_bot_iff.mpr fun x hx => (mem_bot R).mpr (h x hx)⟩

@[ext high]
-/
protected theorem eq_bot_iff (p : Submodule R M) : p = ⊥ ↔ forall x in p, x = (0 : M) :=
  ⟨fun h => h.symm ▸ fun _ hx => (mem_bot R).mp hx,
    fun h => eq_bot_iff.mpr fun x hx => (mem_bot R).mpr (h x hx)⟩

@[ext high]
/--
theorem `bot_ext` / 定理 `bot_ext`

English:
theorem bot_ext
  given: (x y : (⊥ : Submodule R M))
  statement: x = y
  proof: by
  subsingleton

中文:
定理 bot_ext
  条件: (x y : (⊥ : Submodule R M))
  结论: x = y
  证明: by
  subsingleton
-/
protected theorem bot_ext (x y : (⊥ : Submodule R M)) : x = y := by
  subsingleton

/--
theorem `ne_bot_iff` / 定理 `ne_bot_iff`

English:
theorem ne_bot_iff
  given: (p : Submodule R M)
  statement: p != ⊥ ↔ exists x in p, x != (0 : M)
  proof: by
  simp only [ne_eq, p.eq_bot_iff, not_forall, exists_prop]

中文:
定理 ne_bot_iff
  条件: (p : Submodule R M)
  结论: p != ⊥ ↔ 存在 x in p, x != (0 : M)
  证明: by
  simp only [ne_eq, p.eq_bot_iff, not_forall, exists_prop]
-/
protected theorem ne_bot_iff (p : Submodule R M) : p != ⊥ ↔ exists x in p, x != (0 : M) := by
  simp only [ne_eq, p.eq_bot_iff, not_forall, exists_prop]

/--
theorem `nonzero_mem_of_bot_lt` / 定理 `nonzero_mem_of_bot_lt`

English:
theorem nonzero_mem_of_bot_lt
  given: {p : Submodule R M} (bot_lt : ⊥ < p)
  statement: exists a : p, a != 0
  proof: let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne'
  ⟨⟨b, hb₁⟩, hb₂ ∘ congr_arg Subtype.val⟩

中文:
定理 nonzero_mem_of_bot_lt
  条件: {p : Submodule R M} (bot_lt : ⊥ < p)
  结论: 存在 a : p, a != 0
  证明: let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne'
  ⟨⟨b, hb₁⟩, hb₂ ∘ congr_arg Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val, bot_lt, bot_lt.ne, congr_arg, ne_bot_iff, p.ne_bot_iff.mp
-/
theorem nonzero_mem_of_bot_lt {p : Submodule R M} (bot_lt : ⊥ < p) : exists a : p, a != 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne'
  ⟨⟨b, hb₁⟩, hb₂ ∘ congr_arg Subtype.val⟩

/--
theorem `exists_mem_ne_zero_of_ne_bot` / 定理 `exists_mem_ne_zero_of_ne_bot`

English:
theorem exists_mem_ne_zero_of_ne_bot
  given: {p : Submodule R M} (h : p != ⊥)
  statement: exists b : M, b in p ∧ b != 0
  proof: let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h
  ⟨b, hb₁, hb₂⟩

中文:
定理 exists_mem_ne_zero_of_ne_bot
  条件: {p : Submodule R M} (h : p != ⊥)
  结论: 存在 b : M, b in p ∧ b != 0
  证明: let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h
  ⟨b, hb₁, hb₂⟩

Depends on / 依赖: ne_bot_iff, p.ne_bot_iff.mp
-/
theorem exists_mem_ne_zero_of_ne_bot {p : Submodule R M} (h : p != ⊥) : exists b : M, b in p ∧ b != 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h
  ⟨b, hb₁, hb₂⟩

-- FIXME: we default PUnit to PUnit.{1} here without the explicit universe annotation
/-- The bottom submodule is linearly equivalent to punit as an `R`-module. -/
@[simps]
/--
Definition of `botEquivPUnit` / `botEquivPUnit` 的定义

English:
definition botEquivPUnit
  signature: : (⊥ : Submodule R M) ≃ₗ[R] PUnit.{v + 1} where
  body: PUnit.unit
  invFun _ := 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 botEquivPUnit
  签名: : (⊥ : Submodule R M) ≃ₗ[R] PUnit.{v + 1} where
  定义体: PUnit.unit
  invFun _ := 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: PUnit.unit
-/
def botEquivPUnit : (⊥ : Submodule R M) ≃ₗ[R] PUnit.{v + 1} where
  toFun _ := PUnit.unit
  invFun _ := 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
theorem `subsingleton_iff_eq_bot` / 定理 `subsingleton_iff_eq_bot`

English:
theorem subsingleton_iff_eq_bot
  statement: Subsingleton p ↔ p = ⊥
  proof: by
  rw [subsingleton_iff]; rw [Submodule.eq_bot_iff]
  refine ⟨fun h x hx => by simpa using h ⟨x, hx⟩ ⟨0, p.zero_mem⟩,
    fun h ⟨x, hx⟩ ⟨y, hy⟩ => by simp [h x hx, h y hy]⟩

中文:
定理 subsingleton_iff_eq_bot
  结论: Subsingleton p ↔ p = ⊥
  证明: by
  rw [subsingleton_iff]; rw [Submodule.eq_bot_iff]
  refine ⟨fun h x hx => by simpa using h ⟨x, hx⟩ ⟨0, p.zero_mem⟩,
    fun h ⟨x, hx⟩ ⟨y, hy⟩ => by simp [h x hx, h y hy]⟩

Depends on / 依赖: Submodule, Submodule.eq_bot_iff, eq_bot_iff, p.zero_mem, subsingleton_iff, zero_mem
-/
theorem subsingleton_iff_eq_bot : Subsingleton p ↔ p = ⊥ := by
  rw [subsingleton_iff]; rw [Submodule.eq_bot_iff]
  refine ⟨fun h x hx => by simpa using h ⟨x, hx⟩ ⟨0, p.zero_mem⟩,
    fun h ⟨x, hx⟩ ⟨y, hy⟩ => by simp [h x hx, h y hy]⟩

/--
theorem `eq_bot_of_subsingleton` / 定理 `eq_bot_of_subsingleton`

English:
theorem eq_bot_of_subsingleton
  given: [Subsingleton p]
  statement: p = ⊥
  proof: subsingleton_iff_eq_bot.mp inferInstance

中文:
定理 eq_bot_of_subsingleton
  条件: [Subsingleton p]
  结论: p = ⊥
  证明: subsingleton_iff_eq_bot.mp inferInstance

Depends on / 依赖: subsingleton_iff_eq_bot, subsingleton_iff_eq_bot.mp
-/
theorem eq_bot_of_subsingleton [Subsingleton p] : p = ⊥ :=
  subsingleton_iff_eq_bot.mp inferInstance

/--
theorem `nontrivial_iff_ne_bot` / 定理 `nontrivial_iff_ne_bot`

English:
theorem nontrivial_iff_ne_bot
  statement: Nontrivial p ↔ p != ⊥
  proof: by
  rw [iff_not_comm]; rw [not_nontrivial_iff_subsingleton]; rw [subsingleton_iff_eq_bot]

中文:
定理 nontrivial_iff_ne_bot
  结论: Nontrivial p ↔ p != ⊥
  证明: by
  rw [iff_not_comm]; rw [not_nontrivial_iff_subsingleton]; rw [subsingleton_iff_eq_bot]

Depends on / 依赖: iff_not_comm, not_nontrivial_iff_subsingleton, subsingleton_iff_eq_bot
-/
theorem nontrivial_iff_ne_bot : Nontrivial p ↔ p != ⊥ := by
  rw [iff_not_comm]; rw [not_nontrivial_iff_subsingleton]; rw [subsingleton_iff_eq_bot]

/-!
## Top element of a submodule
-/

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Submodule R M)
  body: ⟨{ (⊤ : AddSubmonoid M) with
      carrier := Set.univ
      smul_mem' := fun _ _ _ => trivial }⟩

@[simp]

中文:
实例 :
  签名: Top (Submodule R M)
  定义体: ⟨{ (⊤ : AddSubmonoid M) with
      carrier := Set.univ
      smul_mem' := fun _ _ _ => trivial }⟩

@[simp]

Depends on / 依赖: AddSubmonoid, Set.univ, carrier, smul_mem
-/
instance : Top (Submodule R M) :=
  ⟨{ (⊤ : AddSubmonoid M) with
      carrier := Set.univ
      smul_mem' := fun _ _ _ => trivial }⟩

@[simp]
/--
theorem `top_coe` / 定理 `top_coe`

English:
theorem top_coe
  statement: ((⊤ : Submodule R M) : Set M) = Set.univ
  proof: rfl

@[simp]

中文:
定理 top_coe
  结论: ((⊤ : Submodule R M) : Set M) = Set.univ
  证明: rfl

@[simp]
-/
theorem top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ :=
  rfl

@[simp]
/--
theorem `coe_eq_univ` / 定理 `coe_eq_univ`

English:
theorem coe_eq_univ
  statement: (p : Set M) = Set.univ ↔ p = ⊤
  proof: by
  rw [iff_comm]; rw [← SetLike.coe_set_eq]; rw [top_coe]

中文:
定理 coe_eq_univ
  结论: (p : Set M) = Set.univ ↔ p = ⊤
  证明: by
  rw [iff_comm]; rw [← SetLike.coe_set_eq]; rw [top_coe]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq, iff_comm, top_coe
-/
theorem coe_eq_univ : (p : Set M) = Set.univ ↔ p = ⊤ := by
  rw [iff_comm]; rw [← SetLike.coe_set_eq]; rw [top_coe]

/--
lemma `mem_top` / 引理 `mem_top`

English:
lemma mem_top
  given: {x : M}
  statement: x in (⊤ : Submodule R M)
  proof: trivial

@[simp]

中文:
引理 mem_top
  条件: {x : M}
  结论: x in (⊤ : Submodule R M)
  证明: trivial

@[simp]
-/
@[simp] lemma mem_top {x : M} : x in (⊤ : Submodule R M) := trivial

@[simp]
/--
theorem `top_toAddSubmonoid` / 定理 `top_toAddSubmonoid`

English:
theorem top_toAddSubmonoid
  statement: (⊤ : Submodule R M).toAddSubmonoid = ⊤
  proof: rfl

@[simp]

中文:
定理 top_toAddSubmonoid
  结论: (⊤ : Submodule R M).toAddSubmonoid = ⊤
  证明: rfl

@[simp]
-/
theorem top_toAddSubmonoid : (⊤ : Submodule R M).toAddSubmonoid = ⊤ :=
  rfl

@[simp]
/--
lemma `top_toAddSubgroup` / 引理 `top_toAddSubgroup`

English:
lemma top_toAddSubgroup
  given: {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  proof: rfl

@[simp]

中文:
引理 top_toAddSubgroup
  条件: {R M : 类型} [Ring R] [AddCommGroup M] [Module R M]
  证明: rfl

@[simp]
-/
lemma top_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] :
    (⊤ : Submodule R M).toAddSubgroup = ⊤ := rfl

@[simp]
/--
lemma `toAddSubgroup_eq_top` / 引理 `toAddSubgroup_eq_top`

English:
lemma toAddSubgroup_eq_top
  statement: {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  proof: by simp [← toAddSubgroup_inj]

中文:
引理 toAddSubgroup_eq_top
  结论: {R M : 类型} [Ring R] [AddCommGroup M] [Module R M]
  证明: by simp [← toAddSubgroup_inj]

Depends on / 依赖: toAddSubgroup_inj
-/
lemma toAddSubgroup_eq_top {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} : p.toAddSubgroup = ⊤ ↔ p = ⊤ := by simp [← toAddSubgroup_inj]

/--
lemma `mk_eq_top` / 引理 `mk_eq_top`

English:
lemma mk_eq_top
  given: (carrier : AddSubmonoid M) (smul_mem')
  proof: by simp [← toAddSubmonoid_inj]

中文:
引理 mk_eq_top
  条件: (carrier : AddSubmonoid M) (smul_mem')
  证明: by simp [← toAddSubmonoid_inj]
-/
@[simp] lemma mk_eq_top (carrier : AddSubmonoid M) (smul_mem') :
    mk carrier smul_mem' = (⊤ : Submodule R M) ↔ carrier = ⊤ := by simp [← toAddSubmonoid_inj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (Submodule R M)
  body: trivial

中文:
实例 :
  签名: OrderTop (Submodule R M)
  定义体: trivial
-/
instance : OrderTop (Submodule R M) where
  le_top _ _ _ := trivial

/--
theorem `eq_top_iff'` / 定理 `eq_top_iff'`

English:
theorem eq_top_iff'
  given: {p : Submodule R M}
  statement: p = ⊤ ↔ forall x, x in p
  proof: eq_top_iff.trans ⟨fun h _ => h trivial, fun h x _ => h x⟩

中文:
定理 eq_top_iff'
  条件: {p : Submodule R M}
  结论: p = ⊤ ↔ 对任意 x, x in p
  证明: eq_top_iff.trans ⟨fun h _ => h trivial, fun h x _ => h x⟩

Depends on / 依赖: eq_top_iff, eq_top_iff.trans
-/
theorem eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall x, x in p :=
  eq_top_iff.trans ⟨fun h _ => h trivial, fun h x _ => h x⟩

/-- The top submodule is linearly equivalent to the module.

This is the module version of `AddSubmonoid.topEquiv`. -/
@[simps]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : Submodule R M) ≃ₗ[R] M where
  body: x
  invFun x := ⟨x, mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 topEquiv
  签名: : (⊤ : Submodule R M) ≃ₗ[R] M where
  定义体: x
  invFun x := ⟨x, mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M where
  toFun x := x
  invFun x := ⟨x, mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Submodule R M)
  body: ⟨fun S =>
    { carrier := ⋂ s in S, (s : Set M)
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩

中文:
实例 :
  签名: InfSet (Submodule R M)
  定义体: ⟨fun S =>
    { carrier := ⋂ s in S, (s : Set M)
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩

Depends on / 依赖: add_mem, carrier, contextual, smul_mem, zero_mem
-/
instance : InfSet (Submodule R M) :=
  ⟨fun S =>
    { carrier := ⋂ s in S, (s : Set M)
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩

/--
theorem `isGLB_sInf` / 定理 `isGLB_sInf`

English:
theorem isGLB_sInf
  given: {S : Set (Submodule R M)}
  statement: IsGLB S (sInf S)
  proof: .of_image SetLike.coe_subset_coe isGLB_biInf

中文:
定理 isGLB_sInf
  条件: {S : Set (Submodule R M)}
  结论: IsGLB S (sInf S)
  证明: .of_image SetLike.coe_subset_coe isGLB_biInf
-/
protected theorem isGLB_sInf {S : Set (Submodule R M)} : IsGLB S (sInf S) :=
  .of_image SetLike.coe_subset_coe isGLB_biInf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Submodule R M)
  body: ⟨fun p q =>
    { carrier := p inter q
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩

中文:
实例 :
  签名: Min (Submodule R M)
  定义体: ⟨fun p q =>
    { carrier := p inter q
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩

Depends on / 依赖: add_mem, carrier, contextual, smul_mem, zero_mem
-/
instance : Min (Submodule R M) :=
  ⟨fun p q =>
    { carrier := p inter q
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩

/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (Submodule R M) where
  body: sInf { x | a <= x ∧ b <= x }
  le_sup_left _ _ := Set.subset_iInter₂ fun _ ⟨h, _⟩ => h
  le_sup_right _ _ := Set.subset_iInter₂ fun _ ⟨_, h⟩ => h
  sup_le _ _ _ h₁ h₂ := Set.biInter_subset_of_mem ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf _ _ _ := Set.subset_inter
  inf_le_left _ _ := Set.inter_subset_left


中文:
实例 completeLattice
  签名: : CompleteLattice (Submodule R M) where
  定义体: sInf { x | a <= x ∧ b <= x }
  le_sup_left _ _ := Set.subset_iInter₂ fun _ ⟨h, _⟩ => h
  le_sup_right _ _ := Set.subset_iInter₂ fun _ ⟨_, h⟩ => h
  sup_le _ _ _ h₁ h₂ := Set.biInter_subset_of_mem ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf _ _ _ := Set.subset_inter
  inf_le_left _ _ := Set.inter_subset_left

-/
instance completeLattice : CompleteLattice (Submodule R M) where
  sup a b := sInf { x | a <= x ∧ b <= x }
  le_sup_left _ _ := Set.subset_iInter₂ fun _ ⟨h, _⟩ => h
  le_sup_right _ _ := Set.subset_iInter₂ fun _ ⟨_, h⟩ => h
  sup_le _ _ _ h₁ h₂ := Set.biInter_subset_of_mem ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf _ _ _ := Set.subset_inter
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  sSup S := sInf {sm | forall s in S, s <= sm}
  isLUB_sSup _ := isGLB_upperBounds.mp Submodule.isGLB_sInf
  isGLB_sInf _ := Submodule.isGLB_sInf

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  statement: ↑(p ⊓ q) = (p inter q : Set M)
  proof: rfl

@[simp]

中文:
定理 coe_inf
  结论: ↑(p ⊓ q) = (p inter q : Set M)
  证明: rfl

@[simp]
-/
theorem coe_inf : ↑(p ⊓ q) = (p inter q : Set M) :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p q : Submodule R M} {x : M}
  statement: x in p ⊓ q ↔ x in p ∧ x in q
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_inf
  条件: {p q : Submodule R M} {x : M}
  结论: x in p ⊓ q ↔ x in p ∧ x in q
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ x in p ∧ x in q :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (P : Set (Submodule R M))
  statement: (↑(sInf P) : Set M) = ⋂ p in P, ↑p
  proof: rfl

@[simp]

中文:
定理 coe_sInf
  条件: (P : Set (Submodule R M))
  结论: (↑(sInf P) : Set M) = ⋂ p in P, ↑p
  证明: rfl

@[simp]
-/
theorem coe_sInf (P : Set (Submodule R M)) : (↑(sInf P) : Set M) = ⋂ p in P, ↑p :=
  rfl

@[simp]
/--
theorem `coe_finsetInf` / 定理 `coe_finsetInf`

English:
theorem coe_finsetInf
  given: {ι} (s : Finset ι) (p : ι -> Submodule R M)
  proof: by
  let := Classical.decEq ι
  refine s.induction_on ?_ fun i s _ ih => ?_
  · simp
  · rw [Finset.inf_insert, coe_inf, ih]
    simp

@[simp, norm_cast]

中文:
定理 coe_finsetInf
  条件: {ι} (s : Finset ι) (p : ι -> Submodule R M)
  证明: by
  let := Classical.decEq ι
  refine s.induction_on ?_ fun i s _ ih => ?_
  · simp
  · rw [Finset.inf_insert, coe_inf, ih]
    simp

@[simp, norm_cast]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.inf_insert, coe_inf, induction_on, inf_insert, s.induction_on
-/
theorem coe_finsetInf {ι} (s : Finset ι) (p : ι -> Submodule R M) :
    (↑(s.inf p) : Set M) = ⋂ i in s, ↑(p i) := by
  let := Classical.decEq ι
  refine s.induction_on ?_ fun i s _ ih => ?_
  · simp
  · rw [Finset.inf_insert, coe_inf, ih]
    simp

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι} (p : ι -> Submodule R M)
  statement: (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i)
  proof: by
  rw [iInf]; rw [coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[simp]

中文:
定理 coe_iInf
  条件: {ι} (p : ι -> Submodule R M)
  结论: (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i)
  证明: by
  rw [iInf]; rw [coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[simp]

Depends on / 依赖: Set.iInter_exists, Set.iInter_iInter_eq, Set.mem_range, coe_sInf, iInter_exists, iInter_iInter_eq, mem_range
-/
theorem coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf]; rw [coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (Submodule R M)} {x : M}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: Set.mem_iInter₂

@[simp]

中文:
定理 mem_sInf
  条件: {S : Set (Submodule R M)} {x : M}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: Set.mem_iInter₂

@[simp]

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {S : Set (Submodule R M)} {x : M} : x in sInf S ↔ forall p in S, x in p :=
  Set.mem_iInter₂

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι} (p : ι -> Submodule R M) {x}
  statement: x in ⨅ i, p i ↔ forall i, x in p i
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_iInf]; rw [Set.mem_iInter]; rfl

@[simp]

中文:
定理 mem_iInf
  条件: {ι} (p : ι -> Submodule R M) {x}
  结论: x in ⨅ i, p i ↔ 对任意 i, x in p i
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_iInf]; rw [Set.mem_iInter]; rfl

@[simp]

Depends on / 依赖: Set.mem_iInter, SetLike, SetLike.mem_coe, coe_iInf, mem_coe, mem_iInter
-/
theorem mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i, p i ↔ forall i, x in p i := by
  rw [← SetLike.mem_coe]; rw [coe_iInf]; rw [Set.mem_iInter]; rfl

@[simp]
/--
theorem `mem_finsetInf` / 定理 `mem_finsetInf`

English:
theorem mem_finsetInf
  given: {ι} {s : Finset ι} {p : ι -> Submodule R M} {x : M}
  proof: by
  simp only [← SetLike.mem_coe, coe_finsetInf, Set.mem_iInter]

中文:
定理 mem_finsetInf
  条件: {ι} {s : Finset ι} {p : ι -> Submodule R M} {x : M}
  证明: by
  simp only [← SetLike.mem_coe, coe_finsetInf, Set.mem_iInter]

Depends on / 依赖: Set.mem_iInter, SetLike, SetLike.mem_coe, coe_finsetInf, mem_coe, mem_iInter
-/
theorem mem_finsetInf {ι} {s : Finset ι} {p : ι -> Submodule R M} {x : M} :
    x in s.inf p ↔ forall i in s, x in p i := by
  simp only [← SetLike.mem_coe, coe_finsetInf, Set.mem_iInter]

/--
lemma `inf_iInf` / 引理 `inf_iInf`

English:
lemma inf_iInf
  given: {ι : Sort*} [Nonempty ι] {p : ι -> Submodule R M} (q : Submodule R M)
  proof: SetLike.coe_injective by simpa only [coe_inf, coe_iInf] using Set.inter_iInter _ _

中文:
引理 inf_iInf
  条件: {ι : Sort*} [Nonempty ι] {p : ι -> Submodule R M} (q : Submodule R M)
  证明: SetLike.coe_injective by simpa only [coe_inf, coe_iInf] using Set.inter_iInter _ _

Depends on / 依赖: Set.inter_iInter, SetLike, SetLike.coe_injective, coe_iInf, coe_inf, coe_injective, inter_iInter
-/
lemma inf_iInf {ι : Sort*} [Nonempty ι] {p : ι -> Submodule R M} (q : Submodule R M) :
    q ⊓ ⨅ i, p i = ⨅ i, q ⊓ p i :=
SetLike.coe_injective by simpa only [coe_inf, coe_iInf] using Set.inter_iInter _ _

/--
theorem `mem_sup_left` / 定理 `mem_sup_left`

English:
theorem mem_sup_left
  given: {S T : Submodule R M}
  statement: forall {x : M}, x in S -> x in S ⊔ T
  proof: by
  have : S <= S ⊔ T := le_sup_left
  rw [LE.le] at this
  exact this

中文:
定理 mem_sup_left
  条件: {S T : Submodule R M}
  结论: 对任意 {x : M}, x in S -> x in S ⊔ T
  证明: by
  have : S <= S ⊔ T := le_sup_left
  rw [LE.le] at this
  exact this

Depends on / 依赖: LE.le, le_sup_left
-/
theorem mem_sup_left {S T : Submodule R M} : forall {x : M}, x in S -> x in S ⊔ T := by
  have : S <= S ⊔ T := le_sup_left
  rw [LE.le] at this
  exact this

/--
theorem `mem_sup_right` / 定理 `mem_sup_right`

English:
theorem mem_sup_right
  given: {S T : Submodule R M}
  statement: forall {x : M}, x in T -> x in S ⊔ T
  proof: by
  have : T <= S ⊔ T := le_sup_right
  rw [LE.le] at this
  exact this

中文:
定理 mem_sup_right
  条件: {S T : Submodule R M}
  结论: 对任意 {x : M}, x in T -> x in S ⊔ T
  证明: by
  have : T <= S ⊔ T := le_sup_right
  rw [LE.le] at this
  exact this

Depends on / 依赖: LE.le, le_sup_right
-/
theorem mem_sup_right {S T : Submodule R M} : forall {x : M}, x in T -> x in S ⊔ T := by
  have : T <= S ⊔ T := le_sup_right
  rw [LE.le] at this
  exact this

/--
theorem `add_mem_sup` / 定理 `add_mem_sup`

English:
theorem add_mem_sup
  given: {S T : Submodule R M} {s t : M} (hs : s in S) (ht : t in T)
  statement: s + t in S ⊔ T
  proof: add_mem (mem_sup_left hs) (mem_sup_right ht)

中文:
定理 add_mem_sup
  条件: {S T : Submodule R M} {s t : M} (hs : s in S) (ht : t in T)
  结论: s + t in S ⊔ T
  证明: add_mem (mem_sup_left hs) (mem_sup_right ht)

Depends on / 依赖: add_mem, mem_sup_left, mem_sup_right
-/
theorem add_mem_sup {S T : Submodule R M} {s t : M} (hs : s in S) (ht : t in T) : s + t in S ⊔ T :=
  add_mem (mem_sup_left hs) (mem_sup_right ht)

/--
theorem `sub_mem_sup` / 定理 `sub_mem_sup`

English:
theorem sub_mem_sup
  statement: {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M']
  proof: by
  rw [sub_eq_add_neg]
  exact add_mem_sup hs (neg_mem ht)

中文:
定理 sub_mem_sup
  结论: {R' M' : 类型} [Ring R'] [AddCommGroup M'] [Module R' M']
  证明: by
  rw [sub_eq_add_neg]
  exact add_mem_sup hs (neg_mem ht)

Depends on / 依赖: add_mem_sup, neg_mem, sub_eq_add_neg
-/
theorem sub_mem_sup {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M']
    {S T : Submodule R' M'} {s t : M'} (hs : s in S) (ht : t in T) : s - t in S ⊔ T := by
  rw [sub_eq_add_neg]
  exact add_mem_sup hs (neg_mem ht)

/--
theorem `mem_iSup_of_mem` / 定理 `mem_iSup_of_mem`

English:
theorem mem_iSup_of_mem
  given: {ι : Sort*} {b : M} {p : ι -> Submodule R M} (i : ι) (h : b in p i)
  proof: (le_iSup p i) h

中文:
定理 mem_iSup_of_mem
  条件: {ι : Sort*} {b : M} {p : ι -> Submodule R M} (i : ι) (h : b in p i)
  证明: (le_iSup p i) h

Depends on / 依赖: le_iSup
-/
theorem mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι -> Submodule R M} (i : ι) (h : b in p i) :
    b in ⨆ i, p i :=
  (le_iSup p i) h

/--
theorem `sum_mem_iSup` / 定理 `sum_mem_iSup`

English:
theorem sum_mem_iSup
  statement: {ι : Type*} [Fintype ι] {f : ι -> M} {p : ι -> Submodule R M}
  proof: sum_mem fun i _ => mem_iSup_of_mem i (h i)

中文:
定理 sum_mem_iSup
  结论: {ι : 类型} [Fintype ι] {f : ι -> M} {p : ι -> Submodule R M}
  证明: sum_mem fun i _ => mem_iSup_of_mem i (h i)

Depends on / 依赖: mem_iSup_of_mem, sum_mem
-/
theorem sum_mem_iSup {ι : Type*} [Fintype ι] {f : ι -> M} {p : ι -> Submodule R M}
    (h : forall i, f i in p i) : (∑ i, f i) in ⨆ i, p i :=
  sum_mem fun i _ => mem_iSup_of_mem i (h i)

/--
theorem `sum_mem_biSup` / 定理 `sum_mem_biSup`

English:
theorem sum_mem_biSup
  statement: {ι : Type*} {s : Finset ι} {f : ι -> M} {p : ι -> Submodule R M}
  proof: sum_mem fun i hi => mem_iSup_of_mem i mem_iSup_of_mem hi (h i hi)

中文:
定理 sum_mem_biSup
  结论: {ι : 类型} {s : Finset ι} {f : ι -> M} {p : ι -> Submodule R M}
  证明: sum_mem fun i hi => mem_iSup_of_mem i mem_iSup_of_mem hi (h i hi)

Depends on / 依赖: mem_iSup_of_mem, sum_mem
-/
theorem sum_mem_biSup {ι : Type*} {s : Finset ι} {f : ι -> M} {p : ι -> Submodule R M}
    (h : forall i in s, f i in p i) : (∑ i in s, f i) in ⨆ i in s, p i :=
sum_mem fun i hi => mem_iSup_of_mem i mem_iSup_of_mem hi (h i hi)



/--
theorem `mem_sSup_of_mem` / 定理 `mem_sSup_of_mem`

English:
theorem mem_sSup_of_mem
  given: {S : Set (Submodule R M)} {s : Submodule R M} (hs : s in S)
  proof: by
  have := le_sSup hs
  rw [LE.le] at this
  exact this

@[simp]

中文:
定理 mem_sSup_of_mem
  条件: {S : Set (Submodule R M)} {s : Submodule R M} (hs : s in S)
  证明: by
  have := le_sSup hs
  rw [LE.le] at this
  exact this

@[simp]

Depends on / 依赖: LE.le, le_sSup
-/
theorem mem_sSup_of_mem {S : Set (Submodule R M)} {s : Submodule R M} (hs : s in S) :
    forall {x : M}, x in s -> x in sSup S := by
  have := le_sSup hs
  rw [LE.le] at this
  exact this

@[simp]
/--
theorem `toAddSubmonoid_sSup` / 定理 `toAddSubmonoid_sSup`

English:
theorem toAddSubmonoid_sSup
  given: (s : Set (Submodule R M))
  proof: by
  let p : Submodule R M :=
    { toAddSubmonoid := sSup (toAddSubmonoid '' s)
      smul_mem' := fun t {m} h => by
        simp_rw [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, sSup_eq_iSup'] at h ⊢
        induction h using AddSubmonoid.iSup_induction' with
        | mem p x hx 

中文:
定理 toAddSubmonoid_sSup
  条件: (s : Set (Submodule R M))
  证明: by
  let p : Submodule R M :=
    { toAddSubmonoid := sSup (toAddSubmonoid '' s)
      smul_mem' := fun t {m} h => by
        simp_rw [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, sSup_eq_iSup'] at h ⊢
        induction h using AddSubmonoid.iSup_induction' with
        | mem p x hx 

Depends on / 依赖: AddSubmonoid, AddSubmonoid.iSup_induction, AddSubmonoid.mem_toSubsemigroup, AddSubsemigroup, AddSubsemigroup.mem_carrier, Submodule, Subtype, Subtype.range_coe_subtype, iSup_induction, le_sSup, mem_carrier, mem_toSubsemigroup, p.toAddSubmonoid, range_coe_subtype, sSup_eq_iSup, simp_rw, smul_mem, toAddSubmonoid
-/
theorem toAddSubmonoid_sSup (s : Set (Submodule R M)) :
    (sSup s).toAddSubmonoid = sSup (toAddSubmonoid '' s) := by
  let p : Submodule R M :=
    { toAddSubmonoid := sSup (toAddSubmonoid '' s)
      smul_mem' := fun t {m} h => by
        simp_rw [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, sSup_eq_iSup'] at h ⊢
        induction h using AddSubmonoid.iSup_induction' with
        | mem p x hx =>
          obtain ⟨-, ⟨p : Submodule R M, hp : p in s, rfl⟩⟩ := p
          suffices p.toAddSubmonoid <= ⨆ q : toAddSubmonoid '' s, (q : AddSubmonoid M) by
            exact this (smul_mem p t hx)
          apply le_sSup
          rw [Subtype.range_coe_subtype]
          exact ⟨p, hp, rfl⟩
        | zero => simpa only [smul_zero] using zero_mem _
        | add _ _ _ _ mx my => revert mx my; simp_rw [smul_add]; exact add_mem }
  refine le_antisymm (?_ : sSup s <= p) ?_
· exact sSup_le fun q hq => le_sSup Set.mem_image_of_mem toAddSubmonoid hq
  · exact sSup_le fun _ ⟨q, hq, hq'⟩ => hq'.symm ▸ le_sSup hq

variable (R)

@[simp]
/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton (Submodule R M) ↔ Subsingleton M
  proof: have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top]; rw [← subsingleton_iff_bot_eq_top]; rw [← toAddSubmonoid_inj]; rw [bot_toAddSubmonoid]; rw [top_toAddSubmonoid]
  h.trans AddSubmonoid.subsingleton_iff

@[simp]

中文:
定理 subsingleton_iff
  结论: Subsingleton (Submodule R M) ↔ Subsingleton M
  证明: have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top]; rw [← subsingleton_iff_bot_eq_top]; rw [← toAddSubmonoid_inj]; rw [bot_toAddSubmonoid]; rw [top_toAddSubmonoid]
  h.trans AddSubmonoid.subsingleton_iff

@[simp]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.subsingleton_iff, Submodule, Subsingleton, bot_toAddSubmonoid, h.trans, subsingleton_iff, subsingleton_iff_bot_eq_top, toAddSubmonoid_inj, top_toAddSubmonoid
-/
theorem subsingleton_iff : Subsingleton (Submodule R M) ↔ Subsingleton M :=
  have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top]; rw [← subsingleton_iff_bot_eq_top]; rw [← toAddSubmonoid_inj]; rw [bot_toAddSubmonoid]; rw [top_toAddSubmonoid]
  h.trans AddSubmonoid.subsingleton_iff

@[simp]
/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  statement: Nontrivial (Submodule R M) ↔ Nontrivial M
  proof: not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R).trans
      not_nontrivial_iff_subsingleton.symm)

中文:
定理 nontrivial_iff
  结论: Nontrivial (Submodule R M) ↔ Nontrivial M
  证明: not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R).trans
      not_nontrivial_iff_subsingleton.symm)

Depends on / 依赖: not_iff_not, not_iff_not.mp, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton.symm, not_nontrivial_iff_subsingleton.trans, subsingleton_iff
-/
theorem nontrivial_iff : Nontrivial (Submodule R M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R).trans
      not_nontrivial_iff_subsingleton.symm)

variable {R}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : Unique (Submodule R M)
  body: ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ ((subsingleton_iff R).mpr ‹_›) a _⟩

中文:
实例 [Subsingleton
  签名: M] : Unique (Submodule R M)
  定义体: ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ ((subsingleton_iff R).mpr ‹_›) a _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, subsingleton_iff
-/
instance [Subsingleton M] : Unique (Submodule R M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ ((subsingleton_iff R).mpr ‹_›) a _⟩

/--
Instance `unique'` / 实例 `unique'`

English:
instance unique'
  signature: [Subsingleton R]
  body: by
  haveI := Module.subsingleton R M; infer_instance

中文:
实例 unique'
  签名: [Subsingleton R]
  定义体: by
  haveI := Module.subsingleton R M; infer_instance

Depends on / 依赖: Module, Module.subsingleton, infer_instance, subsingleton
-/
instance unique' [Subsingleton R] : Unique (Submodule R M) := by
  haveI := Module.subsingleton R M; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nontrivial (Submodule R M)
  body: (nontrivial_iff R).mpr ‹_›

中文:
实例 [Nontrivial
  签名: M] : Nontrivial (Submodule R M)
  定义体: (nontrivial_iff R).mpr ‹_›

Depends on / 依赖: nontrivial_iff
-/
instance [Nontrivial M] : Nontrivial (Submodule R M) :=
  (nontrivial_iff R).mpr ‹_›


/--
theorem `disjoint_def` / 定理 `disjoint_def`

English:
theorem disjoint_def
  given: {p p' : Submodule R M}
  statement: Disjoint p p' ↔ forall x in p, x in p' -> x = (0 : M)
  proof: disjoint_iff_inf_le.trans show (forall x, x in p ∧ x in p' -> x in ({0} : Set M)) ↔ _ by simp

中文:
定理 disjoint_def
  条件: {p p' : Submodule R M}
  结论: Disjoint p p' ↔ 对任意 x in p, x in p' -> x = (0 : M)
  证明: disjoint_iff_inf_le.trans show (forall x, x in p ∧ x in p' -> x in ({0} : Set M)) ↔ _ by simp

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.trans
-/
theorem disjoint_def {p p' : Submodule R M} : Disjoint p p' ↔ forall x in p, x in p' -> x = (0 : M) :=
disjoint_iff_inf_le.trans show (forall x, x in p ∧ x in p' -> x in ({0} : Set M)) ↔ _ by simp

/--
theorem `disjoint_def'` / 定理 `disjoint_def'`

English:
theorem disjoint_def'
  given: {p p' : Submodule R M}
  proof: disjoint_def.trans
⟨fun h x hx _ hy hxy => h x hx hxy.symm ▸ hy, fun h x hx hx' => h _ hx x hx' rfl⟩

中文:
定理 disjoint_def'
  条件: {p p' : Submodule R M}
  证明: disjoint_def.trans
⟨fun h x hx _ hy hxy => h x hx hxy.symm ▸ hy, fun h x hx hx' => h _ hx x hx' rfl⟩

Depends on / 依赖: disjoint_def, disjoint_def.trans, hxy.symm
-/
theorem disjoint_def' {p p' : Submodule R M} :
    Disjoint p p' ↔ forall x in p, forall y in p', x = y -> x = (0 : M) :=
  disjoint_def.trans
⟨fun h x hx _ hy hxy => h x hx hxy.symm ▸ hy, fun h x hx hx' => h _ hx x hx' rfl⟩

/--
theorem `eq_zero_of_coe_mem_of_disjoint` / 定理 `eq_zero_of_coe_mem_of_disjoint`

English:
theorem eq_zero_of_coe_mem_of_disjoint
  given: (hpq : Disjoint p q) {a : p} (ha : (a : M) in q)
  statement: a = 0
  proof: mod_cast disjoint_def.mp hpq a (coe_mem a) ha

中文:
定理 eq_zero_of_coe_mem_of_disjoint
  条件: (hpq : Disjoint p q) {a : p} (ha : (a : M) in q)
  结论: a = 0
  证明: mod_cast disjoint_def.mp hpq a (coe_mem a) ha

Depends on / 依赖: coe_mem, disjoint_def, disjoint_def.mp, mod_cast
-/
theorem eq_zero_of_coe_mem_of_disjoint (hpq : Disjoint p q) {a : p} (ha : (a : M) in q) : a = 0 :=
  mod_cast disjoint_def.mp hpq a (coe_mem a) ha

/--
theorem `mem_right_iff_eq_zero_of_disjoint` / 定理 `mem_right_iff_eq_zero_of_disjoint`

English:
theorem mem_right_iff_eq_zero_of_disjoint
  given: {p p' : Submodule R M} (h : Disjoint p p') {x : p}
  proof: ⟨fun hx => coe_eq_zero.1 disjoint_def.1 h x x.2 hx, fun h => h.symm ▸ p'.zero_mem⟩

中文:
定理 mem_right_iff_eq_zero_of_disjoint
  条件: {p p' : Submodule R M} (h : Disjoint p p') {x : p}
  证明: ⟨fun hx => coe_eq_zero.1 disjoint_def.1 h x x.2 hx, fun h => h.symm ▸ p'.zero_mem⟩

Depends on / 依赖: coe_eq_zero, disjoint_def, h.symm, zero_mem
-/
theorem mem_right_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p} :
    (x : M) in p' ↔ x = 0 :=
⟨fun hx => coe_eq_zero.1 disjoint_def.1 h x x.2 hx, fun h => h.symm ▸ p'.zero_mem⟩

/--
theorem `mem_left_iff_eq_zero_of_disjoint` / 定理 `mem_left_iff_eq_zero_of_disjoint`

English:
theorem mem_left_iff_eq_zero_of_disjoint
  given: {p p' : Submodule R M} (h : Disjoint p p') {x : p'}
  proof: ⟨fun hx => coe_eq_zero.1 disjoint_def.1 h x hx x.2, fun h => h.symm ▸ p.zero_mem⟩

中文:
定理 mem_left_iff_eq_zero_of_disjoint
  条件: {p p' : Submodule R M} (h : Disjoint p p') {x : p'}
  证明: ⟨fun hx => coe_eq_zero.1 disjoint_def.1 h x hx x.2, fun h => h.symm ▸ p.zero_mem⟩

Depends on / 依赖: coe_eq_zero, disjoint_def, h.symm, p.zero_mem, zero_mem
-/
theorem mem_left_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p'} :
    (x : M) in p ↔ x = 0 :=
⟨fun hx => coe_eq_zero.1 disjoint_def.1 h x hx x.2, fun h => h.symm ▸ p.zero_mem⟩

/--
theorem `disjoint_iff_add_eq_zero` / 定理 `disjoint_iff_add_eq_zero`

English:
theorem disjoint_iff_add_eq_zero
  statement: {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]
  proof: by
  simp only [← Submodule.mem_toAddSubgroup, ← AddSubgroup.disjoint_iff_add_eq_zero]
  aesop (add norm [disjoint_def', AddSubgroup.disjoint_def'])

中文:
定理 disjoint_iff_add_eq_zero
  结论: {M R : 类型} [Ring R] [AddCommGroup M] [Module R M]
  证明: by
  simp only [← Submodule.mem_toAddSubgroup, ← AddSubgroup.disjoint_iff_add_eq_zero]
  aesop (add norm [disjoint_def', AddSubgroup.disjoint_def'])

Depends on / 依赖: AddSubgroup, AddSubgroup.disjoint_def, AddSubgroup.disjoint_iff_add_eq_zero, Submodule, Submodule.mem_toAddSubgroup, disjoint_def, disjoint_iff_add_eq_zero, mem_toAddSubgroup
-/
theorem disjoint_iff_add_eq_zero {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N₁ N₂ : Submodule R M} :
    Disjoint N₁ N₂ ↔ forall {x y : M}, x in N₁ -> y in N₂ -> x + y = 0 -> x = 0 ∧ y = 0 := by
  simp only [← Submodule.mem_toAddSubgroup, ← AddSubgroup.disjoint_iff_add_eq_zero]
  aesop (add norm [disjoint_def', AddSubgroup.disjoint_def'])

end Submodule

section NatSubmodule

/-!
## ℕ-submodules
-/

/--
Definition of `AddSubmonoid.toNatSubmodule` / `AddSubmonoid.toNatSubmodule` 的定义

English:
definition AddSubmonoid.toNatSubmodule
  signature: : AddSubmonoid M ≃o Submodule Nat M where
  body: { S with smul_mem' := fun r s hs => show r • s in S from nsmul_mem hs _ }
  invFun := Submodule.toAddSubmonoid
  map_rel_iff' := Iff.rfl

@[simp]

中文:
定义 AddSubmonoid.toNatSubmodule
  签名: : AddSubmonoid M ≃o Submodule 自然数 M where
  定义体: { S with smul_mem' := fun r s hs => show r • s in S from nsmul_mem hs _ }
  invFun := Submodule.toAddSubmonoid
  map_rel_iff' := Iff.rfl

@[simp]

Depends on / 依赖: nsmul_mem, smul_mem
-/
def AddSubmonoid.toNatSubmodule : AddSubmonoid M ≃o Submodule Nat M where
  toFun S := { S with smul_mem' := fun r s hs => show r • s in S from nsmul_mem hs _ }
  invFun := Submodule.toAddSubmonoid
  map_rel_iff' := Iff.rfl

@[simp]
/--
theorem `AddSubmonoid.toNatSubmodule_symm` / 定理 `AddSubmonoid.toNatSubmodule_symm`

English:
theorem AddSubmonoid.toNatSubmodule_symm
  proof: rfl

@[simp]

中文:
定理 AddSubmonoid.toNatSubmodule_symm
  证明: rfl

@[simp]
-/
theorem AddSubmonoid.toNatSubmodule_symm :
    ⇑(AddSubmonoid.toNatSubmodule.symm : _ ≃o AddSubmonoid M) = Submodule.toAddSubmonoid :=
  rfl

@[simp]
/--
theorem `AddSubmonoid.coe_toNatSubmodule` / 定理 `AddSubmonoid.coe_toNatSubmodule`

English:
theorem AddSubmonoid.coe_toNatSubmodule
  given: (S : AddSubmonoid M)
  proof: rfl

@[simp]

中文:
定理 AddSubmonoid.coe_toNatSubmodule
  条件: (S : AddSubmonoid M)
  证明: rfl

@[simp]
-/
theorem AddSubmonoid.coe_toNatSubmodule (S : AddSubmonoid M) :
    (S.toNatSubmodule : Set M) = S :=
  rfl

@[simp]
/--
theorem `AddSubmonoid.toNatSubmodule_toAddSubmonoid` / 定理 `AddSubmonoid.toNatSubmodule_toAddSubmonoid`

English:
theorem AddSubmonoid.toNatSubmodule_toAddSubmonoid
  given: (S : AddSubmonoid M)
  proof: AddSubmonoid.toNatSubmodule.symm_apply_apply S

@[simp]

中文:
定理 AddSubmonoid.toNatSubmodule_toAddSubmonoid
  条件: (S : AddSubmonoid M)
  证明: AddSubmonoid.toNatSubmodule.symm_apply_apply S

@[simp]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.toNatSubmodule.symm_apply_apply, symm_apply_apply, toNatSubmodule
-/
theorem AddSubmonoid.toNatSubmodule_toAddSubmonoid (S : AddSubmonoid M) :
    S.toNatSubmodule.toAddSubmonoid = S :=
  AddSubmonoid.toNatSubmodule.symm_apply_apply S

@[simp]
/--
theorem `Submodule.toAddSubmonoid_toNatSubmodule` / 定理 `Submodule.toAddSubmonoid_toNatSubmodule`

English:
theorem Submodule.toAddSubmonoid_toNatSubmodule
  given: (S : Submodule Nat M)
  proof: AddSubmonoid.toNatSubmodule.apply_symm_apply S

中文:
定理 Submodule.toAddSubmonoid_toNatSubmodule
  条件: (S : Submodule 自然数 M)
  证明: AddSubmonoid.toNatSubmodule.apply_symm_apply S

Depends on / 依赖: AddSubmonoid, AddSubmonoid.toNatSubmodule.apply_symm_apply, apply_symm_apply, toNatSubmodule
-/
theorem Submodule.toAddSubmonoid_toNatSubmodule (S : Submodule Nat M) :
    S.toAddSubmonoid.toNatSubmodule = S :=
  AddSubmonoid.toNatSubmodule.apply_symm_apply S

end NatSubmodule

end AddCommMonoid

section IntSubmodule

/-!
## ℤ-submodules
-/

variable [AddCommGroup M]

/--
Definition of `AddSubgroup.toIntSubmodule` / `AddSubgroup.toIntSubmodule` 的定义

English:
definition AddSubgroup.toIntSubmodule
  signature: : AddSubgroup M ≃o Submodule Int M where
  body: { S with smul_mem' := fun _ _ hs => S.zsmul_mem hs _ }
  invFun := Submodule.toAddSubgroup
  map_rel_iff' := Iff.rfl

@[simp]

中文:
定义 AddSubgroup.toIntSubmodule
  签名: : AddSubgroup M ≃o Submodule 整数 M where
  定义体: { S with smul_mem' := fun _ _ hs => S.zsmul_mem hs _ }
  invFun := Submodule.toAddSubgroup
  map_rel_iff' := Iff.rfl

@[simp]

Depends on / 依赖: S.zsmul_mem, smul_mem, zsmul_mem
-/
def AddSubgroup.toIntSubmodule : AddSubgroup M ≃o Submodule Int M where
  toFun S := { S with smul_mem' := fun _ _ hs => S.zsmul_mem hs _ }
  invFun := Submodule.toAddSubgroup
  map_rel_iff' := Iff.rfl

@[simp]
/--
theorem `AddSubgroup.toIntSubmodule_symm` / 定理 `AddSubgroup.toIntSubmodule_symm`

English:
theorem AddSubgroup.toIntSubmodule_symm
  proof: rfl

@[simp]

中文:
定理 AddSubgroup.toIntSubmodule_symm
  证明: rfl

@[simp]
-/
theorem AddSubgroup.toIntSubmodule_symm :
    ⇑(AddSubgroup.toIntSubmodule.symm : _ ≃o AddSubgroup M) = Submodule.toAddSubgroup :=
  rfl

@[simp]
/--
theorem `AddSubgroup.coe_toIntSubmodule` / 定理 `AddSubgroup.coe_toIntSubmodule`

English:
theorem AddSubgroup.coe_toIntSubmodule
  given: (S : AddSubgroup M)
  proof: rfl

@[simp]

中文:
定理 AddSubgroup.coe_toIntSubmodule
  条件: (S : AddSubgroup M)
  证明: rfl

@[simp]
-/
theorem AddSubgroup.coe_toIntSubmodule (S : AddSubgroup M) :
    (S.toIntSubmodule : Set M) = S :=
  rfl

@[simp]
/--
theorem `AddSubgroup.toIntSubmodule_toAddSubgroup` / 定理 `AddSubgroup.toIntSubmodule_toAddSubgroup`

English:
theorem AddSubgroup.toIntSubmodule_toAddSubgroup
  given: (S : AddSubgroup M)
  proof: AddSubgroup.toIntSubmodule.symm_apply_apply S

中文:
定理 AddSubgroup.toIntSubmodule_toAddSubgroup
  条件: (S : AddSubgroup M)
  证明: AddSubgroup.toIntSubmodule.symm_apply_apply S

Depends on / 依赖: AddSubgroup, AddSubgroup.toIntSubmodule.symm_apply_apply, symm_apply_apply, toIntSubmodule
-/
theorem AddSubgroup.toIntSubmodule_toAddSubgroup (S : AddSubgroup M) :
    S.toIntSubmodule.toAddSubgroup = S :=
  AddSubgroup.toIntSubmodule.symm_apply_apply S

/--
theorem `Submodule.toAddSubgroup_toIntSubmodule` / 定理 `Submodule.toAddSubgroup_toIntSubmodule`

English:
theorem Submodule.toAddSubgroup_toIntSubmodule
  given: (S : Submodule Int M)
  proof: AddSubgroup.toIntSubmodule.apply_symm_apply S

中文:
定理 Submodule.toAddSubgroup_toIntSubmodule
  条件: (S : Submodule 整数 M)
  证明: AddSubgroup.toIntSubmodule.apply_symm_apply S

Depends on / 依赖: AddSubgroup, AddSubgroup.toIntSubmodule.apply_symm_apply, apply_symm_apply, toIntSubmodule
-/
theorem Submodule.toAddSubgroup_toIntSubmodule (S : Submodule Int M) :
    S.toAddSubgroup.toIntSubmodule = S :=
  AddSubgroup.toIntSubmodule.apply_symm_apply S

end IntSubmodule
