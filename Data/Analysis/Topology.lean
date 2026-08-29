/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Analysis.Filter
public import Mathlib.Topology.Bases
public import Mathlib.Topology.LocallyFinite

/-!
# Computational realization of topological spaces (experimental)

This file provides infrastructure to compute with topological spaces.

## Main declarations

* `Ctop`: Realization of a topology basis.
* `Ctop.Realizer`: Realization of a topological space. `Ctop` that generates the given topology.
* `LocallyFinite.Realizer`: Realization of the local finiteness of an indexed family of sets.
* `Compact.Realizer`: Realization of the compactness of a set.
-/

@[expose] public section


open Set

open Filter hiding Realizer

open Topology

/--
Definition of `Ctop` / `Ctop` 的定义

English:
structure Ctop
  parameters: (α σ : Type*)
  axioms and operations (6):
    - f : σ -> Set α
    - top : α -> σ
    - top_mem : forall x : α, x in f (top x)
    - inter : forall (a b) (x : α), x in f a inter f b -> σ
    - inter_mem : forall a b x h, x in f (inter a b x h)
    - inter_sub : forall a b x h, f (inter a b x h) subseteq f a inter f b

中文:
结构 Ctop
  参数: (α σ : 类型)
  公理与运算 (6 个):
    - f : σ -> 集合 α
    - top : α -> σ
    - top_mem : 对任意 x : α, x in f (top x)
    - inter : 对任意 (a b) (x : α), x in f a inter f b -> σ
    - inter_mem : 对任意 a b x h, x in f (inter a b x h)
    - inter_sub : 对任意 a b x h, f (inter a b x h) subseteq f a inter f b
-/
structure Ctop (α σ : Type*) where
  f : σ -> Set α
  top : α -> σ
  top_mem : forall x : α, x in f (top x)
  inter : forall (a b) (x : α), x in f a inter f b -> σ
  inter_mem : forall a b x h, x in f (inter a b x h)
  inter_sub : forall a b x h, f (inter a b x h) subseteq f a inter f b

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Ctop α (Set α))
  body: ⟨{ f := id
      top := singleton
      top_mem := mem_singleton
      inter := fun s t _ _ => s inter t
      inter_mem := fun _s _t _a => id
      inter_sub := fun _s _t _a _ha => Subset.rfl }⟩

中文:
实例 :
  签名: 可居 (Ctop α (集合 α))
  定义体: ⟨{ f := id
      top := singleton
      top_mem := mem_singleton
      inter := fun s t _ _ => s inter t
      inter_mem := fun _s _t _a => id
      inter_sub := fun _s _t _a _ha => Subset.rfl }⟩

Depends on / 依赖: Subset, Subset.rfl, inter_mem, inter_sub, mem_singleton, singleton, top_mem
-/
instance : Inhabited (Ctop α (Set α)) :=
  ⟨{ f := id
      top := singleton
      top_mem := mem_singleton
      inter := fun s t _ _ => s inter t
      inter_mem := fun _s _t _a => id
      inter_sub := fun _s _t _a _ha => Subset.rfl }⟩

namespace Ctop

section

variable (F : Ctop α σ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Ctop α σ) fun _ => σ -> Set α
  body: ⟨Ctop.f⟩

中文:
实例 :
  签名: CoeFun (Ctop α σ) fun _ => σ -> 集合 α
  定义体: ⟨Ctop.f⟩

Depends on / 依赖: Ctop.f
-/
instance : CoeFun (Ctop α σ) fun _ => σ -> Set α :=
  ⟨Ctop.f⟩

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f T h₁ I h₂ h₃ a)
  statement: (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a
  proof: rfl

中文:
定理 coe_mk
  条件: (f T h₁ I h₂ h₃ a)
  结论: (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a
  证明: rfl
-/
theorem coe_mk (f T h₁ I h₂ h₃ a) : (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a := rfl

/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: (E : σ ≃ τ)

中文:
定义 ofEquiv
  签名: (E : σ ≃ τ)

Depends on / 依赖: E.symm
-/
def ofEquiv (E : σ ≃ τ) : Ctop α σ -> Ctop α τ
  | ⟨f, T, h₁, I, h₂, h₃⟩ =>
    { f := fun a => f (E.symm a)
      top := fun x => E (T x)
      top_mem := fun x => by simpa using h₁ x
      inter := fun a b x h => E (I (E.symm a) (E.symm b) x h)
      inter_mem := fun a b x h => by simpa using h₂ (E.symm a) (E.symm b) x h
      inter_sub := fun a b x h => by simpa using h₃ (E.symm a) (E.symm b) x h }

@[simp]
/--
theorem `ofEquiv_val` / 定理 `ofEquiv_val`

English:
theorem ofEquiv_val
  given: (E : σ ≃ τ) (F : Ctop α σ) (a : τ)
  statement: F.ofEquiv E a = F (E.symm a)
  proof: by
  cases F; rfl

中文:
定理 ofEquiv_val
  条件: (E : σ ≃ τ) (F : Ctop α σ) (a : τ)
  结论: F.ofEquiv E a = F (E.symm a)
  证明: by
  cases F; rfl
-/
theorem ofEquiv_val (E : σ ≃ τ) (F : Ctop α σ) (a : τ) : F.ofEquiv E a = F (E.symm a) := by
  cases F; rfl

end

/-- Every `Ctop` is a topological space. -/
@[instance_reducible]
/--
Definition of `toTopsp` / `toTopsp` 的定义

English:
definition toTopsp
  signature: (F : Ctop α σ)
  body: TopologicalSpace.generateFrom (Set.range F.f)

中文:
定义 toTopsp
  签名: (F : Ctop α σ)
  定义体: TopologicalSpace.generateFrom (Set.range F.f)

Depends on / 依赖: Set.range, TopologicalSpace, TopologicalSpace.generateFrom, generateFrom
-/
def toTopsp (F : Ctop α σ) : TopologicalSpace α := TopologicalSpace.generateFrom (Set.range F.f)

/--
theorem `toTopsp_isTopologicalBasis` / 定理 `toTopsp_isTopologicalBasis`

English:
theorem toTopsp_isTopologicalBasis
  given: (F : Ctop α σ)
  proof: letI := F.toTopsp
  ⟨fun _u ⟨a, e₁⟩ _v ⟨b, e₂⟩ =>
    e₁ ▸ e₂ ▸ fun x h => ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩,
    eq_univ_iff_forall.2 fun x => ⟨_, ⟨_, rfl⟩, F.top_mem x⟩, rfl⟩

@[simp]

中文:
定理 toTopsp_isTopologicalBasis
  条件: (F : Ctop α σ)
  证明: letI := F.toTopsp
  ⟨fun _u ⟨a, e₁⟩ _v ⟨b, e₂⟩ =>
    e₁ ▸ e₂ ▸ fun x h => ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩,
    eq_univ_iff_forall.2 fun x => ⟨_, ⟨_, rfl⟩, F.top_mem x⟩, rfl⟩

@[simp]

Depends on / 依赖: F.inter_mem, F.inter_sub, F.toTopsp, F.top_mem, eq_univ_iff_forall, inter_mem, inter_sub, toTopsp, top_mem
-/
theorem toTopsp_isTopologicalBasis (F : Ctop α σ) :
    @TopologicalSpace.IsTopologicalBasis _ F.toTopsp (Set.range F.f) :=
  letI := F.toTopsp
  ⟨fun _u ⟨a, e₁⟩ _v ⟨b, e₂⟩ =>
    e₁ ▸ e₂ ▸ fun x h => ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩,
    eq_univ_iff_forall.2 fun x => ⟨_, ⟨_, rfl⟩, F.top_mem x⟩, rfl⟩

@[simp]
/--
theorem `mem_nhds_toTopsp` / 定理 `mem_nhds_toTopsp`

English:
theorem mem_nhds_toTopsp
  given: (F : Ctop α σ) {s : Set α} {a : α}
  proof: (@TopologicalSpace.IsTopologicalBasis.mem_nhds_iff _ F.toTopsp _ _ _
        F.toTopsp_isTopologicalBasis).trans <|
    ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨_, ⟨x, rfl⟩, h⟩⟩

中文:
定理 mem_nhds_toTopsp
  条件: (F : Ctop α σ) {s : 集合 α} {a : α}
  证明: (@TopologicalSpace.IsTopologicalBasis.mem_nhds_iff _ F.toTopsp _ _ _
        F.toTopsp_isTopologicalBasis).trans <|
    ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨_, ⟨x, rfl⟩, h⟩⟩

Depends on / 依赖: F.toTopsp, F.toTopsp_isTopologicalBasis, IsTopologicalBasis, TopologicalSpace, TopologicalSpace.IsTopologicalBasis.mem_nhds_iff, mem_nhds_iff, toTopsp, toTopsp_isTopologicalBasis
-/
theorem mem_nhds_toTopsp (F : Ctop α σ) {s : Set α} {a : α} :
    s in @nhds _ F.toTopsp a ↔ exists b, a in F b ∧ F b subseteq s :=
  (@TopologicalSpace.IsTopologicalBasis.mem_nhds_iff _ F.toTopsp _ _ _
        F.toTopsp_isTopologicalBasis).trans <|
    ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨_, ⟨x, rfl⟩, h⟩⟩

end Ctop

/--
Definition of `Ctop.Realizer` / `Ctop.Realizer` 的定义

English:
structure Ctop.Realizer
  parameters: (α) [T : TopologicalSpace α]
  axioms and operations (3):
    - σ : Type*
    - F : Ctop α σ
    - eq : F.toTopsp = T

中文:
结构 Ctop.实数izer
  参数: (α) [T : 拓扑空间 α]
  公理与运算 (3 个):
    - σ : 类型
    - F : Ctop α σ
    - eq : F.toTopsp = T

Depends on / 依赖: Ctop.Realizer.mk, F.toTopsp, Realizer, toTopsp
-/
structure Ctop.Realizer (α) [T : TopologicalSpace α] where
  σ : Type*
  F : Ctop α σ
  eq : F.toTopsp = T

open Ctop

/--
Definition of `Ctop.toRealizer` / `Ctop.toRealizer` 的定义

English:
definition Ctop.toRealizer
  signature: (F : Ctop α σ)
  body: @Ctop.Realizer.mk _ F.toTopsp σ F rfl

中文:
定义 Ctop.to实数izer
  签名: (F : Ctop α σ)
  定义体: @Ctop.Realizer.mk _ F.toTopsp σ F rfl
-/
protected def Ctop.toRealizer (F : Ctop α σ) : @Ctop.Realizer _ F.toTopsp :=
  @Ctop.Realizer.mk _ F.toTopsp σ F rfl

instance (F : Ctop α σ) : Inhabited (@Ctop.Realizer _ F.toTopsp) :=
  ⟨F.toRealizer⟩

namespace Ctop.Realizer

/--
theorem `is_basis` / 定理 `is_basis`

English:
theorem is_basis
  given: [T : TopologicalSpace α] (F : Realizer α)
  proof: by
  have := toTopsp_isTopologicalBasis F.F; rwa [F.eq] at this

中文:
定理 is_basis
  条件: [T : 拓扑空间 α] (F : 实数izer α)
  证明: by
  have := toTopsp_isTopologicalBasis F.F; rwa [F.eq] at this
-/
protected theorem is_basis [T : TopologicalSpace α] (F : Realizer α) :
    TopologicalSpace.IsTopologicalBasis (Set.range F.F.f) := by
  have := toTopsp_isTopologicalBasis F.F; rwa [F.eq] at this

/--
theorem `mem_nhds` / 定理 `mem_nhds`

English:
theorem mem_nhds
  given: [T : TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α}
  proof: by
  have := @mem_nhds_toTopsp _ _ F.F s a; rwa [F.eq] at this

中文:
定理 mem_nhds
  条件: [T : 拓扑空间 α] (F : 实数izer α) {s : 集合 α} {a : α}
  证明: by
  have := @mem_nhds_toTopsp _ _ F.F s a; rwa [F.eq] at this
-/
protected theorem mem_nhds [T : TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    s in 𝓝 a ↔ exists b, a in F.F b ∧ F.F b subseteq s := by
  have := @mem_nhds_toTopsp _ _ F.F s a; rwa [F.eq] at this

/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: [TopologicalSpace α] (F : Realizer α) {s : Set α}
  proof: isOpen_iff_mem_nhds.trans forall₂_congr fun _a _h => F.mem_nhds

中文:
定理 isOpen_iff
  条件: [拓扑空间 α] (F : 实数izer α) {s : 集合 α}
  证明: isOpen_iff_mem_nhds.trans forall₂_congr fun _a _h => F.mem_nhds

Depends on / 依赖: F.mem_nhds, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.trans, mem_nhds
-/
theorem isOpen_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsOpen s ↔ forall a in s, exists b, a in F.F b ∧ F.F b subseteq s :=
isOpen_iff_mem_nhds.trans forall₂_congr fun _a _h => F.mem_nhds

/--
theorem `isClosed_iff` / 定理 `isClosed_iff`

English:
theorem isClosed_iff
  given: [TopologicalSpace α] (F : Realizer α) {s : Set α}
  proof: isOpen_compl_iff.symm.trans
F.isOpen_iff.trans
      forall_congr' fun a =>
        show (a ∉ s -> exists b : F.σ, a in F.F b ∧ forall z in F.F b, z ∉ s) ↔ _ by
          have := Classical.propDecidable; rw [not_imp_comm]
          simp [not_exists, not_and, not_forall, and_comm]

中文:
定理 isClosed_iff
  条件: [拓扑空间 α] (F : 实数izer α) {s : 集合 α}
  证明: isOpen_compl_iff.symm.trans
F.isOpen_iff.trans
      forall_congr' fun a =>
        show (a ∉ s -> exists b : F.σ, a in F.F b ∧ forall z in F.F b, z ∉ s) ↔ _ by
          have := Classical.propDecidable; rw [not_imp_comm]
          simp [not_exists, not_and, not_forall, and_comm]

Depends on / 依赖: Classical, Classical.propDecidable, F.isOpen_iff.trans, and_comm, forall_congr, isOpen_compl_iff, isOpen_compl_iff.symm.trans, isOpen_iff, not_and, not_exists, not_forall, not_imp_comm, propDecidable
-/
theorem isClosed_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsClosed s ↔ forall a, (forall b, a in F.F b -> exists z, z in F.F b inter s) -> a in s :=
isOpen_compl_iff.symm.trans
F.isOpen_iff.trans
      forall_congr' fun a =>
        show (a ∉ s -> exists b : F.σ, a in F.F b ∧ forall z in F.F b, z ∉ s) ↔ _ by
          have := Classical.propDecidable; rw [not_imp_comm]
          simp [not_exists, not_and, not_forall, and_comm]

/--
theorem `mem_interior_iff` / 定理 `mem_interior_iff`

English:
theorem mem_interior_iff
  given: [TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α}
  proof: mem_interior_iff_mem_nhds.trans F.mem_nhds

中文:
定理 mem_interior_iff
  条件: [拓扑空间 α] (F : 实数izer α) {s : 集合 α} {a : α}
  证明: mem_interior_iff_mem_nhds.trans F.mem_nhds

Depends on / 依赖: F.mem_nhds, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.trans, mem_nhds
-/
theorem mem_interior_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    a in interior s ↔ exists b, a in F.F b ∧ F.F b subseteq s :=
  mem_interior_iff_mem_nhds.trans F.mem_nhds

/--
theorem `isOpen` / 定理 `isOpen`

English:
theorem isOpen
  given: [TopologicalSpace α] (F : Realizer α) (s : F.σ)
  statement: IsOpen (F.F s)
  proof: isOpen_iff_nhds.2 fun a m => by simpa using F.mem_nhds.2 ⟨s, m, Subset.refl _⟩

中文:
定理 isOpen
  条件: [拓扑空间 α] (F : 实数izer α) (s : F.σ)
  结论: 是开集 (F.F s)
  证明: isOpen_iff_nhds.2 fun a m => by simpa using F.mem_nhds.2 ⟨s, m, Subset.refl _⟩
-/
protected theorem isOpen [TopologicalSpace α] (F : Realizer α) (s : F.σ) : IsOpen (F.F s) :=
  isOpen_iff_nhds.2 fun a m => by simpa using F.mem_nhds.2 ⟨s, m, Subset.refl _⟩

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  statement: [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ}
  proof: by
  refine TopologicalSpace.ext_nhds fun x => ?_
  ext s
  rw [mem_nhds_toTopsp]; rw [H]

中文:
定理 ext'
  结论: [T : 拓扑空间 α] {σ : 类型} {F : Ctop α σ}
  证明: by
  refine TopologicalSpace.ext_nhds fun x => ?_
  ext s
  rw [mem_nhds_toTopsp]; rw [H]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext_nhds, ext_nhds, mem_nhds_toTopsp
-/
theorem ext' [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ}
    (H : forall a s, s in 𝓝 a ↔ exists b, a in F b ∧ F b subseteq s) : F.toTopsp = T := by
  refine TopologicalSpace.ext_nhds fun x => ?_
  ext s
  rw [mem_nhds_toTopsp]; rw [H]

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ} (H₁ : forall a, IsOpen (F a))
  proof: ext' fun a s => ⟨H₂ a s, fun ⟨_b, h₁, h₂⟩ => mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩

中文:
定理 ext
  结论: [T : 拓扑空间 α] {σ : 类型} {F : Ctop α σ} (H₁ : 对任意 a, 是开集 (F a))
  证明: ext' fun a s => ⟨H₂ a s, fun ⟨_b, h₁, h₂⟩ => mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩

Depends on / 依赖: mem_nhds_iff
-/
theorem ext [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ} (H₁ : forall a, IsOpen (F a))
    (H₂ : forall a s, s in 𝓝 a -> exists b, a in F b ∧ F b subseteq s) : F.toTopsp = T :=
  ext' fun a s => ⟨H₂ a s, fun ⟨_b, h₁, h₂⟩ => mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩

variable [TopologicalSpace α]

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Realizer α
  body: ⟨{ x : Set α // IsOpen x },
    { f := Subtype.val
      top := fun _ => ⟨univ, isOpen_univ⟩
      top_mem := mem_univ
      inter := fun ⟨_x, h₁⟩ ⟨_y, h₂⟩ _a _h₃ => ⟨_, h₁.inter h₂⟩
      inter_mem := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a => id
      inter_sub := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a _h₃ => Subset.refl _ },
    ext Subtype.property fun _x _s h =>
      let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h
      ⟨⟨t, o⟩, m, h⟩⟩

中文:
定义 id
  签名: : 实数izer α
  定义体: ⟨{ x : Set α // IsOpen x },
    { f := Subtype.val
      top := fun _ => ⟨univ, isOpen_univ⟩
      top_mem := mem_univ
      inter := fun ⟨_x, h₁⟩ ⟨_y, h₂⟩ _a _h₃ => ⟨_, h₁.inter h₂⟩
      inter_mem := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a => id
      inter_sub := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a _h₃ => Subset.refl _ },
    ext Subtype.property fun _x _s h =>
      let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h
      ⟨⟨t, o⟩, m, h⟩⟩
-/
protected def id : Realizer α :=
  ⟨{ x : Set α // IsOpen x },
    { f := Subtype.val
      top := fun _ => ⟨univ, isOpen_univ⟩
      top_mem := mem_univ
      inter := fun ⟨_x, h₁⟩ ⟨_y, h₂⟩ _a _h₃ => ⟨_, h₁.inter h₂⟩
      inter_mem := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a => id
      inter_sub := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a _h₃ => Subset.refl _ },
    ext Subtype.property fun _x _s h =>
      let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h
      ⟨⟨t, o⟩, m, h⟩⟩

/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: (F : Realizer α) (E : F.σ ≃ τ)
  body: ⟨τ, F.F.ofEquiv E,
    ext' fun a s =>
F.mem_nhds.trans
        ⟨fun ⟨s, h⟩ => ⟨E s, by simpa using h⟩, fun ⟨t, h⟩ => ⟨E.symm t, by simpa using h⟩⟩⟩

@[simp]

中文:
定义 ofEquiv
  签名: (F : 实数izer α) (E : F.σ ≃ τ)
  定义体: ⟨τ, F.F.ofEquiv E,
    ext' fun a s =>
F.mem_nhds.trans
        ⟨fun ⟨s, h⟩ => ⟨E s, by simpa using h⟩, fun ⟨t, h⟩ => ⟨E.symm t, by simpa using h⟩⟩⟩

@[simp]

Depends on / 依赖: E.symm, F.F.ofEquiv, F.mem_nhds.trans, mem_nhds, ofEquiv
-/
def ofEquiv (F : Realizer α) (E : F.σ ≃ τ) : Realizer α :=
  ⟨τ, F.F.ofEquiv E,
    ext' fun a s =>
F.mem_nhds.trans
        ⟨fun ⟨s, h⟩ => ⟨E s, by simpa using h⟩, fun ⟨t, h⟩ => ⟨E.symm t, by simpa using h⟩⟩⟩

@[simp]
/--
theorem `ofEquiv_σ` / 定理 `ofEquiv_σ`

English:
theorem ofEquiv_σ
  given: (F : Realizer α) (E : F.σ ≃ τ)
  statement: (F.ofEquiv E).σ = τ
  proof: rfl

@[simp]

中文:
定理 ofEquiv_σ
  条件: (F : 实数izer α) (E : F.σ ≃ τ)
  结论: (F.ofEquiv E).σ = τ
  证明: rfl

@[simp]
-/
theorem ofEquiv_σ (F : Realizer α) (E : F.σ ≃ τ) : (F.ofEquiv E).σ = τ := rfl

@[simp]
/--
theorem `ofEquiv_F` / 定理 `ofEquiv_F`

English:
theorem ofEquiv_F
  given: (F : Realizer α) (E : F.σ ≃ τ) (s : τ)
  statement: (F.ofEquiv E).F s = F.F (E.symm s)
  proof: by
  delta ofEquiv; simp

中文:
定理 ofEquiv_F
  条件: (F : 实数izer α) (E : F.σ ≃ τ) (s : τ)
  结论: (F.ofEquiv E).F s = F.F (E.symm s)
  证明: by
  delta ofEquiv; simp

Depends on / 依赖: ofEquiv
-/
theorem ofEquiv_F (F : Realizer α) (E : F.σ ≃ τ) (s : τ) : (F.ofEquiv E).F s = F.F (E.symm s) := by
  delta ofEquiv; simp

/--
Definition of `nhds` / `nhds` 的定义

English:
definition nhds
  signature: (F : Realizer α) (a : α)
  body: ⟨{ s : F.σ // a in F.F s },
    { f := fun s => F.F s.1
      pt := ⟨_, F.F.top_mem a⟩
      inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => ⟨_, F.F.inter_mem x y a ⟨h₁, h₂⟩⟩
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h => (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).1
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h => (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
filter_eq
      Set.ext fun _x =>
        ⟨fun ⟨⟨_s, as⟩, h⟩ => mem_nhds_iff.2 ⟨_, h, F.isOpen _, as⟩, fun h =>
          let ⟨s, h, as⟩ := F.mem_nhds.1 h
          ⟨⟨s, h⟩, as⟩⟩⟩

@[simp]

中文:
定义 邻域滤子
  签名: (F : 实数izer α) (a : α)
  定义体: ⟨{ s : F.σ // a in F.F s },
    { f := fun s => F.F s.1
      pt := ⟨_, F.F.top_mem a⟩
      inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => ⟨_, F.F.inter_mem x y a ⟨h₁, h₂⟩⟩
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h => (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).1
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h => (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
filter_eq
      Set.ext fun _x =>
        ⟨fun ⟨⟨_s, as⟩, h⟩ => mem_nhds_iff.2 ⟨_, h, F.isOpen _, as⟩, fun h =>
          let ⟨s, h, as⟩ := F.mem_nhds.1 h
          ⟨⟨s, h⟩, as⟩⟩⟩

@[simp]
-/
protected def nhds (F : Realizer α) (a : α) : (𝓝 a).Realizer :=
  ⟨{ s : F.σ // a in F.F s },
    { f := fun s => F.F s.1
      pt := ⟨_, F.F.top_mem a⟩
      inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => ⟨_, F.F.inter_mem x y a ⟨h₁, h₂⟩⟩
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h => (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).1
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h => (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
filter_eq
      Set.ext fun _x =>
        ⟨fun ⟨⟨_s, as⟩, h⟩ => mem_nhds_iff.2 ⟨_, h, F.isOpen _, as⟩, fun h =>
          let ⟨s, h, as⟩ := F.mem_nhds.1 h
          ⟨⟨s, h⟩, as⟩⟩⟩

@[simp]
/--
theorem `nhds_σ` / 定理 `nhds_σ`

English:
theorem nhds_σ
  given: (F : Realizer α) (a : α)
  statement: (F.nhds a).σ = { s : F.σ // a in F.F s }
  proof: rfl

@[simp]

中文:
定理 nhds_σ
  条件: (F : 实数izer α) (a : α)
  结论: (F.邻域滤子 a).σ = { s : F.σ // a in F.F s }
  证明: rfl

@[simp]
-/
theorem nhds_σ (F : Realizer α) (a : α) : (F.nhds a).σ = { s : F.σ // a in F.F s } := rfl

@[simp]
/--
theorem `nhds_F` / 定理 `nhds_F`

English:
theorem nhds_F
  given: (F : Realizer α) (a : α) (s)
  statement: (F.nhds a).F s = F.F s.1
  proof: rfl

中文:
定理 nhds_F
  条件: (F : 实数izer α) (a : α) (s)
  结论: (F.邻域滤子 a).F s = F.F s.1
  证明: rfl
-/
theorem nhds_F (F : Realizer α) (a : α) (s) : (F.nhds a).F s = F.F s.1 := rfl

/--
theorem `tendsto_nhds_iff` / 定理 `tendsto_nhds_iff`

English:
theorem tendsto_nhds_iff
  given: {m : β -> α} {f : Filter β} (F : f.Realizer) (R : Realizer α) {a : α}
  proof: (F.tendsto_iff _ (R.nhds a)).trans Subtype.forall

中文:
定理 tendsto_nhds_iff
  条件: {m : β -> α} {f : 滤子 β} (F : f.实数izer) (R : 实数izer α) {a : α}
  证明: (F.tendsto_iff _ (R.nhds a)).trans Subtype.forall

Depends on / 依赖: F.tendsto_iff, R.nhds, Subtype, Subtype.forall, tendsto_iff
-/
theorem tendsto_nhds_iff {m : β -> α} {f : Filter β} (F : f.Realizer) (R : Realizer α) {a : α} :
    Tendsto m f (𝓝 a) ↔ forall t, a in R.F t -> exists s, forall x in F.F s, m x in R.F t :=
  (F.tendsto_iff _ (R.nhds a)).trans Subtype.forall

end Ctop.Realizer

/--
Definition of `LocallyFinite.Realizer` / `LocallyFinite.Realizer` 的定义

English:
structure LocallyFinite.Realizer
  parameters: [TopologicalSpace α] (F : Ctop.Realizer α) (f : β -> Set α)
  axioms and operations (2):
    - bas : forall a, { s // a in F.F s }
    - sets : forall x : α, Fintype { i | (f i inter F.F (bas x)).Nonempty }

中文:
结构 局部有限.实数izer
  参数: [拓扑空间 α] (F : Ctop.实数izer α) (f : β -> 集合 α)
  公理与运算 (2 个):
    - bas : 对任意 a, { s // a in F.F s }
    - sets : 对任意 x : α, 有限类型 { i | (f i inter F.F (bas x)).非空 }
-/
structure LocallyFinite.Realizer [TopologicalSpace α] (F : Ctop.Realizer α) (f : β -> Set α) where
  bas : forall a, { s // a in F.F s }
  sets : forall x : α, Fintype { i | (f i inter F.F (bas x)).Nonempty }

/--
theorem `LocallyFinite.Realizer.to_locallyFinite` / 定理 `LocallyFinite.Realizer.to_locallyFinite`

English:
theorem LocallyFinite.Realizer.to_locallyFinite
  statement: [TopologicalSpace α] {F : Ctop.Realizer α}
  proof: fun a =>
  ⟨_, F.mem_nhds.2 ⟨(R.bas a).1, (R.bas a).2, Subset.rfl⟩, have := R.sets a; Set.toFinite _⟩

中文:
定理 局部有限.实数izer.to_locallyFinite
  结论: [拓扑空间 α] {F : Ctop.实数izer α}
  证明: fun a =>
  ⟨_, F.mem_nhds.2 ⟨(R.bas a).1, (R.bas a).2, Subset.rfl⟩, have := R.sets a; Set.toFinite _⟩
-/
theorem LocallyFinite.Realizer.to_locallyFinite [TopologicalSpace α] {F : Ctop.Realizer α}
    {f : β -> Set α} (R : LocallyFinite.Realizer F f) : LocallyFinite f := fun a =>
  ⟨_, F.mem_nhds.2 ⟨(R.bas a).1, (R.bas a).2, Subset.rfl⟩, have := R.sets a; Set.toFinite _⟩

/--
theorem `locallyFinite_iff_exists_realizer` / 定理 `locallyFinite_iff_exists_realizer`

English:
theorem locallyFinite_iff_exists_realizer
  statement: [TopologicalSpace α] (F : Ctop.Realizer α)
  proof: ⟨fun h =>
    let ⟨g, h₁⟩ := Classical.axiom_of_choice h
    let ⟨g₂, h₂⟩ :=
      Classical.axiom_of_choice fun x =>
        show exists b : F.σ, x in F.F b ∧ F.F b subseteq g x from
          let ⟨h, _h'⟩ := h₁ x
          F.mem_nhds.1 h
    ⟨⟨fun x => ⟨g₂ x, (h₂ x).1⟩, fun x =>
Finite.fintype
          let ⟨_h, h'⟩ := h₁ x
          h'.subset fun _i hi => hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
    fun ⟨R⟩ => R.to_locallyFinite⟩

中文:
定理 locallyFinite_iff_存在_realizer
  结论: [拓扑空间 α] (F : Ctop.实数izer α)
  证明: ⟨fun h =>
    let ⟨g, h₁⟩ := Classical.axiom_of_choice h
    let ⟨g₂, h₂⟩ :=
      Classical.axiom_of_choice fun x =>
        show exists b : F.σ, x in F.F b ∧ F.F b subseteq g x from
          let ⟨h, _h'⟩ := h₁ x
          F.mem_nhds.1 h
    ⟨⟨fun x => ⟨g₂ x, (h₂ x).1⟩, fun x =>
Finite.fintype
          let ⟨_h, h'⟩ := h₁ x
          h'.subset fun _i hi => hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
    fun ⟨R⟩ => R.to_locallyFinite⟩

Depends on / 依赖: Classical, Classical.axiom_of_choice, F.mem_nhds, Finite, Finite.fintype, R.to_locallyFinite, axiom_of_choice, fintype, hi.mono, inter_subset_inter_right, mem_nhds, subset, subseteq, to_locallyFinite
-/
theorem locallyFinite_iff_exists_realizer [TopologicalSpace α] (F : Ctop.Realizer α)
    {f : β -> Set α} : LocallyFinite f ↔ Nonempty (LocallyFinite.Realizer F f) :=
  ⟨fun h =>
    let ⟨g, h₁⟩ := Classical.axiom_of_choice h
    let ⟨g₂, h₂⟩ :=
      Classical.axiom_of_choice fun x =>
        show exists b : F.σ, x in F.F b ∧ F.F b subseteq g x from
          let ⟨h, _h'⟩ := h₁ x
          F.mem_nhds.1 h
    ⟨⟨fun x => ⟨g₂ x, (h₂ x).1⟩, fun x =>
Finite.fintype
          let ⟨_h, h'⟩ := h₁ x
          h'.subset fun _i hi => hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
    fun ⟨R⟩ => R.to_locallyFinite⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [Finite β] (F
  body: (locallyFinite_iff_exists_realizer _).1 locallyFinite_of_finite _

中文:
实例 [拓扑空间
  签名: α] [有限 β] (F
  定义体: (locallyFinite_iff_exists_realizer _).1 locallyFinite_of_finite _

Depends on / 依赖: locallyFinite_iff_exists_realizer, locallyFinite_of_finite
-/
instance [TopologicalSpace α] [Finite β] (F : Ctop.Realizer α) (f : β -> Set α) :
    Nonempty (LocallyFinite.Realizer F f) :=
(locallyFinite_iff_exists_realizer _).1 locallyFinite_of_finite _

/--
Definition of `Compact.Realizer` / `Compact.Realizer` 的定义

English:
definition Compact.Realizer
  signature: [TopologicalSpace α] (s : Set α)
  body: forall {f : Filter α} (F : f.Realizer) (x : F.σ), f != ⊥ -> F.F x subseteq s -> { a // a in s ∧ 𝓝 a ⊓ f != ⊥ }

中文:
定义 紧.实数izer
  签名: [拓扑空间 α] (s : 集合 α)
  定义体: forall {f : Filter α} (F : f.Realizer) (x : F.σ), f != ⊥ -> F.F x subseteq s -> { a // a in s ∧ 𝓝 a ⊓ f != ⊥ }

Depends on / 依赖: Filter, Realizer, f.Realizer, subseteq
-/
def Compact.Realizer [TopologicalSpace α] (s : Set α) :=
  forall {f : Filter α} (F : f.Realizer) (x : F.σ), f != ⊥ -> F.F x subseteq s -> { a // a in s ∧ 𝓝 a ⊓ f != ⊥ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] : Inhabited (Compact.Realizer (∅ : Set α))
  body: ⟨fun {f} F x h hF => by
    suffices f = ⊥ from absurd this h
    rw [← F.eq]; rw [eq_bot_iff]
    exact fun s _ => ⟨x, hF.trans s.empty_subset⟩⟩

中文:
实例 [拓扑空间
  签名: α] : 可居 (紧.实数izer (∅ : 集合 α))
  定义体: ⟨fun {f} F x h hF => by
    suffices f = ⊥ from absurd this h
    rw [← F.eq]; rw [eq_bot_iff]
    exact fun s _ => ⟨x, hF.trans s.empty_subset⟩⟩

Depends on / 依赖: F.eq, absurd, empty_subset, eq_bot_iff, hF.trans, s.empty_subset
-/
instance [TopologicalSpace α] : Inhabited (Compact.Realizer (∅ : Set α)) :=
  ⟨fun {f} F x h hF => by
    suffices f = ⊥ from absurd this h
    rw [← F.eq]; rw [eq_bot_iff]
    exact fun s _ => ⟨x, hF.trans s.empty_subset⟩⟩
