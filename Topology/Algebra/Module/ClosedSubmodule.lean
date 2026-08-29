/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Sets.Closeds

/-!
# Closed submodules of a topological module

This file builds the frame of closed `R`-submodules of a topological module `M`.

One can turn `s : Submodule R E` + `hs : IsClosed s` into `s : ClosedSubmodule R E` in a tactic
block by doing `lift s to ClosedSubmodule R E using hs`.

## TODO

Actually provide the `Order.Frame (ClosedSubmodule R M)` instance.
-/

@[expose] public section

open Function Order TopologicalSpace

variable {ι : Sort*} {R M N O : Type*} [Semiring R]
  [AddCommMonoid M] [TopologicalSpace M] [Module R M]
  [AddCommMonoid N] [TopologicalSpace N] [Module R N]
  [AddCommMonoid O] [TopologicalSpace O] [Module R O]

variable (R M) in
/-- The type of closed submodules of a topological module. -/
@[ext]
/--
Definition of `ClosedSubmodule` / `ClosedSubmodule` 的定义

English:
structure ClosedSubmodule
  parameters: extends Submodule R M, Closeds M
  extends: Submodule R M, Closeds M
  (no additional axioms)

中文:
结构 闭子模
  参数: extends 子模 R M, Closeds M
  继承: 子模 R M, Closeds M
  (无附加公理)
-/
structure ClosedSubmodule extends Submodule R M, Closeds M where

namespace ClosedSubmodule
variable {s t : ClosedSubmodule R M} {x : M}

attribute [coe] toSubmodule toCloseds

/-- Reinterpret a closed submodule as a submodule. -/
add_decl_doc toSubmodule

/-- Reinterpret a closed submodule as a closed set. -/
add_decl_doc toCloseds

/--
lemma `toSubmodule_injective` / 引理 `toSubmodule_injective`

English:
lemma toSubmodule_injective
  statement: Injective (toSubmodule : ClosedSubmodule R M -> Submodule R M)
  proof: fun s t h => by cases s; congr!

中文:
引理 toSubmodule_injective
  结论: 单射 (toSubmodule : 闭子模 R M -> 子模 R M)
  证明: fun s t h => by cases s; congr!
-/
lemma toSubmodule_injective : Injective (toSubmodule : ClosedSubmodule R M -> Submodule R M) :=
  fun s t h => by cases s; congr!

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (ClosedSubmodule R M) M
  body: s.1
coe_injective _ _ h := toSubmodule_injective SetLike.coe_injective h

中文:
实例 :
  签名: 集合状 (闭子模 R M) M
  定义体: s.1
coe_injective _ _ h := toSubmodule_injective SetLike.coe_injective h
-/
instance : SetLike (ClosedSubmodule R M) M where
  coe s := s.1
coe_injective _ _ h := toSubmodule_injective SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ClosedSubmodule R M)
  body: .ofSetLike (ClosedSubmodule R M) M

中文:
实例 :
  签名: 偏序 (闭子模 R M)
  定义体: .ofSetLike (ClosedSubmodule R M) M

Depends on / 依赖: ClosedSubmodule, ofSetLike
-/
instance : PartialOrder (ClosedSubmodule R M) := .ofSetLike (ClosedSubmodule R M) M

/--
lemma `toCloseds_injective` / 引理 `toCloseds_injective`

English:
lemma toCloseds_injective
  statement: Injective (toCloseds : ClosedSubmodule R M -> Closeds M)
  proof: fun _s _t h => SetLike.coe_injective congr(($h : Set M))

中文:
引理 toCloseds_injective
  结论: 单射 (toCloseds : 闭子模 R M -> Closeds M)
  证明: fun _s _t h => SetLike.coe_injective congr(($h : Set M))

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
lemma toCloseds_injective : Injective (toCloseds : ClosedSubmodule R M -> Closeds M) :=
  fun _s _t h => SetLike.coe_injective congr(($h : Set M))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddSubmonoidClass (ClosedSubmodule R M) M
  body: s.zero_mem
  add_mem {s} := s.add_mem

中文:
实例 :
  签名: 加法子幺半群类 (闭子模 R M) M
  定义体: s.zero_mem
  add_mem {s} := s.add_mem

Depends on / 依赖: s.zero_mem, zero_mem
-/
instance : AddSubmonoidClass (ClosedSubmodule R M) M where
  zero_mem s := s.zero_mem
  add_mem {s} := s.add_mem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulMemClass (ClosedSubmodule R M) R M
  body: s.smul_mem r

中文:
实例 :
  签名: SMulMem类 (闭子模 R M) R M
  定义体: s.smul_mem r

Depends on / 依赖: s.smul_mem, smul_mem
-/
instance : SMulMemClass (ClosedSubmodule R M) R M where
  smul_mem {s} r := s.smul_mem r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (ClosedSubmodule R M) (Submodule R M)
  body: toSubmodule

中文:
实例 :
  签名: Coe (闭子模 R M) (子模 R M)
  定义体: toSubmodule

Depends on / 依赖: toSubmodule
-/
instance : Coe (ClosedSubmodule R M) (Submodule R M) where
  coe := toSubmodule

/--
lemma `carrier_eq_coe` / 引理 `carrier_eq_coe`

English:
lemma carrier_eq_coe
  given: (s : ClosedSubmodule R M)
  statement: s.carrier = s
  proof: rfl

中文:
引理 carrier_eq_coe
  条件: (s : 闭子模 R M)
  结论: s.carrier = s
  证明: rfl
-/
@[simp] lemma carrier_eq_coe (s : ClosedSubmodule R M) : s.carrier = s := rfl

/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: {s : Submodule R M} {hs}
  statement: x in mk s hs ↔ x in s
  proof: .rfl

@[simp, norm_cast]

中文:
引理 mem_mk
  条件: {s : 子模 R M} {hs}
  结论: x in mk s hs ↔ x in s
  证明: .rfl

@[simp, norm_cast]
-/
@[simp] lemma mem_mk {s : Submodule R M} {hs} : x in mk s hs ↔ x in s := .rfl

@[simp, norm_cast]
/--
lemma `coe_toSubmodule` / 引理 `coe_toSubmodule`

English:
lemma coe_toSubmodule
  given: (s : ClosedSubmodule R M)
  statement: (s.toSubmodule : Set M) = s
  proof: rfl

@[simp]

中文:
引理 coe_toSubmodule
  条件: (s : 闭子模 R M)
  结论: (s.toSubmodule : 集合 M) = s
  证明: rfl

@[simp]
-/
lemma coe_toSubmodule (s : ClosedSubmodule R M) : (s.toSubmodule : Set M) = s := rfl

@[simp]
/--
lemma `mem_toSubmodule_iff` / 引理 `mem_toSubmodule_iff`

English:
lemma mem_toSubmodule_iff
  given: (x : M) (s : ClosedSubmodule R M)
  statement: x in s.toSubmodule ↔ x in s
  proof: by
  rfl

@[simp]

中文:
引理 mem_toSubmodule_iff
  条件: (x : M) (s : 闭子模 R M)
  结论: x in s.toSubmodule ↔ x in s
  证明: by
  rfl

@[simp]
-/
lemma mem_toSubmodule_iff (x : M) (s : ClosedSubmodule R M) : x in s.toSubmodule ↔ x in s := by
  rfl

@[simp]
/--
lemma `coe_toCloseds` / 引理 `coe_toCloseds`

English:
lemma coe_toCloseds
  given: (s : ClosedSubmodule R M)
  statement: (s.toCloseds : Set M) = s
  proof: rfl

中文:
引理 coe_toCloseds
  条件: (s : 闭子模 R M)
  结论: (s.toCloseds : 集合 M) = s
  证明: rfl
-/
lemma coe_toCloseds (s : ClosedSubmodule R M) : (s.toCloseds : Set M) = s := rfl

/--
lemma `isClosed` / 引理 `isClosed`

English:
lemma isClosed
  given: (s : ClosedSubmodule R M)
  statement: IsClosed (s : Set M)
  proof: s.isClosed'

initialize_simps_projections ClosedSubmodule (carrier -> coe, as_prefix coe)

中文:
引理 isClosed
  条件: (s : 闭子模 R M)
  结论: 是闭集 (s : 集合 M)
  证明: s.isClosed'

initialize_simps_projections ClosedSubmodule (carrier -> coe, as_prefix coe)

Depends on / 依赖: isClosed, s.isClosed
-/
lemma isClosed (s : ClosedSubmodule R M) : IsClosed (s : Set M) := s.isClosed'

initialize_simps_projections ClosedSubmodule (carrier -> coe, as_prefix coe)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (Submodule R M) (ClosedSubmodule R M) toSubmodule (IsClosed (X := M) ·)
  body: ⟨⟨s, hs⟩, rfl⟩

中文:
实例 :
  签名: CanLift (子模 R M) (闭子模 R M) toSubmodule (是闭集 (X := M) ·)
  定义体: ⟨⟨s, hs⟩, rfl⟩
-/
instance : CanLift (Submodule R M) (ClosedSubmodule R M) toSubmodule (IsClosed (X := M) ·) where
  prf s hs := ⟨⟨s, hs⟩, rfl⟩

/--
lemma `toSubmodule_le_toSubmodule` / 引理 `toSubmodule_le_toSubmodule`

English:
lemma toSubmodule_le_toSubmodule
  given: {s t : ClosedSubmodule R M}
  proof: .rfl

中文:
引理 toSubmodule_le_toSubmodule
  条件: {s t : 闭子模 R M}
  证明: .rfl
-/
@[simp, norm_cast] lemma toSubmodule_le_toSubmodule {s t : ClosedSubmodule R M} :
    s.toSubmodule <= t.toSubmodule ↔ s <= t := .rfl

/-- The preimage of a closed submodule under a continuous linear map as a closed submodule. -/
@[simps!]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : M ->L[R] N) (s : ClosedSubmodule R N)
  body: .comap (f : M ->ₗ[R] N) s
  isClosed' := by simpa using s.isClosed.preimage f.continuous

@[simp]

中文:
定义 comap
  签名: (f : M ->L[R] N) (s : 闭子模 R N)
  定义体: .comap (f : M ->ₗ[R] N) s
  isClosed' := by simpa using s.isClosed.preimage f.continuous

@[simp]
-/
def comap (f : M ->L[R] N) (s : ClosedSubmodule R N) : ClosedSubmodule R M where
  toSubmodule := .comap (f : M ->ₗ[R] N) s
  isClosed' := by simpa using s.isClosed.preimage f.continuous

@[simp]
/--
lemma `mem_comap` / 引理 `mem_comap`

English:
lemma mem_comap
  given: {f : M ->L[R] N} {s : ClosedSubmodule R N} {x : M}
  statement: x in s.comap f ↔ f x in s
  proof: .rfl

中文:
引理 mem_comap
  条件: {f : M ->L[R] N} {s : 闭子模 R N} {x : M}
  结论: x in s.comap f ↔ f x in s
  证明: .rfl
-/
lemma mem_comap {f : M ->L[R] N} {s : ClosedSubmodule R N} {x : M} : x in s.comap f ↔ f x in s := .rfl

/--
lemma `toSubmodule_comap` / 引理 `toSubmodule_comap`

English:
lemma toSubmodule_comap
  given: (f : M ->L[R] N) (s : ClosedSubmodule R N)
  proof: rfl

中文:
引理 toSubmodule_comap
  条件: (f : M ->L[R] N) (s : 闭子模 R N)
  证明: rfl
-/
@[simp] lemma toSubmodule_comap (f : M ->L[R] N) (s : ClosedSubmodule R N) :
    (s.comap f).toSubmodule = s.toSubmodule.comap (f : M ->ₗ[R] N) := rfl

/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (s : ClosedSubmodule R M)
  statement: s.comap (.id _ _) = s
  proof: rfl

中文:
引理 comap_id
  条件: (s : 闭子模 R M)
  结论: s.comap (.id _ _) = s
  证明: rfl
-/
@[simp] lemma comap_id (s : ClosedSubmodule R M) : s.comap (.id _ _) = s := rfl

/--
lemma `comap_comap` / 引理 `comap_comap`

English:
lemma comap_comap
  given: (g : N ->L[R] O) (f : M ->L[R] N) (s : ClosedSubmodule R O)
  proof: rfl

中文:
引理 comap_comap
  条件: (g : N ->L[R] O) (f : M ->L[R] N) (s : 闭子模 R O)
  证明: rfl
-/
lemma comap_comap (g : N ->L[R] O) (f : M ->L[R] N) (s : ClosedSubmodule R O) :
    (s.comap g).comap f = s.comap (g.comp f) := rfl

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (ClosedSubmodule R M) where
  body: ⟨s ⊓ t, s.isClosed.inter t.isClosed⟩

中文:
实例 instInf
  签名: : 最小值 (闭子模 R M) where
  定义体: ⟨s ⊓ t, s.isClosed.inter t.isClosed⟩

Depends on / 依赖: isClosed, s.isClosed.inter, t.isClosed
-/
instance instInf : Min (ClosedSubmodule R M) where
  min s t := ⟨s ⊓ t, s.isClosed.inter t.isClosed⟩

/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: : InfSet (ClosedSubmodule R M) where
  body: ⟨⨅ s in S, s, by simpa using isClosed_biInter fun x hx => x.isClosed⟩

@[simp, norm_cast]

中文:
实例 instInfSet
  签名: : 下确界集 (闭子模 R M) where
  定义体: ⟨⨅ s in S, s, by simpa using isClosed_biInter fun x hx => x.isClosed⟩

@[simp, norm_cast]

Depends on / 依赖: isClosed, isClosed_biInter, x.isClosed
-/
instance instInfSet : InfSet (ClosedSubmodule R M) where
  sInf S := ⟨⨅ s in S, s, by simpa using isClosed_biInter fun x hx => x.isClosed⟩

@[simp, norm_cast]
/--
lemma `toSubmodule_sInf` / 引理 `toSubmodule_sInf`

English:
lemma toSubmodule_sInf
  given: (S : Set (ClosedSubmodule R M))
  proof: rfl

@[simp, norm_cast]

中文:
引理 toSubmodule_sInf
  条件: (S : 集合 (闭子模 R M))
  证明: rfl

@[simp, norm_cast]
-/
lemma toSubmodule_sInf (S : Set (ClosedSubmodule R M)) :
    toSubmodule (sInf S) = ⨅ s in S, s.toSubmodule := rfl

@[simp, norm_cast]
/--
lemma `toSubmodule_iInf` / 引理 `toSubmodule_iInf`

English:
lemma toSubmodule_iInf
  given: (f : ι -> ClosedSubmodule R M)
  proof: by rw [iInf, toSubmodule_sInf, iInf_range]

@[simp, norm_cast]

中文:
引理 toSubmodule_iInf
  条件: (f : ι -> 闭子模 R M)
  证明: by rw [iInf, toSubmodule_sInf, iInf_range]

@[simp, norm_cast]

Depends on / 依赖: iInf_range, toSubmodule_sInf
-/
lemma toSubmodule_iInf (f : ι -> ClosedSubmodule R M) :
    toSubmodule (⨅ i, f i) = ⨅ i, (f i).toSubmodule := by rw [iInf, toSubmodule_sInf, iInf_range]

@[simp, norm_cast]
/--
lemma `coe_sInf` / 引理 `coe_sInf`

English:
lemma coe_sInf
  given: (S : Set (ClosedSubmodule R M))
  statement: ↑(sInf S) = ⨅ s in S, (s : Set M)
  proof: by
  simp [← coe_toSubmodule]

@[simp, norm_cast]

中文:
引理 coe_sInf
  条件: (S : 集合 (闭子模 R M))
  结论: ↑(sInf S) = ⨅ s in S, (s : 集合 M)
  证明: by
  simp [← coe_toSubmodule]

@[simp, norm_cast]

Depends on / 依赖: coe_toSubmodule
-/
lemma coe_sInf (S : Set (ClosedSubmodule R M)) : ↑(sInf S) = ⨅ s in S, (s : Set M) := by
  simp [← coe_toSubmodule]

@[simp, norm_cast]
/--
lemma `coe_iInf` / 引理 `coe_iInf`

English:
lemma coe_iInf
  given: (f : ι -> ClosedSubmodule R M)
  statement: ↑(⨅ i, f i) = ⨅ i, (f i : Set M)
  proof: by
  simp [← coe_toSubmodule]

中文:
引理 coe_iInf
  条件: (f : ι -> 闭子模 R M)
  结论: ↑(⨅ i, f i) = ⨅ i, (f i : 集合 M)
  证明: by
  simp [← coe_toSubmodule]

Depends on / 依赖: coe_toSubmodule
-/
lemma coe_iInf (f : ι -> ClosedSubmodule R M) : ↑(⨅ i, f i) = ⨅ i, (f i : Set M) := by
  simp [← coe_toSubmodule]

/--
lemma `mem_sInf` / 引理 `mem_sInf`

English:
lemma mem_sInf
  given: {S : Set (ClosedSubmodule R M)}
  statement: x in sInf S ↔ forall s in S, x in s
  proof: by
  simp [← SetLike.mem_coe]

中文:
引理 mem_sInf
  条件: {S : 集合 (闭子模 R M)}
  结论: x in sInf S ↔ 对任意 s in S, x in s
  证明: by
  simp [← SetLike.mem_coe]
-/
@[simp] lemma mem_sInf {S : Set (ClosedSubmodule R M)} : x in sInf S ↔ forall s in S, x in s := by
  simp [← SetLike.mem_coe]

/--
lemma `mem_iInf` / 引理 `mem_iInf`

English:
lemma mem_iInf
  given: {f : ι -> ClosedSubmodule R M}
  statement: x in ⨅ i, f i ↔ forall i, x in f i
  proof: by
  simp [← SetLike.mem_coe]

中文:
引理 mem_iInf
  条件: {f : ι -> 闭子模 R M}
  结论: x in ⨅ i, f i ↔ 对任意 i, x in f i
  证明: by
  simp [← SetLike.mem_coe]
-/
@[simp] lemma mem_iInf {f : ι -> ClosedSubmodule R M} : x in ⨅ i, f i ↔ forall i, x in f i := by
  simp [← SetLike.mem_coe]

/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: : SemilatticeInf (ClosedSubmodule R M)
  body: toSubmodule_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[simp, norm_cast]

中文:
实例 instSemilatticeInf
  签名: : SemilatticeInf (闭子模 R M)
  定义体: toSubmodule_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[simp, norm_cast]

Depends on / 依赖: semilatticeInf, toSubmodule_injective, toSubmodule_injective.semilatticeInf
-/
instance instSemilatticeInf : SemilatticeInf (ClosedSubmodule R M) :=
  toSubmodule_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[simp, norm_cast]
/--
lemma `toSubmodule_inf` / 引理 `toSubmodule_inf`

English:
lemma toSubmodule_inf
  given: (s t : ClosedSubmodule R M)
  proof: rfl

中文:
引理 toSubmodule_inf
  条件: (s t : 闭子模 R M)
  证明: rfl
-/
lemma toSubmodule_inf (s t : ClosedSubmodule R M) :
    toSubmodule (s ⊓ t) = s.toSubmodule ⊓ t.toSubmodule := rfl

/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (s t : ClosedSubmodule R M)
  statement: ↑(s ⊓ t) = (s ⊓ t : Set M)
  proof: rfl

中文:
引理 coe_inf
  条件: (s t : 闭子模 R M)
  结论: ↑(s ⊓ t) = (s ⊓ t : 集合 M)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (s t : ClosedSubmodule R M) : ↑(s ⊓ t) = (s ⊓ t : Set M) := rfl

/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  statement: x in s ⊓ t ↔ x in s ∧ x in t
  proof: .rfl

中文:
引理 mem_inf
  结论: x in s ⊓ t ↔ x in s ∧ x in t
  证明: .rfl
-/
@[simp] lemma mem_inf : x in s ⊓ t ↔ x in s ∧ x in t := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (ClosedSubmodule R M)
  body: .of_image toSubmodule_le_toSubmodule isGLB_biInf

中文:
实例 :
  签名: 余mpleteSemilatticeInf (闭子模 R M)
  定义体: .of_image toSubmodule_le_toSubmodule isGLB_biInf

Depends on / 依赖: isGLB_biInf, of_image, toSubmodule_le_toSubmodule
-/
instance : CompleteSemilatticeInf (ClosedSubmodule R M) where
  isGLB_sInf _ := .of_image toSubmodule_le_toSubmodule isGLB_biInf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (ClosedSubmodule R M)
  body: ⟨⊤, isClosed_univ⟩
  le_top s := le_top (a := s.toSubmodule)

中文:
实例 :
  签名: 有顶序 (闭子模 R M)
  定义体: ⟨⊤, isClosed_univ⟩
  le_top s := le_top (a := s.toSubmodule)

Depends on / 依赖: isClosed_univ
-/
instance : OrderTop (ClosedSubmodule R M) where
  top := ⟨⊤, isClosed_univ⟩
  le_top s := le_top (a := s.toSubmodule)

/--
lemma `toSubmodule_top` / 引理 `toSubmodule_top`

English:
lemma toSubmodule_top
  statement: toSubmodule (⊤ : ClosedSubmodule R M) = ⊤
  proof: rfl

中文:
引理 toSubmodule_top
  结论: toSubmodule (⊤ : 闭子模 R M) = ⊤
  证明: rfl
-/
@[simp, norm_cast] lemma toSubmodule_top : toSubmodule (⊤ : ClosedSubmodule R M) = ⊤ := rfl

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: ((⊤ : ClosedSubmodule R M) : Set M) = .univ
  proof: rfl

中文:
引理 coe_top
  结论: ((⊤ : 闭子模 R M) : 集合 M) = .univ
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : ((⊤ : ClosedSubmodule R M) : Set M) = .univ := rfl

/--
lemma `mem_top` / 引理 `mem_top`

English:
lemma mem_top
  statement: x in (⊤ : ClosedSubmodule R M)
  proof: trivial

中文:
引理 mem_top
  结论: x in (⊤ : 闭子模 R M)
  证明: trivial
-/
@[simp] lemma mem_top : x in (⊤ : ClosedSubmodule R M) := trivial

section T1Space
variable [T1Space M]

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot (ClosedSubmodule R M) where
  body: ⟨⊥, isClosed_singleton⟩
  bot_le s := bot_le (a := s.toSubmodule)

中文:
实例 instOrderBot
  签名: : 有底序 (闭子模 R M) where
  定义体: ⟨⊥, isClosed_singleton⟩
  bot_le s := bot_le (a := s.toSubmodule)

Depends on / 依赖: isClosed_singleton
-/
instance instOrderBot : OrderBot (ClosedSubmodule R M) where
  bot := ⟨⊥, isClosed_singleton⟩
  bot_le s := bot_le (a := s.toSubmodule)

/--
lemma `toSubmodule_bot` / 引理 `toSubmodule_bot`

English:
lemma toSubmodule_bot
  statement: toSubmodule (⊥ : ClosedSubmodule R M) = ⊥
  proof: rfl

中文:
引理 toSubmodule_bot
  结论: toSubmodule (⊥ : 闭子模 R M) = ⊥
  证明: rfl
-/
@[simp, norm_cast] lemma toSubmodule_bot : toSubmodule (⊥ : ClosedSubmodule R M) = ⊥ := rfl

/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: ((⊥ : ClosedSubmodule R M) : Set M) = {0}
  proof: rfl

中文:
引理 coe_bot
  结论: ((⊥ : 闭子模 R M) : 集合 M) = {0}
  证明: rfl
-/
@[simp, norm_cast] lemma coe_bot : ((⊥ : ClosedSubmodule R M) : Set M) = {0} := rfl

/--
lemma `mem_bot` / 引理 `mem_bot`

English:
lemma mem_bot
  statement: x in (⊥ : ClosedSubmodule R M) ↔ x = 0
  proof: .rfl

中文:
引理 mem_bot
  结论: x in (⊥ : 闭子模 R M) ↔ x = 0
  证明: .rfl
-/
@[simp] lemma mem_bot : x in (⊥ : ClosedSubmodule R M) ↔ x = 0 := .rfl

end T1Space
end ClosedSubmodule

namespace Submodule
variable [ContinuousAdd M] [ContinuousConstSMul R M]

/-- The closure of a submodule as a closed submodule. -/
@[simps!]
/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Submodule R M)
  body: s.topologicalClosure
  isClosed' := isClosed_closure

中文:
定义 closure
  签名: (s : 子模 R M)
  定义体: s.topologicalClosure
  isClosed' := isClosed_closure
-/
protected def closure (s : Submodule R M) : ClosedSubmodule R M where
  toSubmodule := s.topologicalClosure
  isClosed' := isClosed_closure

/--
lemma `closure_le` / 引理 `closure_le`

English:
lemma closure_le
  given: {s : Submodule R M} {t : ClosedSubmodule R M}
  statement: s.closure <= t ↔ s <= t
  proof: t.isClosed.closure_subset_iff

@[simp]

中文:
引理 closure_le
  条件: {s : 子模 R M} {t : 闭子模 R M}
  结论: s.closure <= t ↔ s <= t
  证明: t.isClosed.closure_subset_iff

@[simp]
-/
@[simp] lemma closure_le {s : Submodule R M} {t : ClosedSubmodule R M} : s.closure <= t ↔ s <= t :=
  t.isClosed.closure_subset_iff

@[simp]
/--
lemma `mem_closure_iff` / 引理 `mem_closure_iff`

English:
lemma mem_closure_iff
  given: {x : M} {s : Submodule R M}
  statement: x in s.closure ↔ x in s.topologicalClosure
  proof: Iff.rfl

@[simp]

中文:
引理 mem_closure_iff
  条件: {x : M} {s : 子模 R M}
  结论: x in s.closure ↔ x in s.topologicalClosure
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_closure_iff {x : M} {s : Submodule R M} : x in s.closure ↔ x in s.topologicalClosure :=
  Iff.rfl

@[simp]
/--
lemma `closure_eq` / 引理 `closure_eq`

English:
lemma closure_eq
  given: {s : ClosedSubmodule R M}
  statement: s.closure = s
  proof: by
  ext
  simp only [carrier_eq_coe, ClosedSubmodule.coe_toSubmodule, coe_closure, SetLike.mem_coe]
  rw [closure_eq_iff_isClosed.mpr]
  · rfl
  · exact s.isClosed'

中文:
引理 closure_eq
  条件: {s : 闭子模 R M}
  结论: s.closure = s
  证明: by
  ext
  simp only [carrier_eq_coe, ClosedSubmodule.coe_toSubmodule, coe_closure, SetLike.mem_coe]
  rw [closure_eq_iff_isClosed.mpr]
  · rfl
  · exact s.isClosed'

Depends on / 依赖: ClosedSubmodule, ClosedSubmodule.coe_toSubmodule, SetLike, SetLike.mem_coe, carrier_eq_coe, closure_eq_iff_isClosed, closure_eq_iff_isClosed.mpr, coe_closure, coe_toSubmodule, isClosed, mem_coe, s.isClosed
-/
lemma closure_eq {s : ClosedSubmodule R M} : s.closure = s := by
  ext
  simp only [carrier_eq_coe, ClosedSubmodule.coe_toSubmodule, coe_closure, SetLike.mem_coe]
  rw [closure_eq_iff_isClosed.mpr]
  · rfl
  · exact s.isClosed'

/--
lemma `closure_eq'` / 引理 `closure_eq'`

English:
lemma closure_eq'
  given: {s : Submodule R M} (hs : IsClosed s.carrier)
  statement: s.closure = ⟨s, hs⟩
  proof: by
  ext; simp

中文:
引理 closure_eq'
  条件: {s : 子模 R M} (hs : 是闭集 s.carrier)
  结论: s.closure = ⟨s, hs⟩
  证明: by
  ext; simp
-/
lemma closure_eq' {s : Submodule R M} (hs : IsClosed s.carrier) : s.closure = ⟨s, hs⟩ := by
  ext; simp

end Submodule

namespace ClosedSubmodule

variable [ContinuousAdd N] [ContinuousConstSMul R N] {f : M ->L[R] N}

/--
lemma `closure_toSubmodule_eq` / 引理 `closure_toSubmodule_eq`

English:
lemma closure_toSubmodule_eq
  given: {s : ClosedSubmodule R N}
  statement: s.toSubmodule.closure = s
  proof: by
  ext x; simp

中文:
引理 closure_toSubmodule_eq
  条件: {s : 闭子模 R N}
  结论: s.toSubmodule.closure = s
  证明: by
  ext x; simp
-/
lemma closure_toSubmodule_eq {s : ClosedSubmodule R N} : s.toSubmodule.closure = s := by
  ext x; simp

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->L[R] N) (s : ClosedSubmodule R M)
  body: (s.toSubmodule.map (f : M ->ₗ[R] N)).closure

@[simp]

中文:
定义 map
  签名: (f : M ->L[R] N) (s : 闭子模 R M)
  定义体: (s.toSubmodule.map (f : M ->ₗ[R] N)).closure

@[simp]

Depends on / 依赖: closure, s.toSubmodule.map, toSubmodule
-/
def map (f : M ->L[R] N) (s : ClosedSubmodule R M) : ClosedSubmodule R N :=
  (s.toSubmodule.map (f : M ->ₗ[R] N)).closure

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: [ContinuousAdd M] [ContinuousConstSMul R M] (s : ClosedSubmodule R M)
  proof: SetLike.coe_injective by simp [map]

中文:
引理 map_id
  条件: [连续加法 M] [连续常数标量乘法 R M] (s : 闭子模 R M)
  证明: SetLike.coe_injective by simp [map]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
lemma map_id [ContinuousAdd M] [ContinuousConstSMul R M] (s : ClosedSubmodule R M) :
s.map (.id _ _) = s := SetLike.coe_injective by simp [map]

/--
lemma `map_le_iff_le_comap` / 引理 `map_le_iff_le_comap`

English:
lemma map_le_iff_le_comap
  given: {s : ClosedSubmodule R M} {t : ClosedSubmodule R N}
  proof: by
  simp [map, Submodule.map_le_iff_le_comap]; simp [← toSubmodule_le_toSubmodule]

中文:
引理 map_le_iff_le_comap
  条件: {s : 闭子模 R M} {t : 闭子模 R N}
  证明: by
  simp [map, Submodule.map_le_iff_le_comap]; simp [← toSubmodule_le_toSubmodule]

Depends on / 依赖: Submodule, Submodule.map_le_iff_le_comap, map_le_iff_le_comap, toSubmodule_le_toSubmodule
-/
lemma map_le_iff_le_comap {s : ClosedSubmodule R M} {t : ClosedSubmodule R N} :
    map f s <= t ↔ s <= comap f t := by
  simp [map, Submodule.map_le_iff_le_comap]; simp [← toSubmodule_le_toSubmodule]

/--
lemma `gc_map_comap` / 引理 `gc_map_comap`

English:
lemma gc_map_comap
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ => map_le_iff_le_comap

中文:
引理 gc_map_comap
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ => map_le_iff_le_comap

Depends on / 依赖: map_le_iff_le_comap
-/
lemma gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap

variable {s t : ClosedSubmodule R N} {x : N}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (ClosedSubmodule R N)
  body: (s.toSubmodule ⊔ t.toSubmodule).closure

@[simp]

中文:
实例 :
  签名: 最大值 (闭子模 R N)
  定义体: (s.toSubmodule ⊔ t.toSubmodule).closure

@[simp]

Depends on / 依赖: closure, s.toSubmodule, t.toSubmodule, toSubmodule
-/
instance : Max (ClosedSubmodule R N) where
  max s t := (s.toSubmodule ⊔ t.toSubmodule).closure

@[simp]
/--
lemma `toSubmodule_sup` / 引理 `toSubmodule_sup`

English:
lemma toSubmodule_sup
  proof: rfl

@[simp, norm_cast]

中文:
引理 toSubmodule_sup
  证明: rfl

@[simp, norm_cast]
-/
lemma toSubmodule_sup :
  toSubmodule (s ⊔ t) = (s.toSubmodule ⊔ t.toSubmodule).closure := rfl

@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  proof: by
  simp only [← coe_toSubmodule, toSubmodule_sup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

中文:
引理 coe_sup
  证明: by
  simp only [← coe_toSubmodule, toSubmodule_sup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

Depends on / 依赖: Submodule, Submodule.carrier_eq_coe, Submodule.coe_closure, carrier_eq_coe, coe_closure, coe_toSubmodule, toSubmodule_sup
-/
lemma coe_sup :
    ↑(s ⊔ t) = closure (s.toSubmodule ⊔ t.toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_sup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

/--
lemma `mem_sup` / 引理 `mem_sup`

English:
lemma mem_sup
  proof: Iff.rfl

中文:
引理 mem_sup
  证明: Iff.rfl
-/
@[simp] lemma mem_sup :
    x in s ⊔ t ↔ x in closure (s.toSubmodule ⊔ t.toSubmodule).carrier := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (ClosedSubmodule R N)
  body: ⟨(⨆ s in S, s.toSubmodule).closure, isClosed_closure⟩

@[simp]

中文:
实例 :
  签名: 上确界集 (闭子模 R N)
  定义体: ⟨(⨆ s in S, s.toSubmodule).closure, isClosed_closure⟩

@[simp]

Depends on / 依赖: closure, isClosed_closure, s.toSubmodule, toSubmodule
-/
instance : SupSet (ClosedSubmodule R N) where
  sSup S := ⟨(⨆ s in S, s.toSubmodule).closure, isClosed_closure⟩

@[simp]
/--
lemma `toSubmodule_sSup` / 引理 `toSubmodule_sSup`

English:
lemma toSubmodule_sSup
  given: (S : Set (ClosedSubmodule R N))
  proof: rfl

@[simp]

中文:
引理 toSubmodule_sSup
  条件: (S : 集合 (闭子模 R N))
  证明: rfl

@[simp]
-/
lemma toSubmodule_sSup (S : Set (ClosedSubmodule R N)) :
    toSubmodule (sSup S) = (⨆ s in S, s.toSubmodule).closure := rfl

@[simp]
/--
lemma `toSubmodule_iSup` / 引理 `toSubmodule_iSup`

English:
lemma toSubmodule_iSup
  given: (f : ι -> ClosedSubmodule R N)
  proof: by
  rw [iSup]; rw [toSubmodule_sSup]; rw [iSup_range]

@[simp, norm_cast]

中文:
引理 toSubmodule_iSup
  条件: (f : ι -> 闭子模 R N)
  证明: by
  rw [iSup]; rw [toSubmodule_sSup]; rw [iSup_range]

@[simp, norm_cast]

Depends on / 依赖: iSup_range, toSubmodule_sSup
-/
lemma toSubmodule_iSup (f : ι -> ClosedSubmodule R N) :
    toSubmodule (⨆ i, f i) = (⨆ i, (f i).toSubmodule).closure := by
  rw [iSup]; rw [toSubmodule_sSup]; rw [iSup_range]

@[simp, norm_cast]
/--
lemma `coe_sSup` / 引理 `coe_sSup`

English:
lemma coe_sSup
  given: (S : Set (ClosedSubmodule R N))
  proof: by
  simp only [← coe_toSubmodule, toSubmodule_sSup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

@[simp, norm_cast]

中文:
引理 coe_sSup
  条件: (S : 集合 (闭子模 R N))
  证明: by
  simp only [← coe_toSubmodule, toSubmodule_sSup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.carrier_eq_coe, Submodule.coe_closure, carrier_eq_coe, coe_closure, coe_toSubmodule, toSubmodule_sSup
-/
lemma coe_sSup (S : Set (ClosedSubmodule R N)) :
    ↑(sSup S) = closure (⨆ s in S, s.toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_sSup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

@[simp, norm_cast]
/--
lemma `coe_iSup` / 引理 `coe_iSup`

English:
lemma coe_iSup
  given: (f : ι -> ClosedSubmodule R N)
  proof: by
  simp only [← coe_toSubmodule, toSubmodule_iSup, Submodule.carrier_eq_coe]
  rfl

中文:
引理 coe_iSup
  条件: (f : ι -> 闭子模 R N)
  证明: by
  simp only [← coe_toSubmodule, toSubmodule_iSup, Submodule.carrier_eq_coe]
  rfl

Depends on / 依赖: Submodule, Submodule.carrier_eq_coe, carrier_eq_coe, coe_toSubmodule, toSubmodule_iSup
-/
lemma coe_iSup (f : ι -> ClosedSubmodule R N) :
    ↑(⨆ i, f i) = closure (⨆ i, (f i).toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_iSup, Submodule.carrier_eq_coe]
  rfl

/--
lemma `mem_sSup` / 引理 `mem_sSup`

English:
lemma mem_sSup
  given: {S : Set (ClosedSubmodule R N)}
  proof: Iff.rfl

中文:
引理 mem_sSup
  条件: {S : 集合 (闭子模 R N)}
  证明: Iff.rfl
-/
@[simp] lemma mem_sSup {S : Set (ClosedSubmodule R N)} :
    x in sSup S ↔ x in closure (⨆ s in S, s.toSubmodule).carrier := Iff.rfl

/--
lemma `mem_iSup` / 引理 `mem_iSup`

English:
lemma mem_iSup
  given: {f : ι -> ClosedSubmodule R N}
  proof: by
  simp [← SetLike.mem_coe]

中文:
引理 mem_iSup
  条件: {f : ι -> 闭子模 R N}
  证明: by
  simp [← SetLike.mem_coe]
-/
@[simp] lemma mem_iSup {f : ι -> ClosedSubmodule R N} :
    x in ⨆ i, f i ↔ x in closure (⨆ i, (f i).toSubmodule).carrier := by
  simp [← SetLike.mem_coe]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (ClosedSubmodule R N)
  body: s ⊔ t
le_sup_left _ _ _ hx := subset_closure Submodule.mem_sup_left hx
le_sup_right _ _ _ hx := subset_closure Submodule.mem_sup_right hx
sup_le _ _ _ ha hb := Submodule.closure_le.mpr sup_le_iff.mpr ⟨ha, hb⟩

中文:
实例 :
  签名: SemilatticeSup (闭子模 R N)
  定义体: s ⊔ t
le_sup_left _ _ _ hx := subset_closure Submodule.mem_sup_left hx
le_sup_right _ _ _ hx := subset_closure Submodule.mem_sup_right hx
sup_le _ _ _ ha hb := Submodule.closure_le.mpr sup_le_iff.mpr ⟨ha, hb⟩
-/
instance : SemilatticeSup (ClosedSubmodule R N) where
  sup s t := s ⊔ t
le_sup_left _ _ _ hx := subset_closure Submodule.mem_sup_left hx
le_sup_right _ _ _ hx := subset_closure Submodule.mem_sup_right hx
sup_le _ _ _ ha hb := Submodule.closure_le.mpr sup_le_iff.mpr ⟨ha, hb⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeSup (ClosedSubmodule R N)
  body: by
    refine ⟨fun a ha x hx => ?_, fun a h x => ?_⟩
· exact subset_closure Submodule.mem_iSup_of_mem _ Submodule.mem_iSup_of_mem ha hx
    · rw [← ClosedSubmodule.closure_toSubmodule_eq (s := a)]
      apply closure_mono
      simp only [Submodule.coe_toAddSubmonoid, coe_toSubmodule]
      intro y hy
      simp only [SetLike.mem_coe, Submodule.mem_iSup] at hy
.mp hz _ fun hb => h hb exact hy a fun b _ hz => Submodule.mem_iSup _

中文:
实例 :
  签名: 余mpleteSemilatticeSup (闭子模 R N)
  定义体: by
    refine ⟨fun a ha x hx => ?_, fun a h x => ?_⟩
· exact subset_closure Submodule.mem_iSup_of_mem _ Submodule.mem_iSup_of_mem ha hx
    · rw [← ClosedSubmodule.closure_toSubmodule_eq (s := a)]
      apply closure_mono
      simp only [Submodule.coe_toAddSubmonoid, coe_toSubmodule]
      intro y hy
      simp only [SetLike.mem_coe, Submodule.mem_iSup] at hy
.mp hz _ fun hb => h hb exact hy a fun b _ hz => Submodule.mem_iSup _

Depends on / 依赖: ClosedSubmodule, ClosedSubmodule.closure_toSubmodule_eq, SetLike, SetLike.mem_coe, Submodule, Submodule.coe_toAddSubmonoid, Submodule.mem_iSup, Submodule.mem_iSup_of_mem, closure_mono, closure_toSubmodule_eq, coe_toAddSubmonoid, coe_toSubmodule, mem_coe, mem_iSup, mem_iSup_of_mem, subset_closure
-/
instance : CompleteSemilatticeSup (ClosedSubmodule R N) where
  isLUB_sSup _ := by
    refine ⟨fun a ha x hx => ?_, fun a h x => ?_⟩
· exact subset_closure Submodule.mem_iSup_of_mem _ Submodule.mem_iSup_of_mem ha hx
    · rw [← ClosedSubmodule.closure_toSubmodule_eq (s := a)]
      apply closure_mono
      simp only [Submodule.coe_toAddSubmonoid, coe_toSubmodule]
      intro y hy
      simp only [SetLike.mem_coe, Submodule.mem_iSup] at hy
.mp hz _ fun hb => h hb exact hy a fun b _ hz => Submodule.mem_iSup _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (ClosedSubmodule R N)

中文:
实例 :
  签名: 格 (闭子模 R N)
-/
instance : Lattice (ClosedSubmodule R N) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: N] : CompleteLattice (ClosedSubmodule R N) where

中文:
实例 [T1空间
  签名: N] : 完备格 (闭子模 R N) where
-/
instance [T1Space N] : CompleteLattice (ClosedSubmodule R N) where

end ClosedSubmodule

namespace ClosedSubmodule

variable (f : M ≃L[R] N)

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: : ClosedSubmodule R M ≃ ClosedSubmodule R N where
  body: ⟨s.toSubmodule.map f.toLinearMap, by simpa using s.isClosed⟩
  invFun t := ⟨t.toSubmodule.map f.symm.toLinearMap, by simpa using t.isClosed⟩
  left_inv := by intro _; ext _; simp
  right_inv := by intro _; ext _; simp

中文:
定义 mapEquiv
  签名: : 闭子模 R M ≃ 闭子模 R N where
  定义体: ⟨s.toSubmodule.map f.toLinearMap, by simpa using s.isClosed⟩
  invFun t := ⟨t.toSubmodule.map f.symm.toLinearMap, by simpa using t.isClosed⟩
  left_inv := by intro _; ext _; simp
  right_inv := by intro _; ext _; simp

Depends on / 依赖: f.toLinearMap, isClosed, s.isClosed, s.toSubmodule.map, toLinearMap, toSubmodule
-/
def mapEquiv : ClosedSubmodule R M ≃ ClosedSubmodule R N where
  toFun s := ⟨s.toSubmodule.map f.toLinearMap, by simpa using s.isClosed⟩
  invFun t := ⟨t.toSubmodule.map f.symm.toLinearMap, by simpa using t.isClosed⟩
  left_inv := by intro _; ext _; simp
  right_inv := by intro _; ext _; simp

variable (s : ClosedSubmodule R M)

@[simp]
/--
lemma `mapEquiv_apply` / 引理 `mapEquiv_apply`

English:
lemma mapEquiv_apply
  statement: (s.mapEquiv f).toSubmodule = s.toSubmodule.map f.toLinearMap
  proof: rfl

@[simp]

中文:
引理 mapEquiv_apply
  结论: (s.mapEquiv f).toSubmodule = s.toSubmodule.map f.toLinearMap
  证明: rfl

@[simp]
-/
lemma mapEquiv_apply : (s.mapEquiv f).toSubmodule = s.toSubmodule.map f.toLinearMap := rfl

@[simp]
/--
lemma `mapEquiv_symm` / 引理 `mapEquiv_symm`

English:
lemma mapEquiv_symm
  statement: mapEquiv f.symm = (mapEquiv f).symm
  proof: rfl

@[simp]

中文:
引理 mapEquiv_symm
  结论: mapEquiv f.symm = (mapEquiv f).symm
  证明: rfl

@[simp]
-/
lemma mapEquiv_symm : mapEquiv f.symm = (mapEquiv f).symm := rfl

@[simp]
/--
lemma `mem_mapEquiv_iff` / 引理 `mem_mapEquiv_iff`

English:
lemma mem_mapEquiv_iff
  given: (x : N)
  statement: x in (s.mapEquiv f) ↔ f.symm x in s
  proof: Submodule.mem_map_equiv (e := f.toLinearEquiv) s.toSubmodule

中文:
引理 mem_mapEquiv_iff
  条件: (x : N)
  结论: x in (s.mapEquiv f) ↔ f.symm x in s
  证明: Submodule.mem_map_equiv (e := f.toLinearEquiv) s.toSubmodule

Depends on / 依赖: Submodule, Submodule.mem_map_equiv, f.toLinearEquiv, mem_map_equiv, s.toSubmodule, toLinearEquiv, toSubmodule
-/
lemma mem_mapEquiv_iff (x : N) : x in (s.mapEquiv f) ↔ f.symm x in s :=
  Submodule.mem_map_equiv (e := f.toLinearEquiv) s.toSubmodule

/--
lemma `mem_mapEquiv_iff'` / 引理 `mem_mapEquiv_iff'`

English:
lemma mem_mapEquiv_iff'
  given: (x : M)
  statement: f x in (s.mapEquiv f) ↔ x in s
  proof: by
  simp

@[simp]

中文:
引理 mem_mapEquiv_iff'
  条件: (x : M)
  结论: f x in (s.mapEquiv f) ↔ x in s
  证明: by
  simp

@[simp]
-/
lemma mem_mapEquiv_iff' (x : M) : f x in (s.mapEquiv f) ↔ x in s := by
  simp

@[simp]
/--
lemma `mapEquiv_bot_eq_bot` / 引理 `mapEquiv_bot_eq_bot`

English:
lemma mapEquiv_bot_eq_bot
  given: [T1Space M] [T1Space N]
  statement: ((⊥ : ClosedSubmodule R M).mapEquiv f) = ⊥
  proof: by
  ext x; simp

@[simp]

中文:
引理 mapEquiv_bot_eq_bot
  条件: [T1空间 M] [T1空间 N]
  结论: ((⊥ : 闭子模 R M).mapEquiv f) = ⊥
  证明: by
  ext x; simp

@[simp]
-/
lemma mapEquiv_bot_eq_bot [T1Space M] [T1Space N] : ((⊥ : ClosedSubmodule R M).mapEquiv f) = ⊥ := by
  ext x; simp

@[simp]
/--
lemma `mapEquiv_top_eq_top` / 引理 `mapEquiv_top_eq_top`

English:
lemma mapEquiv_top_eq_top
  statement: ((⊤ : ClosedSubmodule R M).mapEquiv f) = ⊤
  proof: by
  ext x; simp

@[simp]

中文:
引理 mapEquiv_top_eq_top
  结论: ((⊤ : 闭子模 R M).mapEquiv f) = ⊤
  证明: by
  ext x; simp

@[simp]
-/
lemma mapEquiv_top_eq_top : ((⊤ : ClosedSubmodule R M).mapEquiv f) = ⊤ := by
  ext x; simp

@[simp]
/--
lemma `mapEquiv_inf_eq` / 引理 `mapEquiv_inf_eq`

English:
lemma mapEquiv_inf_eq
  given: (f : M ≃L[R] N) {s t : ClosedSubmodule R M}
  proof: by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe, toSubmodule_inf,
    Submodule.coe_inf, Set.mem_inter_iff, mem_mapEquiv_iff, mem_inf]

中文:
引理 mapEquiv_inf_eq
  条件: (f : M ≃L[R] N) {s t : 闭子模 R M}
  证明: by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe, toSubmodule_inf,
    Submodule.coe_inf, Set.mem_inter_iff, mem_mapEquiv_iff, mem_inf]

Depends on / 依赖: Set.mem_inter_iff, SetLike, SetLike.mem_coe, Submodule, Submodule.carrier_eq_coe, Submodule.coe_inf, carrier_eq_coe, coe_inf, coe_toSubmodule, mem_coe, mem_inf, mem_inter_iff, mem_mapEquiv_iff, toSubmodule_inf
-/
lemma mapEquiv_inf_eq (f : M ≃L[R] N) {s t : ClosedSubmodule R M} :
    (s ⊓ t).mapEquiv f = s.mapEquiv f ⊓ t.mapEquiv f := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe, toSubmodule_inf,
    Submodule.coe_inf, Set.mem_inter_iff, mem_mapEquiv_iff, mem_inf]

variable [ContinuousAdd N] [ContinuousConstSMul R N] [ContinuousAdd M] [ContinuousConstSMul R M]

@[simp]
/--
lemma `closure_map_eq_mapEquiv_closure` / 引理 `closure_map_eq_mapEquiv_closure`

English:
lemma closure_map_eq_mapEquiv_closure
  given: (s : Submodule R M)
  proof: by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, Submodule.coe_closure, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, mapEquiv_apply, Set.mem_image]
  rw [← ContinuousLinearEquiv.image_closure]
  simp

@[simp]

中文:
引理 closure_map_eq_mapEquiv_closure
  条件: (s : 子模 R M)
  证明: by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, Submodule.coe_closure, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, mapEquiv_apply, Set.mem_image]
  rw [← ContinuousLinearEquiv.image_closure]
  simp

@[simp]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.image_closure, LinearEquiv, LinearEquiv.coe_coe, Set.mem_image, Submodule, Submodule.carrier_eq_coe, Submodule.coe_closure, Submodule.map_coe, carrier_eq_coe, coe_closure, coe_coe, coe_toLinearEquiv, coe_toSubmodule, image_closure, mapEquiv_apply, map_coe, mem_image
-/
lemma closure_map_eq_mapEquiv_closure (s : Submodule R M) :
    (s.map f.toLinearMap).closure = s.closure.mapEquiv f := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, Submodule.coe_closure, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, mapEquiv_apply, Set.mem_image]
  rw [← ContinuousLinearEquiv.image_closure]
  simp

@[simp]
/--
lemma `mapEquiv_sup_eq` / 引理 `mapEquiv_sup_eq`

English:
lemma mapEquiv_sup_eq
  given: (f : M ≃L[R] N) {s t : ClosedSubmodule R M}
  proof: by
  ext x
  simp only [mapEquiv_apply, toSubmodule_sup, Submodule.carrier_eq_coe, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, coe_toSubmodule,
    Submodule.coe_closure, Set.mem_image]
  have : f = f.toLinearEquiv.toLinearMap := by
    exact LinearMap.ext (congrFun rfl)
  rw [← this]; rw [← Submodule.coe_closure]; rw [← Submodule.map_sup]; rw [Submodule.map_coe]
  simp [← ContinuousLinearEquiv.image_closure]

中文:
引理 mapEquiv_sup_eq
  条件: (f : M ≃L[R] N) {s t : 闭子模 R M}
  证明: by
  ext x
  simp only [mapEquiv_apply, toSubmodule_sup, Submodule.carrier_eq_coe, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, coe_toSubmodule,
    Submodule.coe_closure, Set.mem_image]
  have : f = f.toLinearEquiv.toLinearMap := by
    exact LinearMap.ext (congrFun rfl)
  rw [← this]; rw [← Submodule.coe_closure]; rw [← Submodule.map_sup]; rw [Submodule.map_coe]
  simp [← ContinuousLinearEquiv.image_closure]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.image_closure, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.ext, Set.mem_image, Submodule, Submodule.carrier_eq_coe, Submodule.coe_closure, Submodule.map_coe, Submodule.map_sup, carrier_eq_coe, coe_closure, coe_coe, coe_toLinearEquiv, coe_toSubmodule, f.toLinearEquiv.toLinearMap, image_closure
-/
lemma mapEquiv_sup_eq (f : M ≃L[R] N) {s t : ClosedSubmodule R M} :
    (s ⊔ t).mapEquiv f = s.mapEquiv f ⊔ t.mapEquiv f := by
  ext x
  simp only [mapEquiv_apply, toSubmodule_sup, Submodule.carrier_eq_coe, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, coe_toSubmodule,
    Submodule.coe_closure, Set.mem_image]
  have : f = f.toLinearEquiv.toLinearMap := by
    exact LinearMap.ext (congrFun rfl)
  rw [← this]; rw [← Submodule.coe_closure]; rw [← Submodule.map_sup]; rw [Submodule.map_coe]
  simp [← ContinuousLinearEquiv.image_closure]

end ClosedSubmodule

section CompleteSpace

instance {𝕜 H : Type*} [Semiring 𝕜] [AddCommMonoid H] [UniformSpace H] [Module 𝕜 H]
    [CompleteSpace H] (K : ClosedSubmodule 𝕜 H) : CompleteSpace K := by
  apply IsComplete.completeSpace_coe
  rw [← ClosedSubmodule.carrier_eq_coe]
  exact K.isClosed'.isComplete

end CompleteSpace
