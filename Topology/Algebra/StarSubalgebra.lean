/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Star

/-!
# Topological star (sub)algebras

A topological star algebra over a topological semiring `R` is a topological semiring with a
compatible continuous scalar multiplication by elements of `R` and a continuous star operation.
We reuse typeclass `ContinuousSMul` for topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a star subalgebra is still a star subalgebra,
which as a star algebra is a topological star algebra.
-/

@[expose] public section

open Topology
namespace StarSubalgebra

section TopologicalStarAlgebra

variable {R A B : Type*} [CommSemiring R] [StarRing R]
variable [TopologicalSpace A] [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalSemiring
  signature: A] (s
  body: s.toSubalgebra.topologicalSemiring

中文:
实例 [是TopologicalSemiring
  签名: A] (s
  定义体: s.toSubalgebra.topologicalSemiring

Depends on / 依赖: s.toSubalgebra.topologicalSemiring, toSubalgebra, topologicalSemiring
-/
instance [IsTopologicalSemiring A] (s : StarSubalgebra R A) : IsTopologicalSemiring s :=
  s.toSubalgebra.topologicalSemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSemitopologicalSemiring
  signature: A] (s
  body: s.toSubalgebra.semitopologicalSemiring

中文:
实例 [是SemitopologicalSemiring
  签名: A] (s
  定义体: s.toSubalgebra.semitopologicalSemiring

Depends on / 依赖: s.toSubalgebra.semitopologicalSemiring, semitopologicalSemiring, toSubalgebra
-/
instance [IsSemitopologicalSemiring A] (s : StarSubalgebra R A) : IsSemitopologicalSemiring s :=
  s.toSubalgebra.semitopologicalSemiring

/--
lemma `isEmbedding_inclusion` / 引理 `isEmbedding_inclusion`

English:
lemma isEmbedding_inclusion
  given: {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂)
  proof: Eq.symm induced_compose
  injective := Subtype.map_injective h Function.injective_id

中文:
引理 isEmbedding_inclusion
  条件: {S₁ S₂ : 对合子代数 R A} (h : S₁ <= S₂)
  证明: Eq.symm induced_compose
  injective := Subtype.map_injective h Function.injective_id

Depends on / 依赖: Eq.symm, induced_compose
-/
lemma isEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) :
    IsEmbedding (inclusion h) where
  eq_induced := Eq.symm induced_compose
  injective := Subtype.map_injective h Function.injective_id

/--
theorem `isClosedEmbedding_inclusion` / 定理 `isClosedEmbedding_inclusion`

English:
theorem isClosedEmbedding_inclusion
  statement: {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂)
  proof: { IsEmbedding.inclusion h with
    isClosed_range := isClosed_induced_iff.2
      ⟨S₁, hS₁, by
          convert! (Set.range_subtype_map id _).symm
          · rw [Set.image_id]; rfl
          · intro _ h'
            apply h h' ⟩ }

中文:
定理 isClosedEmbedding_inclusion
  结论: {S₁ S₂ : 对合子代数 R A} (h : S₁ <= S₂)
  证明: { IsEmbedding.inclusion h with
    isClosed_range := isClosed_induced_iff.2
      ⟨S₁, hS₁, by
          convert! (Set.range_subtype_map id _).symm
          · rw [Set.image_id]; rfl
          · intro _ h'
            apply h h' ⟩ }

Depends on / 依赖: IsEmbedding, IsEmbedding.inclusion, Set.image_id, Set.range_subtype_map, convert, image_id, inclusion, isClosed_induced_iff, isClosed_range, range_subtype_map
-/
theorem isClosedEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂)
    (hS₁ : IsClosed (S₁ : Set A)) : IsClosedEmbedding (inclusion h) :=
  { IsEmbedding.inclusion h with
    isClosed_range := isClosed_induced_iff.2
      ⟨S₁, hS₁, by
          convert! (Set.range_subtype_map id _).symm
          · rw [Set.image_id]; rfl
          · intro _ h'
            apply h h' ⟩ }

variable [IsSemitopologicalSemiring A] [ContinuousStar A]
variable [TopologicalSpace B] [Semiring B] [Algebra R B] [StarRing B]

/--
Definition of `topologicalClosure` / `topologicalClosure` 的定义

English:
definition topologicalClosure
  signature: (s : StarSubalgebra R A)
  body: {
    s.toSubalgebra.topologicalClosure with
    carrier := closure (s : Set A)
    star_mem' := fun ha =>
      map_mem_closure continuous_star ha fun x => (star_mem : x in s -> star x in s) }

中文:
定义 topologicalClosure
  签名: (s : 对合子代数 R A)
  定义体: {
    s.toSubalgebra.topologicalClosure with
    carrier := closure (s : Set A)
    star_mem' := fun ha =>
      map_mem_closure continuous_star ha fun x => (star_mem : x in s -> star x in s) }

Depends on / 依赖: carrier, closure, continuous_star, map_mem_closure, s.toSubalgebra.topologicalClosure, star_mem, toSubalgebra, topologicalClosure
-/
def topologicalClosure (s : StarSubalgebra R A) : StarSubalgebra R A :=
  {
    s.toSubalgebra.topologicalClosure with
    carrier := closure (s : Set A)
    star_mem' := fun ha =>
      map_mem_closure continuous_star ha fun x => (star_mem : x in s -> star x in s) }

/--
theorem `topologicalClosure_toSubalgebra_comm` / 定理 `topologicalClosure_toSubalgebra_comm`

English:
theorem topologicalClosure_toSubalgebra_comm
  given: (s : StarSubalgebra R A)
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 topologicalClosure_toSubalgebra_comm
  条件: (s : 对合子代数 R A)
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem topologicalClosure_toSubalgebra_comm (s : StarSubalgebra R A) :
    s.topologicalClosure.toSubalgebra = s.toSubalgebra.topologicalClosure :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `topologicalClosure_coe` / 定理 `topologicalClosure_coe`

English:
theorem topologicalClosure_coe
  given: (s : StarSubalgebra R A)
  proof: rfl

中文:
定理 topologicalClosure_coe
  条件: (s : 对合子代数 R A)
  证明: rfl
-/
theorem topologicalClosure_coe (s : StarSubalgebra R A) :
    (s.topologicalClosure : Set A) = closure (s : Set A) :=
  rfl

/--
theorem `le_topologicalClosure` / 定理 `le_topologicalClosure`

English:
theorem le_topologicalClosure
  given: (s : StarSubalgebra R A)
  statement: s <= s.topologicalClosure
  proof: subset_closure

中文:
定理 le_topologicalClosure
  条件: (s : 对合子代数 R A)
  结论: s <= s.topologicalClosure
  证明: subset_closure

Depends on / 依赖: subset_closure
-/
theorem le_topologicalClosure (s : StarSubalgebra R A) : s <= s.topologicalClosure :=
  subset_closure

/--
theorem `isClosed_topologicalClosure` / 定理 `isClosed_topologicalClosure`

English:
theorem isClosed_topologicalClosure
  given: (s : StarSubalgebra R A)
  proof: isClosed_closure

中文:
定理 isClosed_topologicalClosure
  条件: (s : 对合子代数 R A)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem isClosed_topologicalClosure (s : StarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) :=
  isClosed_closure

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [IsSemitopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A]
    {S : StarSubalgebra R A} : CompleteSpace S.topologicalClosure :=
  isClosed_closure.completeSpace_coe

/--
theorem `topologicalClosure_minimal` / 定理 `topologicalClosure_minimal`

English:
theorem topologicalClosure_minimal
  statement: {s t : StarSubalgebra R A} (h : s <= t)
  proof: closure_minimal h ht

@[gcongr]

中文:
定理 topologicalClosure_minimal
  结论: {s t : 对合子代数 R A} (h : s <= t)
  证明: closure_minimal h ht

@[gcongr]

Depends on / 依赖: closure_minimal
-/
theorem topologicalClosure_minimal {s t : StarSubalgebra R A} (h : s <= t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure <= t :=
  closure_minimal h ht

@[gcongr]
/--
theorem `topologicalClosure_mono` / 定理 `topologicalClosure_mono`

English:
theorem topologicalClosure_mono
  statement: Monotone (topologicalClosure : _ -> StarSubalgebra R A)
  proof: fun _ S₂ h =>
  topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂) (isClosed_topologicalClosure S₂)

中文:
定理 topologicalClosure_mono
  结论: 递增 (topologicalClosure : _ -> 对合子代数 R A)
  证明: fun _ S₂ h =>
  topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂) (isClosed_topologicalClosure S₂)

Depends on / 依赖: h.trans, isClosed_topologicalClosure, le_topologicalClosure, topologicalClosure_minimal
-/
theorem topologicalClosure_mono : Monotone (topologicalClosure : _ -> StarSubalgebra R A) :=
  fun _ S₂ h =>
  topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂) (isClosed_topologicalClosure S₂)

/--
theorem `topologicalClosure_map_le` / 定理 `topologicalClosure_map_le`

English:
theorem topologicalClosure_map_le
  statement: [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
  proof: hφ.closure_image_subset _

中文:
定理 topologicalClosure_map_le
  结论: [对合模 R B] [是SemitopologicalSemiring B] [余ntinuousStar B]
  证明: hφ.closure_image_subset _

Depends on / 依赖: closure_image_subset
-/
theorem topologicalClosure_map_le [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A ->⋆ₐ[R] B) (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure <= map φ s.topologicalClosure :=
  hφ.closure_image_subset _

/--
theorem `map_topologicalClosure_le` / 定理 `map_topologicalClosure_le`

English:
theorem map_topologicalClosure_le
  statement: [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
  proof: image_closure_subset_closure_image hφ

中文:
定理 map_topologicalClosure_le
  结论: [对合模 R B] [是SemitopologicalSemiring B] [余ntinuousStar B]
  证明: image_closure_subset_closure_image hφ

Depends on / 依赖: image_closure_subset_closure_image
-/
theorem map_topologicalClosure_le [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A ->⋆ₐ[R] B) (hφ : Continuous φ) :
    map φ s.topologicalClosure <= (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ

/--
theorem `topologicalClosure_map` / 定理 `topologicalClosure_map`

English:
theorem topologicalClosure_map
  statement: [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
  proof: SetLike.coe_injective hφ.closure_image_eq_of_continuous hφ' _

中文:
定理 topologicalClosure_map
  结论: [对合模 R B] [是SemitopologicalSemiring B] [余ntinuousStar B]
  证明: SetLike.coe_injective hφ.closure_image_eq_of_continuous hφ' _

Depends on / 依赖: SetLike, SetLike.coe_injective, closure_image_eq_of_continuous, coe_injective
-/
theorem topologicalClosure_map [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A ->⋆ₐ[R] B) (hφ : IsClosedMap φ) (hφ' : Continuous φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
SetLike.coe_injective hφ.closure_image_eq_of_continuous hφ' _

variable (R) in
open StarAlgebra in
/--
lemma `topologicalClosure_adjoin_le_centralizer_centralizer` / 引理 `topologicalClosure_adjoin_le_centralizer_centralizer`

English:
lemma topologicalClosure_adjoin_le_centralizer_centralizer
  given: [T2Space A] (s : Set A)
  proof: topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

中文:
引理 topologicalClosure_adjoin_le_centralizer_centralizer
  条件: [T2空间 A] (s : 集合 A)
  证明: topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

Depends on / 依赖: Set.isClosed_centralizer, adjoin_le_centralizer_centralizer, isClosed_centralizer, topologicalClosure_minimal
-/
lemma topologicalClosure_adjoin_le_centralizer_centralizer [T2Space A] (s : Set A) :
    (adjoin R s).topologicalClosure <= centralizer R (centralizer R s) :=
  topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

/--
theorem `_root_.Subalgebra.topologicalClosure_star_comm` / 定理 `_root_.Subalgebra.topologicalClosure_star_comm`

English:
theorem _root_.Subalgebra.topologicalClosure_star_comm
  given: (s : Subalgebra R A)
  proof: by
  suffices forall t : Subalgebra R A, (star t).topologicalClosure <= star t.topologicalClosure from
    le_antisymm (this s) (by simpa only [star_star] using Subalgebra.star_mono (this (star s)))
  exact fun t => (star t).topologicalClosure_minimal (Subalgebra.star_mono subset_closure)
    (isClosed_closure.preimage continuous_star)

中文:
定理 _root_.子代数.topologicalClosure_star_comm
  条件: (s : 子代数 R A)
  证明: by
  suffices forall t : Subalgebra R A, (star t).topologicalClosure <= star t.topologicalClosure from
    le_antisymm (this s) (by simpa only [star_star] using Subalgebra.star_mono (this (star s)))
  exact fun t => (star t).topologicalClosure_minimal (Subalgebra.star_mono subset_closure)
    (isClosed_closure.preimage continuous_star)

Depends on / 依赖: Subalgebra, Subalgebra.star_mono, continuous_star, isClosed_closure, isClosed_closure.preimage, le_antisymm, preimage, star_mono, star_star, subset_closure, t.topologicalClosure, topologicalClosure, topologicalClosure_minimal
-/
theorem _root_.Subalgebra.topologicalClosure_star_comm (s : Subalgebra R A) :
    (star s).topologicalClosure = star s.topologicalClosure := by
  suffices forall t : Subalgebra R A, (star t).topologicalClosure <= star t.topologicalClosure from
    le_antisymm (this s) (by simpa only [star_star] using Subalgebra.star_mono (this (star s)))
  exact fun t => (star t).topologicalClosure_minimal (Subalgebra.star_mono subset_closure)
    (isClosed_closure.preimage continuous_star)

/--
Definition of `commSemiringTopologicalClosure` / `commSemiringTopologicalClosure` 的定义

English:
abbreviation commSemiringTopologicalClosure
  signature: [T2Space A] (s : StarSubalgebra R A)
  body: fast_instance% s.toSubalgebra.commSemiringTopologicalClosure hs

中文:
缩写 commSemiringTopologicalClosure
  签名: [T2空间 A] (s : 对合子代数 R A)
  定义体: fast_instance% s.toSubalgebra.commSemiringTopologicalClosure hs

Depends on / 依赖: commSemiringTopologicalClosure, fast_instance, s.toSubalgebra.commSemiringTopologicalClosure, toSubalgebra
-/
abbrev commSemiringTopologicalClosure [T2Space A] (s : StarSubalgebra R A)
    (hs : forall x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  fast_instance% s.toSubalgebra.commSemiringTopologicalClosure hs

/--
Definition of `commRingTopologicalClosure` / `commRingTopologicalClosure` 的定义

English:
abbreviation commRingTopologicalClosure
  signature: {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A]
  body: fast_instance% s.toSubalgebra.commRingTopologicalClosure hs

中文:
缩写 commRingTopologicalClosure
  签名: {R A} [交换环 R] [对合环 R] [拓扑空间 A] [环 A]
  定义体: fast_instance% s.toSubalgebra.commRingTopologicalClosure hs

Depends on / 依赖: commRingTopologicalClosure, fast_instance, s.toSubalgebra.commRingTopologicalClosure, toSubalgebra
-/
abbrev commRingTopologicalClosure {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] [IsSemitopologicalRing A] [ContinuousStar A]
    [T2Space A] (s : StarSubalgebra R A) (hs : forall x y : s, x * y = y * x) :
    CommRing s.topologicalClosure :=
  fast_instance% s.toSubalgebra.commRingTopologicalClosure hs

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.StarAlgHom.ext_topologicalClosure` / 定理 `_root_.StarAlgHom.ext_topologicalClosure`

English:
theorem _root_.StarAlgHom.ext_topologicalClosure
  statement: [T2Space B] {S : StarSubalgebra R A}
  proof: by
  rw [DFunLike.ext'_iff]
  have : DenseRange (Set.inclusion (le_topologicalClosure S)) := by simp [-SetLike.coe_sort_coe]
  refine Continuous.ext_on this hφ hψ ?_
  rintro _ ⟨x, rfl⟩
  simpa only using! DFunLike.congr_fun h x

中文:
定理 _root_.StarAlg态射.ext_topologicalClosure
  结论: [T2空间 B] {S : 对合子代数 R A}
  证明: by
  rw [DFunLike.ext'_iff]
  have : DenseRange (Set.inclusion (le_topologicalClosure S)) := by simp [-SetLike.coe_sort_coe]
  refine Continuous.ext_on this hφ hψ ?_
  rintro _ ⟨x, rfl⟩
  simpa only using! DFunLike.congr_fun h x

Depends on / 依赖: Continuous, Continuous.ext_on, DFunLike, DFunLike.congr_fun, DFunLike.ext, DenseRange, Set.inclusion, SetLike, SetLike.coe_sort_coe, _iff, coe_sort_coe, congr_fun, ext_on, inclusion, le_topologicalClosure
-/
theorem _root_.StarAlgHom.ext_topologicalClosure [T2Space B] {S : StarSubalgebra R A}
    {φ ψ : S.topologicalClosure ->⋆ₐ[R] B} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h :
      φ.comp (inclusion (le_topologicalClosure S)) = ψ.comp (inclusion (le_topologicalClosure S))) :
    φ = ψ := by
  rw [DFunLike.ext'_iff]
  have : DenseRange (Set.inclusion (le_topologicalClosure S)) := by simp [-SetLike.coe_sort_coe]
  refine Continuous.ext_on this hφ hψ ?_
  rintro _ ⟨x, rfl⟩
  simpa only using! DFunLike.congr_fun h x

/--
theorem `_root_.StarAlgHomClass.ext_topologicalClosure` / 定理 `_root_.StarAlgHomClass.ext_topologicalClosure`

English:
theorem _root_.StarAlgHomClass.ext_topologicalClosure
  statement: [T2Space B] {F : Type*}
  proof: by
  have : (φ : S.topologicalClosure ->⋆ₐ[R] B) = (ψ : S.topologicalClosure ->⋆ₐ[R] B) := by
    refine StarAlgHom.ext_topologicalClosure (R := R) (A := A) (B := B) hφ hψ (StarAlgHom.ext ?_)
    simpa only [StarAlgHom.coe_comp, StarAlgHom.coe_coe] using! h
  rw [DFunLike.ext'_iff]; rw [← StarAlgHom.coe_coe]
  apply congrArg _ this

中文:
定理 _root_.StarAlgHomClass.ext_topologicalClosure
  结论: [T2空间 B] {F : 类型}
  证明: by
  have : (φ : S.topologicalClosure ->⋆ₐ[R] B) = (ψ : S.topologicalClosure ->⋆ₐ[R] B) := by
    refine StarAlgHom.ext_topologicalClosure (R := R) (A := A) (B := B) hφ hψ (StarAlgHom.ext ?_)
    simpa only [StarAlgHom.coe_comp, StarAlgHom.coe_coe] using! h
  rw [DFunLike.ext'_iff]; rw [← StarAlgHom.coe_coe]
  apply congrArg _ this

Depends on / 依赖: DFunLike, DFunLike.ext, S.topologicalClosure, StarAlgHom, StarAlgHom.coe_coe, StarAlgHom.coe_comp, StarAlgHom.ext, StarAlgHom.ext_topologicalClosure, _iff, coe_coe, coe_comp, ext_topologicalClosure, topologicalClosure
-/
theorem _root_.StarAlgHomClass.ext_topologicalClosure [T2Space B] {F : Type*}
    {S : StarSubalgebra R A} [FunLike F S.topologicalClosure B]
    [AlgHomClass F R S.topologicalClosure B] [StarHomClass F S.topologicalClosure B] {φ ψ : F}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : forall x : S,
        φ (inclusion (le_topologicalClosure S) x) = ψ ((inclusion (le_topologicalClosure S)) x)) :
    φ = ψ := by
  have : (φ : S.topologicalClosure ->⋆ₐ[R] B) = (ψ : S.topologicalClosure ->⋆ₐ[R] B) := by
    refine StarAlgHom.ext_topologicalClosure (R := R) (A := A) (B := B) hφ hψ (StarAlgHom.ext ?_)
    simpa only [StarAlgHom.coe_comp, StarAlgHom.coe_coe] using! h
  rw [DFunLike.ext'_iff]; rw [← StarAlgHom.coe_coe]
  apply congrArg _ this

end TopologicalStarAlgebra

end StarSubalgebra

section Elemental

namespace StarAlgebra

open StarSubalgebra

variable (R : Type*) {A B : Type*} [CommSemiring R] [StarRing R]
variable [TopologicalSpace A] [Semiring A] [StarRing A] [IsSemitopologicalSemiring A]
variable [ContinuousStar A] [Algebra R A] [StarModule R A]
variable [TopologicalSpace B] [Semiring B] [StarRing B] [Algebra R B]

/--
Definition of `elemental` / `elemental` 的定义

English:
definition elemental
  signature: (x : A)
  body: (adjoin R ({x} : Set A)).topologicalClosure

中文:
定义 elemental
  签名: (x : A)
  定义体: (adjoin R ({x} : Set A)).topologicalClosure

Depends on / 依赖: adjoin, topologicalClosure
-/
def elemental (x : A) : StarSubalgebra R A :=
  (adjoin R ({x} : Set A)).topologicalClosure

namespace elemental

@[simp, aesop safe (rule_sets := [SetLike])]
/--
theorem `self_mem` / 定理 `self_mem`

English:
theorem self_mem
  given: (x : A)
  statement: x in elemental R x
  proof: le_topologicalClosure _ (self_mem_adjoin_singleton R x)

@[simp, aesop safe (rule_sets := [SetLike])]

中文:
定理 self_mem
  条件: (x : A)
  结论: x in elemental R x
  证明: le_topologicalClosure _ (self_mem_adjoin_singleton R x)

@[simp, aesop safe (rule_sets := [SetLike])]

Depends on / 依赖: le_topologicalClosure, self_mem_adjoin_singleton
-/
theorem self_mem (x : A) : x in elemental R x :=
  le_topologicalClosure _ (self_mem_adjoin_singleton R x)

@[simp, aesop safe (rule_sets := [SetLike])]
/--
theorem `star_self_mem` / 定理 `star_self_mem`

English:
theorem star_self_mem
  given: (x : A)
  statement: star x in elemental R x
  proof: star_mem self_mem R x

中文:
定理 star_self_mem
  条件: (x : A)
  结论: star x in elemental R x
  证明: star_mem self_mem R x

Depends on / 依赖: self_mem, star_mem
-/
theorem star_self_mem (x : A) : star x in elemental R x :=
star_mem self_mem R x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: A] {x
  body: fast_instance% StarSubalgebra.commSemiringTopologicalClosure _ mul_comm

中文:
实例 [T2空间
  签名: A] {x
  定义体: fast_instance% StarSubalgebra.commSemiringTopologicalClosure _ mul_comm

Depends on / 依赖: StarSubalgebra, StarSubalgebra.commSemiringTopologicalClosure, commSemiringTopologicalClosure, fast_instance, mul_comm
-/
instance [T2Space A] {x : A} [IsStarNormal x] : CommSemiring (elemental R x) :=
  fast_instance% StarSubalgebra.commSemiringTopologicalClosure _ mul_comm

/-- The `elemental` generated by a normal element is commutative. -/
instance {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A] [Algebra R A] [StarRing A]
    [StarModule R A] [IsSemitopologicalRing A] [ContinuousStar A] [T2Space A] {x : A}
    [IsStarNormal x] : CommRing (elemental R x) :=
  fast_instance% StarSubalgebra.commRingTopologicalClosure _ mul_comm

/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: (x : A)
  statement: IsClosed (elemental R x : Set A)
  proof: isClosed_closure

中文:
定理 isClosed
  条件: (x : A)
  结论: 是闭集 (elemental R x : 集合 A)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_closure

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [IsSemitopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

variable {R} in
/--
theorem `le_of_mem` / 定理 `le_of_mem`

English:
theorem le_of_mem
  statement: {S : StarSubalgebra R A} (hS : IsClosed (S : Set A)) {x : A}
  proof: topologicalClosure_minimal (adjoin_le <| Set.singleton_subset_iff.2 hx) hS

中文:
定理 le_of_mem
  结论: {S : 对合子代数 R A} (hS : 是闭集 (S : 集合 A)) {x : A}
  证明: topologicalClosure_minimal (adjoin_le <| Set.singleton_subset_iff.2 hx) hS

Depends on / 依赖: Set.singleton_subset_iff, adjoin_le, singleton_subset_iff, topologicalClosure_minimal
-/
theorem le_of_mem {S : StarSubalgebra R A} (hS : IsClosed (S : Set A)) {x : A}
    (hx : x in S) : elemental R x <= S :=
  topologicalClosure_minimal (adjoin_le <| Set.singleton_subset_iff.2 hx) hS

variable {R} in
/--
theorem `le_iff_mem` / 定理 `le_iff_mem`

English:
theorem le_iff_mem
  given: {x : A} {s : StarSubalgebra R A} (hs : IsClosed (s : Set A))
  proof: ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

中文:
定理 le_iff_mem
  条件: {x : A} {s : 对合子代数 R A} (hs : 是闭集 (s : 集合 A))
  证明: ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

Depends on / 依赖: le_of_mem, self_mem
-/
theorem le_iff_mem {x : A} {s : StarSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x <= s ↔ x in s :=
  ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

/--
theorem `isClosedEmbedding_coe` / 定理 `isClosedEmbedding_coe`

English:
theorem isClosedEmbedding_coe
  given: (x : A)
  statement: IsClosedEmbedding ((↑) : elemental R x -> A) where
  proof: rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

中文:
定理 isClosedEmbedding_coe
  条件: (x : A)
  结论: 是闭嵌入 ((↑) : elemental R x -> A) where
  证明: rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x
-/
theorem isClosedEmbedding_coe (x : A) : IsClosedEmbedding ((↑) : elemental R x -> A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

/--
lemma `le_centralizer_centralizer` / 引理 `le_centralizer_centralizer`

English:
lemma le_centralizer_centralizer
  given: [T2Space A] (x : A)
  proof: topologicalClosure_adjoin_le_centralizer_centralizer ..

@[elab_as_elim]

中文:
引理 le_centralizer_centralizer
  条件: [T2空间 A] (x : A)
  证明: topologicalClosure_adjoin_le_centralizer_centralizer ..

@[elab_as_elim]

Depends on / 依赖: topologicalClosure_adjoin_le_centralizer_centralizer
-/
lemma le_centralizer_centralizer [T2Space A] (x : A) :
    elemental R x <= centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer ..

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {x y : A}
  proof: by
  apply closure (adjoin R {x} : Set A) subset_closure (fun y hy => ?_) y hy
  rw [SetLike.mem_coe]; rw [← mem_toSubalgebra]; rw [adjoin_toSubalgebra] at hy
  induction hy using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ((rfl : u = x) | (hu : star u = x)) := by simpa using hu
    · exact self
    · simp_rw [← hu, star_star] at star_self
      exact star_self
  | algebraMap r => exact algebraMap r
  | add u v hu_mem hv_mem hu hv =>
    exact add u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)
  | mul u v hu_mem hv_mem hu hv =>
    exact mul u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)

中文:
定理 induction_on
  结论: {x y : A}
  证明: by
  apply closure (adjoin R {x} : Set A) subset_closure (fun y hy => ?_) y hy
  rw [SetLike.mem_coe]; rw [← mem_toSubalgebra]; rw [adjoin_toSubalgebra] at hy
  induction hy using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ((rfl : u = x) | (hu : star u = x)) := by simpa using hu
    · exact self
    · simp_rw [← hu, star_star] at star_self
      exact star_self
  | algebraMap r => exact algebraMap r
  | add u v hu_mem hv_mem hu hv =>
    exact add u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)
  | mul u v hu_mem hv_mem hu hv =>
    exact mul u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)

Depends on / 依赖: Algebra, Algebra.adjoin_induction, SetLike, SetLike.mem_coe, adjoin, adjoin_induction, adjoin_toSubalgebra, algebraMap, closure, hu_mem, hv_mem, mem_coe, mem_toSubalgebra, simp_rw, star_self, star_star, subset_closure
-/
theorem induction_on {x y : A}
    (hy : y in elemental R x) {P : (u : A) -> u in elemental R x -> Prop}
    (self : P x (self_mem R x)) (star_self : P (star x) (star_self_mem R x))
    (algebraMap : forall r, P (algebraMap R A r) (algebraMap_mem _ r))
    (add : forall u hu v hv, P u hu -> P v hv -> P (u + v) (add_mem hu hv))
    (mul : forall u hu v hv, P u hu -> P v hv -> P (u * v) (mul_mem hu hv))
    (closure : forall s : Set A, (hs : s subseteq elemental R x) -> (forall u, (hu : u in s) ->
      P u (hs hu)) -> forall v, (hv : v in closure s) -> P v (closure_minimal hs (isClosed R x) hv)) :
    P y hy := by
  apply closure (adjoin R {x} : Set A) subset_closure (fun y hy => ?_) y hy
  rw [SetLike.mem_coe]; rw [← mem_toSubalgebra]; rw [adjoin_toSubalgebra] at hy
  induction hy using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ((rfl : u = x) | (hu : star u = x)) := by simpa using hu
    · exact self
    · simp_rw [← hu, star_star] at star_self
      exact star_self
  | algebraMap r => exact algebraMap r
  | add u v hu_mem hv_mem hu hv =>
    exact add u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)
  | mul u v hu_mem hv_mem hu hv =>
    exact mul u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `starAlgHomClass_ext` / 定理 `starAlgHomClass_ext`

English:
theorem starAlgHomClass_ext
  statement: [T2Space B] {F : Type*} {a : A}
  proof: by
  refine StarAlgHomClass.ext_topologicalClosure hφ hψ fun x => ?_
  refine adjoin_induction_subtype x ?_ ?_ ?_ ?_ ?_
  exacts [fun y hy => by simpa only [Set.mem_singleton_iff.mp hy] using! h, fun r => by
    simp only [AlgHomClass.commutes], fun x y hx hy => by simp only [map_add, hx, hy],
    fun x y hx hy => by simp only [map_mul, hx, hy], fun x hx => by simp only [map_star, hx]]

中文:
定理 starAlgHomClass_ext
  结论: [T2空间 B] {F : 类型} {a : A}
  证明: by
  refine StarAlgHomClass.ext_topologicalClosure hφ hψ fun x => ?_
  refine adjoin_induction_subtype x ?_ ?_ ?_ ?_ ?_
  exacts [fun y hy => by simpa only [Set.mem_singleton_iff.mp hy] using! h, fun r => by
    simp only [AlgHomClass.commutes], fun x y hx hy => by simp only [map_add, hx, hy],
    fun x y hx hy => by simp only [map_mul, hx, hy], fun x hx => by simp only [map_star, hx]]

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, Set.mem_singleton_iff.mp, StarAlgHomClass, StarAlgHomClass.ext_topologicalClosure, adjoin_induction_subtype, commutes, exacts, ext_topologicalClosure, map_add, map_mul, map_star, mem_singleton_iff
-/
theorem starAlgHomClass_ext [T2Space B] {F : Type*} {a : A}
    [FunLike F (elemental R a) B] [AlgHomClass F R _ B] [StarHomClass F _ B]
    {φ ψ : F} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : φ ⟨a, self_mem R a⟩ = ψ ⟨a, self_mem R a⟩) : φ = ψ := by
  refine StarAlgHomClass.ext_topologicalClosure hφ hψ fun x => ?_
  refine adjoin_induction_subtype x ?_ ?_ ?_ ?_ ?_
  exacts [fun y hy => by simpa only [Set.mem_singleton_iff.mp hy] using! h, fun r => by
    simp only [AlgHomClass.commutes], fun x y hx hy => by simp only [map_add, hx, hy],
    fun x y hx hy => by simp only [map_mul, hx, hy], fun x hx => by simp only [map_star, hx]]

end elemental

end StarAlgebra

end Elemental
