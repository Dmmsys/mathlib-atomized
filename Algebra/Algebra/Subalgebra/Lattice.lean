/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Complete lattice structure of subalgebras

In this file we define `Algebra.adjoin` and the complete lattice structure on subalgebras.

More lemmas about `adjoin` can be found in `Mathlib/RingTheory/Adjoin/Basic.lean`.
-/

@[expose] public section

assert_not_exists Polynomial

universe u u' v w w'

namespace Algebra

variable (R : Type u) {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The minimal subalgebra that includes `s`. -/
@[simps -isSimp toSubsemiring]
/--
Definition of `adjoin` / `adjoin` 的定义

English:
definition adjoin
  signature: (s : Set A)
  body: { Subsemiring.closure (Set.range (algebraMap R A) union s) with
algebraMap_mem' := fun r => Subsemiring.subset_closure Or.inl ⟨r, rfl⟩ }

中文:
定义 adjoin
  签名: (s : 集合 A)
  定义体: { Subsemiring.closure (Set.range (algebraMap R A) union s) with
algebraMap_mem' := fun r => Subsemiring.subset_closure Or.inl ⟨r, rfl⟩ }

Depends on / 依赖: Or.inl, Set.range, Subsemiring, Subsemiring.closure, Subsemiring.subset_closure, algebraMap, algebraMap_mem, closure, subset_closure, toNonUnitalAlgHom
-/
def adjoin (s : Set A) : Subalgebra R A :=
  { Subsemiring.closure (Set.range (algebraMap R A) union s) with
algebraMap_mem' := fun r => Subsemiring.subset_closure Or.inl ⟨r, rfl⟩ }

variable {R}

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection (adjoin R : Set A -> Subalgebra R A) (↑)
  proof: fun s S =>
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subsemiring.subset_closure) H,
   fun H => show Subsemiring.closure (Set.range (algebraMap R A) union s) <= S.toSubsemiring from
Subsemiring.closure_le.2 Set.union_subset S.range_subset H⟩

中文:
定理 gc
  结论: GaloisConnection (adjoin R : 集合 A -> 子代数 R A) (↑)
  证明: fun s S =>
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subsemiring.subset_closure) H,
   fun H => show Subsemiring.closure (Set.range (algebraMap R A) union s) <= S.toSubsemiring from
Subsemiring.closure_le.2 Set.union_subset S.range_subset H⟩
-/
protected theorem gc : GaloisConnection (adjoin R : Set A -> Subalgebra R A) (↑) := fun s S =>
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subsemiring.subset_closure) H,
   fun H => show Subsemiring.closure (Set.range (algebraMap R A) union s) <= S.toSubsemiring from
Subsemiring.closure_le.2 Set.union_subset S.range_subset H⟩

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (adjoin R : Set A -> Subalgebra R A) (↑) where
  body: (adjoin R s).copy s le_antisymm (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
le_l_u S := (Algebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := Subalgebra.copy_eq _ _ _

中文:
定义 gi
  签名: : Galois嵌入 (adjoin R : 集合 A -> 子代数 R A) (↑) where
  定义体: (adjoin R s).copy s le_antisymm (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
le_l_u S := (Algebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := Subalgebra.copy_eq _ _ _
-/
protected def gi : GaloisInsertion (adjoin R : Set A -> Subalgebra R A) (↑) where
choice s hs := (adjoin R s).copy s le_antisymm (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
le_l_u S := (Algebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := Subalgebra.copy_eq _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subalgebra R A)
  body: GaloisInsertion.liftCompleteLattice Algebra.gi
  bot := (Algebra.ofId R A).range
  bot_le _S := fun _a ⟨_r, hr⟩ => hr ▸ algebraMap_mem _ _

中文:
实例 :
  签名: 完备格 (子代数 R A)
  定义体: GaloisInsertion.liftCompleteLattice Algebra.gi
  bot := (Algebra.ofId R A).range
  bot_le _S := fun _a ⟨_r, hr⟩ => hr ▸ algebraMap_mem _ _

Depends on / 依赖: Algebra, Algebra.gi, GaloisInsertion, GaloisInsertion.liftCompleteLattice, liftCompleteLattice
-/
instance : CompleteLattice (Subalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice Algebra.gi
  bot := (Algebra.ofId R A).range
  bot_le _S := fun _a ⟨_r, hr⟩ => hr ▸ algebraMap_mem _ _

instance {C : Type*} [CommSemiring C] [Algebra R C] (S₁ S₂ : Subalgebra R C) :
  Algebra ↑(min S₁ S₂) S₁ := RingHom.toAlgebra (Subalgebra.inclusion inf_le_left).toRingHom

instance {C : Type*} [CommSemiring C] [Algebra R C] (S₁ S₂ : Subalgebra R C) :
  Algebra ↑(S₁ ⊓ S₂) S₂ := RingHom.toAlgebra (Subalgebra.inclusion inf_le_right).toRingHom

/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  given: (S T : Subalgebra R A)
  statement: S ⊔ T = adjoin R (S union T : Set A)
  proof: rfl

中文:
定理 sup_def
  条件: (S T : 子代数 R A)
  结论: S ⊔ T = adjoin R (S union T : 集合 A)
  证明: rfl
-/
theorem sup_def (S T : Subalgebra R A) : S ⊔ T = adjoin R (S union T : Set A) := rfl

/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: (S : Set (Subalgebra R A))
  statement: sSup S = adjoin R (⋃₀ (SetLike.coe '' S))
  proof: rfl

@[simp, norm_cast]

中文:
定理 sSup_def
  条件: (S : 集合 (子代数 R A))
  结论: sSup S = adjoin R (⋃₀ (集合状.coe '' S))
  证明: rfl

@[simp, norm_cast]
-/
theorem sSup_def (S : Set (Subalgebra R A)) : sSup S = adjoin R (⋃₀ (SetLike.coe '' S)) := rfl

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: (↑(⊤ : Subalgebra R A) : Set A) = Set.univ
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: (↑(⊤ : 子代数 R A) : 集合 A) = 集合.univ
  证明: rfl

@[simp]
-/
theorem coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ := rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: {x : A}
  statement: x in (⊤ : Subalgebra R A)
  proof: Set.mem_univ x

@[simp]

中文:
定理 mem_top
  条件: {x : A}
  结论: x in (⊤ : 子代数 R A)
  证明: Set.mem_univ x

@[simp]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top {x : A} : x in (⊤ : Subalgebra R A) := Set.mem_univ x

@[simp]
/--
theorem `top_toSubmodule` / 定理 `top_toSubmodule`

English:
theorem top_toSubmodule
  statement: Subalgebra.toSubmodule (⊤ : Subalgebra R A) = ⊤
  proof: rfl

@[simp]

中文:
定理 top_toSubmodule
  结论: 子代数.toSubmodule (⊤ : 子代数 R A) = ⊤
  证明: rfl

@[simp]
-/
theorem top_toSubmodule : Subalgebra.toSubmodule (⊤ : Subalgebra R A) = ⊤ := rfl

@[simp]
/--
theorem `top_toSubsemiring` / 定理 `top_toSubsemiring`

English:
theorem top_toSubsemiring
  statement: (⊤ : Subalgebra R A).toSubsemiring = ⊤
  proof: rfl

@[simp]

中文:
定理 top_toSubsemiring
  结论: (⊤ : 子代数 R A).toSubsemiring = ⊤
  证明: rfl

@[simp]
-/
theorem top_toSubsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤ := rfl

@[simp]
/--
theorem `top_toSubring` / 定理 `top_toSubring`

English:
theorem top_toSubring
  given: {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  proof: rfl

@[simp]

中文:
定理 top_toSubring
  条件: {R A : 类型} [交换环 R] [环 A] [代数 R A]
  证明: rfl

@[simp]
-/
theorem top_toSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    (⊤ : Subalgebra R A).toSubring = ⊤ := rfl

@[simp]
/--
theorem `toSubmodule_eq_top` / 定理 `toSubmodule_eq_top`

English:
theorem toSubmodule_eq_top
  given: {S : Subalgebra R A}
  statement: Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤
  proof: Subalgebra.toSubmodule.injective.eq_iff' top_toSubmodule

@[simp]

中文:
定理 toSubmodule_eq_top
  条件: {S : 子代数 R A}
  结论: 子代数.toSubmodule S = ⊤ ↔ S = ⊤
  证明: Subalgebra.toSubmodule.injective.eq_iff' top_toSubmodule

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.toSubmodule.injective.eq_iff, eq_iff, injective, toSubmodule, top_toSubmodule
-/
theorem toSubmodule_eq_top {S : Subalgebra R A} : Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubmodule.injective.eq_iff' top_toSubmodule

@[simp]
/--
theorem `toSubsemiring_eq_top` / 定理 `toSubsemiring_eq_top`

English:
theorem toSubsemiring_eq_top
  given: {S : Subalgebra R A}
  statement: S.toSubsemiring = ⊤ ↔ S = ⊤
  proof: Subalgebra.toSubsemiring_injective.eq_iff' top_toSubsemiring

@[simp]

中文:
定理 toSubsemiring_eq_top
  条件: {S : 子代数 R A}
  结论: S.toSubsemiring = ⊤ ↔ S = ⊤
  证明: Subalgebra.toSubsemiring_injective.eq_iff' top_toSubsemiring

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.toSubsemiring_injective.eq_iff, eq_iff, toSubsemiring_injective, top_toSubsemiring
-/
theorem toSubsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubsemiring_injective.eq_iff' top_toSubsemiring

@[simp]
/--
theorem `toSubring_eq_top` / 定理 `toSubring_eq_top`

English:
theorem toSubring_eq_top
  given: {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Subalgebra R A}
  proof: Subalgebra.toSubring_injective.eq_iff' top_toSubring

中文:
定理 toSubring_eq_top
  条件: {R A : 类型} [交换环 R] [环 A] [代数 R A] {S : 子代数 R A}
  证明: Subalgebra.toSubring_injective.eq_iff' top_toSubring

Depends on / 依赖: Subalgebra, Subalgebra.toSubring_injective.eq_iff, eq_iff, toSubring_injective, top_toSubring
-/
theorem toSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Subalgebra R A} :
    S.toSubring = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubring_injective.eq_iff' top_toSubring

/--
theorem `mem_sup_left` / 定理 `mem_sup_left`

English:
theorem mem_sup_left
  given: {S T : Subalgebra R A}
  statement: forall {x : A}, x in S -> x in S ⊔ T
  proof: have : S <= S ⊔ T := le_sup_left; (this ·)

中文:
定理 mem_sup_left
  条件: {S T : 子代数 R A}
  结论: 对任意 {x : A}, x in S -> x in S ⊔ T
  证明: have : S <= S ⊔ T := le_sup_left; (this ·)

Depends on / 依赖: le_sup_left
-/
theorem mem_sup_left {S T : Subalgebra R A} : forall {x : A}, x in S -> x in S ⊔ T :=
  have : S <= S ⊔ T := le_sup_left; (this ·)

/--
theorem `mem_sup_right` / 定理 `mem_sup_right`

English:
theorem mem_sup_right
  given: {S T : Subalgebra R A}
  statement: forall {x : A}, x in T -> x in S ⊔ T
  proof: have : T <= S ⊔ T := le_sup_right; (this ·)

中文:
定理 mem_sup_right
  条件: {S T : 子代数 R A}
  结论: 对任意 {x : A}, x in T -> x in S ⊔ T
  证明: have : T <= S ⊔ T := le_sup_right; (this ·)

Depends on / 依赖: le_sup_right
-/
theorem mem_sup_right {S T : Subalgebra R A} : forall {x : A}, x in T -> x in S ⊔ T :=
  have : T <= S ⊔ T := le_sup_right; (this ·)

/--
theorem `mul_mem_sup` / 定理 `mul_mem_sup`

English:
theorem mul_mem_sup
  given: {S T : Subalgebra R A} {x y : A} (hx : x in S) (hy : y in T)
  statement: x * y in S ⊔ T
  proof: (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

中文:
定理 mul_mem_sup
  条件: {S T : 子代数 R A} {x y : A} (hx : x in S) (hy : y in T)
  结论: x * y in S ⊔ T
  证明: (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

Depends on / 依赖: mem_sup_left, mem_sup_right, mul_mem
-/
theorem mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x in S) (hy : y in T) : x * y in S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (f : A ->ₐ[R] B) (S T : Subalgebra R A)
  statement: (S ⊔ T).map f = S.map f ⊔ T.map f
  proof: (Subalgebra.gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (f : A ->ₐ[R] B) (S T : 子代数 R A)
  结论: (S ⊔ T).map f = S.map f ⊔ T.map f
  证明: (Subalgebra.gc_map_comap f).l_sup

Depends on / 依赖: Subalgebra, Subalgebra.gc_map_comap, gc_map_comap, l_sup
-/
theorem map_sup (f : A ->ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (Subalgebra.gc_map_comap f).l_sup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (f : A ->ₐ[R] B) (hf : Function.Injective f) (S T : Subalgebra R A)
  proof: SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]

中文:
定理 map_inf
  条件: (f : A ->ₐ[R] B) (hf : 函数.单射 f) (S T : 子代数 R A)
  证明: SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (f : A ->ₐ[R] B) (hf : Function.Injective f) (S T : Subalgebra R A) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (S T : Subalgebra R A)
  statement: (↑(S ⊓ T) : Set A) = (S inter T : Set A)
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (S T : 子代数 R A)
  结论: (↑(S ⊓ T) : 集合 A) = (S inter T : 集合 A)
  证明: rfl

@[simp]
-/
theorem coe_inf (S T : Subalgebra R A) : (↑(S ⊓ T) : Set A) = (S inter T : Set A) := rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {S T : Subalgebra R A} {x : A}
  statement: x in S ⊓ T ↔ x in S ∧ x in T
  proof: Iff.rfl

中文:
定理 mem_inf
  条件: {S T : 子代数 R A} {x : A}
  结论: x in S ⊓ T ↔ x in S ∧ x in T
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {S T : Subalgebra R A} {x : A} : x in S ⊓ T ↔ x in S ∧ x in T := Iff.rfl

open Subalgebra in
@[simp]
/--
theorem `inf_toSubmodule` / 定理 `inf_toSubmodule`

English:
theorem inf_toSubmodule
  given: (S T : Subalgebra R A)
  proof: rfl

@[simp]

中文:
定理 inf_toSubmodule
  条件: (S T : 子代数 R A)
  证明: rfl

@[simp]
-/
theorem inf_toSubmodule (S T : Subalgebra R A) :
    toSubmodule (S ⊓ T) = toSubmodule S ⊓ toSubmodule T := rfl

@[simp]
/--
theorem `inf_toSubsemiring` / 定理 `inf_toSubsemiring`

English:
theorem inf_toSubsemiring
  given: (S T : Subalgebra R A)
  proof: rfl

@[simp]

中文:
定理 inf_toSubsemiring
  条件: (S T : 子代数 R A)
  证明: rfl

@[simp]
-/
theorem inf_toSubsemiring (S T : Subalgebra R A) :
    (S ⊓ T).toSubsemiring = S.toSubsemiring ⊓ T.toSubsemiring :=
  rfl

@[simp]
/--
theorem `sup_toSubsemiring` / 定理 `sup_toSubsemiring`

English:
theorem sup_toSubsemiring
  given: (S T : Subalgebra R A)
  proof: by
  rw [← S.toSubsemiring.closure_eq]; rw [← T.toSubsemiring.closure_eq]; rw [← Subsemiring.closure_union]
  simp_rw [sup_def, adjoin_toSubsemiring, Subalgebra.coe_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_

中文:
定理 sup_toSubsemiring
  条件: (S T : 子代数 R A)
  证明: by
  rw [← S.toSubsemiring.closure_eq]; rw [← T.toSubsemiring.closure_eq]; rw [← Subsemiring.closure_union]
  simp_rw [sup_def, adjoin_toSubsemiring, Subalgebra.coe_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_

Depends on / 依赖: S.toSubsemiring.closure_eq, Set.mem_union_left, Set.union_eq_right, Subalgebra, Subalgebra.coe_toSubsemiring, Subsemiring, Subsemiring.closure_union, T.toSubsemiring.closure_eq, adjoin_toSubsemiring, algebraMap_mem, closure_eq, closure_union, coe_toSubsemiring, mem_union_left, simp_rw, sup_def, toSubsemiring, union_eq_right
-/
theorem sup_toSubsemiring (S T : Subalgebra R A) :
    (S ⊔ T).toSubsemiring = S.toSubsemiring ⊔ T.toSubsemiring := by
  rw [← S.toSubsemiring.closure_eq]; rw [← T.toSubsemiring.closure_eq]; rw [← Subsemiring.closure_union]
  simp_rw [sup_def, adjoin_toSubsemiring, Subalgebra.coe_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (Subalgebra R A))
  statement: (↑(sInf S) : Set A) = ⋂ s in S, ↑s
  proof: sInf_image

@[simp]

中文:
定理 coe_sInf
  条件: (S : 集合 (子代数 R A))
  结论: (↑(sInf S) : 集合 A) = ⋂ s in S, ↑s
  证明: sInf_image

@[simp]

Depends on / 依赖: sInf_image
-/
theorem coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s in S, ↑s :=
  sInf_image

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (Subalgebra R A)} {x : A}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]

中文:
定理 mem_sInf
  条件: {S : 集合 (子代数 R A)} {x : A}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]

Depends on / 依赖: Set.mem_iInter, SetLike, SetLike.mem_coe, coe_sInf, mem_coe
-/
theorem mem_sInf {S : Set (Subalgebra R A)} {x : A} : x in sInf S ↔ forall p in S, x in p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
/--
theorem `sInf_toSubmodule` / 定理 `sInf_toSubmodule`

English:
theorem sInf_toSubmodule
  given: (S : Set (Subalgebra R A))
  proof: SetLike.coe_injective by simp

@[simp]

中文:
定理 sInf_toSubmodule
  条件: (S : 集合 (子代数 R A))
  证明: SetLike.coe_injective by simp

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem sInf_toSubmodule (S : Set (Subalgebra R A)) :
    Subalgebra.toSubmodule (sInf S) = sInf (Subalgebra.toSubmodule '' S) :=
SetLike.coe_injective by simp

@[simp]
/--
theorem `sInf_toSubsemiring` / 定理 `sInf_toSubsemiring`

English:
theorem sInf_toSubsemiring
  given: (S : Set (Subalgebra R A))
  proof: SetLike.coe_injective by simp

中文:
定理 sInf_toSubsemiring
  条件: (S : 集合 (子代数 R A))
  证明: SetLike.coe_injective by simp

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem sInf_toSubsemiring (S : Set (Subalgebra R A)) :
    (sInf S).toSubsemiring = sInf (Subalgebra.toSubsemiring '' S) :=
SetLike.coe_injective by simp

open Subalgebra in
@[simp]
/--
theorem `sSup_toSubsemiring` / 定理 `sSup_toSubsemiring`

English:
theorem sSup_toSubsemiring
  given: (S : Set (Subalgebra R A)) (hS : S.Nonempty)
  proof: by
  have h : toSubsemiring '' S = Subsemiring.closure '' SetLike.coe '' S := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubsemiring.closure_eq.symm
  rw [h]; rw [sSup_image]; rw [← Subsemiring.closure_sUnion]; rw [sSup_def]; rw [adjoin_toSubsemiring]
  congr 1
  rw [Set.union_eq_ri

中文:
定理 sSup_toSubsemiring
  条件: (S : 集合 (子代数 R A)) (hS : S.非空)
  证明: by
  have h : toSubsemiring '' S = Subsemiring.closure '' SetLike.coe '' S := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubsemiring.closure_eq.symm
  rw [h]; rw [sSup_image]; rw [← Subsemiring.closure_sUnion]; rw [sSup_def]; rw [adjoin_toSubsemiring]
  congr 1
  rw [Set.union_eq_ri

Depends on / 依赖: Set.image_image, Set.mem_image, Set.mem_sUnion, Set.union_eq_right, SetLike, SetLike.coe, SetLike.mem_coe, Subsemiring, Subsemiring.closure, Subsemiring.closure_sUnion, adjoin_toSubsemiring, algebraMap_mem, closure, closure_eq, closure_sUnion, exists_exists_and_eq_and, image_image, mem_coe, mem_image, mem_sUnion
-/
theorem sSup_toSubsemiring (S : Set (Subalgebra R A)) (hS : S.Nonempty) :
    (sSup S).toSubsemiring = sSup (toSubsemiring '' S) := by
  have h : toSubsemiring '' S = Subsemiring.closure '' SetLike.coe '' S := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubsemiring.closure_eq.symm
  rw [h]; rw [sSup_image]; rw [← Subsemiring.closure_sUnion]; rw [sSup_def]; rw [adjoin_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hS
  simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and, SetLike.mem_coe]
  exact ⟨y, hy, algebraMap_mem y x⟩

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> Subalgebra R A}
  statement: (↑(⨅ i, S i) : Set A) = ⋂ i, S i
  proof: by
  simp [iInf]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> 子代数 R A}
  结论: (↑(⨅ i, S i) : 集合 A) = ⋂ i, S i
  证明: by
  simp [iInf]

@[simp]
-/
theorem coe_iInf {ι : Sort*} {S : ι -> Subalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> Subalgebra R A} {x : A}
  statement: x in ⨅ i, S i ↔ forall i, x in S i
  proof: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> 子代数 R A} {x : A}
  结论: x in ⨅ i, S i ↔ 对任意 i, x in S i
  证明: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> Subalgebra R A} {x : A} : x in ⨅ i, S i ↔ forall i, x in S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  statement: {ι : Sort*} [Nonempty ι] (f : A ->ₐ[R] B) (hf : Function.Injective f)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

中文:
定理 map_iInf
  结论: {ι : 类型层*} [非空 ι] (f : A ->ₐ[R] B) (hf : 函数.单射 f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A ->ₐ[R] B) (hf : Function.Injective f)
    (s : ι -> Subalgebra R A) : (iInf s).map f = ⨅ (i : ι), (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

open Subalgebra in
@[simp]
/--
theorem `iInf_toSubmodule` / 定理 `iInf_toSubmodule`

English:
theorem iInf_toSubmodule
  given: {ι : Sort*} (S : ι -> Subalgebra R A)
  proof: SetLike.coe_injective by simp

@[simp]

中文:
定理 iInf_toSubmodule
  条件: {ι : 类型层*} (S : ι -> 子代数 R A)
  证明: SetLike.coe_injective by simp

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem iInf_toSubmodule {ι : Sort*} (S : ι -> Subalgebra R A) :
    toSubmodule (⨅ i, S i) = ⨅ i, toSubmodule (S i) :=
SetLike.coe_injective by simp

@[simp]
/--
theorem `iInf_toSubsemiring` / 定理 `iInf_toSubsemiring`

English:
theorem iInf_toSubsemiring
  given: {ι : Sort*} (S : ι -> Subalgebra R A)
  proof: by
  simp only [iInf, sInf_toSubsemiring, ← Set.range_comp, Function.comp_def]

@[simp]

中文:
定理 iInf_toSubsemiring
  条件: {ι : 类型层*} (S : ι -> 子代数 R A)
  证明: by
  simp only [iInf, sInf_toSubsemiring, ← Set.range_comp, Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Set.range_comp, comp_def, range_comp, sInf_toSubsemiring
-/
theorem iInf_toSubsemiring {ι : Sort*} (S : ι -> Subalgebra R A) :
    (iInf S).toSubsemiring = ⨅ i, (S i).toSubsemiring := by
  simp only [iInf, sInf_toSubsemiring, ← Set.range_comp, Function.comp_def]

@[simp]
/--
theorem `iSup_toSubsemiring` / 定理 `iSup_toSubsemiring`

English:
theorem iSup_toSubsemiring
  given: {ι : Sort*} [Nonempty ι] (S : ι -> Subalgebra R A)
  proof: by
  simp only [iSup, Set.range_nonempty, sSup_toSubsemiring, ← Set.range_comp, Function.comp_def]

中文:
定理 iSup_toSubsemiring
  条件: {ι : 类型层*} [非空 ι] (S : ι -> 子代数 R A)
  证明: by
  simp only [iSup, Set.range_nonempty, sSup_toSubsemiring, ← Set.range_comp, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Set.range_comp, Set.range_nonempty, comp_def, range_comp, range_nonempty, sSup_toSubsemiring
-/
theorem iSup_toSubsemiring {ι : Sort*} [Nonempty ι] (S : ι -> Subalgebra R A) :
    (iSup S).toSubsemiring = ⨆ i, (S i).toSubsemiring := by
  simp only [iSup, Set.range_nonempty, sSup_toSubsemiring, ← Set.range_comp, Function.comp_def]

/--
lemma `mem_iSup_of_mem` / 引理 `mem_iSup_of_mem`

English:
lemma mem_iSup_of_mem
  given: {ι : Sort*} {S : ι -> Subalgebra R A} (i : ι) {x : A} (hx : x in S i)
  proof: le_iSup S i hx

@[elab_as_elim]

中文:
引理 mem_iSup_of_mem
  条件: {ι : 类型层*} {S : ι -> 子代数 R A} (i : ι) {x : A} (hx : x in S i)
  证明: le_iSup S i hx

@[elab_as_elim]

Depends on / 依赖: le_iSup
-/
lemma mem_iSup_of_mem {ι : Sort*} {S : ι -> Subalgebra R A} (i : ι) {x : A} (hx : x in S i) :
    x in iSup S :=
  le_iSup S i hx

@[elab_as_elim]
/--
lemma `iSup_induction` / 引理 `iSup_induction`

English:
lemma iSup_induction
  statement: {ι : Sort*} (S : ι -> Subalgebra R A) {motive : A -> Prop}
  proof: by
  let T : Subalgebra R A :=
  { carrier := {x | motive x}
    mul_mem' {a b} := mul a b
    add_mem' {a b} := add a b
    algebraMap_mem' := algebraMap }
  suffices iSup S <= T from this mem
  rwa [iSup_le_iff]

中文:
引理 iSup_induction
  结论: {ι : 类型层*} (S : ι -> 子代数 R A) {motive : A -> 命题}
  证明: by
  let T : Subalgebra R A :=
  { carrier := {x | motive x}
    mul_mem' {a b} := mul a b
    add_mem' {a b} := add a b
    algebraMap_mem' := algebraMap }
  suffices iSup S <= T from this mem
  rwa [iSup_le_iff]

Depends on / 依赖: Subalgebra, add_mem, algebraMap, algebraMap_mem, carrier, iSup_le_iff, motive, mul_mem
-/
lemma iSup_induction {ι : Sort*} (S : ι -> Subalgebra R A) {motive : A -> Prop}
    {x : A} (mem : x in ⨆ i, S i)
    (basic : forall i, forall a in S i, motive a)
    (add : forall a b, motive a -> motive b -> motive (a + b))
    (mul : forall a b, motive a -> motive b -> motive (a * b))
    (algebraMap : forall r, motive (algebraMap R A r)) : motive x := by
  let T : Subalgebra R A :=
  { carrier := {x | motive x}
    mul_mem' {a b} := mul a b
    add_mem' {a b} := add a b
    algebraMap_mem' := algebraMap }
  suffices iSup S <= T from this mem
  rwa [iSup_le_iff]

/-- A dependent version of `Subalgebra.iSup_induction`. -/
@[elab_as_elim]
/--
theorem `iSup_induction'` / 定理 `iSup_induction'`

English:
theorem iSup_induction'
  statement: {ι : Sort*} (S : ι -> Subalgebra R A) {motive : forall x, (x in ⨆ i, S i) -> Prop}
  proof: by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, S i) (hc : motive x hx) => hc
  exact iSup_induction S (motive := fun x' => exists h, motive x' h) mem
    (fun _ _ h => ⟨_, basic _ _ h⟩) (fun _ _ h h' => ⟨_, add _ _ _ _ h.2 h'.2⟩)
    (fun _ _ h h' => ⟨_, mul _ _ _ _ h.2 h'.2⟩) fun _ => ⟨_, algebraMa

中文:
定理 iSup_induction'
  结论: {ι : 类型层*} (S : ι -> 子代数 R A) {motive : 对任意 x, (x in ⨆ i, S i) -> 命题}
  证明: by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, S i) (hc : motive x hx) => hc
  exact iSup_induction S (motive := fun x' => exists h, motive x' h) mem
    (fun _ _ h => ⟨_, basic _ _ h⟩) (fun _ _ h h' => ⟨_, add _ _ _ _ h.2 h'.2⟩)
    (fun _ _ h h' => ⟨_, mul _ _ _ _ h.2 h'.2⟩) fun _ => ⟨_, algebraMa

Depends on / 依赖: Exists, Exists.elim, algebraMap, iSup_induction, motive
-/
theorem iSup_induction' {ι : Sort*} (S : ι -> Subalgebra R A) {motive : forall x, (x in ⨆ i, S i) -> Prop}
    {x : A} (mem : x in ⨆ i, S i)
    (basic : forall (i) (x) (hx : x in S i), motive x (mem_iSup_of_mem i hx))
    (add : forall x y hx hy, motive x hx -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›))
    (mul : forall x y hx hy, motive x hx -> motive y hy -> motive (x * y) (mul_mem ‹_› ‹_›))
    (algebraMap : forall r, motive (algebraMap R A r) (Subalgebra.algebraMap_mem (⨆ i, S i) ‹_›)) :
    motive x mem := by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, S i) (hc : motive x hx) => hc
  exact iSup_induction S (motive := fun x' => exists h, motive x' h) mem
    (fun _ _ h => ⟨_, basic _ _ h⟩) (fun _ _ h h' => ⟨_, add _ _ _ _ h.2 h'.2⟩)
    (fun _ _ h h' => ⟨_, mul _ _ _ _ h.2 h'.2⟩) fun _ => ⟨_, algebraMap _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Subalgebra R A)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (子代数 R A)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (Subalgebra R A) := ⟨⊥⟩

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : A}
  statement: x in (⊥ : Subalgebra R A) ↔ x in Set.range (algebraMap R A)
  proof: Iff.rfl

中文:
定理 mem_bot
  条件: {x : A}
  结论: x in (⊥ : 子代数 R A) ↔ x in 集合.range (algebraMap R A)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.range (algebraMap R A) := Iff.rfl

/--
theorem `toSubmodule_bot` / 定理 `toSubmodule_bot`

English:
theorem toSubmodule_bot
  statement: Subalgebra.toSubmodule (⊥ : Subalgebra R A) = 1
  proof: Submodule.one_eq_range.symm

@[simp, norm_cast]

中文:
定理 toSubmodule_bot
  结论: 子代数.toSubmodule (⊥ : 子代数 R A) = 1
  证明: Submodule.one_eq_range.symm

@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.one_eq_range.symm, one_eq_range
-/
theorem toSubmodule_bot : Subalgebra.toSubmodule (⊥ : Subalgebra R A) = 1 :=
  Submodule.one_eq_range.symm

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Subalgebra R A) : Set A) = Set.range (algebraMap R A)
  proof: rfl

@[simp]

中文:
定理 coe_bot
  结论: ((⊥ : 子代数 R A) : 集合 A) = 集合.range (algebraMap R A)
  证明: rfl

@[simp]
-/
theorem coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.range (algebraMap R A) := rfl

@[simp]
/--
theorem `toSubring_bot` / 定理 `toSubring_bot`

English:
theorem toSubring_bot
  given: (A : Type*) [CommRing A] (R : Subring A)
  proof: by
  aesop (add norm Subalgebra.mem_carrier.symm)

中文:
定理 toSubring_bot
  条件: (A : 类型) [交换环 A] (R : 子环 A)
  证明: by
  aesop (add norm Subalgebra.mem_carrier.symm)

Depends on / 依赖: Subalgebra, Subalgebra.mem_carrier.symm, mem_carrier
-/
theorem toSubring_bot (A : Type*) [CommRing A] (R : Subring A) :
    (⊥ : Subalgebra R A).toSubring = R := by
  aesop (add norm Subalgebra.mem_carrier.symm)

/--
theorem `eq_top_iff` / 定理 `eq_top_iff`

English:
theorem eq_top_iff
  given: {S : Subalgebra R A}
  statement: S = ⊤ ↔ forall x : A, x in S
  proof: ⟨fun h x => by rw [h]; exact mem_top, fun h => by
    ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

中文:
定理 eq_top_iff
  条件: {S : 子代数 R A}
  结论: S = ⊤ ↔ 对任意 x : A, x in S
  证明: ⟨fun h x => by rw [h]; exact mem_top, fun h => by
    ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

Depends on / 依赖: mem_top
-/
theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x : A, x in S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by
    ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

/--
theorem `_root_.AlgHom.range_eq_top` / 定理 `_root_.AlgHom.range_eq_top`

English:
theorem _root_.AlgHom.range_eq_top
  given: (f : A ->ₐ[R] B)
  proof: Algebra.eq_top_iff

@[simp]

中文:
定理 _root_.代数态射.range_eq_top
  条件: (f : A ->ₐ[R] B)
  证明: Algebra.eq_top_iff

@[simp]

Depends on / 依赖: Algebra, Algebra.eq_top_iff, eq_top_iff
-/
theorem _root_.AlgHom.range_eq_top (f : A ->ₐ[R] B) :
    f.range = (⊤ : Subalgebra R B) ↔ Function.Surjective f :=
  Algebra.eq_top_iff

@[simp]
/--
theorem `range_ofId` / 定理 `range_ofId`

English:
theorem range_ofId
  statement: (Algebra.ofId R A).range = ⊥
  proof: rfl

@[simp]

中文:
定理 range_ofId
  结论: (代数.ofId R A).range = ⊥
  证明: rfl

@[simp]
-/
theorem range_ofId : (Algebra.ofId R A).range = ⊥ := rfl

@[simp]
/--
theorem `range_id` / 定理 `range_id`

English:
theorem range_id
  statement: (AlgHom.id R A).range = ⊤
  proof: SetLike.coe_injective Set.range_id

@[simp]

中文:
定理 range_id
  结论: (代数态射.id R A).range = ⊤
  证明: SetLike.coe_injective Set.range_id

@[simp]

Depends on / 依赖: Set.range_id, SetLike, SetLike.coe_injective, coe_injective, range_id
-/
theorem range_id : (AlgHom.id R A).range = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  given: (f : A ->ₐ[R] B)
  statement: (⊤ : Subalgebra R A).map f = f.range
  proof: SetLike.coe_injective Set.image_univ

@[simp]

中文:
定理 map_top
  条件: (f : A ->ₐ[R] B)
  结论: (⊤ : 子代数 R A).map f = f.range
  证明: SetLike.coe_injective Set.image_univ

@[simp]

Depends on / 依赖: Set.image_univ, SetLike, SetLike.coe_injective, coe_injective, image_univ
-/
theorem map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range :=
  SetLike.coe_injective Set.image_univ

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : A ->ₐ[R] B)
  statement: (⊥ : Subalgebra R A).map f = ⊥
  proof: Subalgebra.toSubmodule_injective by
    simpa only [Subalgebra.map_toSubmodule, toSubmodule_bot] using Submodule.map_one _

@[simp]

中文:
定理 map_bot
  条件: (f : A ->ₐ[R] B)
  结论: (⊥ : 子代数 R A).map f = ⊥
  证明: Subalgebra.toSubmodule_injective by
    simpa only [Subalgebra.map_toSubmodule, toSubmodule_bot] using Submodule.map_one _

@[simp]

Depends on / 依赖: AlgHomClass, FunLike, NonUnitalAlgHomClass, Subalgebra, Subalgebra.map_toSubmodule, Subalgebra.toSubmodule_injective, Submodule, Submodule.map_one, map_one, map_toSubmodule, toSubmodule_bot, toSubmodule_injective
-/
theorem map_bot (f : A ->ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥ :=
Subalgebra.toSubmodule_injective by
    simpa only [Subalgebra.map_toSubmodule, toSubmodule_bot] using Submodule.map_one _

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : A ->ₐ[R] B)
  statement: (⊤ : Subalgebra R B).comap f = ⊤
  proof: eq_top_iff.2 fun _x => mem_top

中文:
定理 comap_top
  条件: (f : A ->ₐ[R] B)
  结论: (⊤ : 子代数 R B).comap f = ⊤
  证明: eq_top_iff.2 fun _x => mem_top

Depends on / 依赖: eq_top_iff, mem_top
-/
theorem comap_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top

/--
Definition of `toTop` / `toTop` 的定义

English:
definition toTop
  signature: : A ->ₐ[R] (⊤ : Subalgebra R A)
  body: (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top

中文:
定义 toTop
  签名: : A ->ₐ[R] (⊤ : 子代数 R A)
  定义体: (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top

Depends on / 依赖: AlgHom, AlgHom.id, codRestrict, mem_top
-/
def toTop : A ->ₐ[R] (⊤ : Subalgebra R A) :=
  (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top

/--
theorem `surjective_algebraMap_iff` / 定理 `surjective_algebraMap_iff`

English:
theorem surjective_algebraMap_iff
  proof: ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨_x, hx⟩ := h y
      hx ▸ Subalgebra.algebraMap_mem _ _,
fun h y => Algebra.mem_bot.1 eq_bot_iff.1 h (Algebra.mem_top : y in _)⟩

中文:
定理 surjective_algebraMap_iff
  证明: ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨_x, hx⟩ := h y
      hx ▸ Subalgebra.algebraMap_mem _ _,
fun h y => Algebra.mem_bot.1 eq_bot_iff.1 h (Algebra.mem_top : y in _)⟩

Depends on / 依赖: Algebra, Algebra.mem_bot, Algebra.mem_top, Subalgebra, Subalgebra.algebraMap_mem, algebraMap_mem, eq_bot_iff, mem_bot, mem_top
-/
theorem surjective_algebraMap_iff :
    Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨_x, hx⟩ := h y
      hx ▸ Subalgebra.algebraMap_mem _ _,
fun h y => Algebra.mem_bot.1 eq_bot_iff.1 h (Algebra.mem_top : y in _)⟩

/--
theorem `bijective_algebraMap_iff` / 定理 `bijective_algebraMap_iff`

English:
theorem bijective_algebraMap_iff
  statement: {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
  proof: ⟨fun h => surjective_algebraMap_iff.1 h.2, fun h =>
    ⟨(algebraMap R A).injective, surjective_algebraMap_iff.2 h⟩⟩

中文:
定理 bijective_algebraMap_iff
  结论: {R A : 类型} [域 R] [半环 A] [非平凡 A]
  证明: ⟨fun h => surjective_algebraMap_iff.1 h.2, fun h =>
    ⟨(algebraMap R A).injective, surjective_algebraMap_iff.2 h⟩⟩

Depends on / 依赖: algebraMap, injective, surjective_algebraMap_iff
-/
theorem bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
    [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h => surjective_algebraMap_iff.1 h.2, fun h =>
    ⟨(algebraMap R A).injective, surjective_algebraMap_iff.2 h⟩⟩

/--
Definition of `botEquivOfInjective` / `botEquivOfInjective` 的定义

English:
definition botEquivOfInjective
  signature: (h : Function.Injective (algebraMap R A))
  body: AlgEquiv.symm
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun _x _y hxy => h (congr_arg Subtype.val hxy :), fun ⟨_y, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

#adaptation_note

中文:
定义 botEquivOfInjective
  签名: (h : 函数.单射 (algebraMap R A))
  定义体: AlgEquiv.symm
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun _x _y hxy => h (congr_arg Subtype.val hxy :), fun ⟨_y, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

#adaptation_note

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, AlgEquiv.symm, Algebra, Algebra.ofId, Subtype, Subtype.ext, Subtype.val, congr_arg, ofBijective
-/
noncomputable def botEquivOfInjective (h : Function.Injective (algebraMap R A)) :
    (⊥ : Subalgebra R A) ≃ₐ[R] R :=
AlgEquiv.symm
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun _x _y hxy => h (congr_arg Subtype.val hxy :), fun ⟨_y, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The bottom subalgebra is isomorphic to the field. -/
@[simps! symm_apply]
/--
Definition of `botEquiv` / `botEquiv` 的定义

English:
definition botEquiv
  signature: (F R : Type*) [Field F] [Semiring R] [Nontrivial R] [Algebra F R]
  body: botEquivOfInjective (RingHom.injective _)

中文:
定义 botEquiv
  签名: (F R : 类型) [域 F] [半环 R] [非平凡 R] [代数 F R]
  定义体: botEquivOfInjective (RingHom.injective _)

Depends on / 依赖: RingHom, RingHom.injective, botEquivOfInjective, injective
-/
noncomputable def botEquiv (F R : Type*) [Field F] [Semiring R] [Nontrivial R] [Algebra F R] :
    (⊥ : Subalgebra F R) ≃ₐ[F] F :=
  botEquivOfInjective (RingHom.injective _)

end Algebra

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A)

/-- The top subalgebra is isomorphic to the algebra.

This is the algebra version of `Submodule.topEquiv`. -/
@[simps!]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : Subalgebra R A) ≃ₐ[R] A
  body: AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl rfl

中文:
定义 topEquiv
  签名: : (⊤ : 子代数 R A) ≃ₐ[R] A
  定义体: AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, Subalgebra, Subalgebra.val, ofAlgHom
-/
def topEquiv : (⊤ : Subalgebra R A) ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl rfl

/--
Instance `_root_.AlgHom.subsingleton` / 实例 `_root_.AlgHom.subsingleton`

English:
instance _root_.AlgHom.subsingleton
  signature: [Subsingleton (Subalgebra R A)]
  body: ⟨fun f g =>
    AlgHom.ext fun a =>
      have : a in (⊥ : Subalgebra R A) := Subsingleton.elim (⊤ : Subalgebra R A) ⊥ ▸ mem_top
      let ⟨_x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
      hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

中文:
实例 _root_.代数态射.subsingleton
  签名: [子单例 (子代数 R A)]
  定义体: ⟨fun f g =>
    AlgHom.ext fun a =>
      have : a in (⊥ : Subalgebra R A) := Subsingleton.elim (⊤ : Subalgebra R A) ⊥ ▸ mem_top
      let ⟨_x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
      hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

Depends on / 依赖: AlgHom, AlgHom.ext, Set.mem_range.mp, Subalgebra, Subsingleton, Subsingleton.elim, commutes, f.commutes, g.commutes, mem_bot, mem_bot.mp, mem_range, mem_top
-/
instance _root_.AlgHom.subsingleton [Subsingleton (Subalgebra R A)] : Subsingleton (A ->ₐ[R] B) :=
  ⟨fun f g =>
    AlgHom.ext fun a =>
      have : a in (⊥ : Subalgebra R A) := Subsingleton.elim (⊤ : Subalgebra R A) ⊥ ▸ mem_top
      let ⟨_x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
      hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

/--
Instance `_root_.AlgEquiv.subsingleton_left` / 实例 `_root_.AlgEquiv.subsingleton_left`

English:
instance _root_.AlgEquiv.subsingleton_left
  signature: [Subsingleton (Subalgebra R A)]
  body: ⟨fun f g => AlgEquiv.ext fun x => AlgHom.ext_iff.mp (Subsingleton.elim f.toAlgHom g.toAlgHom) x⟩

中文:
实例 _root_.代数等价.subsingleton_left
  签名: [子单例 (子代数 R A)]
  定义体: ⟨fun f g => AlgEquiv.ext fun x => AlgHom.ext_iff.mp (Subsingleton.elim f.toAlgHom g.toAlgHom) x⟩

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, AlgHom, AlgHom.ext_iff.mp, Subsingleton, Subsingleton.elim, ext_iff, f.toAlgHom, g.toAlgHom, toAlgHom
-/
instance _root_.AlgEquiv.subsingleton_left [Subsingleton (Subalgebra R A)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => AlgEquiv.ext fun x => AlgHom.ext_iff.mp (Subsingleton.elim f.toAlgHom g.toAlgHom) x⟩

/--
Instance `_root_.AlgEquiv.subsingleton_right` / 实例 `_root_.AlgEquiv.subsingleton_right`

English:
instance _root_.AlgEquiv.subsingleton_right
  signature: [Subsingleton (Subalgebra R B)]
  body: ⟨fun f g => by rw [← f.symm_symm, Subsingleton.elim f.symm g.symm, g.symm_symm]⟩

中文:
实例 _root_.代数等价.subsingleton_right
  签名: [子单例 (子代数 R B)]
  定义体: ⟨fun f g => by rw [← f.symm_symm, Subsingleton.elim f.symm g.symm, g.symm_symm]⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, f.symm, f.symm_symm, g.symm, g.symm_symm, symm_symm
-/
instance _root_.AlgEquiv.subsingleton_right [Subsingleton (Subalgebra R B)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => by rw [← f.symm_symm, Subsingleton.elim f.symm g.symm, g.symm_symm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (Subalgebra R R)
  body: { (inferInstance : Inhabited (Subalgebra R R)) with
    uniq := by
      intro S
      refine le_antisymm ?_ bot_le
      intro _ _
      simp only [Set.mem_range, mem_bot, algebraMap_self_apply, exists_apply_eq_apply, default] }

中文:
实例 :
  签名: 唯一 (子代数 R R)
  定义体: { (inferInstance : Inhabited (Subalgebra R R)) with
    uniq := by
      intro S
      refine le_antisymm ?_ bot_le
      intro _ _
      simp only [Set.mem_range, mem_bot, algebraMap_self_apply, exists_apply_eq_apply, default] }

Depends on / 依赖: Inhabited, Set.mem_range, Subalgebra, algebraMap_self_apply, bot_le, exists_apply_eq_apply, le_antisymm, mem_bot, mem_range
-/
instance : Unique (Subalgebra R R) :=
  { (inferInstance : Inhabited (Subalgebra R R)) with
    uniq := by
      intro S
      refine le_antisymm ?_ bot_le
      intro _ _
      simp only [Set.mem_range, mem_bot, algebraMap_self_apply, exists_apply_eq_apply, default] }

section Center

variable (R A)

@[simp]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  given: (A : Type*) [CommSemiring A] [Algebra R A]
  statement: center R A = ⊤
  proof: SetLike.coe_injective (Set.center_eq_univ A)

中文:
定理 center_eq_top
  条件: (A : 类型) [交换半环 A] [代数 R A]
  结论: center R A = ⊤
  证明: SetLike.coe_injective (Set.center_eq_univ A)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top (A : Type*) [CommSemiring A] [Algebra R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

end Center

section Centralizer

variable (R)

@[simp]
/--
theorem `centralizer_eq_top_iff_subset` / 定理 `centralizer_eq_top_iff_subset`

English:
theorem centralizer_eq_top_iff_subset
  given: {s : Set A}
  statement: centralizer R s = ⊤ ↔ s subseteq center R A
  proof: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

中文:
定理 centralizer_eq_top_iff_subset
  条件: {s : 集合 A}
  结论: centralizer R s = ⊤ ↔ s subseteq center R A
  证明: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

Depends on / 依赖: Set.centralizer_eq_top_iff_subset, SetLike, SetLike.ext, _iff, _iff.trans, centralizer_eq_top_iff_subset
-/
theorem centralizer_eq_top_iff_subset {s : Set A} : centralizer R s = ⊤ ↔ s subseteq center R A :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

end Centralizer

end Subalgebra

section Equalizer

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

@[simp]
/--
theorem `equalizer_eq_top` / 定理 `equalizer_eq_top`

English:
theorem equalizer_eq_top
  given: {φ ψ : A ->ₐ[R] B}
  statement: equalizer φ ψ = ⊤ ↔ φ = ψ
  proof: by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]

中文:
定理 equalizer_eq_top
  条件: {φ ψ : A ->ₐ[R] B}
  结论: equalizer φ ψ = ⊤ ↔ φ = ψ
  证明: by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, SetLike, SetLike.ext_iff, ext_iff
-/
theorem equalizer_eq_top {φ ψ : A ->ₐ[R] B} : equalizer φ ψ = ⊤ ↔ φ = ψ := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]
/--
theorem `equalizer_same` / 定理 `equalizer_same`

English:
theorem equalizer_same
  given: (φ : A ->ₐ[R] B)
  statement: equalizer φ φ = ⊤
  proof: equalizer_eq_top.2 rfl

中文:
定理 equalizer_same
  条件: (φ : A ->ₐ[R] B)
  结论: equalizer φ φ = ⊤
  证明: equalizer_eq_top.2 rfl

Depends on / 依赖: equalizer_eq_top
-/
theorem equalizer_same (φ : A ->ₐ[R] B) : equalizer φ φ = ⊤ := equalizer_eq_top.2 rfl

variable {F : Type*} [FunLike F A B] [AlgHomClass F R A B]

/--
theorem `eqOn_sup` / 定理 `eqOn_sup`

English:
theorem eqOn_sup
  given: {φ ψ : F} {S T : Subalgebra R A} (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T)
  proof: by
  rw [← AlgHom.coe_coe φ]; rw [← AlgHom.coe_coe ψ]; rw [← le_equalizer] at hS hT ⊢
  exact sup_le hS hT

中文:
定理 eqOn_sup
  条件: {φ ψ : F} {S T : 子代数 R A} (hS : 集合.EqOn φ ψ S) (hT : 集合.EqOn φ ψ T)
  证明: by
  rw [← AlgHom.coe_coe φ]; rw [← AlgHom.coe_coe ψ]; rw [← le_equalizer] at hS hT ⊢
  exact sup_le hS hT

Depends on / 依赖: AlgHom, AlgHom.coe_coe, coe_coe, le_equalizer, sup_le
-/
theorem eqOn_sup {φ ψ : F} {S T : Subalgebra R A} (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) :
    Set.EqOn φ ψ ↑(S ⊔ T) := by
  rw [← AlgHom.coe_coe φ]; rw [← AlgHom.coe_coe ψ]; rw [← le_equalizer] at hS hT ⊢
  exact sup_le hS hT

/--
theorem `ext_on_codisjoint` / 定理 `ext_on_codisjoint`

English:
theorem ext_on_codisjoint
  statement: {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T)
  proof: DFunLike.ext _ _ fun _ => eqOn_sup hS hT hST.eq_top.symm ▸ trivial

中文:
定理 ext_on_codisjoint
  结论: {φ ψ : F} {S T : 子代数 R A} (hST : Codisjoint S T)
  证明: DFunLike.ext _ _ fun _ => eqOn_sup hS hT hST.eq_top.symm ▸ trivial

Depends on / 依赖: DFunLike, DFunLike.ext, eqOn_sup, eq_top, hST.eq_top.symm
-/
theorem ext_on_codisjoint {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T)
    (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) : φ = ψ :=
DFunLike.ext _ _ fun _ => eqOn_sup hS hT hST.eq_top.symm ▸ trivial

end AlgHom

end Equalizer

section MapComap

namespace Subalgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (f : A ->ₐ[R] B) (S : Subalgebra R B)
  statement: (S.comap f).map f = S ⊓ f.range
  proof: SetLike.coe_injective Set.image_preimage_eq_inter_range

中文:
定理 map_comap_eq
  条件: (f : A ->ₐ[R] B) (S : 子代数 R B)
  结论: (S.comap f).map f = S ⊓ f.range
  证明: SetLike.coe_injective Set.image_preimage_eq_inter_range

Depends on / 依赖: Set.image_preimage_eq_inter_range, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq_inter_range
-/
theorem map_comap_eq (f : A ->ₐ[R] B) (S : Subalgebra R B) : (S.comap f).map f = S ⊓ f.range :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

/--
theorem `map_comap_eq_self` / 定理 `map_comap_eq_self`

English:
theorem map_comap_eq_self
  proof: by
  simpa only [inf_of_le_left h] using map_comap_eq f S

中文:
定理 map_comap_eq_self
  证明: by
  simpa only [inf_of_le_left h] using map_comap_eq f S

Depends on / 依赖: CanLift, NonUnitalSubalgebra, inf_of_le_left, map_comap_eq
-/
theorem map_comap_eq_self
    {f : A ->ₐ[R] B} {S : Subalgebra R B} (h : S <= f.range) : (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

/--
theorem `map_comap_eq_self_of_surjective` / 定理 `map_comap_eq_self_of_surjective`

English:
theorem map_comap_eq_self_of_surjective
  proof: map_comap_eq_self by simp [(AlgHom.range_eq_top f).2 hf]

中文:
定理 map_comap_eq_self_of_surjective
  证明: map_comap_eq_self by simp [(AlgHom.range_eq_top f).2 hf]

Depends on / 依赖: AlgHom, AlgHom.range_eq_top, map_comap_eq_self, range_eq_top
-/
theorem map_comap_eq_self_of_surjective
    {f : A ->ₐ[R] B} (hf : Function.Surjective f) (S : Subalgebra R B) : (S.comap f).map f = S :=
map_comap_eq_self by simp [(AlgHom.range_eq_top f).2 hf]

end Subalgebra

end MapComap

section saturation

namespace Subalgebra

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M <= s.toSubmonoid}

/--
Definition of `saturation` / `saturation` 的定义

English:
definition saturation
  signature: (s : Subalgebra R S) (M : Submonoid S) (H : M <= s.toSubmonoid)
  body: { x | exists m in M, m * x in s }
  mul_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hm hn, mul_mul_mul_comm m n a b ▸ mul_mem ha hb⟩
  add_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hn hm, ?_⟩
    rw [mul_add]; rw [mul_assoc]; rw [mul_comm n m

中文:
定义 saturation
  签名: (s : 子代数 R S) (M : 子幺半群 S) (H : M <= s.toSubmonoid)
  定义体: { x | exists m in M, m * x in s }
  mul_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hm hn, mul_mul_mul_comm m n a b ▸ mul_mem ha hb⟩
  add_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hn hm, ?_⟩
    rw [mul_add]; rw [mul_assoc]; rw [mul_comm n m
-/
def saturation (s : Subalgebra R S) (M : Submonoid S) (H : M <= s.toSubmonoid) :
    Subalgebra R S where
  carrier := { x | exists m in M, m * x in s }
  mul_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hm hn, mul_mul_mul_comm m n a b ▸ mul_mem ha hb⟩
  add_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hn hm, ?_⟩
    rw [mul_add]; rw [mul_assoc]; rw [mul_comm n m]; rw [mul_assoc]
    exact add_mem (mul_mem (H hn) ha) (mul_mem (H hm) hb)
  algebraMap_mem' r := ⟨1, one_mem _, by simp⟩

/--
lemma `mem_saturation_iff` / 引理 `mem_saturation_iff`

English:
lemma mem_saturation_iff
  given: {x : S}
  proof: .rfl

中文:
引理 mem_saturation_iff
  条件: {x : S}
  证明: .rfl
-/
@[simp] lemma mem_saturation_iff {x : S} :
    x in s.saturation M H ↔ exists m in M, m • x in s := .rfl

/--
lemma `le_saturation` / 引理 `le_saturation`

English:
lemma le_saturation
  statement: s <= s.saturation M H
  proof: fun x hx => ⟨1, one_mem M, by simpa⟩

中文:
引理 le_saturation
  结论: s <= s.saturation M H
  证明: fun x hx => ⟨1, one_mem M, by simpa⟩

Depends on / 依赖: one_mem
-/
lemma le_saturation : s <= s.saturation M H :=
  fun x hx => ⟨1, one_mem M, by simpa⟩

/--
lemma `saturation_saturation` / 引理 `saturation_saturation`

English:
lemma saturation_saturation
  proof: le_saturation.antisymm' fun x ⟨m, hm, n, hn, h⟩ => ⟨_, M.mul_mem hn hm, mul_assoc n m x ▸ h⟩

中文:
引理 saturation_saturation
  证明: le_saturation.antisymm' fun x ⟨m, hm, n, hn, h⟩ => ⟨_, M.mul_mem hn hm, mul_assoc n m x ▸ h⟩
-/
@[simp] lemma saturation_saturation :
    (s.saturation M H).saturation M (H.trans s.le_saturation) = s.saturation M H :=
  le_saturation.antisymm' fun x ⟨m, hm, n, hn, h⟩ => ⟨_, M.mul_mem hn hm, mul_assoc n m x ▸ h⟩

/--
lemma `mem_saturation_of_mul_mem_left` / 引理 `mem_saturation_of_mul_mem_left`

English:
lemma mem_saturation_of_mul_mem_left
  statement: {x y} (hxy : x * y in s.saturation M H)
  proof: saturation_saturation.le ⟨_, hx, hxy⟩

中文:
引理 mem_saturation_of_mul_mem_left
  结论: {x y} (hxy : x * y in s.saturation M H)
  证明: saturation_saturation.le ⟨_, hx, hxy⟩

Depends on / 依赖: saturation_saturation, saturation_saturation.le
-/
lemma mem_saturation_of_mul_mem_left {x y} (hxy : x * y in s.saturation M H)
    (hx : x in M) : y in s.saturation M H :=
  saturation_saturation.le ⟨_, hx, hxy⟩

/--
lemma `mem_saturation_of_mul_mem_right` / 引理 `mem_saturation_of_mul_mem_right`

English:
lemma mem_saturation_of_mul_mem_right
  statement: {x y} (hxy : x * y in s.saturation M H)
  proof: mem_saturation_of_mul_mem_left (mul_comm x y ▸ hxy) hy

中文:
引理 mem_saturation_of_mul_mem_right
  结论: {x y} (hxy : x * y in s.saturation M H)
  证明: mem_saturation_of_mul_mem_left (mul_comm x y ▸ hxy) hy

Depends on / 依赖: mem_saturation_of_mul_mem_left, mul_comm
-/
lemma mem_saturation_of_mul_mem_right {x y} (hxy : x * y in s.saturation M H)
    (hy : y in M) : x in s.saturation M H :=
  mem_saturation_of_mul_mem_left (mul_comm x y ▸ hxy) hy

end Subalgebra

end saturation

section Adjoin

universe uR uS uA uB

open Submodule Subsemiring

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

namespace Algebra

/--
If `x₁ x₂ ... xₙ : A` then `R[x₁,x₂,...,xₙ]` is the `Subalgebra R A` generated by these elements. -/
scoped syntax:max (name := subalgebra_adjoin) term "[" term,* (" : " term)? "]" : term

/--
If `x₁ x₂ ... xₙ : A` then `R[x₁,x₂,...,xₙ]` is the `Subalgebra R A` generated by these elements. -/
macro_rules (kind := subalgebra_adjoin)
  | `($R[$xs,*]) => `(Algebra.adjoin $R {$xs:term,*})
  | `($R[$xs,* : $A]) => do
    let xs' ← xs.getElems.mapM fun x => `(($x : $A))
    `(Algebra.adjoin $R ({$[$xs':term],*} : Set $A))

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Supporting function for the `R[x₁,x₂,...,xₙ]` adjunction notation. -/
@[app_delab Algebra.adjoin]
meta partial def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
  withOverApp 6 do
  let F ← withNaryArg 0 delab
  let xs ← withNaryArg 5 delabInsertArray
  `($F[$(xs.toArray),*])
where
  delabInsertArray : DelabM (List Term) := do
    let e ← getExpr
    if e.isAppOfArity ``EmptyCollection.emptyCollection 2 then
      return []
    if e.isAppOfArity ``singleton 4 then
      let x ← withNaryArg 3 delab
      return [x]
    if e.isAppOfArity ``insert 5 then
      let x ← withNaryArg 3 delab
      let xs ← withNaryArg 4 delabInsertArray
      return x :: xs
    failure

open Algebra

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]
variable {s t : Set A}

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `subset_adjoin` / 定理 `subset_adjoin`

English:
theorem subset_adjoin
  statement: s subseteq adjoin R s
  proof: Algebra.gc.le_u_l s

@[aesop 80% (rule_sets := [SetLike])]

中文:
定理 subset_adjoin
  结论: s subseteq adjoin R s
  证明: Algebra.gc.le_u_l s

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: Algebra, Algebra.gc.le_u_l, le_u_l
-/
theorem subset_adjoin : s subseteq adjoin R s :=
  Algebra.gc.le_u_l s

@[aesop 80% (rule_sets := [SetLike])]
/--
theorem `mem_adjoin_of_mem` / 定理 `mem_adjoin_of_mem`

English:
theorem mem_adjoin_of_mem
  given: {s : Set A} {x : A} (hx : x in s)
  statement: x in adjoin R s
  proof: subset_adjoin hx

中文:
定理 mem_adjoin_of_mem
  条件: {s : 集合 A} {x : A} (hx : x in s)
  结论: x in adjoin R s
  证明: subset_adjoin hx

Depends on / 依赖: subset_adjoin
-/
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x in s) : x in adjoin R s := subset_adjoin hx

/-
The following set-up allows one to write `xₖ : R[x₁, ..., xₙ]` instead of
`(⟨xₖ, "membership proof"⟩ : R[x₁, ..., xₙ])`.

The idea is to recurse through the list of `x₁, ..., xₙ` until we find the appropriate `xₖ`.
By design, it only triggers if the set is of the form `insert x₁ (insert x₂ (...(s)))` or
`{x₁, ..., xₙ}`.
-/

variable {α : Type*}

/--
Definition of `CoeAdjoinAux` / `CoeAdjoinAux` 的定义

English:
class CoeAdjoinAux
  parameters: (x : α) (s : Set α)
  (no additional axioms)

中文:
类 余eAdjoinAux
  参数: (x : α) (s : 集合 α)
  (无附加公理)

Depends on / 依赖: Set.mem_singleton, mem_singleton
-/
class CoeAdjoinAux (x : α) (s : Set α) : Prop where mem : x in s

scoped instance (x : α) : CoeAdjoinAux x {x} := ⟨Set.mem_singleton x⟩

scoped instance (x : α) (s : Set α) : CoeAdjoinAux x (insert x s) := ⟨Set.mem_insert x s⟩

scoped instance (x y : α) (s : Set α) [CoeAdjoinAux x s] : CoeAdjoinAux x (insert y s) :=
  ⟨Set.mem_insert_of_mem y CoeAdjoinAux.mem⟩

/-- Enables notation `xₖ : R[x₁, ..., xₙ]` instead of
`(⟨xₖ, "membership proof"⟩ : R[x₁, ..., xₙ])`. -/
scoped instance {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (s : Set B) (x : B) [CoeAdjoinAux x s] :
    CoeDep B x (adjoin A s) where
  coe := ⟨x, mem_adjoin_of_mem CoeAdjoinAux.mem⟩

/--
theorem `adjoin_le` / 定理 `adjoin_le`

English:
theorem adjoin_le
  given: {S : Subalgebra R A} (H : s subseteq S)
  statement: adjoin R s <= S
  proof: Algebra.gc.l_le H

中文:
定理 adjoin_le
  条件: {S : 子代数 R A} (H : s subseteq S)
  结论: adjoin R s <= S
  证明: Algebra.gc.l_le H

Depends on / 依赖: Algebra, Algebra.gc.l_le, S.toNonUnitalSubsemiring, l_le, toNonUnitalSubsemiring
-/
theorem adjoin_le {S : Subalgebra R A} (H : s subseteq S) : adjoin R s <= S :=
  Algebra.gc.l_le H

/--
theorem `adjoin_singleton_le` / 定理 `adjoin_singleton_le`

English:
theorem adjoin_singleton_le
  given: {S : Subalgebra R A} {a : A} (H : a in S)
  statement: R[a] <= S
  proof: adjoin_le (Set.singleton_subset_iff.mpr H)

中文:
定理 adjoin_singleton_le
  条件: {S : 子代数 R A} {a : A} (H : a in S)
  结论: R[a] <= S
  证明: adjoin_le (Set.singleton_subset_iff.mpr H)

Depends on / 依赖: Set.singleton_subset_iff.mpr, adjoin_le, singleton_subset_iff
-/
theorem adjoin_singleton_le {S : Subalgebra R A} {a : A} (H : a in S) : R[a] <= S :=
  adjoin_le (Set.singleton_subset_iff.mpr H)

/--
theorem `adjoin_eq_sInf` / 定理 `adjoin_eq_sInf`

English:
theorem adjoin_eq_sInf
  statement: adjoin R s = sInf { p : Subalgebra R A | s subseteq p }
  proof: le_antisymm (le_sInf fun _ h => adjoin_le h) (sInf_le subset_adjoin)

中文:
定理 adjoin_eq_sInf
  结论: adjoin R s = sInf { p : 子代数 R A | s subseteq p }
  证明: le_antisymm (le_sInf fun _ h => adjoin_le h) (sInf_le subset_adjoin)

Depends on / 依赖: adjoin_le, le_antisymm, le_sInf, sInf_le, subset_adjoin
-/
theorem adjoin_eq_sInf : adjoin R s = sInf { p : Subalgebra R A | s subseteq p } :=
  le_antisymm (le_sInf fun _ h => adjoin_le h) (sInf_le subset_adjoin)

/--
theorem `adjoin_le_iff` / 定理 `adjoin_le_iff`

English:
theorem adjoin_le_iff
  given: {S : Subalgebra R A}
  statement: adjoin R s <= S ↔ s subseteq S
  proof: Algebra.gc _ _

@[gcongr]

中文:
定理 adjoin_le_iff
  条件: {S : 子代数 R A}
  结论: adjoin R s <= S ↔ s subseteq S
  证明: Algebra.gc _ _

@[gcongr]

Depends on / 依赖: Algebra, Algebra.gc
-/
theorem adjoin_le_iff {S : Subalgebra R A} : adjoin R s <= S ↔ s subseteq S :=
  Algebra.gc _ _

@[gcongr]
/--
theorem `adjoin_mono` / 定理 `adjoin_mono`

English:
theorem adjoin_mono
  given: (H : s subseteq t)
  statement: adjoin R s <= adjoin R t
  proof: Algebra.gc.monotone_l H

中文:
定理 adjoin_mono
  条件: (H : s subseteq t)
  结论: adjoin R s <= adjoin R t
  证明: Algebra.gc.monotone_l H

Depends on / 依赖: Algebra, Algebra.gc.monotone_l, monotone_l
-/
theorem adjoin_mono (H : s subseteq t) : adjoin R s <= adjoin R t :=
  Algebra.gc.monotone_l H

/--
theorem `adjoin_eq_of_le` / 定理 `adjoin_eq_of_le`

English:
theorem adjoin_eq_of_le
  given: (S : Subalgebra R A) (h₁ : s subseteq S) (h₂ : S <= adjoin R s)
  statement: adjoin R s = S
  proof: le_antisymm (adjoin_le h₁) h₂

中文:
定理 adjoin_eq_of_le
  条件: (S : 子代数 R A) (h₁ : s subseteq S) (h₂ : S <= adjoin R s)
  结论: adjoin R s = S
  证明: le_antisymm (adjoin_le h₁) h₂

Depends on / 依赖: adjoin_le, le_antisymm
-/
theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s subseteq S) (h₂ : S <= adjoin R s) : adjoin R s = S :=
  le_antisymm (adjoin_le h₁) h₂

/--
theorem `adjoin_eq` / 定理 `adjoin_eq`

English:
theorem adjoin_eq
  given: (S : Subalgebra R A)
  statement: adjoin R ↑S = S
  proof: adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin

中文:
定理 adjoin_eq
  条件: (S : 子代数 R A)
  结论: adjoin R ↑S = S
  证明: adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin

Depends on / 依赖: Set.Subset.refl, Subset, adjoin_eq_of_le, subset_adjoin
-/
theorem adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S :=
  adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin

/--
theorem `adjoin_iUnion` / 定理 `adjoin_iUnion`

English:
theorem adjoin_iUnion
  given: {α : Type*} (s : α -> Set A)
  proof: (@Algebra.gc R A _ _ _).l_iSup

中文:
定理 adjoin_iUnion
  条件: {α : 类型} (s : α -> 集合 A)
  证明: (@Algebra.gc R A _ _ _).l_iSup

Depends on / 依赖: Algebra, Algebra.gc, l_iSup
-/
theorem adjoin_iUnion {α : Type*} (s : α -> Set A) :
    adjoin R (Set.iUnion s) = ⨆ i : α, adjoin R (s i) :=
  (@Algebra.gc R A _ _ _).l_iSup

/--
theorem `adjoin_attach_biUnion` / 定理 `adjoin_attach_biUnion`

English:
theorem adjoin_attach_biUnion
  given: [DecidableEq A] {α : Type*} {s : Finset α} (f : s -> Finset A)
  proof: by simp [adjoin_iUnion]

@[elab_as_elim]

中文:
定理 adjoin_attach_biUnion
  条件: [DecidableEq A] {α : 类型} {s : 有限集 α} (f : s -> 有限集 A)
  证明: by simp [adjoin_iUnion]

@[elab_as_elim]

Depends on / 依赖: adjoin_iUnion
-/
theorem adjoin_attach_biUnion [DecidableEq A] {α : Type*} {s : Finset α} (f : s -> Finset A) :
    adjoin R (s.attach.biUnion f : Set A) = ⨆ x, adjoin R (f x) := by simp [adjoin_iUnion]

@[elab_as_elim]
/--
theorem `adjoin_induction` / 定理 `adjoin_induction`

English:
theorem adjoin_induction
  statement: {p : (x : A) -> x in adjoin R s -> Prop}
  proof: let S : Subalgebra R A :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, add _ _ _ _ hpx hpy⟩
      algebraMap_mem' := fun r => ⟨_, algebraMap r⟩ }
.elim fun _ =

中文:
定理 adjoin_induction
  结论: {p : (x : A) -> x in adjoin R s -> 命题}
  证明: let S : Subalgebra R A :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, add _ _ _ _ hpx hpy⟩
      algebraMap_mem' := fun r => ⟨_, algebraMap r⟩ }
.elim fun _ =

Depends on / 依赖: Subalgebra, _root_, _root_.id, add_mem, adjoin_le, algebraMap, algebraMap_mem, carrier, mul_mem, subset_adjoin
-/
theorem adjoin_induction {p : (x : A) -> x in adjoin R s -> Prop}
    (mem : forall (x) (hx : x in s), p x (subset_adjoin hx))
    (algebraMap : forall r, p (algebraMap R A r) (algebraMap_mem _ r))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    {x : A} (hx : x in adjoin R s) : p x hx :=
  let S : Subalgebra R A :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, add _ _ _ _ hpx hpy⟩
      algebraMap_mem' := fun r => ⟨_, algebraMap r⟩ }
.elim fun _ => _root_.id adjoin_le (S := S) (fun y hy => ⟨subset_adjoin hy, mem y hy⟩) hx

/-- Induction principle for the algebra generated by a set `s`: show that `p x y` holds for any
`x y ∈ adjoin R s` given that it holds for `x y ∈ s` and that it satisfies a number of
natural properties. -/
@[elab_as_elim]
/--
theorem `adjoin_induction₂` / 定理 `adjoin_induction₂`

English:
theorem adjoin_induction₂
  statement: {s : Set A} {p : (x y : A) -> x in adjoin R s -> y in adjoin R s -> Prop}
  proof: by
  induction hy using adjoin_induction with
  | mem z hz => induction hx using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ 

中文:
定理 adjoin_induction₂
  结论: {s : 集合 A} {p : (x y : A) -> x in adjoin R s -> y in adjoin R s -> 命题}
  证明: by
  induction hy using adjoin_induction with
  | mem z hz => induction hx using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ 

Depends on / 依赖: add_left, adjoin_induction, algebraMap, algebraMap_both, algebraMap_left, algebraMap_right, mem_mem, mul_left
-/
theorem adjoin_induction₂ {s : Set A} {p : (x y : A) -> x in adjoin R s -> y in adjoin R s -> Prop}
    (mem_mem : forall (x) (y) (hx : x in s) (hy : y in s), p x y (subset_adjoin hx) (subset_adjoin hy))
    (algebraMap_both : forall r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂) (algebraMap_mem _ r₁)
      (algebraMap_mem _ r₂))
    (algebraMap_left : forall (r) (x) (hx : x in s), p (algebraMap R A r) x (algebraMap_mem _ r)
      (subset_adjoin hx))
    (algebraMap_right : forall (r) (x) (hx : x in s), p x (algebraMap R A r) (subset_adjoin hx)
      (algebraMap_mem _ r))
    (add_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x + y) z (add_mem hx hy) hz)
    (add_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y + z) hx (add_mem hy hz))
    (mul_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x * y) z (mul_mem hx hy) hz)
    (mul_right : forall x y z hx hy hz, p x y hx hy -> p x z hx hz -> p x (y * z) hx (mul_mem hy hz))
    {x y : A} (hx : x in adjoin R s) (hy : y in adjoin R s) :
    p x y hx hy := by
  induction hy using adjoin_induction with
  | mem z hz => induction hx using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | algebraMap r =>
    induction hx using adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

@[simp]
/--
theorem `adjoin_adjoin_coe_preimage` / 定理 `adjoin_adjoin_coe_preimage`

English:
theorem adjoin_adjoin_coe_preimage
  given: {s : Set A}
  statement: adjoin R (((↑) : adjoin R s -> A) ⁻¹' s) = ⊤
  proof: by
  refine eq_top_iff.2 fun ⟨x, hx⟩ =>
      adjoin_induction (fun a ha => ?_) (fun r => ?_) (fun _ _ _ _ => ?_) (fun _ _ _ _ => ?_) hx
  · exact subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _

中文:
定理 adjoin_adjoin_coe_preimage
  条件: {s : 集合 A}
  结论: adjoin R (((↑) : adjoin R s -> A) ⁻¹' s) = ⊤
  证明: by
  refine eq_top_iff.2 fun ⟨x, hx⟩ =>
      adjoin_induction (fun a ha => ?_) (fun r => ?_) (fun _ _ _ _ => ?_) (fun _ _ _ _ => ?_) hx
  · exact subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _

Depends on / 依赖: Subalgebra, Subalgebra.add_mem, Subalgebra.algebraMap_mem, Subalgebra.mul_mem, add_mem, adjoin_induction, algebraMap_mem, eq_top_iff, mul_mem, subset_adjoin
-/
theorem adjoin_adjoin_coe_preimage {s : Set A} : adjoin R (((↑) : adjoin R s -> A) ⁻¹' s) = ⊤ := by
  refine eq_top_iff.2 fun ⟨x, hx⟩ =>
      adjoin_induction (fun a ha => ?_) (fun r => ?_) (fun _ _ _ _ => ?_) (fun _ _ _ _ => ?_) hx
  · exact subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _

/--
theorem `adjoin_union` / 定理 `adjoin_union`

English:
theorem adjoin_union
  given: (s t : Set A)
  statement: adjoin R (s union t) = adjoin R s ⊔ adjoin R t
  proof: (Algebra.gc : GaloisConnection _ ((↑) : Subalgebra R A -> Set A)).l_sup

中文:
定理 adjoin_union
  条件: (s t : 集合 A)
  结论: adjoin R (s union t) = adjoin R s ⊔ adjoin R t
  证明: (Algebra.gc : GaloisConnection _ ((↑) : Subalgebra R A -> Set A)).l_sup

Depends on / 依赖: Algebra, Algebra.gc, GaloisConnection, Subalgebra, l_sup
-/
theorem adjoin_union (s t : Set A) : adjoin R (s union t) = adjoin R s ⊔ adjoin R t :=
  (Algebra.gc : GaloisConnection _ ((↑) : Subalgebra R A -> Set A)).l_sup

variable (R A)

@[simp]
/--
theorem `adjoin_empty` / 定理 `adjoin_empty`

English:
theorem adjoin_empty
  statement: adjoin R (∅ : Set A) = ⊥
  proof: Algebra.gc.l_bot

@[simp]

中文:
定理 adjoin_empty
  结论: adjoin R (∅ : 集合 A) = ⊥
  证明: Algebra.gc.l_bot

@[simp]

Depends on / 依赖: Algebra, Algebra.gc.l_bot, l_bot
-/
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ := Algebra.gc.l_bot

@[simp]
/--
theorem `adjoin_univ` / 定理 `adjoin_univ`

English:
theorem adjoin_univ
  statement: adjoin R (Set.univ : Set A) = ⊤
  proof: Algebra.gi.l_top

中文:
定理 adjoin_univ
  结论: adjoin R (集合.univ : 集合 A) = ⊤
  证明: Algebra.gi.l_top

Depends on / 依赖: Algebra, Algebra.gi.l_top, l_top
-/
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ := Algebra.gi.l_top

variable {R} in
@[simp]
/--
theorem `adjoin_singleton_algebraMap` / 定理 `adjoin_singleton_algebraMap`

English:
theorem adjoin_singleton_algebraMap
  given: (x : R)
  statement: R[algebraMap R A x] = ⊥
  proof: bot_unique adjoin_singleton_le Subalgebra.algebraMap_mem _ _

@[simp]

中文:
定理 adjoin_singleton_algebraMap
  条件: (x : R)
  结论: R[algebraMap R A x] = ⊥
  证明: bot_unique adjoin_singleton_le Subalgebra.algebraMap_mem _ _

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.algebraMap_mem, adjoin_singleton_le, algebraMap_mem, bot_unique
-/
theorem adjoin_singleton_algebraMap (x : R) : R[algebraMap R A x] = ⊥ :=
bot_unique adjoin_singleton_le Subalgebra.algebraMap_mem _ _

@[simp]
/--
theorem `adjoin_singleton_natCast` / 定理 `adjoin_singleton_natCast`

English:
theorem adjoin_singleton_natCast
  given: (n : Nat)
  statement: R[n : A] = ⊥
  proof: by
  simpa using adjoin_singleton_algebraMap A (n : R)

@[simp]

中文:
定理 adjoin_singleton_natCast
  条件: (n : 自然数)
  结论: R[n : A] = ⊥
  证明: by
  simpa using adjoin_singleton_algebraMap A (n : R)

@[simp]

Depends on / 依赖: adjoin_singleton_algebraMap
-/
theorem adjoin_singleton_natCast (n : Nat) : R[n : A] = ⊥ := by
  simpa using adjoin_singleton_algebraMap A (n : R)

@[simp]
/--
theorem `adjoin_singleton_zero` / 定理 `adjoin_singleton_zero`

English:
theorem adjoin_singleton_zero
  statement: R[0 : A] = ⊥
  proof: mod_cast adjoin_singleton_natCast R A 0

@[simp]

中文:
定理 adjoin_singleton_zero
  结论: R[0 : A] = ⊥
  证明: mod_cast adjoin_singleton_natCast R A 0

@[simp]

Depends on / 依赖: adjoin_singleton_natCast, mod_cast
-/
theorem adjoin_singleton_zero : R[0 : A] = ⊥ :=
  mod_cast adjoin_singleton_natCast R A 0

@[simp]
/--
theorem `adjoin_singleton_one` / 定理 `adjoin_singleton_one`

English:
theorem adjoin_singleton_one
  statement: R[1 : A]= ⊥
  proof: mod_cast adjoin_singleton_natCast R A 1

中文:
定理 adjoin_singleton_one
  结论: R[1 : A]= ⊥
  证明: mod_cast adjoin_singleton_natCast R A 1

Depends on / 依赖: adjoin_singleton_natCast, mod_cast
-/
theorem adjoin_singleton_one : R[1 : A]= ⊥ :=
  mod_cast adjoin_singleton_natCast R A 1

variable {A} (s)

variable {R} in
@[simp]
/--
theorem `adjoin_insert_algebraMap` / 定理 `adjoin_insert_algebraMap`

English:
theorem adjoin_insert_algebraMap
  given: (x : R) (s : Set A)
  proof: by
  rw [Set.insert_eq]; rw [adjoin_union]
  simp

@[simp]

中文:
定理 adjoin_insert_algebraMap
  条件: (x : R) (s : 集合 A)
  证明: by
  rw [Set.insert_eq]; rw [adjoin_union]
  simp

@[simp]

Depends on / 依赖: Set.insert_eq, adjoin_union, insert_eq
-/
theorem adjoin_insert_algebraMap (x : R) (s : Set A) :
    adjoin R (insert (algebraMap R A x) s) = adjoin R s := by
  rw [Set.insert_eq]; rw [adjoin_union]
  simp

@[simp]
/--
theorem `adjoin_insert_natCast` / 定理 `adjoin_insert_natCast`

English:
theorem adjoin_insert_natCast
  given: (n : Nat) (s : Set A)
  statement: adjoin R (insert (n : A) s) = adjoin R s
  proof: mod_cast adjoin_insert_algebraMap (n : R) s

@[simp]

中文:
定理 adjoin_insert_natCast
  条件: (n : 自然数) (s : 集合 A)
  结论: adjoin R (insert (n : A) s) = adjoin R s
  证明: mod_cast adjoin_insert_algebraMap (n : R) s

@[simp]

Depends on / 依赖: adjoin_insert_algebraMap, mod_cast
-/
theorem adjoin_insert_natCast (n : Nat) (s : Set A) : adjoin R (insert (n : A) s) = adjoin R s :=
  mod_cast adjoin_insert_algebraMap (n : R) s

@[simp]
/--
theorem `adjoin_insert_zero` / 定理 `adjoin_insert_zero`

English:
theorem adjoin_insert_zero
  given: (s : Set A)
  statement: adjoin R (insert 0 s) = adjoin R s
  proof: mod_cast adjoin_insert_natCast R 0 s

@[simp]

中文:
定理 adjoin_insert_zero
  条件: (s : 集合 A)
  结论: adjoin R (insert 0 s) = adjoin R s
  证明: mod_cast adjoin_insert_natCast R 0 s

@[simp]

Depends on / 依赖: adjoin_insert_natCast, mod_cast
-/
theorem adjoin_insert_zero (s : Set A) : adjoin R (insert 0 s) = adjoin R s :=
  mod_cast adjoin_insert_natCast R 0 s

@[simp]
/--
theorem `adjoin_insert_one` / 定理 `adjoin_insert_one`

English:
theorem adjoin_insert_one
  given: (s : Set A)
  statement: adjoin R (insert 1 s) = adjoin R s
  proof: mod_cast adjoin_insert_natCast R 1 s

中文:
定理 adjoin_insert_one
  条件: (s : 集合 A)
  结论: adjoin R (insert 1 s) = adjoin R s
  证明: mod_cast adjoin_insert_natCast R 1 s

Depends on / 依赖: adjoin_insert_natCast, mod_cast
-/
theorem adjoin_insert_one (s : Set A) : adjoin R (insert 1 s) = adjoin R s :=
  mod_cast adjoin_insert_natCast R 1 s

/--
theorem `adjoin_eq_span` / 定理 `adjoin_eq_span`

English:
theorem adjoin_eq_span
  statement: Subalgebra.toSubmodule (adjoin R s) = span R (Submonoid.closure s)
  proof: by
  apply le_antisymm
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction L with
    | nil => exact zero_mem _
    | cons hd tl ih => ?_
    rw [List.forall_mem_cons] at HL
    rw [List.map_cons]; rw [List.sum_cons]
    refine Submodul

中文:
定理 adjoin_eq_span
  结论: 子代数.toSubmodule (adjoin R s) = span R (子幺半群.closure s)
  证明: by
  apply le_antisymm
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction L with
    | nil => exact zero_mem _
    | cons hd tl ih => ?_
    rw [List.forall_mem_cons] at HL
    rw [List.map_cons]; rw [List.sum_cons]
    refine Submodul

Depends on / 依赖: List.forall_mem_cons, List.map_cons, List.prod, List.sum_cons, Submodule, Submodule.add_mem, Submonoid, Submonoid.closure, Subsemiring, Subsemiring.mem_closure_iff_exists_list, add_mem, closure, forall_mem_cons, le_antisymm, map_cons, mem_closure_iff_exists_list, replace, smul_mem, subset_span, sum_cons
-/
theorem adjoin_eq_span : Subalgebra.toSubmodule (adjoin R s) = span R (Submonoid.closure s) := by
  apply le_antisymm
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction L with
    | nil => exact zero_mem _
    | cons hd tl ih => ?_
    rw [List.forall_mem_cons] at HL
    rw [List.map_cons]; rw [List.sum_cons]
    refine Submodule.add_mem _ ?_ (ih HL.2)
    replace HL := HL.1
    clear ih tl
    suffices exists (z r : _) (_hr : r in Submonoid.closure s), z • r = List.prod hd by
      rcases this with ⟨z, r, hr, hzr⟩
      rw [← hzr]
      exact smul_mem _ _ (subset_span hr)
    induction hd with
    | nil => exact ⟨1, 1, (Submonoid.closure s).one_mem', one_smul _ _⟩
    | cons hd tl ih => ?_
    rw [List.forall_mem_cons] at HL
    rcases ih HL.2 with ⟨z, r, hr, hzr⟩
    rw [List.prod_cons]; rw [← hzr]
    rcases HL.1 with (⟨hd, rfl⟩ | hs)
    · refine ⟨hd * z, r, hr, ?_⟩
      rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [(algebraMap _ _).map_mul]; rw [_root_.mul_assoc]
    · exact
        ⟨z, hd * r, Submonoid.mul_mem _ (Submonoid.subset_closure hs) hr,
          (mul_smul_comm _ _ _).symm⟩
  refine span_le.2 ?_
  change Submonoid.closure s <= (adjoin R s).toSubsemiring.toSubmonoid
  exact Submonoid.closure_le.2 subset_adjoin

/--
theorem `span_le_adjoin` / 定理 `span_le_adjoin`

English:
theorem span_le_adjoin
  given: (s : Set A)
  statement: span R s <= Subalgebra.toSubmodule (adjoin R s)
  proof: span_le.mpr subset_adjoin

中文:
定理 span_le_adjoin
  条件: (s : 集合 A)
  结论: span R s <= 子代数.toSubmodule (adjoin R s)
  证明: span_le.mpr subset_adjoin

Depends on / 依赖: span_le, span_le.mpr, subset_adjoin
-/
theorem span_le_adjoin (s : Set A) : span R s <= Subalgebra.toSubmodule (adjoin R s) :=
  span_le.mpr subset_adjoin

/--
theorem `adjoin_toSubmodule_le` / 定理 `adjoin_toSubmodule_le`

English:
theorem adjoin_toSubmodule_le
  given: {s : Set A} {t : Submodule R A}
  proof: by
  rw [adjoin_eq_span]; rw [span_le]

中文:
定理 adjoin_toSubmodule_le
  条件: {s : 集合 A} {t : 子模 R A}
  证明: by
  rw [adjoin_eq_span]; rw [span_le]

Depends on / 依赖: adjoin_eq_span, span_le
-/
theorem adjoin_toSubmodule_le {s : Set A} {t : Submodule R A} :
    Subalgebra.toSubmodule (adjoin R s) <= t ↔ ↑(Submonoid.closure s) subseteq (t : Set A) := by
  rw [adjoin_eq_span]; rw [span_le]

/--
theorem `adjoin_eq_span_of_subset` / 定理 `adjoin_eq_span_of_subset`

English:
theorem adjoin_eq_span_of_subset
  given: {s : Set A} (hs : ↑(Submonoid.closure s) subseteq (span R s : Set A))
  proof: le_antisymm ((adjoin_toSubmodule_le R).mpr hs) (span_le_adjoin R s)

@[simp]

中文:
定理 adjoin_eq_span_of_subset
  条件: {s : 集合 A} (hs : ↑(子幺半群.closure s) subseteq (span R s : 集合 A))
  证明: le_antisymm ((adjoin_toSubmodule_le R).mpr hs) (span_le_adjoin R s)

@[simp]

Depends on / 依赖: adjoin_toSubmodule_le, le_antisymm, span_le_adjoin
-/
theorem adjoin_eq_span_of_subset {s : Set A} (hs : ↑(Submonoid.closure s) subseteq (span R s : Set A)) :
    Subalgebra.toSubmodule (adjoin R s) = span R s :=
  le_antisymm ((adjoin_toSubmodule_le R).mpr hs) (span_le_adjoin R s)

@[simp]
/--
theorem `adjoin_span` / 定理 `adjoin_span`

English:
theorem adjoin_span
  given: {s : Set A}
  statement: adjoin R (Submodule.span R s : Set A) = adjoin R s
  proof: le_antisymm (adjoin_le (span_le_adjoin _ _)) (adjoin_mono Submodule.subset_span)

中文:
定理 adjoin_span
  条件: {s : 集合 A}
  结论: adjoin R (子模.span R s : 集合 A) = adjoin R s
  证明: le_antisymm (adjoin_le (span_le_adjoin _ _)) (adjoin_mono Submodule.subset_span)

Depends on / 依赖: Submodule, Submodule.subset_span, adjoin_le, adjoin_mono, le_antisymm, span_le_adjoin, subset_span
-/
theorem adjoin_span {s : Set A} : adjoin R (Submodule.span R s : Set A) = adjoin R s :=
  le_antisymm (adjoin_le (span_le_adjoin _ _)) (adjoin_mono Submodule.subset_span)

/--
theorem `adjoin_image` / 定理 `adjoin_image`

English:
theorem adjoin_image
  given: (f : A ->ₐ[R] B) (s : Set A)
  statement: adjoin R (f '' s) = (adjoin R s).map f
  proof: eq_of_forall_ge_iff fun t => by simp [Subalgebra.map_le, adjoin_le_iff]

@[simp]

中文:
定理 adjoin_image
  条件: (f : A ->ₐ[R] B) (s : 集合 A)
  结论: adjoin R (f '' s) = (adjoin R s).map f
  证明: eq_of_forall_ge_iff fun t => by simp [Subalgebra.map_le, adjoin_le_iff]

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.map_le, adjoin_le_iff, eq_of_forall_ge_iff, map_le
-/
theorem adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R s).map f :=
  eq_of_forall_ge_iff fun t => by simp [Subalgebra.map_le, adjoin_le_iff]

@[simp]
/--
theorem `adjoin_insert_adjoin` / 定理 `adjoin_insert_adjoin`

English:
theorem adjoin_insert_adjoin
  given: (x : A)
  statement: adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s)
  proof: eq_of_forall_ge_iff fun t => by simp [adjoin_le_iff, Set.insert_subset_iff]

中文:
定理 adjoin_insert_adjoin
  条件: (x : A)
  结论: adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s)
  证明: eq_of_forall_ge_iff fun t => by simp [adjoin_le_iff, Set.insert_subset_iff]

Depends on / 依赖: Set.insert_subset_iff, adjoin_le_iff, eq_of_forall_ge_iff, insert_subset_iff
-/
theorem adjoin_insert_adjoin (x : A) : adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s) :=
  eq_of_forall_ge_iff fun t => by simp [adjoin_le_iff, Set.insert_subset_iff]

/--
theorem `mem_adjoin_of_map_mul` / 定理 `mem_adjoin_of_map_mul`

English:
theorem mem_adjoin_of_map_mul
  statement: {s} {x : A} {f : A ->ₗ[R] B} (hf : forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
  proof: by
  induction h using adjoin_induction with
  | mem a ha => exact subset_adjoin ⟨a, ⟨Set.subset_union_left ha, rfl⟩⟩
  | algebraMap r =>
    have : f 1 in adjoin R (f '' (s union {1})) :=
subset_adjoin ⟨1, ⟨Set.subset_union_right Set.mem_singleton 1, rfl⟩⟩
    convert! Subalgebra.smul_mem (adjoin R

中文:
定理 mem_adjoin_of_map_mul
  结论: {s} {x : A} {f : A ->ₗ[R] B} (hf : 对任意 a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
  证明: by
  induction h using adjoin_induction with
  | mem a ha => exact subset_adjoin ⟨a, ⟨Set.subset_union_left ha, rfl⟩⟩
  | algebraMap r =>
    have : f 1 in adjoin R (f '' (s union {1})) :=
subset_adjoin ⟨1, ⟨Set.subset_union_right Set.mem_singleton 1, rfl⟩⟩
    convert! Subalgebra.smul_mem (adjoin R

Depends on / 依赖: Set.mem_singleton, Set.subset_union_left, Set.subset_union_right, Subalgebra, Subalgebra.add_mem, Subalgebra.mul, Subalgebra.smul_mem, add_mem, adjoin, adjoin_induction, algebraMap, algebraMap_eq_smul_one, convert, f.map_smul, map_smul, mem_singleton, smul_mem, subset_adjoin, subset_union_left, subset_union_right
-/
theorem mem_adjoin_of_map_mul {s} {x : A} {f : A ->ₗ[R] B} (hf : forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
    (h : x in adjoin R s) : f x in adjoin R (f '' (s union {1})) := by
  induction h using adjoin_induction with
  | mem a ha => exact subset_adjoin ⟨a, ⟨Set.subset_union_left ha, rfl⟩⟩
  | algebraMap r =>
    have : f 1 in adjoin R (f '' (s union {1})) :=
subset_adjoin ⟨1, ⟨Set.subset_union_right Set.mem_singleton 1, rfl⟩⟩
    convert! Subalgebra.smul_mem (adjoin R (f '' (s union { 1 }))) this r
    rw [algebraMap_eq_smul_one]
    exact f.map_smul _ _
  | add y z _ _ hy hz => simpa [hy, hz] using Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => simpa [hf, hy, hz] using Subalgebra.mul_mem _ hy hz

/--
lemma `adjoin_le_centralizer_centralizer` / 引理 `adjoin_le_centralizer_centralizer`

English:
lemma adjoin_le_centralizer_centralizer
  given: (s : Set A)
  proof: adjoin_le Set.subset_centralizer_centralizer

中文:
引理 adjoin_le_centralizer_centralizer
  条件: (s : 集合 A)
  证明: adjoin_le Set.subset_centralizer_centralizer

Depends on / 依赖: Set.subset_centralizer_centralizer, adjoin_le, subset_centralizer_centralizer
-/
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s <= Subalgebra.centralizer R (Subalgebra.centralizer R s) :=
  adjoin_le Set.subset_centralizer_centralizer

/--
theorem `isMulCommutative_adjoin` / 定理 `isMulCommutative_adjoin`

English:
theorem isMulCommutative_adjoin
  given: {s : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x)
  proof: have := adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

中文:
定理 isMulCommutative_adjoin
  条件: {s : 集合 A} (hcomm : 对任意 x in s, 对任意 y in s, x * y = y * x)
  证明: have := adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, adjoin_le_centralizer_centralizer, centralizer_centralizer_comm_of_comm, of_setLike_mul_comm
-/
theorem isMulCommutative_adjoin {s : Set A} (hcomm : forall x in s, forall y in s, x * y = y * x) :
    IsMulCommutative (adjoin R s) :=
  have := adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

/--
Instance `isMulCommutative_adjoin_singleton` / 实例 `isMulCommutative_adjoin_singleton`

English:
instance isMulCommutative_adjoin_singleton
  signature: (x : A)
  body: isMulCommutative_adjoin R (by simp)

中文:
实例 isMulCommutative_adjoin_singleton
  签名: (x : A)
  定义体: isMulCommutative_adjoin R (by simp)

Depends on / 依赖: isMulCommutative_adjoin
-/
instance isMulCommutative_adjoin_singleton (x : A) :
    IsMulCommutative (adjoin R ({x} : Set A)) :=
  isMulCommutative_adjoin R (by simp)

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a non-unital commutative
semiring.

See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/--
Definition of `adjoinCommSemiringOfComm` / `adjoinCommSemiringOfComm` 的定义

English:
abbreviation adjoinCommSemiringOfComm
  signature: {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a)
  body: have := isMulCommutative_adjoin R hcomm
  inferInstance

中文:
缩写 adjoinCommSemiringOfComm
  签名: {s : 集合 A} (hcomm : 对任意 a in s, 对任意 b in s, a * b = b * a)
  定义体: have := isMulCommutative_adjoin R hcomm
  inferInstance

Depends on / 依赖: isMulCommutative_adjoin
-/
abbrev adjoinCommSemiringOfComm {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a) :
    CommSemiring (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm
  inferInstance

/--
Instance `instIsMulCommutative_adjoin` / 实例 `instIsMulCommutative_adjoin`

English:
instance instIsMulCommutative_adjoin
  signature: {S : Type*} [SetLike S A] [MulMemClass S A] (s : S)
  body: isMulCommutative_adjoin R fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

中文:
实例 instIsMulCommutative_adjoin
  签名: {S : 类型} [集合状 S A] [MulMem类 S A] (s : S)
  定义体: isMulCommutative_adjoin R fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

Depends on / 依赖: isMulCommutative_adjoin, setLike_mul_comm
-/
instance instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] (s : S)
    [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A)) :=
  isMulCommutative_adjoin R fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

variable {R}

/--
lemma `commute_of_mem_adjoin_of_forall_mem_commute` / 引理 `commute_of_mem_adjoin_of_forall_mem_commute`

English:
lemma commute_of_mem_adjoin_of_forall_mem_commute
  statement: {a b : A} {s : Set A}
  proof: by
  induction hb using adjoin_induction with
  | mem x hx => exact h x hx
.symm | algebraMap r => exact commutes r a
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz

中文:
引理 commute_of_mem_adjoin_of_对任意_mem_commute
  结论: {a b : A} {s : 集合 A}
  证明: by
  induction hb using adjoin_induction with
  | mem x hx => exact h x hx
.symm | algebraMap r => exact commutes r a
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz

Depends on / 依赖: add_right, adjoin_induction, algebraMap, commutes, hy.add_right, hy.mul_right, mul_right
-/
lemma commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b in adjoin R s) (h : forall b in s, Commute a b) :
    Commute a b := by
  induction hb using adjoin_induction with
  | mem x hx => exact h x hx
.symm | algebraMap r => exact commutes r a
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz

/--
lemma `commute_of_mem_adjoin_singleton_of_commute` / 引理 `commute_of_mem_adjoin_singleton_of_commute`

English:
lemma commute_of_mem_adjoin_singleton_of_commute
  statement: {a b c : A}
  proof: commute_of_mem_adjoin_of_forall_mem_commute hc by simpa

中文:
引理 commute_of_mem_adjoin_singleton_of_commute
  结论: {a b c : A}
  证明: commute_of_mem_adjoin_of_forall_mem_commute hc by simpa

Depends on / 依赖: commute_of_mem_adjoin_of_forall_mem_commute
-/
lemma commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c in R[b]) (h : Commute a b) :
    Commute a c :=
commute_of_mem_adjoin_of_forall_mem_commute hc by simpa

/--
lemma `commute_of_mem_adjoin_self` / 引理 `commute_of_mem_adjoin_self`

English:
lemma commute_of_mem_adjoin_self
  given: {a b : A} (hb : b in R[a])
  proof: commute_of_mem_adjoin_singleton_of_commute hb rfl

中文:
引理 commute_of_mem_adjoin_self
  条件: {a b : A} (hb : b in R[a])
  证明: commute_of_mem_adjoin_singleton_of_commute hb rfl

Depends on / 依赖: commute_of_mem_adjoin_singleton_of_commute
-/
lemma commute_of_mem_adjoin_self {a b : A} (hb : b in R[a]) :
    Commute a b :=
  commute_of_mem_adjoin_singleton_of_commute hb rfl

variable (R)

@[simp]
/--
theorem `self_mem_adjoin_singleton` / 定理 `self_mem_adjoin_singleton`

English:
theorem self_mem_adjoin_singleton
  given: (x : A)
  statement: x in R[x]
  proof: Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)

中文:
定理 self_mem_adjoin_singleton
  条件: (x : A)
  结论: x in R[x]
  证明: Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Set.mem_singleton_iff.mpr, mem_singleton_iff, subset_adjoin
-/
theorem self_mem_adjoin_singleton (x : A) : x in R[x] :=
  Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [Algebra R A] {s t : Set A}
variable (R s t)

/--
theorem `adjoin_union_coe_submodule` / 定理 `adjoin_union_coe_submodule`

English:
theorem adjoin_union_coe_submodule
  proof: by
  rw [adjoin_eq_span]; rw [adjoin_eq_span]; rw [adjoin_eq_span]; rw [span_mul_span]
  congr 1 with z; simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]

中文:
定理 adjoin_union_coe_submodule
  证明: by
  rw [adjoin_eq_span]; rw [adjoin_eq_span]; rw [adjoin_eq_span]; rw [span_mul_span]
  congr 1 with z; simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]

Depends on / 依赖: Set.mem_mul, Submonoid, Submonoid.closure_union, Submonoid.mem_sup, adjoin_eq_span, closure_union, mem_mul, mem_sup, span_mul_span
-/
theorem adjoin_union_coe_submodule :
    Subalgebra.toSubmodule (adjoin R (s union t)) =
      Subalgebra.toSubmodule (adjoin R s) * Subalgebra.toSubmodule (adjoin R t) := by
  rw [adjoin_eq_span]; rw [adjoin_eq_span]; rw [adjoin_eq_span]; rw [span_mul_span]
  congr 1 with z; simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]

end CommSemiring

section Ring

variable [CommRing R] [Ring A]
variable [Algebra R A] {s t : Set A}

@[simp]
/--
theorem `adjoin_singleton_intCast` / 定理 `adjoin_singleton_intCast`

English:
theorem adjoin_singleton_intCast
  given: (n : Int)
  statement: R[n : A] = ⊥
  proof: by
  simpa using adjoin_singleton_algebraMap A (n : R)

@[simp]

中文:
定理 adjoin_singleton_intCast
  条件: (n : 整数)
  结论: R[n : A] = ⊥
  证明: by
  simpa using adjoin_singleton_algebraMap A (n : R)

@[simp]

Depends on / 依赖: adjoin_singleton_algebraMap
-/
theorem adjoin_singleton_intCast (n : Int) : R[n : A] = ⊥ := by
  simpa using adjoin_singleton_algebraMap A (n : R)

@[simp]
/--
theorem `adjoin_insert_intCast` / 定理 `adjoin_insert_intCast`

English:
theorem adjoin_insert_intCast
  given: (n : Int) (s : Set A)
  statement: adjoin R (insert (n : A) s) = adjoin R s
  proof: by
  simpa using adjoin_insert_algebraMap (n : R) s

中文:
定理 adjoin_insert_intCast
  条件: (n : 整数) (s : 集合 A)
  结论: adjoin R (insert (n : A) s) = adjoin R s
  证明: by
  simpa using adjoin_insert_algebraMap (n : R) s

Depends on / 依赖: adjoin_insert_algebraMap
-/
theorem adjoin_insert_intCast (n : Int) (s : Set A) : adjoin R (insert (n : A) s) = adjoin R s := by
  simpa using adjoin_insert_algebraMap (n : R) s

/--
theorem `adjoin_eq_ring_closure` / 定理 `adjoin_eq_ring_closure`

English:
theorem adjoin_eq_ring_closure
  given: (s : Set A)
  proof: .symm Subring.closure_eq_of_le (by simp [adjoin]) fun x hx =>
    Subsemiring.closure_induction Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ _ _ => Subring.add_mem _) (fun _ _ _ _ => Subring.mul_mem _) hx

中文:
定理 adjoin_eq_ring_closure
  条件: (s : 集合 A)
  证明: .symm Subring.closure_eq_of_le (by simp [adjoin]) fun x hx =>
    Subsemiring.closure_induction Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ _ _ => Subring.add_mem _) (fun _ _ _ _ => Subring.mul_mem _) hx

Depends on / 依赖: Subring, Subring.add_mem, Subring.closure_eq_of_le, Subring.mul_mem, Subring.one_mem, Subring.subset_closure, Subring.zero_mem, Subsemiring, Subsemiring.closure_induction, add_mem, adjoin, closure_eq_of_le, closure_induction, mul_mem, one_mem, subset_closure, zero_mem
-/
theorem adjoin_eq_ring_closure (s : Set A) :
    (adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) union s) :=
.symm Subring.closure_eq_of_le (by simp [adjoin]) fun x hx =>
    Subsemiring.closure_induction Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ _ _ => Subring.add_mem _) (fun _ _ _ _ => Subring.mul_mem _) hx

/--
theorem `mem_adjoin_iff` / 定理 `mem_adjoin_iff`

English:
theorem mem_adjoin_iff
  given: {s : Set A} {x : A}
  proof: by
  rw [← Subalgebra.mem_toSubring]; rw [adjoin_eq_ring_closure]

中文:
定理 mem_adjoin_iff
  条件: {s : 集合 A} {x : A}
  证明: by
  rw [← Subalgebra.mem_toSubring]; rw [adjoin_eq_ring_closure]

Depends on / 依赖: Subalgebra, Subalgebra.mem_toSubring, adjoin_eq_ring_closure, mem_toSubring
-/
theorem mem_adjoin_iff {s : Set A} {x : A} :
    x in adjoin R s ↔ x in Subring.closure (Set.range (algebraMap R A) union s) := by
  rw [← Subalgebra.mem_toSubring]; rw [adjoin_eq_ring_closure]

variable (R)

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a commutative
ring. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/--
Definition of `adjoinCommRingOfComm` / `adjoinCommRingOfComm` 的定义

English:
abbreviation adjoinCommRingOfComm
  signature: {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a)
  body: have := isMulCommutative_adjoin R hcomm
  inferInstance

中文:
缩写 adjoinCommRingOfComm
  签名: {s : 集合 A} (hcomm : 对任意 a in s, 对任意 b in s, a * b = b * a)
  定义体: have := isMulCommutative_adjoin R hcomm
  inferInstance

Depends on / 依赖: isMulCommutative_adjoin
-/
abbrev adjoinCommRingOfComm {s : Set A} (hcomm : forall a in s, forall b in s, a * b = b * a) :
    CommRing (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm
  inferInstance

end Ring

end Algebra

open Algebra Subalgebra

namespace AlgHom

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/--
theorem `map_adjoin` / 定理 `map_adjoin`

English:
theorem map_adjoin
  given: (φ : A ->ₐ[R] B) (s : Set A)
  statement: (adjoin R s).map φ = adjoin R (φ '' s)
  proof: (adjoin_image _ _ _).symm

@[simp]

中文:
定理 map_adjoin
  条件: (φ : A ->ₐ[R] B) (s : 集合 A)
  结论: (adjoin R s).map φ = adjoin R (φ '' s)
  证明: (adjoin_image _ _ _).symm

@[simp]

Depends on / 依赖: adjoin_image
-/
theorem map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ '' s) :=
  (adjoin_image _ _ _).symm

@[simp]
/--
theorem `map_adjoin_singleton` / 定理 `map_adjoin_singleton`

English:
theorem map_adjoin_singleton
  given: (e : A ->ₐ[R] B) (x : A)
  proof: by
  rw [map_adjoin]; rw [Set.image_singleton]

中文:
定理 map_adjoin_singleton
  条件: (e : A ->ₐ[R] B) (x : A)
  证明: by
  rw [map_adjoin]; rw [Set.image_singleton]

Depends on / 依赖: Set.image_singleton, image_singleton, map_adjoin
-/
theorem map_adjoin_singleton (e : A ->ₐ[R] B) (x : A) :
    (R[x]).map e = R[e x] := by
  rw [map_adjoin]; rw [Set.image_singleton]

/--
theorem `adjoin_le_equalizer` / 定理 `adjoin_le_equalizer`

English:
theorem adjoin_le_equalizer
  given: (φ₁ φ₂ : A ->ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂)
  proof: adjoin_le h

中文:
定理 adjoin_le_equalizer
  条件: (φ₁ φ₂ : A ->ₐ[R] B) {s : 集合 A} (h : s.EqOn φ₁ φ₂)
  证明: adjoin_le h

Depends on / 依赖: adjoin_le
-/
theorem adjoin_le_equalizer (φ₁ φ₂ : A ->ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂) :
    adjoin R s <= equalizer φ₁ φ₂ :=
  adjoin_le h

/--
theorem `ext_of_adjoin_eq_top` / 定理 `ext_of_adjoin_eq_top`

English:
theorem ext_of_adjoin_eq_top
  given: {s : Set A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂
  statement: A ->ₐ[R] B⦄
  proof: ext fun _x => adjoin_le_equalizer φ₁ φ₂ hs h.symm ▸ trivial

中文:
定理 ext_of_adjoin_eq_top
  条件: {s : 集合 A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂
  结论: A ->ₐ[R] B⦄
  证明: ext fun _x => adjoin_le_equalizer φ₁ φ₂ hs h.symm ▸ trivial

Depends on / 依赖: adjoin_le_equalizer, h.symm
-/
theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂ : A ->ₐ[R] B⦄
    (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂ :=
ext fun _x => adjoin_le_equalizer φ₁ φ₂ hs h.symm ▸ trivial

/--
theorem `eqOn_adjoin_iff` / 定理 `eqOn_adjoin_iff`

English:
theorem eqOn_adjoin_iff
  given: {φ ψ : A ->ₐ[R] B} {s : Set A}
  proof: by
  have (S : Set A) : S <= equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl
  simp only [← this, SetLike.coe_subset_coe, adjoin_le_iff]

中文:
定理 eqOn_adjoin_iff
  条件: {φ ψ : A ->ₐ[R] B} {s : 集合 A}
  证明: by
  have (S : Set A) : S <= equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl
  simp only [← this, SetLike.coe_subset_coe, adjoin_le_iff]

Depends on / 依赖: Iff.rfl, Set.EqOn, SetLike, SetLike.coe_subset_coe, adjoin_le_iff, coe_subset_coe, equalizer
-/
theorem eqOn_adjoin_iff {φ ψ : A ->ₐ[R] B} {s : Set A} :
    Set.EqOn φ ψ (adjoin R s) ↔ Set.EqOn φ ψ s := by
  have (S : Set A) : S <= equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl
  simp only [← this, SetLike.coe_subset_coe, adjoin_le_iff]

/--
theorem `adjoin_ext` / 定理 `adjoin_ext`

English:
theorem adjoin_ext
  given: {s : Set A} ⦃φ₁ φ₂
  statement: adjoin R s ->ₐ[R] B⦄
  proof: ext fun ⟨x, hx⟩ => adjoin_induction h (fun _ => φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl) hx

中文:
定理 adjoin_ext
  条件: {s : 集合 A} ⦃φ₁ φ₂
  结论: adjoin R s ->ₐ[R] B⦄
  证明: ext fun ⟨x, hx⟩ => adjoin_induction h (fun _ => φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl) hx

Depends on / 依赖: adjoin_induction, commutes, convert, map_add, map_mul
-/
theorem adjoin_ext {s : Set A} ⦃φ₁ φ₂ : adjoin R s ->ₐ[R] B⦄
    (h : forall x hx, φ₁ ⟨x, subset_adjoin hx⟩ = φ₂ ⟨x, subset_adjoin hx⟩) : φ₁ = φ₂ :=
  ext fun ⟨x, hx⟩ => adjoin_induction h (fun _ => φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl) hx

/--
theorem `ext_of_eq_adjoin` / 定理 `ext_of_eq_adjoin`

English:
theorem ext_of_eq_adjoin
  given: {S : Subalgebra R A} {s : Set A} (hS : S = adjoin R s) ⦃φ₁ φ₂
  statement: S ->ₐ[R] B⦄
  proof: by
  subst hS; exact adjoin_ext h

中文:
定理 ext_of_eq_adjoin
  条件: {S : 子代数 R A} {s : 集合 A} (hS : S = adjoin R s) ⦃φ₁ φ₂
  结论: S ->ₐ[R] B⦄
  证明: by
  subst hS; exact adjoin_ext h

Depends on / 依赖: adjoin_ext
-/
theorem ext_of_eq_adjoin {S : Subalgebra R A} {s : Set A} (hS : S = adjoin R s) ⦃φ₁ φ₂ : S ->ₐ[R] B⦄
    (h : forall x hx, φ₁ ⟨x, hS.ge (subset_adjoin hx)⟩ = φ₂ ⟨x, hS.ge (subset_adjoin hx)⟩) :
    φ₁ = φ₂ := by
  subst hS; exact adjoin_ext h

/--
theorem `_root_.Algebra.forall_mem_adjoin_smul_eq_self_iff` / 定理 `_root_.Algebra.forall_mem_adjoin_smul_eq_self_iff`

English:
theorem _root_.Algebra.forall_mem_adjoin_smul_eq_self_iff
  statement: (S : Set A) {M : Type*} [Monoid M]
  proof: AlgHom.eqOn_adjoin_iff (φ := MulSemiringAction.toAlgHom R A m) (ψ := .id R A)

中文:
定理 _root_.代数.对任意_mem_adjoin_smul_eq_self_iff
  结论: (S : 集合 A) {M : 类型} [幺半群 M]
  证明: AlgHom.eqOn_adjoin_iff (φ := MulSemiringAction.toAlgHom R A m) (ψ := .id R A)

Depends on / 依赖: AlgHom, AlgHom.eqOn_adjoin_iff, MulSemiringAction, MulSemiringAction.toAlgHom, eqOn_adjoin_iff, toAlgHom
-/
theorem _root_.Algebra.forall_mem_adjoin_smul_eq_self_iff (S : Set A) {M : Type*} [Monoid M]
    [MulSemiringAction M A] [SMulCommClass M R A] (m : M) :
    (forall x in adjoin R S, m • x = x) ↔ (forall x in S, m • x = x) :=
  AlgHom.eqOn_adjoin_iff (φ := MulSemiringAction.toAlgHom R A m) (ψ := .id R A)

end AlgHom

section NatInt

/--
theorem `Algebra.adjoin_nat` / 定理 `Algebra.adjoin_nat`

English:
theorem Algebra.adjoin_nat
  given: {R : Type*} [Semiring R] (s : Set R)
  proof: le_antisymm (adjoin_le Subsemiring.subset_closure)
    (Subsemiring.closure_le.2 subset_adjoin : Subsemiring.closure s <= (adjoin Nat s).toSubsemiring)

中文:
定理 代数.adjoin_nat
  条件: {R : 类型} [半环 R] (s : 集合 R)
  证明: le_antisymm (adjoin_le Subsemiring.subset_closure)
    (Subsemiring.closure_le.2 subset_adjoin : Subsemiring.closure s <= (adjoin Nat s).toSubsemiring)

Depends on / 依赖: Subsemiring, Subsemiring.closure, Subsemiring.closure_le, Subsemiring.subset_closure, adjoin, adjoin_le, closure, closure_le, le_antisymm, subset_adjoin, subset_closure, toSubsemiring
-/
theorem Algebra.adjoin_nat {R : Type*} [Semiring R] (s : Set R) :
    adjoin Nat s = subalgebraOfSubsemiring (Subsemiring.closure s) :=
  le_antisymm (adjoin_le Subsemiring.subset_closure)
    (Subsemiring.closure_le.2 subset_adjoin : Subsemiring.closure s <= (adjoin Nat s).toSubsemiring)

/--
theorem `Algebra.adjoin_int` / 定理 `Algebra.adjoin_int`

English:
theorem Algebra.adjoin_int
  given: {R : Type*} [Ring R] (s : Set R)
  proof: le_antisymm (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s <= (adjoin Int s).toSubring)

中文:
定理 代数.adjoin_int
  条件: {R : 类型} [环 R] (s : 集合 R)
  证明: le_antisymm (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s <= (adjoin Int s).toSubring)

Depends on / 依赖: Subring, Subring.closure, Subring.closure_le, Subring.subset_closure, adjoin, adjoin_le, closure, closure_le, le_antisymm, subset_adjoin, subset_closure, toSubring
-/
theorem Algebra.adjoin_int {R : Type*} [Ring R] (s : Set R) :
    adjoin Int s = subalgebraOfSubring (Subring.closure s) :=
  le_antisymm (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s <= (adjoin Int s).toSubring)

/--
Definition of `Subsemiring.closureEquivAdjoinNat` / `Subsemiring.closureEquivAdjoinNat` 的定义

English:
definition Subsemiring.closureEquivAdjoinNat
  signature: {R : Type*} [Semiring R] (s : Set R)
  body: Subalgebra.equivOfEq (subalgebraOfSubsemiring <| Subsemiring.closure s) _ (adjoin_nat s).symm

中文:
定义 子半环.closureEquivAdjoin自然数
  签名: {R : 类型} [半环 R] (s : 集合 R)
  定义体: Subalgebra.equivOfEq (subalgebraOfSubsemiring <| Subsemiring.closure s) _ (adjoin_nat s).symm

Depends on / 依赖: Subalgebra, Subalgebra.equivOfEq, Subsemiring, Subsemiring.closure, adjoin_nat, closure, equivOfEq, subalgebraOfSubsemiring
-/
def Subsemiring.closureEquivAdjoinNat {R : Type*} [Semiring R] (s : Set R) :
    Subsemiring.closure s ≃ₐ[Nat] Algebra.adjoin Nat s :=
  Subalgebra.equivOfEq (subalgebraOfSubsemiring <| Subsemiring.closure s) _ (adjoin_nat s).symm

/--
Definition of `Subring.closureEquivAdjoinInt` / `Subring.closureEquivAdjoinInt` 的定义

English:
definition Subring.closureEquivAdjoinInt
  signature: {R : Type*} [Ring R] (s : Set R)
  body: Subalgebra.equivOfEq (subalgebraOfSubring <| Subring.closure s) _ (adjoin_int s).symm

中文:
定义 子环.closureEquivAdjoin整数
  签名: {R : 类型} [环 R] (s : 集合 R)
  定义体: Subalgebra.equivOfEq (subalgebraOfSubring <| Subring.closure s) _ (adjoin_int s).symm

Depends on / 依赖: Subalgebra, Subalgebra.equivOfEq, Subring, Subring.closure, adjoin_int, closure, equivOfEq, subalgebraOfSubring
-/
def Subring.closureEquivAdjoinInt {R : Type*} [Ring R] (s : Set R) :
    Subring.closure s ≃ₐ[Int] Algebra.adjoin Int s :=
  Subalgebra.equivOfEq (subalgebraOfSubring <| Subring.closure s) _ (adjoin_int s).symm

end NatInt

section

variable (F E : Type*) {K : Type*} [CommSemiring E] [Semiring K] [SMul F E] [Algebra E K]

/--
theorem `Submonoid.adjoin_eq_span_of_eq_span` / 定理 `Submonoid.adjoin_eq_span_of_eq_span`

English:
theorem Submonoid.adjoin_eq_span_of_eq_span
  statement: [Semiring F] [Module F K] [IsScalarTower F E K]
  proof: by
  rw [adjoin_eq_span]; rw [L.closure_eq]; rw [h]
  exact (span_le.mpr <| span_subset_span _ _ _).antisymm (span_mono subset_span)

中文:
定理 子幺半群.adjoin_eq_span_of_eq_span
  结论: [半环 F] [模 F K] [标量塔 F E K]
  证明: by
  rw [adjoin_eq_span]; rw [L.closure_eq]; rw [h]
  exact (span_le.mpr <| span_subset_span _ _ _).antisymm (span_mono subset_span)

Depends on / 依赖: L.closure_eq, adjoin_eq_span, antisymm, closure_eq, span_le, span_le.mpr, span_mono, span_subset_span, subset_span
-/
theorem Submonoid.adjoin_eq_span_of_eq_span [Semiring F] [Module F K] [IsScalarTower F E K]
    (L : Submonoid K) {S : Set K} (h : (L : Set K) = span F S) :
    toSubmodule (adjoin E (L : Set K)) = span E S := by
  rw [adjoin_eq_span]; rw [L.closure_eq]; rw [h]
  exact (span_le.mpr <| span_subset_span _ _ _).antisymm (span_mono subset_span)

variable [CommSemiring F] [Algebra F K] [IsScalarTower F E K] (L : Subalgebra F K) {F}

/--
theorem `Subalgebra.adjoin_eq_span_of_eq_span` / 定理 `Subalgebra.adjoin_eq_span_of_eq_span`

English:
theorem Subalgebra.adjoin_eq_span_of_eq_span
  given: {S : Set K} (h : toSubmodule L = span F S)
  proof: L.toSubmonoid.adjoin_eq_span_of_eq_span F E (congr_arg ((↑) : _ -> Set K) h)

中文:
定理 子代数.adjoin_eq_span_of_eq_span
  条件: {S : 集合 K} (h : toSubmodule L = span F S)
  证明: L.toSubmonoid.adjoin_eq_span_of_eq_span F E (congr_arg ((↑) : _ -> Set K) h)

Depends on / 依赖: L.toSubmonoid.adjoin_eq_span_of_eq_span, adjoin_eq_span_of_eq_span, congr_arg, toSubmonoid
-/
theorem Subalgebra.adjoin_eq_span_of_eq_span {S : Set K} (h : toSubmodule L = span F S) :
    toSubmodule (adjoin E (L : Set K)) = span E S :=
  L.toSubmonoid.adjoin_eq_span_of_eq_span F E (congr_arg ((↑) : _ -> Set K) h)

end

section CommSemiring
variable (R) [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/--
lemma `NonUnitalAlgebra.adjoin_le_algebra_adjoin` / 引理 `NonUnitalAlgebra.adjoin_le_algebra_adjoin`

English:
lemma NonUnitalAlgebra.adjoin_le_algebra_adjoin
  given: (s : Set A)
  proof: adjoin_le Algebra.subset_adjoin

中文:
引理 NonUnitalAlgebra.adjoin_le_algebra_adjoin
  条件: (s : 集合 A)
  证明: adjoin_le Algebra.subset_adjoin

Depends on / 依赖: Algebra, Algebra.subset_adjoin, adjoin_le, subset_adjoin
-/
lemma NonUnitalAlgebra.adjoin_le_algebra_adjoin (s : Set A) :
    adjoin R s <= (Algebra.adjoin R s).toNonUnitalSubalgebra := adjoin_le Algebra.subset_adjoin

/--
lemma `Algebra.adjoin_nonUnitalSubalgebra` / 引理 `Algebra.adjoin_nonUnitalSubalgebra`

English:
lemma Algebra.adjoin_nonUnitalSubalgebra
  given: (s : Set A)
  proof: le_antisymm
    (adjoin_le <| NonUnitalAlgebra.adjoin_le_algebra_adjoin R s)
    (adjoin_le <| (NonUnitalAlgebra.subset_adjoin R).trans subset_adjoin)

中文:
引理 代数.adjoin_nonUnitalSubalgebra
  条件: (s : 集合 A)
  证明: le_antisymm
    (adjoin_le <| NonUnitalAlgebra.adjoin_le_algebra_adjoin R s)
    (adjoin_le <| (NonUnitalAlgebra.subset_adjoin R).trans subset_adjoin)

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin_le_algebra_adjoin, NonUnitalAlgebra.subset_adjoin, adjoin_le, adjoin_le_algebra_adjoin, le_antisymm, subset_adjoin
-/
lemma Algebra.adjoin_nonUnitalSubalgebra (s : Set A) :
    adjoin R (NonUnitalAlgebra.adjoin R s : Set A) = adjoin R s :=
  le_antisymm
    (adjoin_le <| NonUnitalAlgebra.adjoin_le_algebra_adjoin R s)
    (adjoin_le <| (NonUnitalAlgebra.subset_adjoin R).trans subset_adjoin)

end CommSemiring

namespace Subalgebra

section toNonUnitalSubalgebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

/--
Definition of `toNonUnitalSubalgebraOrderEmbedding` / `toNonUnitalSubalgebraOrderEmbedding` 的定义

English:
definition toNonUnitalSubalgebraOrderEmbedding
  signature: : Subalgebra R A ↪o NonUnitalSubalgebra R A where
  body: toNonUnitalSubalgebra
  inj' := toNonUnitalSubalgebra_injective
  map_rel_iff' := by simp [SetLike.le_def]

@[simp]

中文:
定义 toNonUnitalSubalgebraOrderEmbedding
  签名: : 子代数 R A ↪o NonUnital子代数 R A where
  定义体: toNonUnitalSubalgebra
  inj' := toNonUnitalSubalgebra_injective
  map_rel_iff' := by simp [SetLike.le_def]

@[simp]

Depends on / 依赖: toNonUnitalSubalgebra
-/
def toNonUnitalSubalgebraOrderEmbedding : Subalgebra R A ↪o NonUnitalSubalgebra R A where
  toFun := toNonUnitalSubalgebra
  inj' := toNonUnitalSubalgebra_injective
  map_rel_iff' := by simp [SetLike.le_def]

@[simp]
/--
lemma `toNonUnitalSubalgebra_le_toNonUnitalSubalgebra` / 引理 `toNonUnitalSubalgebra_le_toNonUnitalSubalgebra`

English:
lemma toNonUnitalSubalgebra_le_toNonUnitalSubalgebra
  given: {S T : Subalgebra R A}
  proof: toNonUnitalSubalgebraOrderEmbedding.le_iff_le

alias ⟨_, toNonUnitalSubalgebra_mono⟩ := toNonUnitalSubalgebra_le_toNonUnitalSubalgebra

中文:
引理 toNonUnitalSubalgebra_le_toNonUnitalSubalgebra
  条件: {S T : 子代数 R A}
  证明: toNonUnitalSubalgebraOrderEmbedding.le_iff_le

alias ⟨_, toNonUnitalSubalgebra_mono⟩ := toNonUnitalSubalgebra_le_toNonUnitalSubalgebra

Depends on / 依赖: le_iff_le, toNonUnitalSubalgebraOrderEmbedding, toNonUnitalSubalgebraOrderEmbedding.le_iff_le
-/
lemma toNonUnitalSubalgebra_le_toNonUnitalSubalgebra {S T : Subalgebra R A} :
    S.toNonUnitalSubalgebra <= T.toNonUnitalSubalgebra ↔ S <= T :=
  toNonUnitalSubalgebraOrderEmbedding.le_iff_le

alias ⟨_, toNonUnitalSubalgebra_mono⟩ := toNonUnitalSubalgebra_le_toNonUnitalSubalgebra

end toNonUnitalSubalgebra

variable [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/--
theorem `comap_map_eq` / 定理 `comap_map_eq`

English:
theorem comap_map_eq
  given: (f : A ->ₐ[R] B) (S : Subalgebra R A)
  proof: by
  apply le_antisymm
  · intro x hx
    rw [mem_comap]; rw [mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y in f ⁻¹' {0} := by simp [hxy]
    rw [← Algebra.adjoin_eq S]; rw [← Algebra.adjoin_union]; rw [← add_sub_cancel y x]
    exact Subalgebra.add_mem _
      (Algebra.subset

中文:
定理 comap_map_eq
  条件: (f : A ->ₐ[R] B) (S : 子代数 R A)
  证明: by
  apply le_antisymm
  · intro x hx
    rw [mem_comap]; rw [mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y in f ⁻¹' {0} := by simp [hxy]
    rw [← Algebra.adjoin_eq S]; rw [← Algebra.adjoin_union]; rw [← add_sub_cancel y x]
    exact Subalgebra.add_mem _
      (Algebra.subset

Depends on / 依赖: Algebra, Algebra.adjoin_eq, Algebra.adjoin_le_iff, Algebra.adjoin_union, Algebra.map_sup, Algebra.subset_adjoin, Or.inl, Or.inr, Set.image_preimage_subset, Set.singleton_su, Subalgebra, Subalgebra.add_mem, add_mem, add_sub_cancel, adjoin_eq, adjoin_le_iff, adjoin_union, f.map_adjoin, image_preimage_subset, le_antisymm
-/
theorem comap_map_eq (f : A ->ₐ[R] B) (S : Subalgebra R A) :
    (S.map f).comap f = S ⊔ Algebra.adjoin R (f ⁻¹' {0}) := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap]; rw [mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y in f ⁻¹' {0} := by simp [hxy]
    rw [← Algebra.adjoin_eq S]; rw [← Algebra.adjoin_union]; rw [← add_sub_cancel y x]
    exact Subalgebra.add_mem _
      (Algebra.subset_adjoin <| Or.inl hy) (Algebra.subset_adjoin <| Or.inr hxy)
  · rw [← map_le, Algebra.map_sup, f.map_adjoin]
    apply le_of_eq
    rw [sup_eq_left]; rw [Algebra.adjoin_le_iff]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (S.map f).zero_mem)

/--
theorem `comap_map_eq_self` / 定理 `comap_map_eq_self`

English:
theorem comap_map_eq_self
  statement: {f : A ->ₐ[R] B} {S : Subalgebra R A}
  proof: by
  convert! comap_map_eq f S
  rwa [left_eq_sup, Algebra.adjoin_le_iff]

中文:
定理 comap_map_eq_self
  结论: {f : A ->ₐ[R] B} {S : 子代数 R A}
  证明: by
  convert! comap_map_eq f S
  rwa [left_eq_sup, Algebra.adjoin_le_iff]

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, adjoin_le_iff, comap_map_eq, convert, left_eq_sup
-/
theorem comap_map_eq_self {f : A ->ₐ[R] B} {S : Subalgebra R A}
    (h : f ⁻¹' {0} subseteq S) : (S.map f).comap f = S := by
  convert! comap_map_eq f S
  rwa [left_eq_sup, Algebra.adjoin_le_iff]

end Subalgebra

end Adjoin
