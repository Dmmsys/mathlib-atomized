/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.Set.UnionLift

/-!
# Subalgebras and directed Unions of sets

## Main results

* `Subalgebra.coe_iSup_of_directed`: a directed supremum consists of the union of the algebras
* `Subalgebra.iSupLift`: define an algebra homomorphism on a directed supremum of subalgebras by
  defining it on each subalgebra, and proving that it agrees on the intersection of subalgebras.
-/

@[expose] public section

namespace Subalgebra

open Algebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι -> Subalgebra R A}

/--
theorem `coe_iSup_of_directed` / 定理 `coe_iSup_of_directed`

English:
theorem coe_iSup_of_directed
  given: (dir : Directed (· <= ·) K)
  statement: ↑(iSup K) = ⋃ i, (K i : Set A)
  proof: by
  let s : Subalgebra R A :=
    { __ := Subsemiring.copy _ _ (Subsemiring.coe_iSup_of_directed dir).symm
      algebraMap_mem' := fun _ => Set.mem_iUnion.2
        ⟨Classical.arbitrary ι, Subalgebra.algebraMap_mem _ _⟩ }
  have : iSup K = s := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (

中文:
定理 coe_iSup_of_directed
  条件: (dir : Directed (· <= ·) K)
  结论: ↑(iSup K) = ⋃ i, (K i : 集合 A)
  证明: by
  let s : Subalgebra R A :=
    { __ := Subsemiring.copy _ _ (Subsemiring.coe_iSup_of_directed dir).symm
      algebraMap_mem' := fun _ => Set.mem_iUnion.2
        ⟨Classical.arbitrary ι, Subalgebra.algebraMap_mem _ _⟩ }
  have : iSup K = s := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (

Depends on / 依赖: Classical, Classical.arbitrary, Set.iUnion_subset, Set.mem_iUnion, Subalgebra, Subalgebra.algebraMap_mem, Subsemiring, Subsemiring.coe_iSup_of_directed, Subsemiring.copy, algebraMap_mem, arbitrary, coe_iSup_of_directed, iSup_le, iUnion_subset, le_antisymm, le_iSup, mem_iUnion
-/
theorem coe_iSup_of_directed (dir : Directed (· <= ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A) := by
  let s : Subalgebra R A :=
    { __ := Subsemiring.copy _ _ (Subsemiring.coe_iSup_of_directed dir).symm
      algebraMap_mem' := fun _ => Set.mem_iUnion.2
        ⟨Classical.arbitrary ι, Subalgebra.algebraMap_mem _ _⟩ }
  have : iSup K = s := le_antisymm
    (iSup_le fun i => le_iSup (fun i => (K i : Set A)) i) (Set.iUnion_subset fun _ => le_iSup K _)
  simp [this, s]

/--
theorem `isMulCommutative_iSup` / 定理 `isMulCommutative_iSup`

English:
theorem isMulCommutative_iSup
  statement: {S : ι -> Subalgebra R A}
  proof: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemiring.coe_iSup_of_directed dir] using Subsemiring.isMulCommutative_iSup dir

中文:
定理 isMulCommutative_iSup
  结论: {S : ι -> 子代数 R A}
  证明: by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemiring.coe_iSup_of_directed dir] using Subsemiring.isMulCommutative_iSup dir

Depends on / 依赖: SetLike, SetLike.mem_coe, Subsemiring, Subsemiring.coe_iSup_of_directed, Subsemiring.isMulCommutative_iSup, coe_iSup_of_directed, isMulCommutative_iSup, isMulCommutative_iff, mem_coe
-/
theorem isMulCommutative_iSup {S : ι -> Subalgebra R A}
    [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) :
    IsMulCommutative (⨆ i, S i : Subalgebra R A) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemiring.coe_iSup_of_directed dir] using Subsemiring.isMulCommutative_iSup dir

/--
Instance `instIsMulCommutative_iSup` / 实例 `instIsMulCommutative_iSup`

English:
instance instIsMulCommutative_iSup
  signature: [Preorder ι] [IsDirectedOrder ι]
  body: isMulCommutative_iSup S.monotone.directed_le

中文:
实例 instIsMulCommutative_iSup
  签名: [预序 ι] [IsDirectedOrder ι]
  定义体: isMulCommutative_iSup S.monotone.directed_le

Depends on / 依赖: S.monotone.directed_le, directed_le, isMulCommutative_iSup, monotone
-/
instance instIsMulCommutative_iSup [Preorder ι] [IsDirectedOrder ι]
    {S : ι ->o Subalgebra R A} [hS : forall i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subalgebra R A) :=
  isMulCommutative_iSup S.monotone.directed_le

variable (K)

/--
Definition of `iSupLift` / `iSupLift` 的定义

English:
definition iSupLift
  signature: (dir : Directed (· <= ·) K) (f : forall i, K i ->ₐ[R] B)
  body: by
  let compat :
      forall (i j) (x : A) (hxi : x in (K i : Set A)) (hxj : x in (K j : Set A)),
        f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases dir i j with ⟨k, hik, hjk⟩
    simp [hf i k hik, hf j k hjk]
  let liftSup : ((iSup K : Subalgebra R A)) ->ₐ[R] B :=
    { 

中文:
定义 iSupLift
  签名: (dir : Directed (· <= ·) K) (f : 对任意 i, K i ->ₐ[R] B)
  定义体: by
  let compat :
      forall (i j) (x : A) (hxi : x in (K i : Set A)) (hxj : x in (K j : Set A)),
        f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases dir i j with ⟨k, hik, hjk⟩
    simp [hf i k hik, hf j k hjk]
  let liftSup : ((iSup K : Subalgebra R A)) ->ₐ[R] B :=
    { 

Depends on / 依赖: Set.iUnionLift, Set.iUnionLift_const, Subalgebra, coe_iSup_of_directed, compat, iUnionLift, iUnionLift_const, le_of_eq, liftSup, map_one, toNonUnitalRingHomClass
-/
noncomputable def iSupLift (dir : Directed (· <= ·) K) (f : forall i, K i ->ₐ[R] B)
    (hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h))
    (T : Subalgebra R A) (hT : T <= iSup K) : ↥T ->ₐ[R] B := by
  let compat :
      forall (i j) (x : A) (hxi : x in (K i : Set A)) (hxj : x in (K j : Set A)),
        f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases dir i j with ⟨k, hik, hjk⟩
    simp [hf i k hik, hf j k hjk]
  let liftSup : ((iSup K : Subalgebra R A)) ->ₐ[R] B :=
    { toFun :=
        Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x) compat
          ((iSup K : Subalgebra R A) : Set A)
          (le_of_eq <| coe_iSup_of_directed (K := K) dir)
      map_one' := by
        dsimp
        exact Set.iUnionLift_const _ (fun i : ι => (1 : K i)) (fun _ => rfl) _ (by simp)
      map_zero' := by
        dsimp
        exact Set.iUnionLift_const _ (fun i : ι => (0 : K i)) (fun _ => rfl) _ (by simp)
      map_mul' := by
        dsimp
        apply Set.iUnionLift_binary (coe_iSup_of_directed (K := K) dir) dir _ (fun _ => (· * ·))
        all_goals simp
      map_add' := by
        dsimp
        apply Set.iUnionLift_binary (coe_iSup_of_directed (K := K) dir) dir _ (fun _ => (· + ·))
        all_goals simp
      commutes' := fun r => by
        dsimp
        exact
          Set.iUnionLift_const _ (fun i : ι => algebraMap R (K i) r) (fun _ => rfl) _ (by simp) }
  exact liftSup.comp (inclusion hT)


set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `iSupLift_inclusion` / 定理 `iSupLift_inclusion`

English:
theorem iSupLift_inclusion
  statement: {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B}
  proof: by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_inclusion]
exact SetLike.coe_subset_coe.mpr h.trans hT

@[simp]

中文:
定理 iSupLift_inclusion
  结论: {dir : Directed (· <= ·) K} {f : 对任意 i, K i ->ₐ[R] B}
  证明: by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_inclusion]
exact SetLike.coe_subset_coe.mpr h.trans hT

@[simp]

Depends on / 依赖: Set.iUnionLift_inclusion, SetLike, SetLike.coe_subset_coe.mpr, coe_subset_coe, h.trans, iSupLift, iUnionLift_inclusion, inclusion
-/
theorem iSupLift_inclusion {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B}
    {hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T <= iSup K} {i : ι} (x : K i) (h : K i <= T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_inclusion]
exact SetLike.coe_subset_coe.mpr h.trans hT

@[simp]
/--
theorem `iSupLift_comp_inclusion` / 定理 `iSupLift_comp_inclusion`

English:
theorem iSupLift_comp_inclusion
  statement: {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B}
  proof: by ext; simp

中文:
定理 iSupLift_comp_inclusion
  结论: {dir : Directed (· <= ·) K} {f : 对任意 i, K i ->ₐ[R] B}
  证明: by ext; simp

Depends on / 依赖: FunLike, Module, NonUnitalAlgHomClass
-/
theorem iSupLift_comp_inclusion {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B}
    {hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T <= iSup K} {i : ι} (h : K i <= T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `iSupLift_mk` / 定理 `iSupLift_mk`

English:
theorem iSupLift_mk
  statement: {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B}
  proof: by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_mk]

中文:
定理 iSupLift_mk
  结论: {dir : Directed (· <= ·) K} {f : 对任意 i, K i ->ₐ[R] B}
  证明: by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_mk]

Depends on / 依赖: Set.iUnionLift_mk, iSupLift, iUnionLift_mk, inclusion
-/
theorem iSupLift_mk {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B}
    {hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T <= iSup K} {i : ι} (x : K i) (hx : (x : A) in T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_mk]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `iSupLift_of_mem` / 定理 `iSupLift_of_mem`

English:
theorem iSupLift_of_mem
  statement: {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B}
  proof: by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_of_mem]

中文:
定理 iSupLift_of_mem
  结论: {dir : Directed (· <= ·) K} {f : 对任意 i, K i ->ₐ[R] B}
  证明: by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_of_mem]

Depends on / 依赖: Set.iUnionLift_of_mem, iSupLift, iUnionLift_of_mem, inclusion, toNonUnitalAlgSemiHom
-/
theorem iSupLift_of_mem {dir : Directed (· <= ·) K} {f : forall i, K i ->ₐ[R] B}
    {hf : forall (i j : ι) (h : K i <= K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T <= iSup K} {i : ι} (x : T) (hx : (x : A) in K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_of_mem]

end Subalgebra
