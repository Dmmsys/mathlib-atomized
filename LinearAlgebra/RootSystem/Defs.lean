/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Root data and root systems

This file contains basic definitions for root systems and root data.

## Main definitions:

* `RootPairing`: Given two perfectly-paired `R`-modules `M` and `N` (over some commutative ring
  `R`) a root pairing with indexing set `ι` is the data of an `ι`-indexed subset of `M`
  ("the roots") an `ι`-indexed subset of `N` ("the coroots"), and an `ι`-indexed set of
  permutations of `ι` such that each root-coroot pair evaluates to `2`, and the permutation
  attached to each element of `ι` is compatible with the reflections on the corresponding roots and
  coroots.
* `RootDatum`: A root datum is a root pairing for which the roots and coroots take values in
  finitely-generated free Abelian groups.
* `RootSystem`: A root system is a root pairing for which the roots span their ambient module.

## Implementation details

A root datum is sometimes defined as two subsets: roots and coroots, together with a bijection
between them, subject to hypotheses. However the hypotheses ensure that the bijection is unique and
so the question arises of whether this bijection should be part of the data of a root datum or
whether one should merely assert its existence. For root systems, things are even more extreme: the
coroots are uniquely determined by the roots. Furthermore a root system induces a canonical
non-degenerate bilinear form on the ambient space and many informal accounts even include this form
as part of the data.

We have opted for a design in which some of the uniquely-determined data is included: the bijection
between roots and coroots is (implicitly) included and the coroots are included for root systems.
Empirically this seems to be by far the most convenient design and by providing extensionality
lemmas expressing the uniqueness we expect to get the best of both worlds.

Furthermore, we require roots and coroots to be injections from a base indexing type `ι` rather than
subsets of their codomains. This design was chosen to avoid the bijection between roots and coroots
being a dependently-typed object. A third option would be to have the roots and coroots be subsets
but to avoid having a dependently-typed bijection by defining it globally with junk value `0`
outside of the roots and coroots. This would work but lacks the convenient symmetry that the chosen
design enjoys: by introducing the indexing type `ι`, one does not have to pick a direction
(`roots → coroots` or `coroots → roots`) for the forward direction of the bijection. Besides,
providing the user with the additional definitional power to specify an indexing type `ι` is a
benefit and the junk-value pattern is a cost.

As a final point of divergence from the classical literature, we make the reflection permutation on
roots and coroots explicit, rather than specifying only that reflection preserves the sets of roots
and coroots. This is necessary when working with infinite root systems, where the coroots are not
uniquely determined by the roots, because without it, the reflection permutations on roots and
coroots may not correspond. For this purpose, we define a map from `ι` to permutations on `ι`, and
require that it is compatible with reflections and coreflections.

-/

@[expose] public section

open Set Function
open Module hiding reflection
open Submodule (span span_image)
open AddSubgroup (zmultiples)

noncomputable section

variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/--
Definition of `RootPairing` / `RootPairing` 的定义

English:
structure RootPairing
  parameters: extends M ->ₗ[R] N ->ₗ[R] R
  extends: M ->ₗ[R] N ->ₗ[R] R
  axioms and operations (7):
    - [isPerfPair_toLinearMap : toLinearMap.IsPerfPair]
    - root : ι ↪ M
    - coroot : ι ↪ N
    - root_coroot_two : forall i, toLinearMap (root i) (coroot i) = 2
    - reflectionPerm : ι -> (ι ≃ ι)
    - reflectionPerm_root : forall i j, root j - toLinearMap (root j) (coroot i) • root i = root (reflectionPerm i j)
    - reflectionPerm_coroot : forall i j, coroot j - toLinearMap (root i) (coroot j) • coroot i = coroot (reflectionPerm i j)

中文:
结构 RootPairing
  参数: extends M ->ₗ[R] N ->ₗ[R] R
  继承: M ->ₗ[R] N ->ₗ[R] R
  公理与运算 (7 个):
    - [isPerfPair_toLinearMap : toLinearMap.是PerfPair]
    - root : ι ↪ M
    - coroot : ι ↪ N
    - root_coroot_two : 对任意 i, toLinearMap (root i) (coroot i) = 2
    - reflectionPerm : ι -> (ι ≃ ι)
    - reflectionPerm_root : 对任意 i j, root j - toLinearMap (root j) (coroot i) • root i = root (reflectionPerm i j)
    - reflectionPerm_coroot : 对任意 i j, coroot j - toLinearMap (root i) (coroot j) • coroot i = coroot (reflectionPerm i j)
-/
structure RootPairing extends M ->ₗ[R] N ->ₗ[R] R where
  [isPerfPair_toLinearMap : toLinearMap.IsPerfPair]
  /-- A parametrized family of vectors, called roots. -/
  root : ι ↪ M
  /-- A parametrized family of dual vectors, called coroots. -/
  coroot : ι ↪ N
  root_coroot_two : forall i, toLinearMap (root i) (coroot i) = 2
  /-- A parametrized family of permutations, induced by reflections. This corresponds to the
  classical requirement that the symmetry attached to each root (later defined in
  `RootPairing.reflection`) leave the whole set of roots stable: as explained above, we
  formalize this stability by fixing the image of the roots through each reflection (whence the
  permutation); and similarly for coroots. -/
  reflectionPerm : ι -> (ι ≃ ι)
  reflectionPerm_root : forall i j,
    root j - toLinearMap (root j) (coroot i) • root i = root (reflectionPerm i j)
  reflectionPerm_coroot : forall i j,
    coroot j - toLinearMap (root i) (coroot j) • coroot i = coroot (reflectionPerm i j)

attribute [instance] RootPairing.isPerfPair_toLinearMap

/--
Definition of `RootDatum` / `RootDatum` 的定义

English:
abbreviation RootDatum
  signature: (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂]
  body: RootPairing ι Int X₁ X₂

中文:
缩写 RootDatum
  签名: (X₁ X₂ : 类型) [加法交换群 X₁] [加法交换群 X₂]
  定义体: RootPairing ι Int X₁ X₂

Depends on / 依赖: NormedAddCommGroup, RootPairing, measureSpaceOfInnerProductSpace
-/
abbrev RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂] := RootPairing ι Int X₁ X₂

namespace RootPairing

variable {ι R M N}
variable (P : RootPairing ι R M N) (i j : ι)

/-- A root system is a root pairing for which the roots and coroots span their ambient modules. -/
@[wikidata Q534131]
/--
Definition of `IsRootSystem` / `IsRootSystem` 的定义

English:
class IsRootSystem
  parameters: : Prop where
  axioms and operations (2):
    - span_root_eq_top : span R (range P.root) = ⊤
    - span_coroot_eq_top : span R (range P.coroot) = ⊤

中文:
类 是RootSystem
  参数: : 命题 where
  公理与运算 (2 个):
    - span_root_eq_top : span R (range P.root) = ⊤
    - span_coroot_eq_top : span R (range P.coroot) = ⊤
-/
class IsRootSystem : Prop where
  span_root_eq_top : span R (range P.root) = ⊤
  span_coroot_eq_top : span R (range P.coroot) = ⊤

attribute [simp] IsRootSystem.span_root_eq_top
attribute [simp] IsRootSystem.span_coroot_eq_top

/-- If we interchange the roles of `M` and `N`, we still have a root pairing. -/
@[simps! root coroot reflectionPerm, simps toLinearMap]
/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: : RootPairing ι R N M where
  body: P.toLinearMap.flip
  root := P.coroot
  coroot := P.root
  root_coroot_two := P.root_coroot_two
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root := P.reflectionPerm_coroot
  reflectionPerm_coroot := P.reflectionPerm_root

@[simp]

中文:
定义 flip
  签名: : RootPairing ι R N M where
  定义体: P.toLinearMap.flip
  root := P.coroot
  coroot := P.root
  root_coroot_two := P.root_coroot_two
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root := P.reflectionPerm_coroot
  reflectionPerm_coroot := P.reflectionPerm_root

@[simp]
-/
protected def flip : RootPairing ι R N M where
  toLinearMap := P.toLinearMap.flip
  root := P.coroot
  coroot := P.root
  root_coroot_two := P.root_coroot_two
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root := P.reflectionPerm_coroot
  reflectionPerm_coroot := P.reflectionPerm_root

@[simp]
/--
lemma `flip_flip` / 引理 `flip_flip`

English:
lemma flip_flip
  statement: P.flip.flip = P
  proof: rfl

中文:
引理 flip_flip
  结论: P.flip.flip = P
  证明: rfl
-/
lemma flip_flip : P.flip.flip = P :=
  rfl

variable (ι R M N) in
/--
Definition of `flipEquiv` / `flipEquiv` 的定义

English:
definition flipEquiv
  signature: : RootPairing ι R N M ≃ RootPairing ι R M N where
  body: P.flip
  invFun P := P.flip

中文:
定义 flipEquiv
  签名: : RootPairing ι R N M ≃ RootPairing ι R M N where
  定义体: P.flip
  invFun P := P.flip
-/
@[simps] def flipEquiv : RootPairing ι R N M ≃ RootPairing ι R M N where
  toFun P := P.flip
  invFun P := P.flip

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsRootSystem]
  signature: : P.flip.IsRootSystem where
  body: IsRootSystem.span_coroot_eq_top
  span_coroot_eq_top := IsRootSystem.span_root_eq_top

中文:
实例 [P.是RootSystem]
  签名: : P.flip.是RootSystem where
  定义体: IsRootSystem.span_coroot_eq_top
  span_coroot_eq_top := IsRootSystem.span_root_eq_top

Depends on / 依赖: IsRootSystem, IsRootSystem.span_coroot_eq_top, span_coroot_eq_top
-/
instance [P.IsRootSystem] : P.flip.IsRootSystem where
  span_root_eq_top := IsRootSystem.span_coroot_eq_top
  span_coroot_eq_top := IsRootSystem.span_root_eq_top

/--
lemma `ne_zero` / 引理 `ne_zero`

English:
lemma ne_zero
  given: [NeZero (2 : R)]
  statement: (P.root i : M) != 0
  proof: fun h => NeZero.ne' (2 : R) by simpa [h] using P.root_coroot_two i

中文:
引理 ne_zero
  条件: [NeZero (2 : R)]
  结论: (P.root i : M) != 0
  证明: fun h => NeZero.ne' (2 : R) by simpa [h] using P.root_coroot_two i

Depends on / 依赖: NeZero, NeZero.ne, P.root_coroot_two, root_coroot_two
-/
lemma ne_zero [NeZero (2 : R)] : (P.root i : M) != 0 :=
fun h => NeZero.ne' (2 : R) by simpa [h] using P.root_coroot_two i

/--
lemma `ne_zero'` / 引理 `ne_zero'`

English:
lemma ne_zero'
  given: [NeZero (2 : R)]
  statement: (P.coroot i : N) != 0
  proof: P.flip.ne_zero i

中文:
引理 ne_zero'
  条件: [NeZero (2 : R)]
  结论: (P.coroot i : N) != 0
  证明: P.flip.ne_zero i

Depends on / 依赖: P.flip.ne_zero, ne_zero
-/
lemma ne_zero' [NeZero (2 : R)] : (P.coroot i : N) != 0 :=
  P.flip.ne_zero i

/--
lemma `zero_notMem_range_root` / 引理 `zero_notMem_range_root`

English:
lemma zero_notMem_range_root
  given: [NeZero (2 : R)]
  statement: 0 ∉ range P.root
  proof: by
  simpa only [mem_range, not_exists] using fun i => P.ne_zero i

中文:
引理 zero_notMem_range_root
  条件: [NeZero (2 : R)]
  结论: 0 ∉ range P.root
  证明: by
  simpa only [mem_range, not_exists] using fun i => P.ne_zero i

Depends on / 依赖: P.ne_zero, mem_range, ne_zero, not_exists
-/
lemma zero_notMem_range_root [NeZero (2 : R)] : 0 ∉ range P.root := by
  simpa only [mem_range, not_exists] using fun i => P.ne_zero i

/--
lemma `zero_notMem_range_coroot` / 引理 `zero_notMem_range_coroot`

English:
lemma zero_notMem_range_coroot
  given: [NeZero (2 : R)]
  statement: 0 ∉ range P.coroot
  proof: P.flip.zero_notMem_range_root

中文:
引理 zero_notMem_range_coroot
  条件: [NeZero (2 : R)]
  结论: 0 ∉ range P.coroot
  证明: P.flip.zero_notMem_range_root

Depends on / 依赖: P.flip.zero_notMem_range_root, zero_notMem_range_root
-/
lemma zero_notMem_range_coroot [NeZero (2 : R)] : 0 ∉ range P.coroot :=
  P.flip.zero_notMem_range_root

/--
lemma `exists_ne_zero` / 引理 `exists_ne_zero`

English:
lemma exists_ne_zero
  given: [Nonempty ι] [NeZero (2 : R)]
  statement: exists i, P.root i != 0
  proof: by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact ⟨i, P.ne_zero i⟩

中文:
引理 存在_ne_zero
  条件: [非空 ι] [NeZero (2 : R)]
  结论: 存在 i, P.root i != 0
  证明: by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact ⟨i, P.ne_zero i⟩

Depends on / 依赖: Nonempty, P.ne_zero, ne_zero
-/
lemma exists_ne_zero [Nonempty ι] [NeZero (2 : R)] : exists i, P.root i != 0 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact ⟨i, P.ne_zero i⟩

/--
lemma `exists_ne_zero'` / 引理 `exists_ne_zero'`

English:
lemma exists_ne_zero'
  given: [Nonempty ι] [NeZero (2 : R)]
  statement: exists i, P.coroot i != 0
  proof: P.flip.exists_ne_zero

include P in

中文:
引理 存在_ne_zero'
  条件: [非空 ι] [NeZero (2 : R)]
  结论: 存在 i, P.coroot i != 0
  证明: P.flip.exists_ne_zero

include P in

Depends on / 依赖: P.flip.exists_ne_zero, exists_ne_zero
-/
lemma exists_ne_zero' [Nonempty ι] [NeZero (2 : R)] : exists i, P.coroot i != 0 :=
  P.flip.exists_ne_zero

include P in
/--
lemma `nontrivial` / 引理 `nontrivial`

English:
lemma nontrivial
  given: [Nonempty ι] [NeZero (2 : R)]
  statement: Nontrivial M
  proof: by
  obtain ⟨i, hi⟩ := P.exists_ne_zero
  exact ⟨P.root i, 0, hi⟩

include P in

中文:
引理 nontrivial
  条件: [非空 ι] [NeZero (2 : R)]
  结论: 非平凡 M
  证明: by
  obtain ⟨i, hi⟩ := P.exists_ne_zero
  exact ⟨P.root i, 0, hi⟩

include P in
-/
protected lemma nontrivial [Nonempty ι] [NeZero (2 : R)] : Nontrivial M := by
  obtain ⟨i, hi⟩ := P.exists_ne_zero
  exact ⟨P.root i, 0, hi⟩

include P in
/--
lemma `nontrivial'` / 引理 `nontrivial'`

English:
lemma nontrivial'
  given: [Nonempty ι] [NeZero (2 : R)]
  statement: Nontrivial N
  proof: P.flip.nontrivial

中文:
引理 nontrivial'
  条件: [非空 ι] [NeZero (2 : R)]
  结论: 非平凡 N
  证明: P.flip.nontrivial
-/
protected lemma nontrivial' [Nonempty ι] [NeZero (2 : R)] : Nontrivial N :=
  P.flip.nontrivial

/--
Definition of `root'` / `root'` 的定义

English:
abbreviation root'
  signature: (i : ι)
  body: P.toLinearMap (P.root i)

中文:
缩写 root'
  签名: (i : ι)
  定义体: P.toLinearMap (P.root i)

Depends on / 依赖: P.root, P.toLinearMap, toLinearMap
-/
abbrev root' (i : ι) : Dual R N := P.toLinearMap (P.root i)

/--
Definition of `coroot'` / `coroot'` 的定义

English:
abbreviation coroot'
  signature: (i : ι)
  body: P.toLinearMap.flip (P.coroot i)

中文:
缩写 coroot'
  签名: (i : ι)
  定义体: P.toLinearMap.flip (P.coroot i)

Depends on / 依赖: P.coroot, P.toLinearMap.flip, coroot, toLinearMap
-/
abbrev coroot' (i : ι) : Dual R M := P.toLinearMap.flip (P.coroot i)

/--
Definition of `pairing` / `pairing` 的定义

English:
definition pairing
  signature: : R
  body: P.root' i (P.coroot j)

中文:
定义 pairing
  签名: : R
  定义体: P.root' i (P.coroot j)

Depends on / 依赖: P.coroot, P.root, coroot
-/
def pairing : R := P.root' i (P.coroot j)

/--
lemma `pairing_flip` / 引理 `pairing_flip`

English:
lemma pairing_flip
  statement: P.flip.pairing i j = P.pairing j i
  proof: rfl

@[simp]

中文:
引理 pairing_flip
  结论: P.flip.pairing i j = P.pairing j i
  证明: rfl

@[simp]
-/
@[simp] lemma pairing_flip : P.flip.pairing i j = P.pairing j i := rfl

@[simp]
/--
lemma `root_coroot_eq_pairing` / 引理 `root_coroot_eq_pairing`

English:
lemma root_coroot_eq_pairing
  statement: P.toLinearMap (P.root i) (P.coroot j) = P.pairing i j
  proof: rfl

@[simp]

中文:
引理 root_coroot_eq_pairing
  结论: P.toLinearMap (P.root i) (P.coroot j) = P.pairing i j
  证明: rfl

@[simp]
-/
lemma root_coroot_eq_pairing : P.toLinearMap (P.root i) (P.coroot j) = P.pairing i j :=
  rfl

@[simp]
/--
lemma `root'_coroot_eq_pairing` / 引理 `root'_coroot_eq_pairing`

English:
lemma root'_coroot_eq_pairing
  statement: P.root' i (P.coroot j) = P.pairing i j
  proof: rfl

@[simp]

中文:
引理 root'_coroot_eq_pairing
  结论: P.root' i (P.coroot j) = P.pairing i j
  证明: rfl

@[simp]
-/
lemma root'_coroot_eq_pairing : P.root' i (P.coroot j) = P.pairing i j :=
  rfl

@[simp]
/--
lemma `root_coroot'_eq_pairing` / 引理 `root_coroot'_eq_pairing`

English:
lemma root_coroot'_eq_pairing
  statement: P.coroot' i (P.root j) = P.pairing j i
  proof: rfl

中文:
引理 root_coroot'_eq_pairing
  结论: P.coroot' i (P.root j) = P.pairing j i
  证明: rfl
-/
lemma root_coroot'_eq_pairing : P.coroot' i (P.root j) = P.pairing j i :=
  rfl

/--
lemma `coroot_root_eq_pairing` / 引理 `coroot_root_eq_pairing`

English:
lemma coroot_root_eq_pairing
  statement: P.toLinearMap.flip (P.coroot i) (P.root j) = P.pairing j i
  proof: by
  simp

@[simp]

中文:
引理 coroot_root_eq_pairing
  结论: P.toLinearMap.flip (P.coroot i) (P.root j) = P.pairing j i
  证明: by
  simp

@[simp]
-/
lemma coroot_root_eq_pairing : P.toLinearMap.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp

@[simp]
/--
lemma `pairing_same` / 引理 `pairing_same`

English:
lemma pairing_same
  statement: P.pairing i i = 2
  proof: P.root_coroot_two i

中文:
引理 pairing_same
  结论: P.pairing i i = 2
  证明: P.root_coroot_two i

Depends on / 依赖: P.root_coroot_two, root_coroot_two
-/
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i

variable {P} in
/--
lemma `pairing_eq_add_of_root_eq_add` / 引理 `pairing_eq_add_of_root_eq_add`

English:
lemma pairing_eq_add_of_root_eq_add
  given: {i j k l : ι} (h : P.root k = P.root i + P.root j)
  proof: by
  simp only [← root_coroot_eq_pairing, h, map_add, LinearMap.add_apply]

中文:
引理 pairing_eq_add_of_root_eq_add
  条件: {i j k l : ι} (h : P.root k = P.root i + P.root j)
  证明: by
  simp only [← root_coroot_eq_pairing, h, map_add, LinearMap.add_apply]

Depends on / 依赖: LinearMap, LinearMap.add_apply, add_apply, map_add, root_coroot_eq_pairing
-/
lemma pairing_eq_add_of_root_eq_add {i j k l : ι} (h : P.root k = P.root i + P.root j) :
    P.pairing k l = P.pairing i l + P.pairing j l := by
  simp only [← root_coroot_eq_pairing, h, map_add, LinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
variable {P} in
/--
lemma `pairing_eq_add_of_root_eq_smul_add_smul` / 引理 `pairing_eq_add_of_root_eq_smul_add_smul`

English:
lemma pairing_eq_add_of_root_eq_smul_add_smul
  proof: by
  simp only [← root_coroot_eq_pairing, h, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]

中文:
引理 pairing_eq_add_of_root_eq_smul_add_smul
  证明: by
  simp only [← root_coroot_eq_pairing, h, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]

Depends on / 依赖: LinearMap, LinearMap.add_apply, LinearMap.smul_apply, add_apply, map_add, map_smul, root_coroot_eq_pairing, smul_apply, smul_eq_mul
-/
lemma pairing_eq_add_of_root_eq_smul_add_smul
    {i j k l : ι} {x y : R} (h : P.root k = x • P.root i + y • P.root l) :
    P.pairing k j = x • P.pairing i j + y • P.pairing l j := by
  simp only [← root_coroot_eq_pairing, h, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]

/--
lemma `coroot_root_two` / 引理 `coroot_root_two`

English:
lemma coroot_root_two
  proof: by
  simp

中文:
引理 coroot_root_two
  证明: by
  simp
-/
lemma coroot_root_two :
    P.toLinearMap.flip (P.coroot i) (P.root i) = 2 := by
  simp

/--
Definition of `reflection` / `reflection` 的定义

English:
definition reflection
  signature: : M ≃ₗ[R] M
  body: Module.reflection (P.flip.root_coroot_two i)

@[simp]

中文:
定义 reflection
  签名: : M ≃ₗ[R] M
  定义体: Module.reflection (P.flip.root_coroot_two i)

@[simp]

Depends on / 依赖: Module, Module.reflection, P.flip.root_coroot_two, reflection, root_coroot_two
-/
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)

@[simp]
/--
lemma `root_reflectionPerm` / 引理 `root_reflectionPerm`

English:
lemma root_reflectionPerm
  given: (j : ι)
  proof: (P.reflectionPerm_root i j).symm

中文:
引理 root_reflectionPerm
  条件: (j : ι)
  证明: (P.reflectionPerm_root i j).symm

Depends on / 依赖: P.reflectionPerm_root, reflectionPerm_root
-/
lemma root_reflectionPerm (j : ι) :
    P.root (P.reflectionPerm i j) = (P.reflection i) (P.root j) :=
  (P.reflectionPerm_root i j).symm

/--
theorem `mapsTo_reflection_root` / 定理 `mapsTo_reflection_root`

English:
theorem mapsTo_reflection_root
  proof: by
  rintro - ⟨j, rfl⟩
  exact P.root_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)

中文:
定理 mapsTo_reflection_root
  证明: by
  rintro - ⟨j, rfl⟩
  exact P.root_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)

Depends on / 依赖: P.reflectionPerm, P.root_reflectionPerm, mem_range_self, reflectionPerm, root_reflectionPerm
-/
theorem mapsTo_reflection_root :
    MapsTo (P.reflection i) (range P.root) (range P.root) := by
  rintro - ⟨j, rfl⟩
  exact P.root_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)

/--
lemma `reflection_apply` / 引理 `reflection_apply`

English:
lemma reflection_apply
  given: (x : M)
  proof: rfl

中文:
引理 reflection_apply
  条件: (x : M)
  证明: rfl
-/
lemma reflection_apply (x : M) :
    P.reflection i x = x - (P.coroot' i x) • P.root i :=
  rfl

/--
lemma `reflection_apply_root` / 引理 `reflection_apply_root`

English:
lemma reflection_apply_root
  proof: rfl

@[simp]

中文:
引理 reflection_apply_root
  证明: rfl

@[simp]
-/
lemma reflection_apply_root :
    P.reflection i (P.root j) = P.root j - (P.pairing j i) • P.root i :=
  rfl

@[simp]
/--
lemma `reflection_apply_self` / 引理 `reflection_apply_self`

English:
lemma reflection_apply_self
  proof: Module.reflection_apply_self (P.coroot_root_two i)

@[simp]

中文:
引理 reflection_apply_self
  证明: Module.reflection_apply_self (P.coroot_root_two i)

@[simp]

Depends on / 依赖: Module, Module.reflection_apply_self, P.coroot_root_two, coroot_root_two, reflection_apply_self
-/
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)

@[simp]
/--
lemma `reflection_same` / 引理 `reflection_same`

English:
lemma reflection_same
  given: (x : M)
  proof: Module.involutive_reflection (P.coroot_root_two i) x

@[simp]

中文:
引理 reflection_same
  条件: (x : M)
  证明: Module.involutive_reflection (P.coroot_root_two i) x

@[simp]

Depends on / 依赖: Module, Module.involutive_reflection, P.coroot_root_two, coroot_root_two, involutive_reflection
-/
lemma reflection_same (x : M) :
    P.reflection i (P.reflection i x) = x :=
  Module.involutive_reflection (P.coroot_root_two i) x

@[simp]
/--
lemma `reflection_inv` / 引理 `reflection_inv`

English:
lemma reflection_inv
  proof: rfl

@[simp]

中文:
引理 reflection_inv
  证明: rfl

@[simp]
-/
lemma reflection_inv :
    (P.reflection i)⁻¹ = P.reflection i :=
  rfl

@[simp]
/--
lemma `reflection_sq` / 引理 `reflection_sq`

English:
lemma reflection_sq
  statement: P.reflection i ^ 2 = 1
  proof: mul_eq_one_iff_eq_inv.mpr rfl

@[simp]

中文:
引理 reflection_sq
  结论: P.reflection i ^ 2 = 1
  证明: mul_eq_one_iff_eq_inv.mpr rfl

@[simp]

Depends on / 依赖: mul_eq_one_iff_eq_inv, mul_eq_one_iff_eq_inv.mpr
-/
lemma reflection_sq : P.reflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl

@[simp]
/--
lemma `reflectionPerm_sq` / 引理 `reflectionPerm_sq`

English:
lemma reflectionPerm_sq
  statement: P.reflectionPerm i ^ 2 = 1
  proof: by
  ext j
  apply P.root.injective
  simp only [sq, Equiv.Perm.mul_apply, root_reflectionPerm, reflection_same, Equiv.Perm.one_apply]

@[simp]

中文:
引理 reflectionPerm_sq
  结论: P.reflectionPerm i ^ 2 = 1
  证明: by
  ext j
  apply P.root.injective
  simp only [sq, Equiv.Perm.mul_apply, root_reflectionPerm, reflection_same, Equiv.Perm.one_apply]

@[simp]

Depends on / 依赖: Equiv.Perm.mul_apply, Equiv.Perm.one_apply, P.root.injective, injective, mul_apply, one_apply, reflection_same, root_reflectionPerm
-/
lemma reflectionPerm_sq : P.reflectionPerm i ^ 2 = 1 := by
  ext j
  apply P.root.injective
  simp only [sq, Equiv.Perm.mul_apply, root_reflectionPerm, reflection_same, Equiv.Perm.one_apply]

@[simp]
/--
lemma `reflectionPerm_inv` / 引理 `reflectionPerm_inv`

English:
lemma reflectionPerm_inv
  statement: (P.reflectionPerm i)⁻¹ = P.reflectionPerm i
  proof: (mul_eq_one_iff_eq_inv.mp <| P.reflectionPerm_sq i).symm

@[simp]

中文:
引理 reflectionPerm_inv
  结论: (P.reflectionPerm i)⁻¹ = P.reflectionPerm i
  证明: (mul_eq_one_iff_eq_inv.mp <| P.reflectionPerm_sq i).symm

@[simp]

Depends on / 依赖: P.reflectionPerm_sq, instInnerRegularOfIsHaarMeasureOfCompactSpace, mul_eq_one_iff_eq_inv, mul_eq_one_iff_eq_inv.mp, reflectionPerm_sq
-/
lemma reflectionPerm_inv : (P.reflectionPerm i)⁻¹ = P.reflectionPerm i :=
  (mul_eq_one_iff_eq_inv.mp <| P.reflectionPerm_sq i).symm

@[simp]
/--
lemma `reflectionPerm_self` / 引理 `reflectionPerm_self`

English:
lemma reflectionPerm_self
  statement: P.reflectionPerm i (P.reflectionPerm i j) = j
  proof: by
  apply P.root.injective
  simp only [root_reflectionPerm, reflection_same]

中文:
引理 reflectionPerm_self
  结论: P.reflectionPerm i (P.reflectionPerm i j) = j
  证明: by
  apply P.root.injective
  simp only [root_reflectionPerm, reflection_same]

Depends on / 依赖: P.root.injective, injective, instRegularOfIsHaarMeasureOfCompactSpace, reflection_same, root_reflectionPerm
-/
lemma reflectionPerm_self : P.reflectionPerm i (P.reflectionPerm i j) = j := by
  apply P.root.injective
  simp only [root_reflectionPerm, reflection_same]

/--
lemma `reflectionPerm_involutive` / 引理 `reflectionPerm_involutive`

English:
lemma reflectionPerm_involutive
  statement: Involutive (P.reflectionPerm i)
  proof: involutive_iff_iter_2_eq_id.mpr (by ext; simp)

@[simp]

中文:
引理 reflectionPerm_involutive
  结论: 对合 (P.reflectionPerm i)
  证明: involutive_iff_iter_2_eq_id.mpr (by ext; simp)

@[simp]

Depends on / 依赖: involutive_iff_iter_2_eq_id, involutive_iff_iter_2_eq_id.mpr
-/
lemma reflectionPerm_involutive : Involutive (P.reflectionPerm i) :=
  involutive_iff_iter_2_eq_id.mpr (by ext; simp)

@[simp]
/--
lemma `reflectionPerm_symm` / 引理 `reflectionPerm_symm`

English:
lemma reflectionPerm_symm
  statement: (P.reflectionPerm i).symm = P.reflectionPerm i
  proof: Involutive.symm_eq_self_of_involutive (P.reflectionPerm i) P.reflectionPerm_involutive i

中文:
引理 reflectionPerm_symm
  结论: (P.reflectionPerm i).symm = P.reflectionPerm i
  证明: Involutive.symm_eq_self_of_involutive (P.reflectionPerm i) P.reflectionPerm_involutive i

Depends on / 依赖: Involutive, Involutive.symm_eq_self_of_involutive, P.reflectionPerm, P.reflectionPerm_involutive, reflectionPerm, reflectionPerm_involutive, symm_eq_self_of_involutive
-/
lemma reflectionPerm_symm : (P.reflectionPerm i).symm = P.reflectionPerm i :=
Involutive.symm_eq_self_of_involutive (P.reflectionPerm i) P.reflectionPerm_involutive i

/--
lemma `bijOn_reflection_root` / 引理 `bijOn_reflection_root`

English:
lemma bijOn_reflection_root
  proof: Module.bijOn_reflection_of_mapsTo _ P.mapsTo_reflection_root i

@[simp]

中文:
引理 bijOn_reflection_root
  证明: Module.bijOn_reflection_of_mapsTo _ P.mapsTo_reflection_root i

@[simp]

Depends on / 依赖: Module, Module.bijOn_reflection_of_mapsTo, P.mapsTo_reflection_root, bijOn_reflection_of_mapsTo, mapsTo_reflection_root
-/
lemma bijOn_reflection_root :
    BijOn (P.reflection i) (range P.root) (range P.root) :=
Module.bijOn_reflection_of_mapsTo _ P.mapsTo_reflection_root i

@[simp]
/--
lemma `reflection_image_eq` / 引理 `reflection_image_eq`

English:
lemma reflection_image_eq
  proof: (P.bijOn_reflection_root i).image_eq

中文:
引理 reflection_image_eq
  证明: (P.bijOn_reflection_root i).image_eq

Depends on / 依赖: P.bijOn_reflection_root, bijOn_reflection_root, image_eq
-/
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  (P.bijOn_reflection_root i).image_eq

/--
Definition of `coreflection` / `coreflection` 的定义

English:
definition coreflection
  signature: : N ≃ₗ[R] N
  body: Module.reflection (P.root_coroot_two i)

@[simp]

中文:
定义 coreflection
  签名: : N ≃ₗ[R] N
  定义体: Module.reflection (P.root_coroot_two i)

@[simp]

Depends on / 依赖: Module, Module.reflection, P.root_coroot_two, reflection, root_coroot_two
-/
def coreflection : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)

@[simp]
/--
lemma `coroot_reflectionPerm` / 引理 `coroot_reflectionPerm`

English:
lemma coroot_reflectionPerm
  given: (j : ι)
  proof: (P.reflectionPerm_coroot i j).symm

中文:
引理 coroot_reflectionPerm
  条件: (j : ι)
  证明: (P.reflectionPerm_coroot i j).symm

Depends on / 依赖: P.reflectionPerm_coroot, reflectionPerm_coroot
-/
lemma coroot_reflectionPerm (j : ι) :
    P.coroot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j) :=
  (P.reflectionPerm_coroot i j).symm

/--
theorem `mapsTo_coreflection_coroot` / 定理 `mapsTo_coreflection_coroot`

English:
theorem mapsTo_coreflection_coroot
  proof: by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)

中文:
定理 mapsTo_coreflection_coroot
  证明: by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)

Depends on / 依赖: P.coroot_reflectionPerm, P.reflectionPerm, coroot_reflectionPerm, mem_range_self, reflectionPerm
-/
theorem mapsTo_coreflection_coroot :
    MapsTo (P.coreflection i) (range P.coroot) (range P.coroot) := by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)

/--
lemma `coreflection_apply` / 引理 `coreflection_apply`

English:
lemma coreflection_apply
  given: (f : N)
  proof: rfl

中文:
引理 coreflection_apply
  条件: (f : N)
  证明: rfl
-/
lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (P.root' i) f • P.coroot i :=
  rfl

/--
lemma `coreflection_apply_coroot` / 引理 `coreflection_apply_coroot`

English:
lemma coreflection_apply_coroot
  proof: rfl

@[simp]

中文:
引理 coreflection_apply_coroot
  证明: rfl

@[simp]
-/
lemma coreflection_apply_coroot :
    P.coreflection i (P.coroot j) = P.coroot j - (P.pairing i j) • P.coroot i :=
  rfl

@[simp]
/--
lemma `coreflection_apply_self` / 引理 `coreflection_apply_self`

English:
lemma coreflection_apply_self
  proof: Module.reflection_apply_self (P.flip.coroot_root_two i)

@[simp]

中文:
引理 coreflection_apply_self
  证明: Module.reflection_apply_self (P.flip.coroot_root_two i)

@[simp]

Depends on / 依赖: IsHaarMeasure, IsHaarMeasure.isInvInvariant_of_regular, Module, Module.reflection_apply_self, P.flip.coroot_root_two, coroot_root_two, isInvInvariant_of_regular, reflection_apply_self
-/
lemma coreflection_apply_self :
    P.coreflection i (P.coroot i) = - P.coroot i :=
  Module.reflection_apply_self (P.flip.coroot_root_two i)

@[simp]
/--
lemma `coreflection_same` / 引理 `coreflection_same`

English:
lemma coreflection_same
  given: (x : N)
  proof: Module.involutive_reflection (P.flip.coroot_root_two i) x

@[simp]

中文:
引理 coreflection_same
  条件: (x : N)
  证明: Module.involutive_reflection (P.flip.coroot_root_two i) x

@[simp]

Depends on / 依赖: IsHaarMeasure, IsHaarMeasure.isInvInvariant_of_innerRegular, Module, Module.involutive_reflection, P.flip.coroot_root_two, coroot_root_two, involutive_reflection, isInvInvariant_of_innerRegular
-/
lemma coreflection_same (x : N) :
    P.coreflection i (P.coreflection i x) = x :=
  Module.involutive_reflection (P.flip.coroot_root_two i) x

@[simp]
/--
lemma `coreflection_inv` / 引理 `coreflection_inv`

English:
lemma coreflection_inv
  proof: rfl

@[simp]

中文:
引理 coreflection_inv
  证明: rfl

@[simp]
-/
lemma coreflection_inv :
    (P.coreflection i)⁻¹ = P.coreflection i :=
  rfl

@[simp]
/--
lemma `coreflection_sq` / 引理 `coreflection_sq`

English:
lemma coreflection_sq
  proof: mul_eq_one_iff_eq_inv.mpr rfl

中文:
引理 coreflection_sq
  证明: mul_eq_one_iff_eq_inv.mpr rfl

Depends on / 依赖: mul_eq_one_iff_eq_inv, mul_eq_one_iff_eq_inv.mpr
-/
lemma coreflection_sq :
    P.coreflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl

/--
lemma `bijOn_coreflection_coroot` / 引理 `bijOn_coreflection_coroot`

English:
lemma bijOn_coreflection_coroot
  statement: BijOn (P.coreflection i) (range P.coroot) (range P.coroot)
  proof: bijOn_reflection_root P.flip i

@[simp]

中文:
引理 bijOn_coreflection_coroot
  结论: 双射限制 (P.coreflection i) (range P.coroot) (range P.coroot)
  证明: bijOn_reflection_root P.flip i

@[simp]

Depends on / 依赖: P.flip, bijOn_reflection_root
-/
lemma bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (range P.coroot) :=
  bijOn_reflection_root P.flip i

@[simp]
/--
lemma `coreflection_image_eq` / 引理 `coreflection_image_eq`

English:
lemma coreflection_image_eq
  proof: (P.bijOn_coreflection_coroot i).image_eq

中文:
引理 coreflection_image_eq
  证明: (P.bijOn_coreflection_coroot i).image_eq

Depends on / 依赖: P.bijOn_coreflection_coroot, bijOn_coreflection_coroot, image_eq
-/
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  (P.bijOn_coreflection_coroot i).image_eq

/--
lemma `coreflection_eq_flip_reflection` / 引理 `coreflection_eq_flip_reflection`

English:
lemma coreflection_eq_flip_reflection
  proof: rfl

中文:
引理 coreflection_eq_flip_reflection
  证明: rfl
-/
lemma coreflection_eq_flip_reflection :
    P.coreflection i = P.flip.reflection i :=
  rfl

/--
lemma `reflection_reflectionPerm` / 引理 `reflection_reflectionPerm`

English:
lemma reflection_reflectionPerm
  given: {i j : ι}
  proof: by
  ext x; simp [reflection_apply, coreflection_apply]; module

中文:
引理 reflection_reflectionPerm
  条件: {i j : ι}
  证明: by
  ext x; simp [reflection_apply, coreflection_apply]; module

Depends on / 依赖: coreflection_apply, module, reflection_apply
-/
lemma reflection_reflectionPerm {i j : ι} :
    P.reflection (P.reflectionPerm j i) = P.reflection j * P.reflection i * P.reflection j := by
  ext x; simp [reflection_apply, coreflection_apply]; module

/--
lemma `reflection_dualMap_eq_coreflection` / 引理 `reflection_dualMap_eq_coreflection`

English:
lemma reflection_dualMap_eq_coreflection
  proof: by
  ext n m
  simp [map_sub, coreflection_apply, reflection_apply, mul_comm (P.toLinearMap m (P.coroot i))]

中文:
引理 reflection_dualMap_eq_coreflection
  证明: by
  ext n m
  simp [map_sub, coreflection_apply, reflection_apply, mul_comm (P.toLinearMap m (P.coroot i))]

Depends on / 依赖: P.coroot, P.toLinearMap, coreflection_apply, coroot, map_sub, mul_comm, reflection_apply, toLinearMap
-/
lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLinearMap.flip = P.toLinearMap.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [map_sub, coreflection_apply, reflection_apply, mul_comm (P.toLinearMap m (P.coroot i))]

/--
lemma `coroot_eq_coreflection_of_root_eq` / 引理 `coroot_eq_coreflection_of_root_eq`

English:
lemma coroot_eq_coreflection_of_root_eq
  proof: by
  rw [← P.root_reflectionPerm]; rw [EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflectionPerm]; rw [hk]

中文:
引理 coroot_eq_coreflection_of_root_eq
  证明: by
  rw [← P.root_reflectionPerm]; rw [EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflectionPerm]; rw [hk]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, P.coroot_reflectionPerm, P.root_reflectionPerm, apply_eq_iff_eq, coroot_reflectionPerm, root_reflectionPerm
-/
lemma coroot_eq_coreflection_of_root_eq
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) := by
  rw [← P.root_reflectionPerm]; rw [EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflectionPerm]; rw [hk]

/--
lemma `coroot'_reflectionPerm` / 引理 `coroot'_reflectionPerm`

English:
lemma coroot'_reflectionPerm
  given: {i j : ι}
  proof: by
  ext y
  simp [coreflection_apply_coroot, reflection_apply, map_sub, mul_comm]

中文:
引理 coroot'_reflectionPerm
  条件: {i j : ι}
  证明: by
  ext y
  simp [coreflection_apply_coroot, reflection_apply, map_sub, mul_comm]
-/
lemma coroot'_reflectionPerm {i j : ι} :
    P.coroot' (P.reflectionPerm i j) = P.coroot' j ∘ₗ P.reflection i := by
  ext y
  simp [coreflection_apply_coroot, reflection_apply, map_sub, mul_comm]

/--
lemma `coroot'_reflection` / 引理 `coroot'_reflection`

English:
lemma coroot'_reflection
  given: {i j : ι} (y : M)
  proof: (LinearMap.congr_fun P.coroot'_reflectionPerm y).symm

中文:
引理 coroot'_reflection
  条件: {i j : ι} (y : M)
  证明: (LinearMap.congr_fun P.coroot'_reflectionPerm y).symm
-/
lemma coroot'_reflection {i j : ι} (y : M) :
    P.coroot' j (P.reflection i y) = P.coroot' (P.reflectionPerm i j) y :=
  (LinearMap.congr_fun P.coroot'_reflectionPerm y).symm

/--
lemma `pairing_reflectionPerm` / 引理 `pairing_reflectionPerm`

English:
lemma pairing_reflectionPerm
  given: (i j k : ι)
  proof: by
  simp only [pairing, root', coroot_reflectionPerm, root_reflectionPerm]
  simp [coreflection_apply_coroot, reflection_apply_root, mul_comm]

@[simp]

中文:
引理 pairing_reflectionPerm
  条件: (i j k : ι)
  证明: by
  simp only [pairing, root', coroot_reflectionPerm, root_reflectionPerm]
  simp [coreflection_apply_coroot, reflection_apply_root, mul_comm]

@[simp]

Depends on / 依赖: coreflection_apply_coroot, coroot_reflectionPerm, mul_comm, pairing, reflection_apply_root, root_reflectionPerm
-/
lemma pairing_reflectionPerm (i j k : ι) :
    P.pairing j (P.reflectionPerm i k) = P.pairing (P.reflectionPerm i j) k := by
  simp only [pairing, root', coroot_reflectionPerm, root_reflectionPerm]
  simp [coreflection_apply_coroot, reflection_apply_root, mul_comm]

@[simp]
/--
lemma `toPerfPair_conj_reflection` / 引理 `toPerfPair_conj_reflection`

English:
lemma toPerfPair_conj_reflection
  proof: by
  ext f n
  simp [reflection_apply, coreflection_apply, mul_comm (f <| P.coroot i)]

@[simp]

中文:
引理 toPerfPair_conj_reflection
  证明: by
  ext f n
  simp [reflection_apply, coreflection_apply, mul_comm (f <| P.coroot i)]

@[simp]

Depends on / 依赖: P.coroot, coreflection_apply, coroot, mul_comm, reflection_apply
-/
lemma toPerfPair_conj_reflection :
    P.toPerfPair.conj (P.reflection i) = (P.coreflection i).toLinearMap.dualMap := by
  ext f n
  simp [reflection_apply, coreflection_apply, mul_comm (f <| P.coroot i)]

@[simp]
/--
lemma `toPerfPair_flip_conj_coreflection` / 引理 `toPerfPair_flip_conj_coreflection`

English:
lemma toPerfPair_flip_conj_coreflection
  proof: P.flip.toPerfPair_conj_reflection i

@[simp]

中文:
引理 toPerfPair_flip_conj_coreflection
  证明: P.flip.toPerfPair_conj_reflection i

@[simp]

Depends on / 依赖: P.flip.toPerfPair_conj_reflection, toPerfPair_conj_reflection
-/
lemma toPerfPair_flip_conj_coreflection :
    P.toLinearMap.flip.toPerfPair.conj (P.coreflection i) = (P.reflection i).toLinearMap.dualMap :=
  P.flip.toPerfPair_conj_reflection i

@[simp]
/--
lemma `pairing_reflectionPerm_self_left` / 引理 `pairing_reflectionPerm_self_left`

English:
lemma pairing_reflectionPerm_self_left
  given: (P : RootPairing ι R M N) (i j : ι)
  proof: by
  rw [pairing]; rw [root']; rw [← reflectionPerm_root]; rw [root'_coroot_eq_pairing]; rw [pairing_same]; rw [two_smul]; rw [sub_add_cancel_left]; rw [LinearMap.map_neg₂]; rw [root'_coroot_eq_pairing]

@[simp]

中文:
引理 pairing_reflectionPerm_self_left
  条件: (P : RootPairing ι R M N) (i j : ι)
  证明: by
  rw [pairing]; rw [root']; rw [← reflectionPerm_root]; rw [root'_coroot_eq_pairing]; rw [pairing_same]; rw [two_smul]; rw [sub_add_cancel_left]; rw [LinearMap.map_neg₂]; rw [root'_coroot_eq_pairing]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.map_neg, _coroot_eq_pairing, pairing, pairing_same, reflectionPerm_root, sub_add_cancel_left, two_smul
-/
lemma pairing_reflectionPerm_self_left (P : RootPairing ι R M N) (i j : ι) :
    P.pairing (P.reflectionPerm i i) j = - P.pairing i j := by
  rw [pairing]; rw [root']; rw [← reflectionPerm_root]; rw [root'_coroot_eq_pairing]; rw [pairing_same]; rw [two_smul]; rw [sub_add_cancel_left]; rw [LinearMap.map_neg₂]; rw [root'_coroot_eq_pairing]

@[simp]
/--
lemma `pairing_reflectionPerm_self_right` / 引理 `pairing_reflectionPerm_self_right`

English:
lemma pairing_reflectionPerm_self_right
  given: (i j : ι)
  proof: by
  rw [pairing]; rw [← reflectionPerm_coroot]; rw [root_coroot_eq_pairing]; rw [pairing_same]; rw [two_smul]; rw [sub_add_cancel_left]; rw [map_neg]; rw [root_coroot_eq_pairing]

中文:
引理 pairing_reflectionPerm_self_right
  条件: (i j : ι)
  证明: by
  rw [pairing]; rw [← reflectionPerm_coroot]; rw [root_coroot_eq_pairing]; rw [pairing_same]; rw [two_smul]; rw [sub_add_cancel_left]; rw [map_neg]; rw [root_coroot_eq_pairing]

Depends on / 依赖: map_neg, pairing, pairing_same, reflectionPerm_coroot, root_coroot_eq_pairing, sub_add_cancel_left, two_smul
-/
lemma pairing_reflectionPerm_self_right (i j : ι) :
    P.pairing i (P.reflectionPerm j j) = - P.pairing i j := by
  rw [pairing]; rw [← reflectionPerm_coroot]; rw [root_coroot_eq_pairing]; rw [pairing_same]; rw [two_smul]; rw [sub_add_cancel_left]; rw [map_neg]; rw [root_coroot_eq_pairing]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `indexNeg` / `indexNeg` 的定义

English:
definition indexNeg
  signature: : InvolutiveNeg ι where
  body: P.reflectionPerm i i
  neg_neg i := by
    apply P.root.injective
    simp only [root_reflectionPerm, reflection_apply, LinearMap.flip_apply, root_coroot_eq_pairing,
      pairing_same, map_sub, coroot_reflectionPerm, coreflection_apply_self, map_neg, neg_smul,
      sub_neg_eq_add, map_smul, smul_add]
    module

中文:
定义 indexNeg
  签名: : InvolutiveNeg ι where
  定义体: P.reflectionPerm i i
  neg_neg i := by
    apply P.root.injective
    simp only [root_reflectionPerm, reflection_apply, LinearMap.flip_apply, root_coroot_eq_pairing,
      pairing_same, map_sub, coroot_reflectionPerm, coreflection_apply_self, map_neg, neg_smul,
      sub_neg_eq_add, map_smul, smul_add]
    module
-/
@[simps, instance_reducible] def indexNeg : InvolutiveNeg ι where
  neg i := P.reflectionPerm i i
  neg_neg i := by
    apply P.root.injective
    simp only [root_reflectionPerm, reflection_apply, LinearMap.flip_apply, root_coroot_eq_pairing,
      pairing_same, map_sub, coroot_reflectionPerm, coreflection_apply_self, map_neg, neg_smul,
      sub_neg_eq_add, map_smul, smul_add]
    module

/--
lemma `ne_neg` / 引理 `ne_neg`

English:
lemma ne_neg
  given: [NeZero (2 : R)] [IsDomain R]
  proof: P.indexNeg
    i != -i := by
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  intro contra
  replace contra : P.root i = -P.root i := by simpa using congr_arg P.root contra
  simp [eq_neg_iff_add_eq_zero, ← two_smul R, NeZero.out, P.ne_zero i] at contra

中文:
引理 ne_neg
  条件: [NeZero (2 : R)] [是整环 R]
  证明: P.indexNeg
    i != -i := by
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  intro contra
  replace contra : P.root i = -P.root i := by simpa using congr_arg P.root contra
  simp [eq_neg_iff_add_eq_zero, ← two_smul R, NeZero.out, P.ne_zero i] at contra

Depends on / 依赖: P.indexNeg, indexNeg
-/
lemma ne_neg [NeZero (2 : R)] [IsDomain R] :
    letI := P.indexNeg
    i != -i := by
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  intro contra
  replace contra : P.root i = -P.root i := by simpa using congr_arg P.root contra
  simp [eq_neg_iff_add_eq_zero, ← two_smul R, NeZero.out, P.ne_zero i] at contra

variable {i j} in
@[simp]
/--
lemma `root_eq_neg_iff` / 引理 `root_eq_neg_iff`

English:
lemma root_eq_neg_iff
  proof: by
  refine ⟨fun h => P.root.injective ?_, fun h => by simp [h]⟩
  rw [root_reflectionPerm]; rw [reflection_apply_self]; rw [h]

中文:
引理 root_eq_neg_iff
  证明: by
  refine ⟨fun h => P.root.injective ?_, fun h => by simp [h]⟩
  rw [root_reflectionPerm]; rw [reflection_apply_self]; rw [h]

Depends on / 依赖: P.root.injective, injective, reflection_apply_self, root_reflectionPerm
-/
lemma root_eq_neg_iff :
    P.root i = - P.root j ↔ i = P.reflectionPerm j j := by
  refine ⟨fun h => P.root.injective ?_, fun h => by simp [h]⟩
  rw [root_reflectionPerm]; rw [reflection_apply_self]; rw [h]

variable {i j} in
@[simp]
/--
lemma `coroot_eq_neg_iff` / 引理 `coroot_eq_neg_iff`

English:
lemma coroot_eq_neg_iff
  proof: P.flip.root_eq_neg_iff

中文:
引理 coroot_eq_neg_iff
  证明: P.flip.root_eq_neg_iff

Depends on / 依赖: P.flip.root_eq_neg_iff, root_eq_neg_iff
-/
lemma coroot_eq_neg_iff :
    P.coroot i = - P.coroot j ↔ i = P.reflectionPerm j j :=
  P.flip.root_eq_neg_iff

/--
lemma `neg_mem_range_root_iff` / 引理 `neg_mem_range_root_iff`

English:
lemma neg_mem_range_root_iff
  given: {x : M}
  proof: by
  suffices forall x : M, -x in range P.root -> x in range P.root by
    refine ⟨this x, fun h => ?_⟩
    rw [← neg_neg x] at h
    exact this (-x) h
  intro y ⟨i, hi⟩
  exact ⟨P.reflectionPerm i i, by simp [neg_eq_iff_eq_neg.mpr hi]⟩

中文:
引理 neg_mem_range_root_iff
  条件: {x : M}
  证明: by
  suffices forall x : M, -x in range P.root -> x in range P.root by
    refine ⟨this x, fun h => ?_⟩
    rw [← neg_neg x] at h
    exact this (-x) h
  intro y ⟨i, hi⟩
  exact ⟨P.reflectionPerm i i, by simp [neg_eq_iff_eq_neg.mpr hi]⟩

Depends on / 依赖: P.reflectionPerm, P.root, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg.mpr, neg_neg, reflectionPerm
-/
lemma neg_mem_range_root_iff {x : M} :
    -x in range P.root ↔ x in range P.root := by
  suffices forall x : M, -x in range P.root -> x in range P.root by
    refine ⟨this x, fun h => ?_⟩
    rw [← neg_neg x] at h
    exact this (-x) h
  intro y ⟨i, hi⟩
  exact ⟨P.reflectionPerm i i, by simp [neg_eq_iff_eq_neg.mpr hi]⟩

/--
lemma `neg_mem_range_coroot_iff` / 引理 `neg_mem_range_coroot_iff`

English:
lemma neg_mem_range_coroot_iff
  given: {x : N}
  proof: P.flip.neg_mem_range_root_iff

中文:
引理 neg_mem_range_coroot_iff
  条件: {x : N}
  证明: P.flip.neg_mem_range_root_iff

Depends on / 依赖: P.flip.neg_mem_range_root_iff, neg_mem_range_root_iff
-/
lemma neg_mem_range_coroot_iff {x : N} :
    -x in range P.coroot ↔ x in range P.coroot :=
  P.flip.neg_mem_range_root_iff

/--
lemma `neg_root_mem` / 引理 `neg_root_mem`

English:
lemma neg_root_mem
  proof: ⟨P.reflectionPerm i i, by simp⟩

中文:
引理 neg_root_mem
  证明: ⟨P.reflectionPerm i i, by simp⟩

Depends on / 依赖: P.reflectionPerm, reflectionPerm
-/
lemma neg_root_mem :
    - P.root i in range P.root :=
  ⟨P.reflectionPerm i i, by simp⟩

/--
lemma `neg_coroot_mem` / 引理 `neg_coroot_mem`

English:
lemma neg_coroot_mem
  proof: P.flip.neg_root_mem i

中文:
引理 neg_coroot_mem
  证明: P.flip.neg_root_mem i

Depends on / 依赖: P.flip.neg_root_mem, neg_root_mem
-/
lemma neg_coroot_mem :
    - P.coroot i in range P.coroot :=
  P.flip.neg_root_mem i

variable {P} in
/--
lemma `smul_coroot_eq_of_root_eq_smul` / 引理 `smul_coroot_eq_of_root_eq_smul`

English:
lemma smul_coroot_eq_of_root_eq_smul
  statement: [Finite ι] [IsAddTorsionFree N] (i j : ι) (t : R)
  proof: by
  have hij : t * P.pairing i j = 2 := by simpa using ((P.coroot' j).congr_arg h).symm
  refine Module.eq_of_mapsTo_reflection_of_mem (f := P.root' i) (g := P.root' i)
    (finite_range P.coroot) (by simp [hij]) (by simp) (by simp [hij]) (by simp) ?_
    (P.mapsTo_coreflection_coroot i) (mem_range_self i)
  convert! P.mapsTo_coreflection_coroot j
  ext x
  replace h : P.root' j = t • P.root' i := by ext; simp [h, root']
  simp [Module.preReflection_apply, coreflection_apply, h, smul_comm _ t, mul_smul]

中文:
引理 smul_coroot_eq_of_root_eq_smul
  结论: [有限 ι] [是加法无挠 N] (i j : ι) (t : R)
  证明: by
  have hij : t * P.pairing i j = 2 := by simpa using ((P.coroot' j).congr_arg h).symm
  refine Module.eq_of_mapsTo_reflection_of_mem (f := P.root' i) (g := P.root' i)
    (finite_range P.coroot) (by simp [hij]) (by simp) (by simp [hij]) (by simp) ?_
    (P.mapsTo_coreflection_coroot i) (mem_range_self i)
  convert! P.mapsTo_coreflection_coroot j
  ext x
  replace h : P.root' j = t • P.root' i := by ext; simp [h, root']
  simp [Module.preReflection_apply, coreflection_apply, h, smul_comm _ t, mul_smul]

Depends on / 依赖: Module, Module.eq_of_mapsTo_reflection_of_mem, Module.preReflection_apply, P.coroot, P.mapsTo_coreflection_coroot, P.pairing, P.root, congr_arg, convert, coreflection_apply, coroot, eq_of_mapsTo_reflection_of_mem, finite_range, mapsTo_coreflection_coroot, mem_range_self, mul_smul, pairing, preReflection_apply, replace, smul_comm
-/
lemma smul_coroot_eq_of_root_eq_smul [Finite ι] [IsAddTorsionFree N] (i j : ι) (t : R)
    (h : P.root j = t • P.root i) :
    t • P.coroot j = P.coroot i := by
  have hij : t * P.pairing i j = 2 := by simpa using ((P.coroot' j).congr_arg h).symm
  refine Module.eq_of_mapsTo_reflection_of_mem (f := P.root' i) (g := P.root' i)
    (finite_range P.coroot) (by simp [hij]) (by simp) (by simp [hij]) (by simp) ?_
    (P.mapsTo_coreflection_coroot i) (mem_range_self i)
  convert! P.mapsTo_coreflection_coroot j
  ext x
  replace h : P.root' j = t • P.root' i := by ext; simp [h, root']
  simp [Module.preReflection_apply, coreflection_apply, h, smul_comm _ t, mul_smul]

variable {P} in
/--
lemma `coroot_eq_smul_coroot_iff` / 引理 `coroot_eq_smul_coroot_iff`

English:
lemma coroot_eq_smul_coroot_iff
  statement: [Finite ι] [IsAddTorsionFree M] [IsAddTorsionFree N]
  proof: ⟨fun h => (P.flip.smul_coroot_eq_of_root_eq_smul j i t h).symm,
    fun h => (P.smul_coroot_eq_of_root_eq_smul i j t h).symm⟩

中文:
引理 coroot_eq_smul_coroot_iff
  结论: [有限 ι] [是加法无挠 M] [是加法无挠 N]
  证明: ⟨fun h => (P.flip.smul_coroot_eq_of_root_eq_smul j i t h).symm,
    fun h => (P.smul_coroot_eq_of_root_eq_smul i j t h).symm⟩
-/
@[simp] lemma coroot_eq_smul_coroot_iff [Finite ι] [IsAddTorsionFree M] [IsAddTorsionFree N]
    {i j : ι} {t : R} :
    P.coroot i = t • P.coroot j ↔ P.root j = t • P.root i :=
  ⟨fun h => (P.flip.smul_coroot_eq_of_root_eq_smul j i t h).symm,
    fun h => (P.smul_coroot_eq_of_root_eq_smul i j t h).symm⟩

/--
lemma `mem_range_root_of_mem_range_reflection_of_mem_range_root` / 引理 `mem_range_root_of_mem_range_reflection_of_mem_range_root`

English:
lemma mem_range_root_of_mem_range_reflection_of_mem_range_root
  proof: by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.root_reflectionPerm i j⟩

中文:
引理 mem_range_root_of_mem_range_reflection_of_mem_range_root
  证明: by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.root_reflectionPerm i j⟩

Depends on / 依赖: P.reflectionPerm, P.root_reflectionPerm, reflectionPerm, root_reflectionPerm
-/
lemma mem_range_root_of_mem_range_reflection_of_mem_range_root
    {r : M ≃ₗ[R] M} {α : M} (hr : r in range P.reflection) (hα : α in range P.root) :
    r • α in range P.root := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.root_reflectionPerm i j⟩

/--
lemma `mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot` / 引理 `mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot`

English:
lemma mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot
  proof: by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.coroot_reflectionPerm i j⟩

中文:
引理 mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot
  证明: by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.coroot_reflectionPerm i j⟩

Depends on / 依赖: P.coroot_reflectionPerm, P.reflectionPerm, coroot_reflectionPerm, reflectionPerm
-/
lemma mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot
    {r : N ≃ₗ[R] N} {α : N} (hr : r in range P.coreflection) (hα : α in range P.coroot) :
    r • α in range P.coroot := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.coroot_reflectionPerm i j⟩

/--
lemma `pairing_smul_root_eq` / 引理 `pairing_smul_root_eq`

English:
lemma pairing_smul_root_eq
  given: (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j)
  proof: by
  have h : P.reflection i (P.root k) = P.reflection j (P.root k) := by
    simp only [← root_reflectionPerm, hij]
  simpa only [reflection_apply_root, sub_right_inj] using h

中文:
引理 pairing_smul_root_eq
  条件: (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j)
  证明: by
  have h : P.reflection i (P.root k) = P.reflection j (P.root k) := by
    simp only [← root_reflectionPerm, hij]
  simpa only [reflection_apply_root, sub_right_inj] using h

Depends on / 依赖: P.reflection, P.root, reflection, reflection_apply_root, root_reflectionPerm, sub_right_inj
-/
lemma pairing_smul_root_eq (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j) :
    P.pairing k i • P.root i = P.pairing k j • P.root j := by
  have h : P.reflection i (P.root k) = P.reflection j (P.root k) := by
    simp only [← root_reflectionPerm, hij]
  simpa only [reflection_apply_root, sub_right_inj] using h

/--
lemma `pairing_smul_coroot_eq` / 引理 `pairing_smul_coroot_eq`

English:
lemma pairing_smul_coroot_eq
  given: (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j)
  proof: by
  have h : P.coreflection i (P.coroot k) = P.coreflection j (P.coroot k) := by
    simp only [← coroot_reflectionPerm, hij]
  simpa only [coreflection_apply_coroot, sub_right_inj] using h

中文:
引理 pairing_smul_coroot_eq
  条件: (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j)
  证明: by
  have h : P.coreflection i (P.coroot k) = P.coreflection j (P.coroot k) := by
    simp only [← coroot_reflectionPerm, hij]
  simpa only [coreflection_apply_coroot, sub_right_inj] using h

Depends on / 依赖: P.coreflection, P.coroot, coreflection, coreflection_apply_coroot, coroot, coroot_reflectionPerm, sub_right_inj
-/
lemma pairing_smul_coroot_eq (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j) :
    P.pairing i k • P.coroot i = P.pairing j k • P.coroot j := by
  have h : P.coreflection i (P.coroot k) = P.coreflection j (P.coroot k) := by
    simp only [← coroot_reflectionPerm, hij]
  simpa only [coreflection_apply_coroot, sub_right_inj] using h

/--
lemma `two_nsmul_reflection_eq_of_perm_eq` / 引理 `two_nsmul_reflection_eq_of_perm_eq`

English:
lemma two_nsmul_reflection_eq_of_perm_eq
  given: (hij : P.reflectionPerm i = P.reflectionPerm j)
  proof: by
  ext x
  suffices
      2 • P.toLinearMap x (P.coroot i) • P.root i = 2 • P.toLinearMap x (P.coroot j) • P.root j by
    simpa [reflection_apply, smul_sub]
  calc 2 • P.toLinearMap x (P.coroot i) • P.root i
      = P.toLinearMap x (P.coroot i) • ((2 : R) • P.root i) := ?_
    _ = P.toLinearMap x (P.coroot i) • (P.pairing i j • P.root j) := ?_
    _ = P.toLinearMap x (P.pairing i j • P.coroot i) • (P.root j) := ?_
    _ = P.toLinearMap x ((2 : R) • P.coroot j) • (P.root j) := ?_
    _ = 2 • P.toLinearMap x (P.coroot j) • P.root j := ?_
  · rw [smul_comm, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]
  · rw [P.pairing_smul_root_eq j i i hij.symm, pairing_same]
  · rw [← smul_comm, ← smul_assoc, map_smul]
  · rw [← P.pairing_smul_coroot_eq j i j hij.symm, pairing_same]
  · rw [map_smul, smul_assoc, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]

中文:
引理 two_nsmul_reflection_eq_of_perm_eq
  条件: (hij : P.reflectionPerm i = P.reflectionPerm j)
  证明: by
  ext x
  suffices
      2 • P.toLinearMap x (P.coroot i) • P.root i = 2 • P.toLinearMap x (P.coroot j) • P.root j by
    simpa [reflection_apply, smul_sub]
  calc 2 • P.toLinearMap x (P.coroot i) • P.root i
      = P.toLinearMap x (P.coroot i) • ((2 : R) • P.root i) := ?_
    _ = P.toLinearMap x (P.coroot i) • (P.pairing i j • P.root j) := ?_
    _ = P.toLinearMap x (P.pairing i j • P.coroot i) • (P.root j) := ?_
    _ = P.toLinearMap x ((2 : R) • P.coroot j) • (P.root j) := ?_
    _ = 2 • P.toLinearMap x (P.coroot j) • P.root j := ?_
  · rw [smul_comm, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]
  · rw [P.pairing_smul_root_eq j i i hij.symm, pairing_same]
  · rw [← smul_comm, ← smul_assoc, map_smul]
  · rw [← P.pairing_smul_coroot_eq j i j hij.symm, pairing_same]
  · rw [map_smul, smul_assoc, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]

Depends on / 依赖: P.coroot, P.pairing, P.root, P.toLinearMap, coroot, pairing, reflection_apply, smul_sub, toLinearMap
-/
lemma two_nsmul_reflection_eq_of_perm_eq (hij : P.reflectionPerm i = P.reflectionPerm j) :
    2 • ⇑(P.reflection i) = 2 • P.reflection j := by
  ext x
  suffices
      2 • P.toLinearMap x (P.coroot i) • P.root i = 2 • P.toLinearMap x (P.coroot j) • P.root j by
    simpa [reflection_apply, smul_sub]
  calc 2 • P.toLinearMap x (P.coroot i) • P.root i
      = P.toLinearMap x (P.coroot i) • ((2 : R) • P.root i) := ?_
    _ = P.toLinearMap x (P.coroot i) • (P.pairing i j • P.root j) := ?_
    _ = P.toLinearMap x (P.pairing i j • P.coroot i) • (P.root j) := ?_
    _ = P.toLinearMap x ((2 : R) • P.coroot j) • (P.root j) := ?_
    _ = 2 • P.toLinearMap x (P.coroot j) • P.root j := ?_
  · rw [smul_comm, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]
  · rw [P.pairing_smul_root_eq j i i hij.symm, pairing_same]
  · rw [← smul_comm, ← smul_assoc, map_smul]
  · rw [← P.pairing_smul_coroot_eq j i j hij.symm, pairing_same]
  · rw [map_smul, smul_assoc, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]

/--
lemma `reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular` / 引理 `reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular`

English:
lemma reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular
  given: (h2 : IsSMulRegular M 2)
  proof: by
refine ⟨fun h => ?_, fun h => Equiv.ext fun k => P.root.injective by simp [h]⟩
  suffices ⇑(P.reflection i) = ⇑(P.reflection j) from DFunLike.coe_injective this
  replace h2 : IsSMulRegular (M -> M) 2 := IsSMulRegular.pi fun _ => h2
exact h2 P.two_nsmul_reflection_eq_of_perm_eq i j h

中文:
引理 reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular
  条件: (h2 : IsSMulRegular M 2)
  证明: by
refine ⟨fun h => ?_, fun h => Equiv.ext fun k => P.root.injective by simp [h]⟩
  suffices ⇑(P.reflection i) = ⇑(P.reflection j) from DFunLike.coe_injective this
  replace h2 : IsSMulRegular (M -> M) 2 := IsSMulRegular.pi fun _ => h2
exact h2 P.two_nsmul_reflection_eq_of_perm_eq i j h

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Equiv.ext, IsSMulRegular, IsSMulRegular.pi, P.reflection, P.root.injective, P.two_nsmul_reflection_eq_of_perm_eq, coe_injective, injective, reflection, replace, two_nsmul_reflection_eq_of_perm_eq
-/
lemma reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular (h2 : IsSMulRegular M 2) :
    P.reflectionPerm i = P.reflectionPerm j ↔ P.reflection i = P.reflection j := by
refine ⟨fun h => ?_, fun h => Equiv.ext fun k => P.root.injective by simp [h]⟩
  suffices ⇑(P.reflection i) = ⇑(P.reflection j) from DFunLike.coe_injective this
  replace h2 : IsSMulRegular (M -> M) 2 := IsSMulRegular.pi fun _ => h2
exact h2 P.two_nsmul_reflection_eq_of_perm_eq i j h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `reflectionPerm_eq_reflectionPerm_iff_of_span` / 引理 `reflectionPerm_eq_reflectionPerm_iff_of_span`

English:
lemma reflectionPerm_eq_reflectionPerm_iff_of_span
  proof: by
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [← root_reflectionPerm, h]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul t x _ hx => simp [hx]
  · ext k
    apply P.root.injective
    simp [h (P.root k) (Submodule.subset_span <| mem_range_self k)]

中文:
引理 reflectionPerm_eq_reflectionPerm_iff_of_span
  证明: by
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [← root_reflectionPerm, h]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul t x _ hx => simp [hx]
  · ext k
    apply P.root.injective
    simp [h (P.root k) (Submodule.subset_span <| mem_range_self k)]

Depends on / 依赖: P.root, P.root.injective, Submodule, Submodule.span_induction, Submodule.subset_span, injective, mem_range_self, root_reflectionPerm, span_induction, subset_span
-/
lemma reflectionPerm_eq_reflectionPerm_iff_of_span :
    P.reflectionPerm i = P.reflectionPerm j ↔
    forall x in span R (range P.root), P.reflection i x = P.reflection j x := by
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [← root_reflectionPerm, h]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul t x _ hx => simp [hx]
  · ext k
    apply P.root.injective
    simp [h (P.root k) (Submodule.subset_span <| mem_range_self k)]

/--
lemma `reflectionPerm_eq_reflectionPerm_iff` / 引理 `reflectionPerm_eq_reflectionPerm_iff`

English:
lemma reflectionPerm_eq_reflectionPerm_iff
  given: [P.IsRootSystem] (i j : ι)
  proof: by
refine ⟨fun h => ?_, fun h => Equiv.ext fun k => P.root.injective by simp [h]⟩
  ext x
exact (P.reflectionPerm_eq_reflectionPerm_iff_of_span i j).mp h x by simp

中文:
引理 reflectionPerm_eq_reflectionPerm_iff
  条件: [P.是RootSystem] (i j : ι)
  证明: by
refine ⟨fun h => ?_, fun h => Equiv.ext fun k => P.root.injective by simp [h]⟩
  ext x
exact (P.reflectionPerm_eq_reflectionPerm_iff_of_span i j).mp h x by simp

Depends on / 依赖: Equiv.ext, P.reflectionPerm_eq_reflectionPerm_iff_of_span, P.root.injective, injective, reflectionPerm_eq_reflectionPerm_iff_of_span
-/
lemma reflectionPerm_eq_reflectionPerm_iff [P.IsRootSystem] (i j : ι) :
    P.reflectionPerm i = P.reflectionPerm j ↔ P.reflection i = P.reflection j := by
refine ⟨fun h => ?_, fun h => Equiv.ext fun k => P.root.injective by simp [h]⟩
  ext x
exact (P.reflectionPerm_eq_reflectionPerm_iff_of_span i j).mp h x by simp

/--
lemma `toPerfPair_comp_root` / 引理 `toPerfPair_comp_root`

English:
lemma toPerfPair_comp_root
  statement: P.toPerfPair ∘ P.root = P.root'
  proof: rfl

中文:
引理 toPerfPair_comp_root
  结论: P.toPerfPair ∘ P.root = P.root'
  证明: rfl
-/
@[simp] lemma toPerfPair_comp_root : P.toPerfPair ∘ P.root = P.root' := rfl

/--
lemma `toPerfPair_flip_comp_coroot` / 引理 `toPerfPair_flip_comp_coroot`

English:
lemma toPerfPair_flip_comp_coroot
  proof: rfl

中文:
引理 toPerfPair_flip_comp_coroot
  证明: rfl
-/
@[simp] lemma toPerfPair_flip_comp_coroot :
    P.toLinearMap.flip.toPerfPair ∘ P.coroot = P.coroot' := rfl

/--
Definition of `coxeterWeight` / `coxeterWeight` 的定义

English:
definition coxeterWeight
  signature: : R
  body: pairing P i j * pairing P j i

中文:
定义 coxeterWeight
  签名: : R
  定义体: pairing P i j * pairing P j i

Depends on / 依赖: pairing
-/
def coxeterWeight : R := pairing P i j * pairing P j i

/--
lemma `coxeterWeight_flip` / 引理 `coxeterWeight_flip`

English:
lemma coxeterWeight_flip
  proof: by
  simp [coxeterWeight, mul_comm (P.pairing j i)]

中文:
引理 coxeterWeight_flip
  证明: by
  simp [coxeterWeight, mul_comm (P.pairing j i)]
-/
@[simp] lemma coxeterWeight_flip :
    P.flip.coxeterWeight i j = P.coxeterWeight i j := by
  simp [coxeterWeight, mul_comm (P.pairing j i)]

/--
lemma `coxeterWeight_swap` / 引理 `coxeterWeight_swap`

English:
lemma coxeterWeight_swap
  statement: coxeterWeight P i j = coxeterWeight P j i
  proof: by
  simp only [coxeterWeight, mul_comm]

中文:
引理 coxeterWeight_swap
  结论: coxeterWeight P i j = coxeterWeight P j i
  证明: by
  simp only [coxeterWeight, mul_comm]

Depends on / 依赖: coxeterWeight, mul_comm
-/
lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]

/--
Definition of `IsOrthogonal` / `IsOrthogonal` 的定义

English:
definition IsOrthogonal
  signature: : Prop
  body: pairing P i j = 0 ∧ pairing P j i = 0

中文:
定义 IsOrthogonal
  签名: : 命题
  定义体: pairing P i j = 0 ∧ pairing P j i = 0

Depends on / 依赖: pairing
-/
def IsOrthogonal : Prop := pairing P i j = 0 ∧ pairing P j i = 0

/--
lemma `isOrthogonal_symm` / 引理 `isOrthogonal_symm`

English:
lemma isOrthogonal_symm
  statement: IsOrthogonal P i j ↔ IsOrthogonal P j i
  proof: by
  simp only [IsOrthogonal, and_comm]

中文:
引理 isOrthogonal_symm
  结论: IsOrthogonal P i j ↔ IsOrthogonal P j i
  证明: by
  simp only [IsOrthogonal, and_comm]

Depends on / 依赖: IsOrthogonal, and_comm
-/
lemma isOrthogonal_symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isOrthogonal_comm` / 引理 `isOrthogonal_comm`

English:
lemma isOrthogonal_comm
  given: (h : IsOrthogonal P i j)
  statement: Commute (P.reflection i) (P.reflection j)
  proof: by
  rw [commute_iff_eq]
  ext
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  simp only [LinearEquiv.mul_apply, reflection_apply, LinearMap.flip_apply, map_sub,
    map_smul, root_coroot_eq_pairing, h, zero_smul, sub_zero]
  abel

中文:
引理 isOrthogonal_comm
  条件: (h : IsOrthogonal P i j)
  结论: Commute (P.reflection i) (P.reflection j)
  证明: by
  rw [commute_iff_eq]
  ext
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  simp only [LinearEquiv.mul_apply, reflection_apply, LinearMap.flip_apply, map_sub,
    map_smul, root_coroot_eq_pairing, h, zero_smul, sub_zero]
  abel

Depends on / 依赖: IsOrthogonal, LinearEquiv, LinearEquiv.mul_apply, LinearMap, LinearMap.flip_apply, P.pairing, commute_iff_eq, flip_apply, map_smul, map_sub, mul_apply, pairing, reflection_apply, replace, root_coroot_eq_pairing, sub_zero, zero_smul
-/
lemma isOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [commute_iff_eq]
  ext
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  simp only [LinearEquiv.mul_apply, reflection_apply, LinearMap.flip_apply, map_sub,
    map_smul, root_coroot_eq_pairing, h, zero_smul, sub_zero]
  abel

variable {P i j}

/--
lemma `IsOrthogonal.flip` / 引理 `IsOrthogonal.flip`

English:
lemma IsOrthogonal.flip
  given: (h : IsOrthogonal P i j)
  statement: IsOrthogonal P.flip i j
  proof: ⟨h.2, h.1⟩

中文:
引理 IsOrthogonal.flip
  条件: (h : IsOrthogonal P i j)
  结论: IsOrthogonal P.flip i j
  证明: ⟨h.2, h.1⟩
-/
lemma IsOrthogonal.flip (h : IsOrthogonal P i j) : IsOrthogonal P.flip i j := ⟨h.2, h.1⟩

/--
lemma `IsOrthogonal.symm` / 引理 `IsOrthogonal.symm`

English:
lemma IsOrthogonal.symm
  given: (h : IsOrthogonal P i j)
  statement: IsOrthogonal P j i
  proof: ⟨h.2, h.1⟩

中文:
引理 IsOrthogonal.symm
  条件: (h : IsOrthogonal P i j)
  结论: IsOrthogonal P j i
  证明: ⟨h.2, h.1⟩
-/
lemma IsOrthogonal.symm (h : IsOrthogonal P i j) : IsOrthogonal P j i := ⟨h.2, h.1⟩

/--
lemma `IsOrthogonal.reflection_apply_left` / 引理 `IsOrthogonal.reflection_apply_left`

English:
lemma IsOrthogonal.reflection_apply_left
  given: (h : IsOrthogonal P i j)
  proof: by
  simp [reflection_apply, h.1]

中文:
引理 IsOrthogonal.reflection_apply_left
  条件: (h : IsOrthogonal P i j)
  证明: by
  simp [reflection_apply, h.1]

Depends on / 依赖: reflection_apply
-/
lemma IsOrthogonal.reflection_apply_left (h : IsOrthogonal P i j) :
    P.reflection j (P.root i) = P.root i := by
  simp [reflection_apply, h.1]

/--
lemma `IsOrthogonal.reflection_apply_right` / 引理 `IsOrthogonal.reflection_apply_right`

English:
lemma IsOrthogonal.reflection_apply_right
  given: (h : IsOrthogonal P j i)
  proof: h.symm.reflection_apply_left

中文:
引理 IsOrthogonal.reflection_apply_right
  条件: (h : IsOrthogonal P j i)
  证明: h.symm.reflection_apply_left

Depends on / 依赖: h.symm.reflection_apply_left, reflection_apply_left
-/
lemma IsOrthogonal.reflection_apply_right (h : IsOrthogonal P j i) :
    P.reflection j (P.root i) = P.root i :=
  h.symm.reflection_apply_left

/--
lemma `IsOrthogonal.coreflection_apply_left` / 引理 `IsOrthogonal.coreflection_apply_left`

English:
lemma IsOrthogonal.coreflection_apply_left
  given: (h : IsOrthogonal P i j)
  proof: h.flip.reflection_apply_left

中文:
引理 IsOrthogonal.coreflection_apply_left
  条件: (h : IsOrthogonal P i j)
  证明: h.flip.reflection_apply_left

Depends on / 依赖: h.flip.reflection_apply_left, reflection_apply_left
-/
lemma IsOrthogonal.coreflection_apply_left (h : IsOrthogonal P i j) :
    P.coreflection j (P.coroot i) = P.coroot i :=
  h.flip.reflection_apply_left

/--
lemma `IsOrthogonal.coreflection_apply_right` / 引理 `IsOrthogonal.coreflection_apply_right`

English:
lemma IsOrthogonal.coreflection_apply_right
  given: (h : IsOrthogonal P j i)
  proof: h.flip.reflection_apply_right

中文:
引理 IsOrthogonal.coreflection_apply_right
  条件: (h : IsOrthogonal P j i)
  证明: h.flip.reflection_apply_right

Depends on / 依赖: h.flip.reflection_apply_right, reflection_apply_right
-/
lemma IsOrthogonal.coreflection_apply_right (h : IsOrthogonal P j i) :
    P.coreflection j (P.coroot i) = P.coroot i :=
  h.flip.reflection_apply_right

/--
lemma `isFixedPt_reflection_of_isOrthogonal` / 引理 `isFixedPt_reflection_of_isOrthogonal`

English:
lemma isFixedPt_reflection_of_isOrthogonal
  statement: {s : Set ι} (hj : forall i in s, P.IsOrthogonal j i)
  proof: by
  rw [IsFixedPt]
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero]
  | add u v hu hv hu' hv' => rw [map_add, hu', hv']
  | smul t u hu hu' => rw [map_smul, hu']
  | mem u hu =>
      obtain ⟨i, his, rfl⟩ := hu
exact IsOrthogonal.reflection_apply_right hj i his

中文:
引理 isFixedPt_reflection_of_isOrthogonal
  结论: {s : 集合 ι} (hj : 对任意 i in s, P.IsOrthogonal j i)
  证明: by
  rw [IsFixedPt]
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero]
  | add u v hu hv hu' hv' => rw [map_add, hu', hv']
  | smul t u hu hu' => rw [map_smul, hu']
  | mem u hu =>
      obtain ⟨i, his, rfl⟩ := hu
exact IsOrthogonal.reflection_apply_right hj i his

Depends on / 依赖: IsFixedPt, IsOrthogonal, IsOrthogonal.reflection_apply_right, Submodule, Submodule.span_induction, map_add, map_smul, map_zero, reflection_apply_right, span_induction
-/
lemma isFixedPt_reflection_of_isOrthogonal {s : Set ι} (hj : forall i in s, P.IsOrthogonal j i)
    {x : M} (hx : x in span R (P.root '' s)) :
    IsFixedPt (P.reflection j) x := by
  rw [IsFixedPt]
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero]
  | add u v hu hv hu' hv' => rw [map_add, hu', hv']
  | smul t u hu hu' => rw [map_smul, hu']
  | mem u hu =>
      obtain ⟨i, his, rfl⟩ := hu
exact IsOrthogonal.reflection_apply_right hj i his

/--
lemma `reflectionPerm_eq_of_pairing_eq_zero` / 引理 `reflectionPerm_eq_of_pairing_eq_zero`

English:
lemma reflectionPerm_eq_of_pairing_eq_zero
  given: (h : P.pairing j i = 0)
  proof: P.root.injective by simp [reflection_apply, h]

中文:
引理 reflectionPerm_eq_of_pairing_eq_zero
  条件: (h : P.pairing j i = 0)
  证明: P.root.injective by simp [reflection_apply, h]

Depends on / 依赖: P.root.injective, injective, reflection_apply
-/
lemma reflectionPerm_eq_of_pairing_eq_zero (h : P.pairing j i = 0) :
    P.reflectionPerm i j = j :=
P.root.injective by simp [reflection_apply, h]

/--
lemma `reflectionPerm_eq_of_pairing_eq_zero'` / 引理 `reflectionPerm_eq_of_pairing_eq_zero'`

English:
lemma reflectionPerm_eq_of_pairing_eq_zero'
  given: (h : P.pairing i j = 0)
  proof: P.flip.reflectionPerm_eq_of_pairing_eq_zero h

中文:
引理 reflectionPerm_eq_of_pairing_eq_zero'
  条件: (h : P.pairing i j = 0)
  证明: P.flip.reflectionPerm_eq_of_pairing_eq_zero h

Depends on / 依赖: P.flip.reflectionPerm_eq_of_pairing_eq_zero, reflectionPerm_eq_of_pairing_eq_zero
-/
lemma reflectionPerm_eq_of_pairing_eq_zero' (h : P.pairing i j = 0) :
    P.reflectionPerm i j = j :=
  P.flip.reflectionPerm_eq_of_pairing_eq_zero h

/--
lemma `reflectionPerm_eq_iff_smul_root` / 引理 `reflectionPerm_eq_iff_smul_root`

English:
lemma reflectionPerm_eq_iff_smul_root
  proof: ⟨fun h => by simpa [h] using P.reflectionPerm_root i j,
fun h => P.root.injective by simp [reflection_apply, h]⟩

中文:
引理 reflectionPerm_eq_iff_smul_root
  证明: ⟨fun h => by simpa [h] using P.reflectionPerm_root i j,
fun h => P.root.injective by simp [reflection_apply, h]⟩

Depends on / 依赖: P.reflectionPerm_root, P.root.injective, injective, reflectionPerm_root, reflection_apply
-/
lemma reflectionPerm_eq_iff_smul_root :
    P.reflectionPerm i j = j ↔ P.pairing j i • P.root i = 0 :=
  ⟨fun h => by simpa [h] using P.reflectionPerm_root i j,
fun h => P.root.injective by simp [reflection_apply, h]⟩

/--
lemma `reflectionPerm_eq_iff_smul_coroot` / 引理 `reflectionPerm_eq_iff_smul_coroot`

English:
lemma reflectionPerm_eq_iff_smul_coroot
  proof: P.flip.reflectionPerm_eq_iff_smul_root

中文:
引理 reflectionPerm_eq_iff_smul_coroot
  证明: P.flip.reflectionPerm_eq_iff_smul_root

Depends on / 依赖: P.flip.reflectionPerm_eq_iff_smul_root, reflectionPerm_eq_iff_smul_root
-/
lemma reflectionPerm_eq_iff_smul_coroot :
    P.reflectionPerm i j = j ↔ P.pairing i j • P.coroot i = 0 :=
  P.flip.reflectionPerm_eq_iff_smul_root

/--
lemma `pairing_eq_zero_iff` / 引理 `pairing_eq_zero_iff`

English:
lemma pairing_eq_zero_iff
  given: [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M]
  proof: by
  suffices forall {i j : ι}, P.pairing i j = 0 -> P.pairing j i = 0 from ⟨this, this⟩
  intro i j h
  simpa [P.ne_zero i, reflectionPerm_eq_iff_smul_root] using
    P.reflectionPerm_eq_of_pairing_eq_zero' h

中文:
引理 pairing_eq_zero_iff
  条件: [NeZero (2 : R)] [是整环 R] [模.是无挠 R M]
  证明: by
  suffices forall {i j : ι}, P.pairing i j = 0 -> P.pairing j i = 0 from ⟨this, this⟩
  intro i j h
  simpa [P.ne_zero i, reflectionPerm_eq_iff_smul_root] using
    P.reflectionPerm_eq_of_pairing_eq_zero' h

Depends on / 依赖: P.ne_zero, P.pairing, P.reflectionPerm_eq_of_pairing_eq_zero, ne_zero, pairing, reflectionPerm_eq_iff_smul_root, reflectionPerm_eq_of_pairing_eq_zero
-/
lemma pairing_eq_zero_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] :
    P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  suffices forall {i j : ι}, P.pairing i j = 0 -> P.pairing j i = 0 from ⟨this, this⟩
  intro i j h
  simpa [P.ne_zero i, reflectionPerm_eq_iff_smul_root] using
    P.reflectionPerm_eq_of_pairing_eq_zero' h

/--
lemma `pairing_eq_zero_iff'` / 引理 `pairing_eq_zero_iff'`

English:
lemma pairing_eq_zero_iff'
  given: [NeZero (2 : R)] [IsDomain R]
  proof: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  exact pairing_eq_zero_iff

中文:
引理 pairing_eq_zero_iff'
  条件: [NeZero (2 : R)] [是整环 R]
  证明: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  exact pairing_eq_zero_iff

Depends on / 依赖: IsReflexive, P.toLinearMap, of_isPerfPair, pairing_eq_zero_iff, toLinearMap
-/
lemma pairing_eq_zero_iff' [NeZero (2 : R)] [IsDomain R] :
    P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  exact pairing_eq_zero_iff

/--
lemma `coxeterWeight_zero_iff_isOrthogonal` / 引理 `coxeterWeight_zero_iff_isOrthogonal`

English:
lemma coxeterWeight_zero_iff_isOrthogonal
  given: [NeZero (2 : R)] [IsDomain R]
  proof: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [coxeterWeight, IsOrthogonal, P.pairing_eq_zero_iff (i := i) (j := j)]

中文:
引理 coxeterWeight_zero_iff_isOrthogonal
  条件: [NeZero (2 : R)] [是整环 R]
  证明: by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [coxeterWeight, IsOrthogonal, P.pairing_eq_zero_iff (i := i) (j := j)]

Depends on / 依赖: IsOrthogonal, IsReflexive, P.pairing_eq_zero_iff, P.toLinearMap, coxeterWeight, of_isPerfPair, pairing_eq_zero_iff, toLinearMap
-/
lemma coxeterWeight_zero_iff_isOrthogonal [NeZero (2 : R)] [IsDomain R] :
    P.coxeterWeight i j = 0 ↔ P.IsOrthogonal i j := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [coxeterWeight, IsOrthogonal, P.pairing_eq_zero_iff (i := i) (j := j)]

/--
lemma `isOrthogonal_iff_pairing_eq_zero` / 引理 `isOrthogonal_iff_pairing_eq_zero`

English:
lemma isOrthogonal_iff_pairing_eq_zero
  given: [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M]
  proof: ⟨fun h => h.1, fun h => ⟨h, pairing_eq_zero_iff.mp h⟩⟩

中文:
引理 isOrthogonal_iff_pairing_eq_zero
  条件: [NeZero (2 : R)] [是整环 R] [模.是无挠 R M]
  证明: ⟨fun h => h.1, fun h => ⟨h, pairing_eq_zero_iff.mp h⟩⟩

Depends on / 依赖: pairing_eq_zero_iff, pairing_eq_zero_iff.mp
-/
lemma isOrthogonal_iff_pairing_eq_zero [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] :
    P.IsOrthogonal i j ↔ P.pairing i j = 0 :=
  ⟨fun h => h.1, fun h => ⟨h, pairing_eq_zero_iff.mp h⟩⟩

/--
lemma `isFixedPt_reflectionPerm_iff` / 引理 `isFixedPt_reflectionPerm_iff`

English:
lemma isFixedPt_reflectionPerm_iff
  given: [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M]
  proof: by
  simp [P.ne_zero i, pairing_eq_zero_iff, IsFixedPt, reflectionPerm_eq_iff_smul_root]

中文:
引理 isFixedPt_reflectionPerm_iff
  条件: [NeZero (2 : R)] [是整环 R] [模.是无挠 R M]
  证明: by
  simp [P.ne_zero i, pairing_eq_zero_iff, IsFixedPt, reflectionPerm_eq_iff_smul_root]

Depends on / 依赖: IsFixedPt, P.ne_zero, ne_zero, pairing_eq_zero_iff, reflectionPerm_eq_iff_smul_root
-/
lemma isFixedPt_reflectionPerm_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] :
    IsFixedPt (P.reflectionPerm i) j ↔ P.pairing i j = 0 := by
  simp [P.ne_zero i, pairing_eq_zero_iff, IsFixedPt, reflectionPerm_eq_iff_smul_root]

section Map

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂)
  body: (f.symm.trans P.toPerfPair).trans g.symm.dualMap
  isPerfPair_toLinearMap := by
    have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
    have : IsReflexive R N₂ := equiv g
    infer_instance
  root := (e.symm.toEmbedding.trans P.root).trans f.toEmbedding
  coroot := (e.symm.toEmbedding.trans P.coroot).trans g.toEmbedding
  root_coroot_two i := by simp
reflectionPerm i := e.symm.trans (P.reflectionPerm (e.symm i)).trans e
  reflectionPerm_root i j := by simp [reflection_apply]
  reflectionPerm_coroot i j := by simp [coreflection_apply]

中文:
定义 map
  签名: (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂)
  定义体: (f.symm.trans P.toPerfPair).trans g.symm.dualMap
  isPerfPair_toLinearMap := by
    have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
    have : IsReflexive R N₂ := equiv g
    infer_instance
  root := (e.symm.toEmbedding.trans P.root).trans f.toEmbedding
  coroot := (e.symm.toEmbedding.trans P.coroot).trans g.toEmbedding
  root_coroot_two i := by simp
reflectionPerm i := e.symm.trans (P.reflectionPerm (e.symm i)).trans e
  reflectionPerm_root i j := by simp [reflection_apply]
  reflectionPerm_coroot i j := by simp [coreflection_apply]
-/
protected def map (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂) :
    RootPairing ι₂ R M₂ N₂ where
  __ := (f.symm.trans P.toPerfPair).trans g.symm.dualMap
  isPerfPair_toLinearMap := by
    have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
    have : IsReflexive R N₂ := equiv g
    infer_instance
  root := (e.symm.toEmbedding.trans P.root).trans f.toEmbedding
  coroot := (e.symm.toEmbedding.trans P.coroot).trans g.toEmbedding
  root_coroot_two i := by simp
reflectionPerm i := e.symm.trans (P.reflectionPerm (e.symm i)).trans e
  reflectionPerm_root i j := by simp [reflection_apply]
  reflectionPerm_coroot i j := by simp [coreflection_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsRootSystem]
  signature: (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂)
  body: by simp [RootPairing.map, Embedding.coe_trans, range_comp]
  span_coroot_eq_top := by simp [Embedding.coe_trans, range_comp, RootPairing.map]

中文:
实例 [P.是RootSystem]
  签名: (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂)
  定义体: by simp [RootPairing.map, Embedding.coe_trans, range_comp]
  span_coroot_eq_top := by simp [Embedding.coe_trans, range_comp, RootPairing.map]

Depends on / 依赖: Embedding, Embedding.coe_trans, RootPairing, RootPairing.map, coe_trans, range_comp, span_coroot_eq_top
-/
instance [P.IsRootSystem] (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂) :
    (P.map e f g).IsRootSystem where
  span_root_eq_top := by simp [RootPairing.map, Embedding.coe_trans, range_comp]
  span_coroot_eq_top := by simp [Embedding.coe_trans, range_comp, RootPairing.map]

end Map

end RootPairing
