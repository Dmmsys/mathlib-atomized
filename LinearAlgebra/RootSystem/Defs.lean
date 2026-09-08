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

/-- Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with indexing set `ι`
is the data of an `ι`-indexed subset of `M` ("the roots"), an `ι`-indexed subset of `N`
("the coroots"), and an `ι`-indexed set of permutations of `ι`, such that each root-coroot pair
evaluates to `2`, and the permutation attached to each element of `ι` is compatible with the
reflections on the corresponding roots and coroots.

It exists to allow for a convenient unification of the theories of root systems and root data. -/
/-
**RootPairing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 →   (R : Type u_2) →     (M : Type u_3) →       (N : Type u_4) → 
        [inst : CommRing R] →           [inst_1 : AddCommGroup M] →             
[_root_.Module R M] →               [inst_3 : AddCommGroup N] → [_root_.Module R
 N] → Type (max (max (max u_1 u_2) u_3) u_4)
参数：R : Type u_2；M : Type u_3；N : Type u_4；max (max (max u_1 u_2) u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with indexing
 set `ι`
is the data of an `ι`-indexed subset of `M` ("the roots"), an `ι`-indexed subset
 of `N`
("the coroots"), and an `ι`-indexed set of permutations of `ι`, such that each r
oot-coroot pair
evaluates to `2`, and the permutation attached to each element of `ι` is compati
ble with the
reflections on the corresponding roots and coroots.

It exists to allow for a convenient unification of the theories of root systems 
and root data.
-/
structure RootPairing extends M →ₗ[R] N →ₗ[R] R where
  [isPerfPair_toLinearMap : toLinearMap.IsPerfPair]
  /-- A parametrized family of vectors, called roots. -/
  root : ι ↪ M
  /-- A parametrized family of dual vectors, called coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLinearMap (root i) (coroot i) = 2
  /-- A parametrized family of permutations, induced by reflections. This corresponds to the
  classical requirement that the symmetry attached to each root (later defined in
  `RootPairing.reflection`) leave the whole set of roots stable: as explained above, we
  formalize this stability by fixing the image of the roots through each reflection (whence the
  permutation); and similarly for coroots. -/
  reflectionPerm : ι → (ι ≃ ι)
  reflectionPerm_root : ∀ i j,
    root j - toLinearMap (root j) (coroot i) • root i = root (reflectionPerm i j)
  reflectionPerm_coroot : ∀ i j,
    coroot j - toLinearMap (root i) (coroot j) • coroot i = coroot (reflectionPerm i j)

attribute [instance] RootPairing.isPerfPair_toLinearMap

/-- A root datum is a root pairing with coefficients in the integers and for which the root and
coroot spaces are finitely-generated free Abelian groups.

Note that the latter assumptions `[Finite ℤ X₁] [Finite ℤ X₂]` should be supplied as mixins, and
that freeness follows automatically since two finitely-generated Abelian groups in perfect pairing
are necessarily free. Moreover Lean knows this, e.g., via `PerfectPairing.reflexive_left`,
`IsReflexive.to_isTorsionFree`, `Module.free_of_finite_type_torsion_free'`. -/
/-
**RootDatum** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂]
参数：X₁ X₂ : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A root datum is a root pairing with coefficients in the integers and for which t
he root and
coroot spaces are finitely-generated free Abelian groups.

Note that the latter assumptions `[Finite ℤ X₁] [Finite ℤ X₂]` should be supplie
d as mixins, and
that freeness follows automatically since two finitely-generated Abelian groups 
in perfect pairing
are necessarily free. Moreover Lean knows this, e.g., via `PerfectPairing.reflex
ive_left`,
`IsReflexive.to_isTorsionFree`, `Module.free_of_finite_type_torsion_free'`.
-/
abbrev RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂] := RootPairing ι ℤ X₁ X₂

namespace RootPairing

variable {ι R M N}
variable (P : RootPairing ι R M N) (i j : ι)

/-- A root system is a root pairing for which the roots and coroots span their ambient modules. -/
@[wikidata Q534131]
/-
**RootPairing.IsRootSystem** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A root system is a root pairing for which the roots and coroots span their ambie
nt modules.
-/
class IsRootSystem : Prop where
  span_root_eq_top : span R (range P.root) = ⊤
  span_coroot_eq_top : span R (range P.coroot) = ⊤

attribute [simp] IsRootSystem.span_root_eq_top
attribute [simp] IsRootSystem.span_coroot_eq_top

/-- If we interchange the roles of `M` and `N`, we still have a root pairing. -/
@[simps! root coroot reflectionPerm, simps toLinearMap]
/-
**RootPairing.flip** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → RootPairing ι R N M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.root_coroot_two`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u
_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _ro
ot_.Module R M] […
· 使用定理 `RootPairing.reflectionPerm_coroot`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `RootPairing.reflectionPerm_root`：∀ {ι : Type u_1} {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 :
 _root_.Module R M] […

--- 原说明 ---
If we interchange the roles of `M` and `N`, we still have a root pairing.
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
/-
**RootPairing.flip_flip** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：flip_flip : P.flip.flip = P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma flip_flip : P.flip.flip = P :=
  rfl

variable (ι R M N) in
/-- `RootPairing.flip` as an equivalence. -/
/-
**RootPairing.flipEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：(ι : Type u_1) →   (R : Type u_2) →     (M : Type u_3) →       (N : Type u
_4) →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R N M ≃ RootPairing ι R M N
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RootPairing.flip` as an equivalence.
-/
@[simps] def flipEquiv : RootPairing ι R N M ≃ RootPairing ι R M N where
  toFun P := P.flip
  invFun P := P.flip
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsRootSystem] : P.flip.IsRootSystem where
  span_root_eq_top := IsRootSystem.span_coroot_eq_top
  span_coroot_eq_top := IsRootSystem.span_root_eq_top
/-
**RootPairing.ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NeZero.ne'`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], 0 ≠
 n
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RootPairing.root_coroot_two`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u
_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _ro
ot_.Module R M] […
-/
lemma ne_zero [NeZero (2 : R)] : (P.root i : M) ≠ 0 :=
  fun h ↦ NeZero.ne' (2 : R) <| by simpa [h] using P.root_coroot_two i
/-
**RootPairing.ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：ne_zero' [NeZero (2 : R)] : (P.coroot i : N) != 0
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
-/
lemma ne_zero' [NeZero (2 : R)] : (P.coroot i : N) ≠ 0 :=
  P.flip.ne_zero i
/-
**RootPairing.zero_notMem_range_root** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：zero_notMem_range_root [NeZero (2 : R)] : 0 ∉ range P.root
参数：2 : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
-/
lemma zero_notMem_range_root [NeZero (2 : R)] : 0 ∉ range P.root := by
  simpa only [mem_range, not_exists] using fun i ↦ P.ne_zero i
/-
**RootPairing.zero_notMem_range_coroot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：zero_notMem_range_coroot [NeZero (2 : R)] : 0 ∉ range P.coroot
参数：2 : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.zero_notMem_range_root`：zero_notMem_range_root [NeZero (2 : 
R)] : 0 ∉ range P.root
-/
lemma zero_notMem_range_coroot [NeZero (2 : R)] : 0 ∉ range P.coroot :=
  P.flip.zero_notMem_range_root
/-
**RootPairing.exists_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：exists_ne_zero [Nonempty ι] [NeZero (2 : R)] : exists i, P.root i != 0
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
-/
lemma exists_ne_zero [Nonempty ι] [NeZero (2 : R)] : ∃ i, P.root i ≠ 0 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact ⟨i, P.ne_zero i⟩
/-
**RootPairing.exists_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：exists_ne_zero' [Nonempty ι] [NeZero (2 : R)] : exists i, P.coroot i != 0
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.exists_ne_zero`：exists_ne_zero [Nonempty ι] [NeZero (2 : R)]
 : exists i, P.root i != 0
-/
lemma exists_ne_zero' [Nonempty ι] [NeZero (2 : R)] : ∃ i, P.coroot i ≠ 0 :=
  P.flip.exists_ne_zero

include P in
/-
**RootPairing.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [Nonempty ι]
 [NeZero 2], Nontrivial M
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.exists_ne_zero`：exists_ne_zero [Nonempty ι] [NeZero (2 : R)]
 : exists i, P.root i != 0
-/
protected lemma nontrivial [Nonempty ι] [NeZero (2 : R)] : Nontrivial M := by
  obtain ⟨i, hi⟩ := P.exists_ne_zero
  exact ⟨P.root i, 0, hi⟩

include P in
/-
**RootPairing.nontrivial'** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [Nonempty ι]
 [NeZero 2], Nontrivial N
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.nontrivial`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {
N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.M
odule R M] […
-/
protected lemma nontrivial' [Nonempty ι] [NeZero (2 : R)] : Nontrivial N :=
  P.flip.nontrivial

/-- Roots written as functionals on the coweight space. -/
/-
**RootPairing.root'** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：root' (i : ι) : Dual R N
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Roots written as functionals on the coweight space.
-/
abbrev root' (i : ι) : Dual R N := P.toLinearMap (P.root i)

/-- Coroots written as functionals on the weight space. -/
/-
**RootPairing.coroot'** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：coroot' (i : ι) : Dual R M
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coroots written as functionals on the weight space.
-/
abbrev coroot' (i : ι) : Dual R M := P.toLinearMap.flip (P.coroot i)

/-- This is the pairing between roots and coroots. -/
/-
**RootPairing.pairing** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：pairing : R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the pairing between roots and coroots.
-/
def pairing : R := P.root' i (P.coroot j)
/-
**RootPairing.pairing_flip** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (i j : ι), P
.flip.pairing i j = P.pairing j i
参数：P : RootPairing ι R M N；i j : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pairing_flip : P.flip.pairing i j = P.pairing j i := rfl

@[simp]
/-
**RootPairing.root_coroot_eq_pairing** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：root_coroot_eq_pairing : P.toLinearMap (P.root i) (P.coroot j) = P.pairing
 i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma root_coroot_eq_pairing : P.toLinearMap (P.root i) (P.coroot j) = P.pairing i j :=
  rfl

@[simp]
/-
**RootPairing.root'_coroot_eq_pairing** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (i j : ι), (
P.root' i) (P.coroot j) = P.pairing i j
参数：P : RootPairing ι R M N；i j : ι；P.root' i；P.coroot j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma root'_coroot_eq_pairing : P.root' i (P.coroot j) = P.pairing i j :=
  rfl

@[simp]
/-
**RootPairing.root_coroot'_eq_pairing** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (i j : ι), (
P.coroot' i) (P.root j) = P.pairing j i
参数：P : RootPairing ι R M N；i j : ι；P.coroot' i；P.root j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma root_coroot'_eq_pairing : P.coroot' i (P.root j) = P.pairing j i :=
  rfl
/-
**RootPairing.coroot_root_eq_pairing** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coroot_root_eq_pairing : P.toLinearMap.flip (P.coroot i) (P.root j) = P.pa
iring j i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coroot_root_eq_pairing : P.toLinearMap.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp

@[simp]
/-
**RootPairing.pairing_same** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_same : P.pairing i i = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.root_coroot_two`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u
_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _ro
ot_.Module R M] […
-/
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i

variable {P} in
/-
**RootPairing.pairing_eq_add_of_root_eq_add** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng`。
形式化陈述：pairing_eq_add_of_root_eq_add {i j k l : ι} (h : P.root k = P.root i + P.r
oot j) : P.pairing k l = P.pairing i l + P.pairing j l
参数：h : P.root k = P.root i + P.root j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_eq_add_of_root_eq_add {i j k l : ι} (h : P.root k = P.root i + P.root j) :
    P.pairing k l = P.pairing i l + P.pairing j l := by
  simp only [← root_coroot_eq_pairing, h, map_add, LinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
variable {P} in
/-
**RootPairing.pairing_eq_add_of_root_eq_smul_add_smul** 是 Mathlib 中的一个引理，位于命名空间 
`RootPairing`。
形式化陈述：pairing_eq_add_of_root_eq_smul_add_smul {i j k l : ι} {x y : R} (h : P.roo
t k = x • P.root i + y • P.root l) : P.pairing k j = x • P.pairing i j + y • P.p
airing l j
参数：h : P.root k = x • P.root i + y • P.root l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_eq_add_of_root_eq_smul_add_smul
    {i j k l : ι} {x y : R} (h : P.root k = x • P.root i + y • P.root l) :
    P.pairing k j = x • P.pairing i j + y • P.pairing l j := by
  simp only [← root_coroot_eq_pairing, h, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
/-
**RootPairing.coroot_root_two** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coroot_root_two : P.toLinearMap.flip (P.coroot i) (P.root i) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coroot_root_two :
    P.toLinearMap.flip (P.coroot i) (P.root i) = 2 := by
  simp

/-- The reflection associated to a root. -/
/-
**RootPairing.reflection** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：reflection : M ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reflection associated to a root.
-/
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)

@[simp]
/-
**RootPairing.root_reflectionPerm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：root_reflectionPerm (j : ι) : P.root (P.reflectionPerm i j) = (P.reflectio
n i) (P.root j)
参数：j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.reflectionPerm_root`：∀ {ι : Type u_1} {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 :
 _root_.Module R M] […
-/
lemma root_reflectionPerm (j : ι) :
    P.root (P.reflectionPerm i j) = (P.reflection i) (P.root j) :=
  (P.reflectionPerm_root i j).symm
/-
**RootPairing.mapsTo_reflection_root** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：mapsTo_reflection_root : MapsTo (P.reflection i) (range P.root) (range P.r
oot)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
-/
theorem mapsTo_reflection_root :
    MapsTo (P.reflection i) (range P.root) (range P.root) := by
  rintro - ⟨j, rfl⟩
  exact P.root_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)
/-
**RootPairing.reflection_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_apply (x : M) : P.reflection i x = x - (P.coroot' i x) • P.root
 i
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reflection_apply (x : M) :
    P.reflection i x = x - (P.coroot' i x) • P.root i :=
  rfl
/-
**RootPairing.reflection_apply_root** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_apply_root : P.reflection i (P.root j) = P.root j - (P.pairing 
j i) • P.root i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reflection_apply_root :
    P.reflection i (P.root j) = P.root j - (P.pairing j i) • P.root i :=
  rfl

@[simp]
/-
**RootPairing.reflection_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_apply_self : P.reflection i (P.root i) = - P.root i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.reflection_apply_self`：reflection_apply_self (h : f x = 2) : refl
ection h x = -x
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RootPairing.coroot_root_two`：coroot_root_two : P.toLinearMap.flip (P.cor
oot i) (P.root i) = 2
-/
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)

@[simp]
/-
**RootPairing.reflection_same** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_same (x : M) : P.reflection i (P.reflection i x) = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.involutive_reflection`：involutive_reflection (h : f x = 2) : Invo
lutive (reflection h)
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RootPairing.coroot_root_two`：coroot_root_two : P.toLinearMap.flip (P.cor
oot i) (P.root i) = 2
-/
lemma reflection_same (x : M) :
    P.reflection i (P.reflection i x) = x :=
  Module.involutive_reflection (P.coroot_root_two i) x

@[simp]
/-
**RootPairing.reflection_inv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_inv : (P.reflection i)⁻¹ = P.reflection i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reflection_inv :
    (P.reflection i)⁻¹ = P.reflection i :=
  rfl

@[simp]
/-
**RootPairing.reflection_sq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_sq : P.reflection i ^ 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
-/
lemma reflection_sq : P.reflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl

@[simp]
/-
**RootPairing.reflectionPerm_sq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflectionPerm_sq : P.reflectionPerm i ^ 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_same`：reflection_same (x : M) : P.reflection i (P
.reflection i x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflectionPerm_sq : P.reflectionPerm i ^ 2 = 1 := by
  ext j
  apply P.root.injective
  simp only [sq, Equiv.Perm.mul_apply, root_reflectionPerm, reflection_same, Equiv.Perm.one_apply]

@[simp]
/-
**RootPairing.reflectionPerm_inv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflectionPerm_inv : (P.reflectionPerm i)⁻¹ = P.reflectionPerm i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用引理 `RootPairing.reflectionPerm_sq`：reflectionPerm_sq : P.reflectionPerm i ^ 
2 = 1
-/
lemma reflectionPerm_inv : (P.reflectionPerm i)⁻¹ = P.reflectionPerm i :=
  (mul_eq_one_iff_eq_inv.mp <| P.reflectionPerm_sq i).symm

@[simp]
/-
**RootPairing.reflectionPerm_self** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflectionPerm_self : P.reflectionPerm i (P.reflectionPerm i j) = j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_same`：reflection_same (x : M) : P.reflection i (P
.reflection i x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflectionPerm_self : P.reflectionPerm i (P.reflectionPerm i j) = j := by
  apply P.root.injective
  simp only [root_reflectionPerm, reflection_same]
/-
**RootPairing.reflectionPerm_involutive** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflectionPerm_involutive : Involutive (P.reflectionPerm i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.involutive_iff_iter_2_eq_id`：involutive_iff_iter_2_eq_id {α} {f
 : α -> α} : Involutive f ↔ f^[2] = id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用引理 `RootPairing.reflectionPerm_self`：reflectionPerm_self : P.reflectionPerm 
i (P.reflectionPerm i j) = j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflectionPerm_involutive : Involutive (P.reflectionPerm i) :=
  involutive_iff_iter_2_eq_id.mpr (by ext; simp)

@[simp]
/-
**RootPairing.reflectionPerm_symm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflectionPerm_symm : (P.reflectionPerm i).symm = P.reflectionPerm i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.symm_eq_self_of_involutive`：symm_eq_self_of_involuti
ve (f : Equiv.Perm α) (h : Involutive f) : f.symm = f
· 使用引理 `RootPairing.reflectionPerm_involutive`：reflectionPerm_involutive : Invol
utive (P.reflectionPerm i)
-/
lemma reflectionPerm_symm : (P.reflectionPerm i).symm = P.reflectionPerm i :=
  Involutive.symm_eq_self_of_involutive (P.reflectionPerm i) <| P.reflectionPerm_involutive i
/-
**RootPairing.bijOn_reflection_root** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：bijOn_reflection_root : BijOn (P.reflection i) (range P.root) (range P.roo
t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.bijOn_reflection_of_mapsTo`：bijOn_reflection_of_mapsTo {Φ : Set M
} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ) : BijOn (reflection h) Φ Φ
· 使用定理 `RootPairing.mapsTo_reflection_root`：mapsTo_reflection_root : MapsTo (P.r
eflection i) (range P.root) (range P.root)
-/
lemma bijOn_reflection_root :
    BijOn (P.reflection i) (range P.root) (range P.root) :=
  Module.bijOn_reflection_of_mapsTo _ <| P.mapsTo_reflection_root i

@[simp]
/-
**RootPairing.reflection_image_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_image_eq : P.reflection i '' (range P.root) = range P.root
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用引理 `RootPairing.bijOn_reflection_root`：bijOn_reflection_root : BijOn (P.refl
ection i) (range P.root) (range P.root)
-/
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  (P.bijOn_reflection_root i).image_eq

/-- The reflection associated to a coroot. -/
/-
**RootPairing.coreflection** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：coreflection : N ≃ₗ[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.root_coroot_two`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u
_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _ro
ot_.Module R M] […

--- 原说明 ---
The reflection associated to a coroot.
-/
def coreflection : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)

@[simp]
/-
**RootPairing.coroot_reflectionPerm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coroot_reflectionPerm (j : ι) : P.coroot (P.reflectionPerm i j) = (P.coref
lection i) (P.coroot j)
参数：j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.reflectionPerm_coroot`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
-/
lemma coroot_reflectionPerm (j : ι) :
    P.coroot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j) :=
  (P.reflectionPerm_coroot i j).symm
/-
**RootPairing.mapsTo_coreflection_coroot** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`
。
形式化陈述：mapsTo_coreflection_coroot : MapsTo (P.coreflection i) (range P.coroot) (r
ange P.coroot)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
-/
theorem mapsTo_coreflection_coroot :
    MapsTo (P.coreflection i) (range P.coroot) (range P.coroot) := by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflectionPerm i j ▸ mem_range_self (P.reflectionPerm i j)
/-
**RootPairing.coreflection_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coreflection_apply (f : N) : P.coreflection i f = f - (P.root' i) f • P.co
root i
参数：f : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (P.root' i) f • P.coroot i :=
  rfl
/-
**RootPairing.coreflection_apply_coroot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coreflection_apply_coroot : P.coreflection i (P.coroot j) = P.coroot j - (
P.pairing i j) • P.coroot i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coreflection_apply_coroot :
    P.coreflection i (P.coroot j) = P.coroot j - (P.pairing i j) • P.coroot i :=
  rfl

@[simp]
/-
**RootPairing.coreflection_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coreflection_apply_self : P.coreflection i (P.coroot i) = - P.coroot i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.reflection_apply_self`：reflection_apply_self (h : f x = 2) : refl
ection h x = -x
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RootPairing.coroot_root_two`：coroot_root_two : P.toLinearMap.flip (P.cor
oot i) (P.root i) = 2
-/
lemma coreflection_apply_self :
    P.coreflection i (P.coroot i) = - P.coroot i :=
  Module.reflection_apply_self (P.flip.coroot_root_two i)

@[simp]
/-
**RootPairing.coreflection_same** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coreflection_same (x : N) : P.coreflection i (P.coreflection i x) = x
参数：x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.involutive_reflection`：involutive_reflection (h : f x = 2) : Invo
lutive (reflection h)
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RootPairing.coroot_root_two`：coroot_root_two : P.toLinearMap.flip (P.cor
oot i) (P.root i) = 2
-/
lemma coreflection_same (x : N) :
    P.coreflection i (P.coreflection i x) = x :=
  Module.involutive_reflection (P.flip.coroot_root_two i) x

@[simp]
/-
**RootPairing.coreflection_inv** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coreflection_inv : (P.coreflection i)⁻¹ = P.coreflection i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coreflection_inv :
    (P.coreflection i)⁻¹ = P.coreflection i :=
  rfl

@[simp]
/-
**RootPairing.coreflection_sq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coreflection_sq : P.coreflection i ^ 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
-/
lemma coreflection_sq :
    P.coreflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl
/-
**RootPairing.bijOn_coreflection_coroot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (ran
ge P.coroot)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.bijOn_reflection_root`：bijOn_reflection_root : BijOn (P.refl
ection i) (range P.root) (range P.root)
-/
lemma bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (range P.coroot) :=
  bijOn_reflection_root P.flip i

@[simp]
/-
**RootPairing.coreflection_image_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coreflection_image_eq : P.coreflection i '' (range P.coroot) = range P.cor
oot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用引理 `RootPairing.bijOn_coreflection_coroot`：bijOn_coreflection_coroot : BijOn
 (P.coreflection i) (range P.coroot) (range P.coroot)
-/
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  (P.bijOn_coreflection_coroot i).image_eq
/-
**RootPairing.coreflection_eq_flip_reflection** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：coreflection_eq_flip_reflection : P.coreflection i = P.flip.reflection i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coreflection_eq_flip_reflection :
    P.coreflection i = P.flip.reflection i :=
  rfl
/-
**RootPairing.reflection_reflectionPerm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_reflectionPerm {i j : ι} : P.reflection (P.reflectionPerm j i) 
= P.reflection j * P.reflection i * P.reflection j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₃`：sub_eq_eval₃ [Ring R] [AddCommGro
up M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::ᵣ l₁)
.eval - l₂.eval = l.eval) :…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
（共 68 条，此处仅展示前 30 条）
-/
lemma reflection_reflectionPerm {i j : ι} :
    P.reflection (P.reflectionPerm j i) = P.reflection j * P.reflection i * P.reflection j := by
  ext x; simp [reflection_apply, coreflection_apply]; module
/-
**RootPairing.reflection_dualMap_eq_coreflection** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：reflection_dualMap_eq_coreflection : (P.reflection i).dualMap ∘ₗ P.toLinea
rMap.flip = P.toLinearMap.flip ∘ₗ P.coreflection i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLinearMap.flip = P.toLinearMap.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [map_sub, coreflection_apply, reflection_apply, mul_comm (P.toLinearMap m (P.coroot i))]
/-
**RootPairing.coroot_eq_coreflection_of_root_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：coroot_eq_coreflection_of_root_eq {i j k : ι} (hk : P.root k = P.reflectio
n i (P.root j)) : P.coroot k = P.coreflection i (P.coroot j)
参数：hk : P.root k = P.reflection i (P.root j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
-/
lemma coroot_eq_coreflection_of_root_eq
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) := by
  rw [← P.root_reflectionPerm, EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflectionPerm, hk]
/-
**RootPairing.coroot'_reflectionPerm** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   {i j : ι}, P
.coroot' ((P.reflectionPerm i) j) = P.coroot' j ∘ₗ ↑(P.reflection i)
参数：P : RootPairing ι R M N；(P.reflectionPerm i) j；P.reflection i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coroot'_reflectionPerm {i j : ι} :
    P.coroot' (P.reflectionPerm i j) = P.coroot' j ∘ₗ P.reflection i := by
  ext y
  simp [coreflection_apply_coroot, reflection_apply, map_sub, mul_comm]
/-
**RootPairing.coroot'_reflection** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   {i j : ι} (y
 : M), (P.coroot' j) ((P.reflection i) y) = (P.coroot' ((P.reflectionPerm i) j))
 y
参数：P : RootPairing ι R M N；y : M；P.coroot' j；(P.reflection i) y；P.coroot' ((P.re
flectionPerm i) j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `RootPairing.coroot'_reflectionPerm`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
-/
lemma coroot'_reflection {i j : ι} (y : M) :
    P.coroot' j (P.reflection i y) = P.coroot' (P.reflectionPerm i j) y :=
  (LinearMap.congr_fun P.coroot'_reflectionPerm y).symm
/-
**RootPairing.pairing_reflectionPerm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_reflectionPerm (i j k : ι) : P.pairing j (P.reflectionPerm i k) = 
P.pairing (P.reflectionPerm i j) k
参数：i j k : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_reflectionPerm (i j k : ι) :
    P.pairing j (P.reflectionPerm i k) = P.pairing (P.reflectionPerm i j) k := by
  simp only [pairing, root', coroot_reflectionPerm, root_reflectionPerm]
  simp [coreflection_apply_coroot, reflection_apply_root, mul_comm]

@[simp]
/-
**RootPairing.toPerfPair_conj_reflection** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`
。
形式化陈述：toPerfPair_conj_reflection : P.toPerfPair.conj (P.reflection i) = (P.coref
lection i).toLinearMap.dualMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.apply_symm_toPerfPair_self`：∀ {R : Type u_1} {M : Type u_3} {N
 : Type u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRin
g R]   [inst_3 : _root_.Mo…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toPerfPair_conj_reflection :
    P.toPerfPair.conj (P.reflection i) = (P.coreflection i).toLinearMap.dualMap := by
  ext f n
  simp [reflection_apply, coreflection_apply, mul_comm (f <| P.coroot i)]

@[simp]
/-
**RootPairing.toPerfPair_flip_conj_coreflection** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：toPerfPair_flip_conj_coreflection : P.toLinearMap.flip.toPerfPair.conj (P.
coreflection i) = (P.reflection i).toLinearMap.dualMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.toPerfPair_conj_reflection`：toPerfPair_conj_reflection : P.t
oPerfPair.conj (P.reflection i) = (P.coreflection i).toLinearMap.dualMap
-/
lemma toPerfPair_flip_conj_coreflection :
    P.toLinearMap.flip.toPerfPair.conj (P.coreflection i) = (P.reflection i).toLinearMap.dualMap :=
  P.flip.toPerfPair_conj_reflection i

@[simp]
/-
**RootPairing.pairing_reflectionPerm_self_left** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring`。
形式化陈述：pairing_reflectionPerm_self_left (P : RootPairing ι R M N) (i j : ι) : P.p
airing (P.reflectionPerm i i) j = - P.pairing i j
参数：P : RootPairing ι R M N；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.pairing.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3}
 {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_
.Module R M] […
· 使用定理 `RootPairing.root'.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {
N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.M
odule R M] […
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.reflectionPerm_root`：∀ {ι : Type u_1} {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 :
 _root_.Module R M] […
· 使用定理 `RootPairing.root'_coroot_eq_pairing`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `LinearMap.map_neg₂`：map_neg₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y) : f
 (-x) y = -f x y
-/
lemma pairing_reflectionPerm_self_left (P : RootPairing ι R M N) (i j : ι) :
    P.pairing (P.reflectionPerm i i) j = - P.pairing i j := by
  rw [pairing, root', ← reflectionPerm_root, root'_coroot_eq_pairing, pairing_same, two_smul,
    sub_add_cancel_left, LinearMap.map_neg₂, root'_coroot_eq_pairing]

@[simp]
/-
**RootPairing.pairing_reflectionPerm_self_right** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：pairing_reflectionPerm_self_right (i j : ι) : P.pairing i (P.reflectionPer
m j j) = - P.pairing i j
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.pairing.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3}
 {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_
.Module R M] […
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.reflectionPerm_coroot`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用引理 `RootPairing.root_coroot_eq_pairing`：root_coroot_eq_pairing : P.toLinearM
ap (P.root i) (P.coroot j) = P.pairing i j
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
lemma pairing_reflectionPerm_self_right (i j : ι) :
    P.pairing i (P.reflectionPerm j j) = - P.pairing i j := by
  rw [pairing, ← reflectionPerm_coroot, root_coroot_eq_pairing, pairing_same, two_smul,
    sub_add_cancel_left, map_neg, root_coroot_eq_pairing]

set_option backward.isDefEq.respectTransparency false in
/-- The indexing set of a root pairing carries an involutive negation, corresponding to the negation
of a root / coroot. -/
/-
**RootPairing.indexNeg** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → InvolutiveNeg ι
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indexing set of a root pairing carries an involutive negation, corresponding
 to the negation
of a root / coroot.
-/
@[simps, instance_reducible] def indexNeg : InvolutiveNeg ι where
  neg i := P.reflectionPerm i i
  neg_neg i := by
    apply P.root.injective
    simp only [root_reflectionPerm, reflection_apply, LinearMap.flip_apply, root_coroot_eq_pairing,
      pairing_same, map_sub, coroot_reflectionPerm, coreflection_apply_self, map_neg, neg_smul,
      sub_neg_eq_add, map_smul, smul_add]
    module
/-
**RootPairing.ne_neg** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：ne_neg [NeZero (2 : R)] [IsDomain R] : letI
参数：2 : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
lemma ne_neg [NeZero (2 : R)] [IsDomain R] :
    letI := P.indexNeg
    i ≠ -i := by
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  intro contra
  replace contra : P.root i = -P.root i := by simpa using congr_arg P.root contra
  simp [eq_neg_iff_add_eq_zero, ← two_smul R, NeZero.out, P.ne_zero i] at contra

variable {i j} in
@[simp]
/-
**RootPairing.root_eq_neg_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：root_eq_neg_iff : P.root i = - P.root j ↔ i = P.reflectionPerm j j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma root_eq_neg_iff :
    P.root i = - P.root j ↔ i = P.reflectionPerm j j := by
  refine ⟨fun h ↦ P.root.injective ?_, fun h ↦ by simp [h]⟩
  rw [root_reflectionPerm, reflection_apply_self, h]

variable {i j} in
@[simp]
/-
**RootPairing.coroot_eq_neg_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coroot_eq_neg_iff : P.coroot i = - P.coroot j ↔ i = P.reflectionPerm j j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.root_eq_neg_iff`：root_eq_neg_iff : P.root i = - P.root j ↔ i
 = P.reflectionPerm j j
-/
lemma coroot_eq_neg_iff :
    P.coroot i = - P.coroot j ↔ i = P.reflectionPerm j j :=
  P.flip.root_eq_neg_iff
/-
**RootPairing.neg_mem_range_root_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：neg_mem_range_root_iff {x : M} : -x in range P.root ↔ x in range P.root
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma neg_mem_range_root_iff {x : M} :
    -x ∈ range P.root ↔ x ∈ range P.root := by
  suffices ∀ x : M, -x ∈ range P.root → x ∈ range P.root by
    refine ⟨this x, fun h ↦ ?_⟩
    rw [← neg_neg x] at h
    exact this (-x) h
  intro y ⟨i, hi⟩
  exact ⟨P.reflectionPerm i i, by simp [neg_eq_iff_eq_neg.mpr hi]⟩
/-
**RootPairing.neg_mem_range_coroot_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：neg_mem_range_coroot_iff {x : N} : -x in range P.coroot ↔ x in range P.cor
oot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.neg_mem_range_root_iff`：neg_mem_range_root_iff {x : M} : -x 
in range P.root ↔ x in range P.root
-/
lemma neg_mem_range_coroot_iff {x : N} :
    -x ∈ range P.coroot ↔ x ∈ range P.coroot :=
  P.flip.neg_mem_range_root_iff
/-
**RootPairing.neg_root_mem** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：neg_root_mem : - P.root i in range P.root
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_root_mem :
    - P.root i ∈ range P.root :=
  ⟨P.reflectionPerm i i, by simp⟩
/-
**RootPairing.neg_coroot_mem** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：neg_coroot_mem : - P.coroot i in range P.coroot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.neg_root_mem`：neg_root_mem : - P.root i in range P.root
-/
lemma neg_coroot_mem :
    - P.coroot i ∈ range P.coroot :=
  P.flip.neg_root_mem i

variable {P} in
/-
**RootPairing.smul_coroot_eq_of_root_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing`。
形式化陈述：smul_coroot_eq_of_root_eq_smul [Finite ι] [IsAddTorsionFree N] (i j : ι) (
t : R) (h : P.root j = t • P.root i) : t • P.coroot j = P.coroot i
参数：i j : ι；t : R；h : P.root j = t • P.root i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.congr_arg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用引理 `Module.eq_of_mapsTo_reflection_of_mem`：eq_of_mapsTo_reflection_of_mem [I
sAddTorsionFree M] {Φ : Set M} (hΦ : Φ.Finite) (hfx : f x = 2) (hgy : g y = 2) (
hgx : g x = 2) (hfy : f y =…
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `Module.preReflection_apply`：preReflection_apply : preReflection x f y = 
y - (f y) • x
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `RootPairing.mapsTo_coreflection_coroot`：mapsTo_coreflection_coroot : Map
sTo (P.coreflection i) (range P.coroot) (range P.coroot)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
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
/-
**RootPairing.coroot_eq_smul_coroot_iff** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [Finite ι] [
IsAddTorsionFree M] [IsAddTorsionFree N] {i j : ι} {t : R},   P.coroot i = t • P
.coroot j ↔ P.root j = t • P.root i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.smul_coroot_eq_of_root_eq_smul`：smul_coroot_eq_of_root_eq_sm
ul [Finite ι] [IsAddTorsionFree N] (i j : ι) (t : R) (h : P.root j = t • P.root 
i) : t • P.coroot j = P.coroot i
-/
@[simp] lemma coroot_eq_smul_coroot_iff [Finite ι] [IsAddTorsionFree M] [IsAddTorsionFree N]
    {i j : ι} {t : R} :
    P.coroot i = t • P.coroot j ↔ P.root j = t • P.root i :=
  ⟨fun h ↦ (P.flip.smul_coroot_eq_of_root_eq_smul j i t h).symm,
    fun h ↦ (P.smul_coroot_eq_of_root_eq_smul i j t h).symm⟩
/-
**RootPairing.mem_range_root_of_mem_range_reflection_of_mem_range_root** 是 Mathl
ib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：mem_range_root_of_mem_range_reflection_of_mem_range_root {r : M ≃ₗ[R] M} {
α : M} (hr : r in range P.reflection) (hα : α in range P.root) : r • α in range 
P.root
参数：hr : r in range P.reflection；hα : α in range P.root。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
-/
lemma mem_range_root_of_mem_range_reflection_of_mem_range_root
    {r : M ≃ₗ[R] M} {α : M} (hr : r ∈ range P.reflection) (hα : α ∈ range P.root) :
    r • α ∈ range P.root := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.root_reflectionPerm i j⟩
/-
**RootPairing.mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot** 是
 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot {r : N ≃ₗ[R
] N} {α : N} (hr : r in range P.coreflection) (hα : α in range P.coroot) : r • α
 in range P.coroot
参数：hr : r in range P.coreflection；hα : α in range P.coroot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
-/
lemma mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot
    {r : N ≃ₗ[R] N} {α : N} (hr : r ∈ range P.coreflection) (hα : α ∈ range P.coroot) :
    r • α ∈ range P.coroot := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflectionPerm i j, P.coroot_reflectionPerm i j⟩
/-
**RootPairing.pairing_smul_root_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_smul_root_eq (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm 
j) : P.pairing k i • P.root i = P.pairing k j • P.root j
参数：k : ι；hij : P.reflectionPerm i = P.reflectionPerm j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_smul_root_eq (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j) :
    P.pairing k i • P.root i = P.pairing k j • P.root j := by
  have h : P.reflection i (P.root k) = P.reflection j (P.root k) := by
    simp only [← root_reflectionPerm, hij]
  simpa only [reflection_apply_root, sub_right_inj] using h
/-
**RootPairing.pairing_smul_coroot_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_smul_coroot_eq (k : ι) (hij : P.reflectionPerm i = P.reflectionPer
m j) : P.pairing i k • P.coroot i = P.pairing j k • P.coroot j
参数：k : ι；hij : P.reflectionPerm i = P.reflectionPerm j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_smul_coroot_eq (k : ι) (hij : P.reflectionPerm i = P.reflectionPerm j) :
    P.pairing i k • P.coroot i = P.pairing j k • P.coroot j := by
  have h : P.coreflection i (P.coroot k) = P.coreflection j (P.coroot k) := by
    simp only [← coroot_reflectionPerm, hij]
  simpa only [coreflection_apply_coroot, sub_right_inj] using h
/-
**RootPairing.two_nsmul_reflection_eq_of_perm_eq** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：two_nsmul_reflection_eq_of_perm_eq (hij : P.reflectionPerm i = P.reflectio
nPerm j) : 2 • ⇑(P.reflection i) = 2 • P.reflection j
参数：hij : P.reflectionPerm i = P.reflectionPerm j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用引理 `RootPairing.pairing_smul_root_eq`：pairing_smul_root_eq (k : ι) (hij : P.
reflectionPerm i = P.reflectionPerm j) : P.pairing k i • P.root i = P.pairing k 
j • P.root j
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `RootPairing.pairing_smul_coroot_eq`：pairing_smul_coroot_eq (k : ι) (hij 
: P.reflectionPerm i = P.reflectionPerm j) : P.pairing i k • P.coroot i = P.pair
ing j k • P.coroot j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
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
/-
**RootPairing.reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular** 是 Mathlib 
中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular (h2 : IsSMulRegular 
M 2) : P.reflectionPerm i = P.reflectionPerm j ↔ P.reflection i = P.reflection j
参数：h2 : IsSMulRegular M 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.pi`：∀ {I : Type u} {f : I → Type v} {α : Type u_1} [inst :
 (i : I) → SMul α (f i)] {k : α},   (∀ (i : I), IsSMulRegular (f i) k) → IsSMulR
egular…
· 使用引理 `RootPairing.two_nsmul_reflection_eq_of_perm_eq`：two_nsmul_reflection_eq_
of_perm_eq (hij : P.reflectionPerm i = P.reflectionPerm j) : 2 • ⇑(P.reflection 
i) = 2 • P.reflection j
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflectionPerm_eq_reflectionPerm_iff_of_isSMulRegular (h2 : IsSMulRegular M 2) :
    P.reflectionPerm i = P.reflectionPerm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  suffices ⇑(P.reflection i) = ⇑(P.reflection j) from DFunLike.coe_injective this
  replace h2 : IsSMulRegular (M → M) 2 := IsSMulRegular.pi fun _ ↦ h2
  exact h2 <| P.two_nsmul_reflection_eq_of_perm_eq i j h

set_option backward.isDefEq.respectTransparency false in
/-
**RootPairing.reflectionPerm_eq_reflectionPerm_iff_of_span** 是 Mathlib 中的一个引理，位于
命名空间 `RootPairing`。
形式化陈述：reflectionPerm_eq_reflectionPerm_iff_of_span : P.reflectionPerm i = P.refl
ectionPerm j ↔ forall x in span R (range P.root), P.reflection i x = P.reflectio
n j x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma reflectionPerm_eq_reflectionPerm_iff_of_span :
    P.reflectionPerm i = P.reflectionPerm j ↔
    ∀ x ∈ span R (range P.root), P.reflection i x = P.reflection j x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
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
/-
**RootPairing.reflectionPerm_eq_reflectionPerm_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：reflectionPerm_eq_reflectionPerm_iff [P.IsRootSystem] (i j : ι) : P.reflec
tionPerm i = P.reflectionPerm j ↔ P.reflection i = P.reflection j
参数：i j : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.reflectionPerm_eq_reflectionPerm_iff_of_span`：reflectionPerm
_eq_reflectionPerm_iff_of_span : P.reflectionPerm i = P.reflectionPerm j ↔ foral
l x in span R (range P.root), P.reflection i x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflectionPerm_eq_reflectionPerm_iff [P.IsRootSystem] (i j : ι) :
    P.reflectionPerm i = P.reflectionPerm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  ext x
  exact (P.reflectionPerm_eq_reflectionPerm_iff_of_span i j).mp h x <| by simp
/-
**RootPairing.toPerfPair_comp_root** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N),   ⇑P.toPerfPa
ir ∘ ⇑P.root = P.root'
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
-/
@[simp] lemma toPerfPair_comp_root : P.toPerfPair ∘ P.root = P.root' := rfl
/-
**RootPairing.toPerfPair_flip_comp_coroot** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing
`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N),   ⇑P.flip.toP
erfPair ∘ ⇑P.coroot = P.coroot'
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
-/
@[simp] lemma toPerfPair_flip_comp_coroot :
    P.toLinearMap.flip.toPerfPair ∘ P.coroot = P.coroot' := rfl

/-- The Coxeter Weight of a pair gives the weight of an edge in a Coxeter diagram, when it is
finite.  It is `4 cos² θ`, where `θ` describes the dihedral angle between hyperplanes. -/
/-
**RootPairing.coxeterWeight** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：coxeterWeight : R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Coxeter Weight of a pair gives the weight of an edge in a Coxeter diagram, w
hen it is
finite.  It is `4 cos² θ`, where `θ` describes the dihedral angle between hyperp
lanes.
-/
def coxeterWeight : R := pairing P i j * pairing P j i
/-
**RootPairing.coxeterWeight_flip** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (i j : ι), P
.flip.coxeterWeight i j = P.coxeterWeight i j
参数：P : RootPairing ι R M N；i j : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coxeterWeight_flip :
    P.flip.coxeterWeight i j = P.coxeterWeight i j := by
  simp [coxeterWeight, mul_comm (P.pairing j i)]
/-
**RootPairing.coxeterWeight_swap** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]

/-- Two roots are orthogonal when they are fixed by each others' reflections. -/
/-
**RootPairing.IsOrthogonal** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：IsOrthogonal : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two roots are orthogonal when they are fixed by each others' reflections.
-/
def IsOrthogonal : Prop := pairing P i j = 0 ∧ pairing P j i = 0
/-
**RootPairing.isOrthogonal_symm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：isOrthogonal_symm : IsOrthogonal P i j ↔ IsOrthogonal P j i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isOrthogonal_symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]

set_option backward.isDefEq.respectTransparency false in
/-
**RootPairing.isOrthogonal_comm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：isOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.r
eflection j)
参数：h : IsOrthogonal P i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Defs.0.RootPairing.isOrthogona
l_comm._abel_1_2`：∀ {ι : Type u_4} {R : Type u_2} {M : Type u_1} {N : Type u_3} 
[inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] […
-/
lemma isOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [commute_iff_eq]
  ext
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  simp only [LinearEquiv.mul_apply, reflection_apply, LinearMap.flip_apply, map_sub,
    map_smul, root_coroot_eq_pairing, h, zero_smul, sub_zero]
  abel

variable {P i j}
/-
**RootPairing.IsOrthogonal.flip** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.IsOrthogo
nal`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {i j : ι}, P
.IsOrthogonal i j → P.flip.IsOrthogonal i j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsOrthogonal.flip (h : IsOrthogonal P i j) : IsOrthogonal P.flip i j := ⟨h.2, h.1⟩
/-
**RootPairing.IsOrthogonal.symm** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.IsOrthogo
nal`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {i j : ι}, P
.IsOrthogonal i j → P.IsOrthogonal j i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsOrthogonal.symm (h : IsOrthogonal P i j) : IsOrthogonal P j i := ⟨h.2, h.1⟩
/-
**RootPairing.IsOrthogonal.reflection_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Root
Pairing.IsOrthogonal`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {i j : ι}, P
.IsOrthogonal i j → (P.reflection j) (P.root i) = P.root i
参数：P.reflection j；P.root i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsOrthogonal.reflection_apply_left (h : IsOrthogonal P i j) :
    P.reflection j (P.root i) = P.root i := by
  simp [reflection_apply, h.1]
/-
**RootPairing.IsOrthogonal.reflection_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Roo
tPairing.IsOrthogonal`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {i j : ι}, P
.IsOrthogonal j i → (P.reflection j) (P.root i) = P.root i
参数：P.reflection j；P.root i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsOrthogonal.reflection_apply_left`：∀ {ι : Type u_1} {R : Ty
pe u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup
 M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.IsOrthogonal.symm`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
-/
lemma IsOrthogonal.reflection_apply_right (h : IsOrthogonal P j i) :
    P.reflection j (P.root i) = P.root i :=
  h.symm.reflection_apply_left
/-
**RootPairing.IsOrthogonal.coreflection_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Ro
otPairing.IsOrthogonal`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {i j : ι}, P
.IsOrthogonal i j → (P.coreflection j) (P.coroot i) = P.coroot i
参数：P.coreflection j；P.coroot i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsOrthogonal.reflection_apply_left`：∀ {ι : Type u_1} {R : Ty
pe u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup
 M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.IsOrthogonal.flip`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
-/
lemma IsOrthogonal.coreflection_apply_left (h : IsOrthogonal P i j) :
    P.coreflection j (P.coroot i) = P.coroot i :=
  h.flip.reflection_apply_left
/-
**RootPairing.IsOrthogonal.coreflection_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `R
ootPairing.IsOrthogonal`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {i j : ι}, P
.IsOrthogonal j i → (P.coreflection j) (P.coroot i) = P.coroot i
参数：P.coreflection j；P.coroot i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsOrthogonal.reflection_apply_right`：∀ {ι : Type u_1} {R : T
ype u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGrou
p M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.IsOrthogonal.flip`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
-/
lemma IsOrthogonal.coreflection_apply_right (h : IsOrthogonal P j i) :
    P.coreflection j (P.coroot i) = P.coroot i :=
  h.flip.reflection_apply_right
/-
**RootPairing.isFixedPt_reflection_of_isOrthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：isFixedPt_reflection_of_isOrthogonal {s : Set ι} (hj : forall i in s, P.Is
Orthogonal j i) {x : M} (hx : x in span R (P.root '' s)) : IsFixedPt (P.reflecti
on j) x
参数：hj : forall i in s, P.IsOrthogonal j i；hx : x in span R (P.root '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsFixedPt.eq_1`：∀ {α : Type u₁} (f : α → α) (x : α), Function.I
sFixedPt f x = (f x = x)
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `RootPairing.IsOrthogonal.reflection_apply_right`：∀ {ι : Type u_1} {R : T
ype u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGrou
p M]   [inst_2 : _root_.Module R M] […
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
lemma isFixedPt_reflection_of_isOrthogonal {s : Set ι} (hj : ∀ i ∈ s, P.IsOrthogonal j i)
    {x : M} (hx : x ∈ span R (P.root '' s)) :
    IsFixedPt (P.reflection j) x := by
  rw [IsFixedPt]
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero]
  | add u v hu hv hu' hv' => rw [map_add, hu', hv']
  | smul t u hu hu' => rw [map_smul, hu']
  | mem u hu =>
      obtain ⟨i, his, rfl⟩ := hu
      exact IsOrthogonal.reflection_apply_right <| hj i his
/-
**RootPairing.reflectionPerm_eq_of_pairing_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：reflectionPerm_eq_of_pairing_eq_zero (h : P.pairing j i = 0) : P.reflectio
nPerm i j = j
参数：h : P.pairing j i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflectionPerm_eq_of_pairing_eq_zero (h : P.pairing j i = 0) :
    P.reflectionPerm i j = j :=
  P.root.injective <| by simp [reflection_apply, h]
/-
**RootPairing.reflectionPerm_eq_of_pairing_eq_zero'** 是 Mathlib 中的一个引理，位于命名空间 `R
ootPairing`。
形式化陈述：reflectionPerm_eq_of_pairing_eq_zero' (h : P.pairing i j = 0) : P.reflecti
onPerm i j = j
参数：h : P.pairing i j = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.reflectionPerm_eq_of_pairing_eq_zero`：reflectionPerm_eq_of_p
airing_eq_zero (h : P.pairing j i = 0) : P.reflectionPerm i j = j
-/
lemma reflectionPerm_eq_of_pairing_eq_zero' (h : P.pairing i j = 0) :
    P.reflectionPerm i j = j :=
  P.flip.reflectionPerm_eq_of_pairing_eq_zero h
/-
**RootPairing.reflectionPerm_eq_iff_smul_root** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：reflectionPerm_eq_iff_smul_root : P.reflectionPerm i j = j ↔ P.pairing j i
 • P.root i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.reflectionPerm_root`：∀ {ι : Type u_1} {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 :
 _root_.Module R M] […
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflectionPerm_eq_iff_smul_root :
    P.reflectionPerm i j = j ↔ P.pairing j i • P.root i = 0 :=
  ⟨fun h ↦ by simpa [h] using P.reflectionPerm_root i j,
    fun h ↦ P.root.injective <| by simp [reflection_apply, h]⟩
/-
**RootPairing.reflectionPerm_eq_iff_smul_coroot** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：reflectionPerm_eq_iff_smul_coroot : P.reflectionPerm i j = j ↔ P.pairing i
 j • P.coroot i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.reflectionPerm_eq_iff_smul_root`：reflectionPerm_eq_iff_smul_
root : P.reflectionPerm i j = j ↔ P.pairing j i • P.root i = 0
-/
lemma reflectionPerm_eq_iff_smul_coroot :
    P.reflectionPerm i j = j ↔ P.pairing i j • P.coroot i = 0 :=
  P.flip.reflectionPerm_eq_iff_smul_root
/-
**RootPairing.pairing_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_eq_zero_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R 
M] : P.pairing i j = 0 ↔ P.pairing j i = 0
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `RootPairing.reflectionPerm_eq_of_pairing_eq_zero'`：reflectionPerm_eq_of_
pairing_eq_zero' (h : P.pairing i j = 0) : P.reflectionPerm i j = j
-/
lemma pairing_eq_zero_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] :
    P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  suffices ∀ {i j : ι}, P.pairing i j = 0 → P.pairing j i = 0 from ⟨this, this⟩
  intro i j h
  simpa [P.ne_zero i, reflectionPerm_eq_iff_smul_root] using
    P.reflectionPerm_eq_of_pairing_eq_zero' h
/-
**RootPairing.pairing_eq_zero_iff'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_eq_zero_iff' [NeZero (2 : R)] [IsDomain R] : P.pairing i j = 0 ↔ P
.pairing j i = 0
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `RootPairing.pairing_eq_zero_iff`：pairing_eq_zero_iff [NeZero (2 : R)] [I
sDomain R] [Module.IsTorsionFree R M] : P.pairing i j = 0 ↔ P.pairing j i = 0
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
-/
lemma pairing_eq_zero_iff' [NeZero (2 : R)] [IsDomain R] :
    P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  exact pairing_eq_zero_iff
/-
**RootPairing.coxeterWeight_zero_iff_isOrthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
形式化陈述：coxeterWeight_zero_iff_isOrthogonal [NeZero (2 : R)] [IsDomain R] : P.coxe
terWeight i j = 0 ↔ P.IsOrthogonal i j
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.pairing_eq_zero_iff`：pairing_eq_zero_iff [NeZero (2 : R)] [I
sDomain R] [Module.IsTorsionFree R M] : P.pairing i j = 0 ↔ P.pairing j i = 0
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coxeterWeight_zero_iff_isOrthogonal [NeZero (2 : R)] [IsDomain R] :
    P.coxeterWeight i j = 0 ↔ P.IsOrthogonal i j := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [coxeterWeight, IsOrthogonal, P.pairing_eq_zero_iff (i := i) (j := j)]
/-
**RootPairing.isOrthogonal_iff_pairing_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring`。
形式化陈述：isOrthogonal_iff_pairing_eq_zero [NeZero (2 : R)] [IsDomain R] [Module.IsT
orsionFree R M] : P.IsOrthogonal i j ↔ P.pairing i j = 0
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.pairing_eq_zero_iff`：pairing_eq_zero_iff [NeZero (2 : R)] [I
sDomain R] [Module.IsTorsionFree R M] : P.pairing i j = 0 ↔ P.pairing j i = 0
-/
lemma isOrthogonal_iff_pairing_eq_zero [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] :
    P.IsOrthogonal i j ↔ P.pairing i j = 0 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, pairing_eq_zero_iff.mp h⟩⟩
/-
**RootPairing.isFixedPt_reflectionPerm_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g`。
形式化陈述：isFixedPt_reflectionPerm_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsi
onFree R M] : IsFixedPt (P.reflectionPerm i) j ↔ P.pairing i j = 0
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isFixedPt_reflectionPerm_iff [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] :
    IsFixedPt (P.reflectionPerm i) j ↔ P.pairing i j = 0 := by
  simp [P.ne_zero i, pairing_eq_zero_iff, IsFixedPt, reflectionPerm_eq_iff_smul_root]

section Map

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]

set_option backward.isDefEq.respectTransparency false in
/-- Push forward a root pairing along linear equivalences, also reindexing the (co)roots. -/
/-
**RootPairing.map** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] →                   {P : RootPairing
 ι R M N} →                     {ι₂ : Type u_5} →                       {M₂ : Ty
pe u_6} →                         {N₂ : Type u_7} →                           [i
nst_5 : AddCommGroup M₂] →                             [inst_6 : _root_.Module R
 M₂] →                               [inst_7 : AddCommGroup N₂] →               
                  [inst_8 : _root_.Module R N₂] →                               
    ι ≃ ι₂ → (M ≃ₗ[R] M₂) → (N ≃ₗ[R] N₂) → RootPairing ι₂ R M₂ N₂
参数：M ≃ₗ[R] M₂；N ≃ₗ[R] N₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Push forward a root pairing along linear equivalences, also reindexing the (co)r
oots.
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
  reflectionPerm i := e.symm.trans <| (P.reflectionPerm (e.symm i)).trans e
  reflectionPerm_root i j := by simp [reflection_apply]
  reflectionPerm_coroot i j := by simp [coreflection_apply]
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsRootSystem] (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂) :
    (P.map e f g).IsRootSystem where
  span_root_eq_top := by simp [RootPairing.map, Embedding.coe_trans, range_comp]
  span_coroot_eq_top := by simp [Embedding.coe_trans, range_comp, RootPairing.map]

end Map

end RootPairing

