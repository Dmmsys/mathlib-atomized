/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Properties of the `𝔤₂` root system.

The `𝔤₂` root pairing is special enough to deserve its own API. We provide one in this file.

As an application we prove the key result that a crystallographic, reduced, irreducible root
pairing containing two roots of Coxeter weight three is spanned by this pair of roots (and thus
is two-dimensional). This result is usually proved only for pairs of roots belonging to a base (as a
corollary of the fact that no node can have degree greater than three) and moreover usually requires
stronger assumptions on the coefficients than here.

## Main results:
* `RootPairing.EmbeddedG2`: a data-bearing typeclass which distinguishes a pair of roots whose
  pairing is `-3` (equivalently, with a distinguished choice of base). This is a sufficient
  condition for the span of this pair of roots to be a `𝔤₂` root system.
* `RootPairing.IsG2`: a prop-valued typeclass characterising the `𝔤₂` root system.
* `RootPairing.IsNotG2`: a prop-valued typeclass stating that a crystallographic, reduced,
  irreducible root system is not `𝔤₂`.
* `RootPairing.EmbeddedG2.shortRoot`: the distinguished short root, which we often donate `α`
* `RootPairing.EmbeddedG2.longRoot`: the distinguished long root, which we often donate `β`
* `RootPairing.EmbeddedG2.shortAddLong`: the short root `α + β`
* `RootPairing.EmbeddedG2.twoShortAddLong`: the short root `2α + β`
* `RootPairing.EmbeddedG2.threeShortAddLong`: the long root `3α + β`
* `RootPairing.EmbeddedG2.threeShortAddTwoLong`: the long root `3α + 2β`
* `RootPairing.EmbeddedG2.span_eq_top`: a crystallographic reduced irreducible root pairing
  containing two roots with pairing `-3` is spanned by this pair (thus two-dimensional).
* `RootPairing.EmbeddedG2.card_index_eq_twelve`: the `𝔤₂` root pairing has twelve roots.

## TODO
Once sufficient API for `RootPairing.Base` has been developed:
* Add `def EmbeddedG2.toBase [P.EmbeddedG2] : P.Base` with `support := {long P, short P}`
* Given `P` satisfying `[P.IsG2]`, distinct elements of a base must pair to `-3` (in one order).

-/

@[expose] public section

noncomputable section

open FaithfulSMul Function Set Submodule
open List hiding mem_toFinset

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

/--
Definition of `EmbeddedG2` / `EmbeddedG2` 的定义

English:
class EmbeddedG2
  parameters: extends P.IsCrystallographic, P.IsReduced
  extends: P.IsCrystallographic, P.IsReduced
  axioms and operations (3):
    - long : ι
    - short : ι
    - pairingIn_long_short : P.pairingIn Int long short = -3

中文:
类 EmbeddedG2
  参数: extends P.IsCrystallographic, P.IsReduced
  继承: P.IsCrystallographic, P.IsReduced
  公理与运算 (3 个):
    - long : ι
    - short : ι
    - pairingIn_long_short : P.pairingIn 整数 long short = -3
-/
class EmbeddedG2 extends P.IsCrystallographic, P.IsReduced where
  /-- The distinguished long root of an embedded `𝔤₂` root pairing. -/
  long : ι
  /-- The distinguished short root of an embedded `𝔤₂` root pairing. -/
  short : ι
  pairingIn_long_short : P.pairingIn Int long short = -3

/--
Definition of `IsG2` / `IsG2` 的定义

English:
class IsG2
  parameters: : Prop extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  extends: P.IsCrystallographic, P.IsReduced, P.IsIrreducible
  axioms and operations (1):
    - exists_pairingIn_neg_three : exists i j, P.pairingIn Int i j = -3

中文:
类 IsG2
  参数: : 命题 extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  继承: P.IsCrystallographic, P.IsReduced, P.IsIrreducible
  公理与运算 (1 个):
    - exists_pairingIn_neg_three : 存在 i j, P.pairingIn 整数 i j = -3
-/
class IsG2 : Prop extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  exists_pairingIn_neg_three : exists i j, P.pairingIn Int i j = -3

/--
Definition of `IsNotG2` / `IsNotG2` 的定义

English:
class IsNotG2
  parameters: : Prop extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  extends: P.IsCrystallographic, P.IsReduced, P.IsIrreducible
  axioms and operations (1):
    - pairingIn_mem_zero_one_two((i j : ι)) : P.pairingIn Int i j in ({-2, -1, 0, 1, 2} : Set Int)

中文:
类 IsNotG2
  参数: : 命题 extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  继承: P.IsCrystallographic, P.IsReduced, P.IsIrreducible
  公理与运算 (1 个):
    - pairingIn_mem_zero_one_two((i j : ι)) : P.pairingIn 整数 i j in ({-2, -1, 0, 1, 2} : Set 整数)
-/
class IsNotG2 : Prop extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  pairingIn_mem_zero_one_two (i j : ι) : P.pairingIn Int i j in ({-2, -1, 0, 1, 2} : Set Int)

section IsG2

/-- By making an arbitrary choice of roots pairing to `-3`, we can obtain an embedded `𝔤₂` root
system just from the knowledge that such a pairs exists. -/
@[instance_reducible]
/--
Definition of `IsG2.toEmbeddedG2` / `IsG2.toEmbeddedG2` 的定义

English:
definition IsG2.toEmbeddedG2
  signature: [P.IsG2]
  body: (IsG2.exists_pairingIn_neg_three (P := P)).choose
  short := (IsG2.exists_pairingIn_neg_three (P := P)).choose_spec.choose
  pairingIn_long_short := (IsG2.exists_pairingIn_neg_three (P := P)).choose_spec.choose_spec

中文:
定义 IsG2.toEmbeddedG2
  签名: [P.IsG2]
  定义体: (IsG2.exists_pairingIn_neg_three (P := P)).choose
  short := (IsG2.exists_pairingIn_neg_three (P := P)).choose_spec.choose
  pairingIn_long_short := (IsG2.exists_pairingIn_neg_three (P := P)).choose_spec.choose_spec

Depends on / 依赖: IsG2.exists_pairingIn_neg_three, exists_pairingIn_neg_three
-/
def IsG2.toEmbeddedG2 [P.IsG2] : P.EmbeddedG2 where
  long := (IsG2.exists_pairingIn_neg_three (P := P)).choose
  short := (IsG2.exists_pairingIn_neg_three (P := P)).choose_spec.choose
  pairingIn_long_short := (IsG2.exists_pairingIn_neg_three (P := P)).choose_spec.choose_spec

/--
lemma `IsG2.nonempty` / 引理 `IsG2.nonempty`

English:
lemma IsG2.nonempty
  given: [P.IsG2]
  statement: Nonempty ι
  proof: ⟨(IsG2.exists_pairingIn_neg_three (P := P)).choose⟩

中文:
引理 IsG2.nonempty
  条件: [P.IsG2]
  结论: Nonempty ι
  证明: ⟨(IsG2.exists_pairingIn_neg_three (P := P)).choose⟩

Depends on / 依赖: IsG2.exists_pairingIn_neg_three, exists_pairingIn_neg_three
-/
lemma IsG2.nonempty [P.IsG2] : Nonempty ι :=
  ⟨(IsG2.exists_pairingIn_neg_three (P := P)).choose⟩

variable [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/--
lemma `isG2_iff` / 引理 `isG2_iff`

English:
lemma isG2_iff
  proof: ⟨fun _ => IsG2.exists_pairingIn_neg_three, fun h => ⟨h⟩⟩

中文:
引理 isG2_iff
  证明: ⟨fun _ => IsG2.exists_pairingIn_neg_three, fun h => ⟨h⟩⟩

Depends on / 依赖: IsG2.exists_pairingIn_neg_three, exists_pairingIn_neg_three
-/
lemma isG2_iff :
    P.IsG2 ↔ exists i j, P.pairingIn Int i j = -3 :=
  ⟨fun _ => IsG2.exists_pairingIn_neg_three, fun h => ⟨h⟩⟩

/--
lemma `isNotG2_iff` / 引理 `isNotG2_iff`

English:
lemma isNotG2_iff
  proof: ⟨fun _ => IsNotG2.pairingIn_mem_zero_one_two, fun h => ⟨h⟩⟩

中文:
引理 isNotG2_iff
  证明: ⟨fun _ => IsNotG2.pairingIn_mem_zero_one_two, fun h => ⟨h⟩⟩

Depends on / 依赖: IsNotG2, IsNotG2.pairingIn_mem_zero_one_two, pairingIn_mem_zero_one_two
-/
lemma isNotG2_iff :
    P.IsNotG2 ↔ forall i j, P.pairingIn Int i j in ({-2, -1, 0, 1, 2} : Set Int) :=
  ⟨fun _ => IsNotG2.pairingIn_mem_zero_one_two, fun h => ⟨h⟩⟩

variable [Finite ι] [CharZero R] [IsDomain R]

@[simp]
/--
lemma `not_isG2_iff_isNotG2` / 引理 `not_isG2_iff_isNotG2`

English:
lemma not_isG2_iff_isNotG2
  proof: by
  simp only [isG2_iff, isNotG2_iff, not_exists, Set.mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h i j => ?_, fun h i j => ?_⟩
  · have hij := h (P.reflectionPerm i i) j
    have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
    aesop
  · specialize h i j
    lia

中文:
引理 not_isG2_iff_isNotG2
  证明: by
  simp only [isG2_iff, isNotG2_iff, not_exists, Set.mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h i j => ?_, fun h i j => ?_⟩
  · have hij := h (P.reflectionPerm i i) j
    have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
    aesop
  · specialize h i j
    lia

Depends on / 依赖: P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, P.reflectionPerm, Set.mem_insert_iff, isG2_iff, isNotG2_iff, mem_insert_iff, mem_singleton_iff, not_exists, pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, reflectionPerm, specialize
-/
lemma not_isG2_iff_isNotG2 :
    ¬ P.IsG2 ↔ P.IsNotG2 := by
  simp only [isG2_iff, isNotG2_iff, not_exists, Set.mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h i j => ?_, fun h i j => ?_⟩
  · have hij := h (P.reflectionPerm i i) j
    have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
    aesop
  · specialize h i j
    lia

set_option linter.overlappingInstances false in
/--
lemma `IsG2.pairingIn_mem_zero_one_three` / 引理 `IsG2.pairingIn_mem_zero_one_three`

English:
lemma IsG2.pairingIn_mem_zero_one_three
  statement: [P.IsG2]
  proof: by
  suffices ¬ (forall i j, P.pairingIn Int i j = P.pairingIn Int j i ∨
                     P.pairingIn Int i j = 2 * P.pairingIn Int j i ∨
                     P.pairingIn Int j i = 2 * P.pairingIn Int i j) by
    have aux₁ := P.forall_pairingIn_eq_swap_or.resolve_left this i j
    have aux₂ := P

中文:
引理 IsG2.pairingIn_mem_zero_one_three
  结论: [P.IsG2]
  证明: by
  suffices ¬ (forall i j, P.pairingIn Int i j = P.pairingIn Int j i ∨
                     P.pairingIn Int i j = 2 * P.pairingIn Int j i ∨
                     P.pairingIn Int j i = 2 * P.pairingIn Int i j) by
    have aux₁ := P.forall_pairingIn_eq_swap_or.resolve_left this i j
    have aux₂ := P

Depends on / 依赖: P.forall_pairingIn_eq_swap_or.resolve_left, P.pairingIn, P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, Prod.mk.injEq, Prod.mk_eq_one, Prod.mk_eq_zero, Prod.mk_one_one, Prod.mk_zero_zero, exists_pairingIn_neg_thre, forall_pairingIn_eq_swap_or, mem_insert_iff, mem_singleton_iff, mk_eq_one, mk_eq_zero, mk_one_one, mk_zero_zero, pairingIn, pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, resolve_left
-/
lemma IsG2.pairingIn_mem_zero_one_three [P.IsG2]
    (i j : ι) (h : P.root i != P.root j) (h' : P.root i != -P.root j) :
    P.pairingIn Int i j in ({-3, -1, 0, 1, 3} : Set Int) := by
  suffices ¬ (forall i j, P.pairingIn Int i j = P.pairingIn Int j i ∨
                     P.pairingIn Int i j = 2 * P.pairingIn Int j i ∨
                     P.pairingIn Int j i = 2 * P.pairingIn Int i j) by
    have aux₁ := P.forall_pairingIn_eq_swap_or.resolve_left this i j
    have aux₂ := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i j h h'
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_zero_zero, Prod.mk_eq_zero,
      Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at aux₂ ⊢
    lia
  obtain ⟨k, l, hkl⟩ := exists_pairingIn_neg_three (P := P)
  push Not
  refine ⟨k, l, ?_⟩
  have aux := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed k l
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_zero_zero, Prod.mk_eq_zero,
      Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at aux
  omega

end IsG2

section IsNotG2

variable {P}
variable [Finite ι] [CharZero R] [IsDomain R] {i j : ι}

variable (i j) in
/--
lemma `chainBotCoeff_add_chainTopCoeff_le_two` / 引理 `chainBotCoeff_add_chainTopCoeff_le_two`

English:
lemma chainBotCoeff_add_chainTopCoeff_le_two
  given: [P.IsNotG2]
  proof: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le]; rw [Nat.cast_add]; rw [Nat.cast_ofNat]; rw [chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := IsNo

中文:
引理 chainBotCoeff_add_chainTopCoeff_le_two
  条件: [P.IsNotG2]
  证明: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le]; rw [Nat.cast_add]; rw [Nat.cast_ofNat]; rw [chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := IsNo

Depends on / 依赖: Int.ofNat_le, IsNotG2, IsNotG2.pairingIn_mem_zero_one_two, LinearIndependent, Nat.cast_add, Nat.cast_ofNat, P.chainTopIdx, P.root, cast_add, cast_ofNat, chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx, chainBotCoeff_of_not_linearIndependent, chainTopCoeff_of_not_linearIndependent, chainTopIdx, ofNat_le, pairingIn_mem_zero_one_two
-/
lemma chainBotCoeff_add_chainTopCoeff_le_two [P.IsNotG2] :
    P.chainBotCoeff i j + P.chainTopCoeff i j <= 2 := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le]; rw [Nat.cast_add]; rw [Nat.cast_ofNat]; rw [chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := IsNotG2.pairingIn_mem_zero_one_two (P := P) (P.chainTopIdx i j) i
  aesop

/--
lemma `pairingIn_le_zero_of_root_add_mem` / 引理 `pairingIn_le_zero_of_root_add_mem`

English:
lemma pairingIn_le_zero_of_root_add_mem
  given: [P.IsNotG2] (h : P.root i + P.root j in range P.root)
  proof: by
have aux₁ := P.linearIndependent_of_add_mem_range_root' add_comm (P.root i) (P.root j) ▸ h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two j i
  have aux₃ : 1 <= P.chainTopCoeff j i := by
    rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff aux₁, one_smul]
  rw [← P.chainBotCoeff_sub_

中文:
引理 pairingIn_le_zero_of_root_add_mem
  条件: [P.IsNotG2] (h : P.root i + P.root j in range P.root)
  证明: by
have aux₁ := P.linearIndependent_of_add_mem_range_root' add_comm (P.root i) (P.root j) ▸ h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two j i
  have aux₃ : 1 <= P.chainTopCoeff j i := by
    rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff aux₁, one_smul]
  rw [← P.chainBotCoeff_sub_

Depends on / 依赖: P.chainBotCoeff_add_chainTopCoeff_le_two, P.chainBotCoeff_sub_chainTopCoeff, P.chainTopCoeff, P.linearIndependent_of_add_mem_range_root, P.root, add_comm, chainBotCoeff_add_chainTopCoeff_le_two, chainBotCoeff_sub_chainTopCoeff, chainTopCoeff, linearIndependent_of_add_mem_range_root, one_smul, root_add_nsmul_mem_range_iff_le_chainTopCoeff
-/
lemma pairingIn_le_zero_of_root_add_mem [P.IsNotG2] (h : P.root i + P.root j in range P.root) :
    P.pairingIn Int i j <= 0 := by
have aux₁ := P.linearIndependent_of_add_mem_range_root' add_comm (P.root i) (P.root j) ▸ h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two j i
  have aux₃ : 1 <= P.chainTopCoeff j i := by
    rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff aux₁, one_smul]
  rw [← P.chainBotCoeff_sub_chainTopCoeff aux₁]
  lia

/--
lemma `zero_le_pairingIn_of_root_sub_mem` / 引理 `zero_le_pairingIn_of_root_sub_mem`

English:
lemma zero_le_pairingIn_of_root_sub_mem
  given: [P.IsNotG2] (h : P.root i - P.root j in range P.root)
  proof: by
  replace h : P.root i + P.root (P.reflectionPerm j j) in range P.root := by simpa [← sub_eq_add_neg]
  simpa using P.pairingIn_le_zero_of_root_add_mem h

中文:
引理 zero_le_pairingIn_of_root_sub_mem
  条件: [P.IsNotG2] (h : P.root i - P.root j in range P.root)
  证明: by
  replace h : P.root i + P.root (P.reflectionPerm j j) in range P.root := by simpa [← sub_eq_add_neg]
  simpa using P.pairingIn_le_zero_of_root_add_mem h

Depends on / 依赖: P.pairingIn_le_zero_of_root_add_mem, P.reflectionPerm, P.root, pairingIn_le_zero_of_root_add_mem, reflectionPerm, replace, sub_eq_add_neg
-/
lemma zero_le_pairingIn_of_root_sub_mem [P.IsNotG2] (h : P.root i - P.root j in range P.root) :
    0 <= P.pairingIn Int i j := by
  replace h : P.root i + P.root (P.reflectionPerm j j) in range P.root := by simpa [← sub_eq_add_neg]
  simpa using P.pairingIn_le_zero_of_root_add_mem h

/--
lemma `chainBotCoeff_if_one_zero` / 引理 `chainBotCoeff_if_one_zero`

English:
lemma chainBotCoeff_if_one_zero
  given: [P.IsNotG2] (h : P.root i + P.root j in range P.root)
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have aux₁ := P.linearIndependent_of_add_mem_range_root' h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two i j
  have aux₃ : 1 <= P.chainTopCoeff i j := P.one_le_chainTopCoeff_of_root_add_mem h
  rcases eq_or_ne (P.chainBotC

中文:
引理 chainBotCoeff_if_one_zero
  条件: [P.IsNotG2] (h : P.root i + P.root j in range P.root)
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have aux₁ := P.linearIndependent_of_add_mem_range_root' h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two i j
  have aux₃ : 1 <= P.chainTopCoeff i j := P.one_le_chainTopCoeff_of_root_add_mem h
  rcases eq_or_ne (P.chainBotC

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, Nat.cast_inj, P.chainBotCoeff, P.chainBotCoeff_add_chainTopCoeff_le_two, P.chainBotCoeff_sub_chainTopCoeff, P.chainTopCoeff, P.linearIndependent_of_add_mem_range_root, P.one_le_chainTopCoeff_of_root_add_mem, P.pairingIn_eq_zero_iff, P.toLinearMap, cast_inj, chainBotCoeff, chainBotCoeff_add_chainTopCoeff_le_two, chainBotCoeff_sub_chainTopCoeff, chainTopCoeff, eq_or_ne, linearIndependent_of_add_mem_range_root, of_isPerfPair
-/
lemma chainBotCoeff_if_one_zero [P.IsNotG2] (h : P.root i + P.root j in range P.root) :
    P.chainBotCoeff i j = if P.pairingIn Int i j = 0 then 1 else 0 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have aux₁ := P.linearIndependent_of_add_mem_range_root' h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two i j
  have aux₃ : 1 <= P.chainTopCoeff i j := P.one_le_chainTopCoeff_of_root_add_mem h
  rcases eq_or_ne (P.chainBotCoeff i j) (P.chainTopCoeff i j) with aux₄ | aux₄ <;>
  simp_rw [P.pairingIn_eq_zero_iff (i := i) (j := j), ← P.chainBotCoeff_sub_chainTopCoeff aux₁,
    sub_eq_zero, Nat.cast_inj, aux₄, reduceIte] <;>
  lia

/--
lemma `chainTopCoeff_if_one_zero` / 引理 `chainTopCoeff_if_one_zero`

English:
lemma chainTopCoeff_if_one_zero
  given: [P.IsNotG2] (h : P.root i - P.root j in range P.root)
  proof: by
  let := P.indexNeg
  replace h : P.root i + P.root (-j) in range P.root := by simpa [← sub_eq_add_neg] using h
  simpa using P.chainBotCoeff_if_one_zero h

中文:
引理 chainTopCoeff_if_one_zero
  条件: [P.IsNotG2] (h : P.root i - P.root j in range P.root)
  证明: by
  let := P.indexNeg
  replace h : P.root i + P.root (-j) in range P.root := by simpa [← sub_eq_add_neg] using h
  simpa using P.chainBotCoeff_if_one_zero h

Depends on / 依赖: P.chainBotCoeff_if_one_zero, P.indexNeg, P.root, chainBotCoeff_if_one_zero, indexNeg, replace, sub_eq_add_neg
-/
lemma chainTopCoeff_if_one_zero [P.IsNotG2] (h : P.root i - P.root j in range P.root) :
    P.chainTopCoeff i j = if P.pairingIn Int i j = 0 then 1 else 0 := by
  let := P.indexNeg
  replace h : P.root i + P.root (-j) in range P.root := by simpa [← sub_eq_add_neg] using h
  simpa using P.chainBotCoeff_if_one_zero h

end IsNotG2

namespace EmbeddedG2

/-- A pair of roots which pair to `+3` are also sufficient to distinguish an embedded `𝔤₂`. -/
@[simps, instance_reducible]
/--
Definition of `ofPairingInThree` / `ofPairingInThree` 的定义

English:
definition ofPairingInThree
  signature: [CharZero R] [P.IsCrystallographic] [P.IsReduced] (long short : ι)
  body: P.reflectionPerm long long
  short := short
  pairingIn_long_short := by simp [h]

中文:
定义 ofPairingInThree
  签名: [CharZero R] [P.IsCrystallographic] [P.IsReduced] (long short : ι)
  定义体: P.reflectionPerm long long
  short := short
  pairingIn_long_short := by simp [h]

Depends on / 依赖: P.reflectionPerm, reflectionPerm
-/
def ofPairingInThree [CharZero R] [P.IsCrystallographic] [P.IsReduced] (long short : ι)
    (h : P.pairingIn Int long short = 3) : P.EmbeddedG2 where
  long := P.reflectionPerm long long
  short := short
  pairingIn_long_short := by simp [h]

variable [P.EmbeddedG2]

attribute [simp] pairingIn_long_short

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsIrreducible]
  signature: : P.IsG2 where
  body: ⟨long P, short P, by simp⟩

@[simp]

中文:
实例 [P.IsIrreducible]
  签名: : P.IsG2 where
  定义体: ⟨long P, short P, by simp⟩

@[simp]
-/
instance [P.IsIrreducible] : P.IsG2 where
  exists_pairingIn_neg_three := ⟨long P, short P, by simp⟩

@[simp]
/--
lemma `pairing_long_short` / 引理 `pairing_long_short`

English:
lemma pairing_long_short
  statement: P.pairing (long P) (short P) = -3
  proof: by
  rw [← P.algebraMap_pairingIn Int]; rw [pairingIn_long_short]
  simp

中文:
引理 pairing_long_short
  结论: P.pairing (long P) (short P) = -3
  证明: by
  rw [← P.algebraMap_pairingIn Int]; rw [pairingIn_long_short]
  simp

Depends on / 依赖: P.algebraMap_pairingIn, algebraMap_pairingIn, pairingIn_long_short
-/
lemma pairing_long_short : P.pairing (long P) (short P) = -3 := by
  rw [← P.algebraMap_pairingIn Int]; rw [pairingIn_long_short]
  simp

/--
Definition of `shortAddLong` / `shortAddLong` 的定义

English:
definition shortAddLong
  signature: : ι
  body: P.reflectionPerm (long P) (short P)

中文:
定义 shortAddLong
  签名: : ι
  定义体: P.reflectionPerm (long P) (short P)

Depends on / 依赖: P.reflectionPerm, reflectionPerm
-/
def shortAddLong : ι := P.reflectionPerm (long P) (short P)

/--
Definition of `twoShortAddLong` / `twoShortAddLong` 的定义

English:
definition twoShortAddLong
  signature: : ι
  body: P.reflectionPerm (short P) P.reflectionPerm (long P) (short P)

中文:
定义 twoShortAddLong
  签名: : ι
  定义体: P.reflectionPerm (short P) P.reflectionPerm (long P) (short P)

Depends on / 依赖: P.reflectionPerm, reflectionPerm
-/
def twoShortAddLong : ι := P.reflectionPerm (short P) P.reflectionPerm (long P) (short P)

/--
Definition of `threeShortAddLong` / `threeShortAddLong` 的定义

English:
definition threeShortAddLong
  signature: : ι
  body: P.reflectionPerm (short P) (long P)

中文:
定义 threeShortAddLong
  签名: : ι
  定义体: P.reflectionPerm (short P) (long P)

Depends on / 依赖: P.reflectionPerm, reflectionPerm
-/
def threeShortAddLong : ι := P.reflectionPerm (short P) (long P)

/--
Definition of `threeShortAddTwoLong` / `threeShortAddTwoLong` 的定义

English:
definition threeShortAddTwoLong
  signature: : ι
  body: P.reflectionPerm (long P) P.reflectionPerm (short P) (long P)

中文:
定义 threeShortAddTwoLong
  签名: : ι
  定义体: P.reflectionPerm (long P) P.reflectionPerm (short P) (long P)

Depends on / 依赖: P.reflectionPerm, reflectionPerm
-/
def threeShortAddTwoLong : ι := P.reflectionPerm (long P) P.reflectionPerm (short P) (long P)

/--
Definition of `shortRoot` / `shortRoot` 的定义

English:
abbreviation shortRoot
  body: P.root (short P)

中文:
缩写 shortRoot
  定义体: P.root (short P)

Depends on / 依赖: P.root
-/
abbrev shortRoot := P.root (short P)

/--
Definition of `longRoot` / `longRoot` 的定义

English:
abbreviation longRoot
  body: P.root (long P)

中文:
缩写 longRoot
  定义体: P.root (long P)

Depends on / 依赖: P.root
-/
abbrev longRoot := P.root (long P)

/--
Definition of `shortAddLongRoot` / `shortAddLongRoot` 的定义

English:
abbreviation shortAddLongRoot
  signature: : M
  body: P.root (shortAddLong P)

中文:
缩写 shortAddLongRoot
  签名: : M
  定义体: P.root (shortAddLong P)

Depends on / 依赖: P.root, shortAddLong
-/
abbrev shortAddLongRoot : M := P.root (shortAddLong P)

/--
Definition of `twoShortAddLongRoot` / `twoShortAddLongRoot` 的定义

English:
abbreviation twoShortAddLongRoot
  signature: : M
  body: P.root (twoShortAddLong P)

中文:
缩写 twoShortAddLongRoot
  签名: : M
  定义体: P.root (twoShortAddLong P)

Depends on / 依赖: P.root, twoShortAddLong
-/
abbrev twoShortAddLongRoot : M := P.root (twoShortAddLong P)

/--
Definition of `threeShortAddLongRoot` / `threeShortAddLongRoot` 的定义

English:
abbreviation threeShortAddLongRoot
  signature: : M
  body: P.root (threeShortAddLong P)

中文:
缩写 threeShortAddLongRoot
  签名: : M
  定义体: P.root (threeShortAddLong P)

Depends on / 依赖: P.root, threeShortAddLong
-/
abbrev threeShortAddLongRoot : M := P.root (threeShortAddLong P)

/--
Definition of `threeShortAddTwoLongRoot` / `threeShortAddTwoLongRoot` 的定义

English:
abbreviation threeShortAddTwoLongRoot
  signature: : M
  body: P.root (threeShortAddTwoLong P)

中文:
缩写 threeShortAddTwoLongRoot
  签名: : M
  定义体: P.root (threeShortAddTwoLong P)

Depends on / 依赖: P.root, isUnifLocDoublingMeasureOfIsAddHaarMeasure, threeShortAddTwoLong
-/
abbrev threeShortAddTwoLongRoot : M := P.root (threeShortAddTwoLong P)

/--
Definition of `allRoots` / `allRoots` 的定义

English:
abbreviation allRoots
  signature: : List M
  body: [ longRoot P, -longRoot P,
    shortRoot P, -shortRoot P,
    shortAddLongRoot P, -shortAddLongRoot P,
    twoShortAddLongRoot P, -twoShortAddLongRoot P,
    threeShortAddLongRoot P, -threeShortAddLongRoot P,
    threeShortAddTwoLongRoot P, -threeShortAddTwoLongRoot P ]

中文:
缩写 allRoots
  签名: : List M
  定义体: [ longRoot P, -longRoot P,
    shortRoot P, -shortRoot P,
    shortAddLongRoot P, -shortAddLongRoot P,
    twoShortAddLongRoot P, -twoShortAddLongRoot P,
    threeShortAddLongRoot P, -threeShortAddLongRoot P,
    threeShortAddTwoLongRoot P, -threeShortAddTwoLongRoot P ]

Depends on / 依赖: longRoot, shortAddLongRoot, shortRoot, threeShortAddLongRoot, threeShortAddTwoLongRoot, twoShortAddLongRoot
-/
abbrev allRoots : List M :=
  [ longRoot P, -longRoot P,
    shortRoot P, -shortRoot P,
    shortAddLongRoot P, -shortAddLongRoot P,
    twoShortAddLongRoot P, -twoShortAddLongRoot P,
    threeShortAddLongRoot P, -threeShortAddLongRoot P,
    threeShortAddTwoLongRoot P, -threeShortAddTwoLongRoot P ]

/--
lemma `allRoots_subset_range_root` / 引理 `allRoots_subset_range_root`

English:
lemma allRoots_subset_range_root
  given: [DecidableEq M]
  proof: by
  intro x hx
  simp only [toFinset_cons, toFinset_nil, insert_empty_eq, Finset.coe_insert,
    Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

中文:
引理 allRoots_subset_range_root
  条件: [DecidableEq M]
  证明: by
  intro x hx
  simp only [toFinset_cons, toFinset_nil, insert_empty_eq, Finset.coe_insert,
    Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

Depends on / 依赖: Finset, Finset.coe_insert, Finset.coe_singleton, coe_insert, coe_singleton, insert_empty_eq, mem_insert_iff, mem_singleton_iff, toFinset_cons, toFinset_nil
-/
lemma allRoots_subset_range_root [DecidableEq M] :
    ↑(allRoots P).toFinset subseteq range P.root := by
  intro x hx
  simp only [toFinset_cons, toFinset_nil, insert_empty_eq, Finset.coe_insert,
    Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

variable [Finite ι] [CharZero R] [IsDomain R]

@[simp]
/--
lemma `pairingIn_short_long` / 引理 `pairingIn_short_long`

English:
lemma pairingIn_short_long
  proof: by
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed (long P) (short P)
  aesop

@[simp]

中文:
引理 pairingIn_short_long
  证明: by
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed (long P) (short P)
  aesop

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.measure, P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, infer_instance, measure, pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed
-/
lemma pairingIn_short_long :
    P.pairingIn Int (short P) (long P) = -1 := by
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed (long P) (short P)
  aesop

@[simp]
/--
lemma `pairing_short_long` / 引理 `pairing_short_long`

English:
lemma pairing_short_long
  proof: by
  rw [← P.algebraMap_pairingIn Int]; rw [pairingIn_short_long]
  simp

中文:
引理 pairing_short_long
  证明: by
  rw [← P.algebraMap_pairingIn Int]; rw [pairingIn_short_long]
  simp

Depends on / 依赖: AlternatingMap, AlternatingMap.measure, P.algebraMap_pairingIn, algebraMap_pairingIn, infer_instance, measure, pairingIn_short_long
-/
lemma pairing_short_long :
    P.pairing (short P) (long P) = -1 := by
  rw [← P.algebraMap_pairingIn Int]; rw [pairingIn_short_long]
  simp

/--
lemma `shortAddLongRoot_eq` / 引理 `shortAddLongRoot_eq`

English:
lemma shortAddLongRoot_eq
  proof: by
  simp [shortAddLongRoot, shortAddLong, reflection_apply_root]

中文:
引理 shortAddLongRoot_eq
  证明: by
  simp [shortAddLongRoot, shortAddLong, reflection_apply_root]

Depends on / 依赖: reflection_apply_root, shortAddLong, shortAddLongRoot
-/
lemma shortAddLongRoot_eq :
    shortAddLongRoot P = shortRoot P + longRoot P := by
  simp [shortAddLongRoot, shortAddLong, reflection_apply_root]

/--
lemma `twoShortAddLongRoot_eq` / 引理 `twoShortAddLongRoot_eq`

English:
lemma twoShortAddLongRoot_eq
  proof: by
  simp [twoShortAddLongRoot, twoShortAddLong, reflection_apply_root]
  module

omit [Finite ι] [CharZero R] [IsDomain R] in

中文:
引理 twoShortAddLongRoot_eq
  证明: by
  simp [twoShortAddLongRoot, twoShortAddLong, reflection_apply_root]
  module

omit [Finite ι] [CharZero R] [IsDomain R] in

Depends on / 依赖: module, reflection_apply_root, twoShortAddLong, twoShortAddLongRoot
-/
lemma twoShortAddLongRoot_eq :
    twoShortAddLongRoot P = (2 : R) • shortRoot P + longRoot P := by
  simp [twoShortAddLongRoot, twoShortAddLong, reflection_apply_root]
  module

omit [Finite ι] [CharZero R] [IsDomain R] in
/--
lemma `threeShortAddLongRoot_eq` / 引理 `threeShortAddLongRoot_eq`

English:
lemma threeShortAddLongRoot_eq
  proof: by
  simp [threeShortAddLongRoot, threeShortAddLong, reflection_apply_root]
  module

中文:
引理 threeShortAddLongRoot_eq
  证明: by
  simp [threeShortAddLongRoot, threeShortAddLong, reflection_apply_root]
  module

Depends on / 依赖: module, reflection_apply_root, threeShortAddLong, threeShortAddLongRoot
-/
lemma threeShortAddLongRoot_eq :
    threeShortAddLongRoot P = (3 : R) • shortRoot P + longRoot P := by
  simp [threeShortAddLongRoot, threeShortAddLong, reflection_apply_root]
  module

/--
lemma `threeShortAddTwoLongRoot_eq` / 引理 `threeShortAddTwoLongRoot_eq`

English:
lemma threeShortAddTwoLongRoot_eq
  proof: by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong, reflection_apply_root]
  module

中文:
引理 threeShortAddTwoLongRoot_eq
  证明: by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong, reflection_apply_root]
  module

Depends on / 依赖: module, reflection_apply_root, threeShortAddTwoLong, threeShortAddTwoLongRoot
-/
lemma threeShortAddTwoLongRoot_eq :
    threeShortAddTwoLongRoot P = (3 : R) • shortRoot P + (2 : R) • longRoot P := by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong, reflection_apply_root]
  module

/--
lemma `linearIndependent_short_long` / 引理 `linearIndependent_short_long`

English:
lemma linearIndependent_short_long
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [P.linearIndependent_iff_coxeterWeightIn_ne_four Int, coxeterWeightIn]

中文:
引理 linearIndependent_short_long
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [P.linearIndependent_iff_coxeterWeightIn_ne_four Int, coxeterWeightIn]

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, P.linearIndependent_iff_coxeterWeightIn_ne_four, P.toLinearMap, coxeterWeightIn, linearIndependent_iff_coxeterWeightIn_ne_four, of_isPerfPair, toLinearMap
-/
lemma linearIndependent_short_long :
    LinearIndependent R ![shortRoot P, longRoot P] := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [P.linearIndependent_iff_coxeterWeightIn_ne_four Int, coxeterWeightIn]

/--
Definition of `allCoeffs` / `allCoeffs` 的定义

English:
abbreviation allCoeffs
  signature: : List (Fin 2 -> Int)
  body: [![0, 1], ![0, -1], ![1, 0], ![-1, 0], ![1, 1], ![-1, -1],
    ![2, 1], ![-2, -1], ![3, 1], ![-3, -1], ![3, 2], ![-3, -2]]

中文:
缩写 allCoeffs
  签名: : List (Fin 2 -> 整数)
  定义体: [![0, 1], ![0, -1], ![1, 0], ![-1, 0], ![1, 1], ![-1, -1],
    ![2, 1], ![-2, -1], ![3, 1], ![-3, -1], ![3, 2], ![-3, -2]]
-/
abbrev allCoeffs : List (Fin 2 -> Int) :=
  [![0, 1], ![0, -1], ![1, 0], ![-1, 0], ![1, 1], ![-1, -1],
    ![2, 1], ![-2, -1], ![3, 1], ![-3, -1], ![3, 2], ![-3, -2]]

/--
lemma `allRoots_eq_map_allCoeffs` / 引理 `allRoots_eq_map_allCoeffs`

English:
lemma allRoots_eq_map_allCoeffs
  proof: by
  simp [Fintype.linearCombination_apply, neg_add, -neg_add_rev, shortAddLongRoot_eq,
    twoShortAddLongRoot_eq, threeShortAddLongRoot_eq, threeShortAddTwoLongRoot_eq,
    ← Int.cast_smul_eq_zsmul R]

中文:
引理 allRoots_eq_map_allCoeffs
  证明: by
  simp [Fintype.linearCombination_apply, neg_add, -neg_add_rev, shortAddLongRoot_eq,
    twoShortAddLongRoot_eq, threeShortAddLongRoot_eq, threeShortAddTwoLongRoot_eq,
    ← Int.cast_smul_eq_zsmul R]

Depends on / 依赖: Fintype, Fintype.linearCombination_apply, Int.cast_smul_eq_zsmul, cast_smul_eq_zsmul, linearCombination_apply, neg_add, neg_add_rev, shortAddLongRoot_eq, threeShortAddLongRoot_eq, threeShortAddTwoLongRoot_eq, twoShortAddLongRoot_eq
-/
lemma allRoots_eq_map_allCoeffs :
    allRoots P = allCoeffs.map (Fintype.linearCombination Int ![shortRoot P, longRoot P]) := by
  simp [Fintype.linearCombination_apply, neg_add, -neg_add_rev, shortAddLongRoot_eq,
    twoShortAddLongRoot_eq, threeShortAddLongRoot_eq, threeShortAddTwoLongRoot_eq,
    ← Int.cast_smul_eq_zsmul R]

/--
lemma `allRoots_nodup` / 引理 `allRoots_nodup`

English:
lemma allRoots_nodup
  statement: (allRoots P).Nodup
  proof: by
  have hli : Injective (Fintype.linearCombination Int ![shortRoot P, longRoot P]) := by
    rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    exact (linearIndependent_short_long P).restrict_scalars' Int
  rw [allRoots_eq_map_allCoeffs]; rw [nodup_map_iff hli]
  decide

中文:
引理 allRoots_nodup
  结论: (allRoots P).Nodup
  证明: by
  have hli : Injective (Fintype.linearCombination Int ![shortRoot P, longRoot P]) := by
    rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    exact (linearIndependent_short_long P).restrict_scalars' Int
  rw [allRoots_eq_map_allCoeffs]; rw [nodup_map_iff hli]
  decide

Depends on / 依赖: Fintype, Fintype.linearCombination, Injective, allRoots_eq_map_allCoeffs, linearCombination, linearIndependent_iff_injective_fintypeLinearCombination, linearIndependent_short_long, longRoot, nodup_map_iff, restrict_scalars, shortRoot
-/
lemma allRoots_nodup : (allRoots P).Nodup := by
  have hli : Injective (Fintype.linearCombination Int ![shortRoot P, longRoot P]) := by
    rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    exact (linearIndependent_short_long P).restrict_scalars' Int
  rw [allRoots_eq_map_allCoeffs]; rw [nodup_map_iff hli]
  decide

/--
lemma `mem_span_of_mem_allRoots` / 引理 `mem_span_of_mem_allRoots`

English:
lemma mem_span_of_mem_allRoots
  given: {x : M} (hx : x in allRoots P)
  proof: by
  have : {longRoot P, shortRoot P} = range ![shortRoot P, longRoot P] := by simp
  simp_rw [this, Submodule.mem_span_range_iff_exists_fun, ← Fintype.linearCombination_apply]
  simp [allRoots_eq_map_allCoeffs] at hx
  tauto

中文:
引理 mem_span_of_mem_allRoots
  条件: {x : M} (hx : x in allRoots P)
  证明: by
  have : {longRoot P, shortRoot P} = range ![shortRoot P, longRoot P] := by simp
  simp_rw [this, Submodule.mem_span_range_iff_exists_fun, ← Fintype.linearCombination_apply]
  simp [allRoots_eq_map_allCoeffs] at hx
  tauto

Depends on / 依赖: Fintype, Fintype.linearCombination_apply, Submodule, Submodule.mem_span_range_iff_exists_fun, allRoots_eq_map_allCoeffs, linearCombination_apply, longRoot, mem_span_range_iff_exists_fun, shortRoot, simp_rw
-/
lemma mem_span_of_mem_allRoots {x : M} (hx : x in allRoots P) :
    x in span Int {longRoot P, shortRoot P} := by
  have : {longRoot P, shortRoot P} = range ![shortRoot P, longRoot P] := by simp
  simp_rw [this, Submodule.mem_span_range_iff_exists_fun, ← Fintype.linearCombination_apply]
  simp [allRoots_eq_map_allCoeffs] at hx
  tauto

section InvariantForm

variable {P}
variable (B : P.InvariantForm)

/--
lemma `long_eq_three_mul_short` / 引理 `long_eq_three_mul_short`

English:
lemma long_eq_three_mul_short
  proof: by
  simpa using B.pairing_mul_eq_pairing_mul_swap (long P) (short P)

omit [Finite ι] [CharZero R] [IsDomain R]

中文:
引理 long_eq_three_mul_short
  证明: by
  simpa using B.pairing_mul_eq_pairing_mul_swap (long P) (short P)

omit [Finite ι] [CharZero R] [IsDomain R]

Depends on / 依赖: B.pairing_mul_eq_pairing_mul_swap, pairing_mul_eq_pairing_mul_swap
-/
lemma long_eq_three_mul_short :
    B.form (longRoot P) (longRoot P) = 3 * B.form (shortRoot P) (shortRoot P) := by
  simpa using B.pairing_mul_eq_pairing_mul_swap (long P) (short P)

omit [Finite ι] [CharZero R] [IsDomain R]

/--
lemma `shortAddLongRoot_shortRoot` / 引理 `shortAddLongRoot_shortRoot`

English:
lemma shortAddLongRoot_shortRoot
  proof: by
  simp [shortAddLongRoot, shortAddLong]

中文:
引理 shortAddLongRoot_shortRoot
  证明: by
  simp [shortAddLongRoot, shortAddLong]
-/
@[simp] lemma shortAddLongRoot_shortRoot :
    B.form (shortAddLongRoot P) (shortAddLongRoot P) = B.form (shortRoot P) (shortRoot P) := by
  simp [shortAddLongRoot, shortAddLong]

/--
lemma `twoShortAddLongRoot_shortRoot` / 引理 `twoShortAddLongRoot_shortRoot`

English:
lemma twoShortAddLongRoot_shortRoot
  proof: by
  simp [twoShortAddLongRoot, twoShortAddLong]

中文:
引理 twoShortAddLongRoot_shortRoot
  证明: by
  simp [twoShortAddLongRoot, twoShortAddLong]
-/
@[simp] lemma twoShortAddLongRoot_shortRoot :
    B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P) =
      B.form (shortRoot P) (shortRoot P) := by
  simp [twoShortAddLongRoot, twoShortAddLong]

/--
lemma `threeShortAddLongRoot_longRoot` / 引理 `threeShortAddLongRoot_longRoot`

English:
lemma threeShortAddLongRoot_longRoot
  proof: by
  simp [threeShortAddLongRoot, threeShortAddLong]

中文:
引理 threeShortAddLongRoot_longRoot
  证明: by
  simp [threeShortAddLongRoot, threeShortAddLong]
-/
@[simp] lemma threeShortAddLongRoot_longRoot :
    B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P) =
      B.form (longRoot P) (longRoot P) := by
  simp [threeShortAddLongRoot, threeShortAddLong]

/--
lemma `threeShortAddTwoLongRoot_longRoot` / 引理 `threeShortAddTwoLongRoot_longRoot`

English:
lemma threeShortAddTwoLongRoot_longRoot
  proof: by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong]

中文:
引理 threeShortAddTwoLongRoot_longRoot
  证明: by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong]
-/
@[simp] lemma threeShortAddTwoLongRoot_longRoot :
    B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P) =
      B.form (longRoot P) (longRoot P) := by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong]

end InvariantForm

section Pairing

variable (i : ι)

/--
lemma `pairingIn_shortAddLong_left` / 引理 `pairingIn_shortAddLong_left`

English:
lemma pairingIn_shortAddLong_left
  proof: by
  rw [pairingIn_eq_add_of_root_eq_add (shortAddLongRoot_eq P)]

中文:
引理 pairingIn_shortAddLong_left
  证明: by
  rw [pairingIn_eq_add_of_root_eq_add (shortAddLongRoot_eq P)]
-/
@[simp] lemma pairingIn_shortAddLong_left :
    P.pairingIn Int (shortAddLong P) i = P.pairingIn Int (short P) i + P.pairingIn Int (long P) i := by
  rw [pairingIn_eq_add_of_root_eq_add (shortAddLongRoot_eq P)]

/--
lemma `pairingIn_shortAddLong_right` / 引理 `pairingIn_shortAddLong_right`

English:
lemma pairingIn_shortAddLong_right
  proof: by
  suffices P.pairing i (shortAddLong P) = P.pairing i (short P) + 3 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  apply mul_right_c

中文:
引理 pairingIn_shortAddLong_right
  证明: by
  suffices P.pairing i (shortAddLong P) = P.pairing i (short P) + 3 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  apply mul_right_c
-/
@[simp] lemma pairingIn_shortAddLong_right :
    P.pairingIn Int i (shortAddLong P) =
      P.pairingIn Int i (short P) + 3 * P.pairingIn Int i (long P) := by
  suffices P.pairing i (shortAddLong P) = P.pairing i (short P) + 3 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero (shortAddLong P))
  calc P.pairing i (shortAddLong P) * B.form (P.root (shortAddLong P)) (P.root (shortAddLong P))
    _ = 2 * B.form (P.root i) (shortAddLongRoot P) := ?_
    _ = 2 * B.form (P.root i) (shortRoot P) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = P.pairing i (short P) * B.form (shortRoot P) (shortRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + 3 * P.pairing i (long P)) *
          B.form (shortAddLongRoot P) (shortAddLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [shortAddLongRoot_eq, map_add, mul_add]
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root]
  · rw [long_eq_three_mul_short, shortAddLongRoot_shortRoot]; ring

/--
lemma `pairingIn_twoShortAddLong_left` / 引理 `pairingIn_twoShortAddLong_left`

English:
lemma pairingIn_twoShortAddLong_left
  proof: by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 2) (y := 1) (i := short P) (l := long P)]
  · simp
  · simp only [twoShortAddLongRoot_eq, one_smul, add_left_inj]
    norm_cast

中文:
引理 pairingIn_twoShortAddLong_left
  证明: by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 2) (y := 1) (i := short P) (l := long P)]
  · simp
  · simp only [twoShortAddLongRoot_eq, one_smul, add_left_inj]
    norm_cast
-/
@[simp] lemma pairingIn_twoShortAddLong_left :
    P.pairingIn Int (twoShortAddLong P) i =
      2 * P.pairingIn Int (short P) i + P.pairingIn Int (long P) i := by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 2) (y := 1) (i := short P) (l := long P)]
  · simp
  · simp only [twoShortAddLongRoot_eq, one_smul, add_left_inj]
    norm_cast

/--
lemma `pairingIn_twoShortAddLong_right` / 引理 `pairingIn_twoShortAddLong_right`

English:
lemma pairingIn_twoShortAddLong_right
  proof: by
  suffices P.pairing i (twoShortAddLong P) =
      2 * P.pairing i (short P) + 3 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  appl

中文:
引理 pairingIn_twoShortAddLong_right
  证明: by
  suffices P.pairing i (twoShortAddLong P) =
      2 * P.pairing i (short P) + 3 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  appl
-/
@[simp] lemma pairingIn_twoShortAddLong_right :
    P.pairingIn Int i (twoShortAddLong P) =
      2 * P.pairingIn Int i (short P) + 3 * P.pairingIn Int i (long P) := by
  suffices P.pairing i (twoShortAddLong P) =
      2 * P.pairing i (short P) + 3 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| twoShortAddLong P)
  calc P.pairing i (twoShortAddLong P) * B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P)
    _ = 2 * B.form (P.root i) (twoShortAddLongRoot P) := ?_
    _ = 2 * (2 * B.form (P.root i) (shortRoot P)) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = 2 * P.pairing i (short P) * B.form (shortRoot P) (shortRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (2 * P.pairing i (short P) +
          3 * P.pairing i (long P)) * B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [twoShortAddLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, mul_assoc]
  · rw [long_eq_three_mul_short, twoShortAddLongRoot_shortRoot]; ring

omit [Finite ι] [IsDomain R] in
/--
lemma `pairingIn_threeShortAddLong_left` / 引理 `pairingIn_threeShortAddLong_left`

English:
lemma pairingIn_threeShortAddLong_left
  proof: by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 3) (y := 1) (i := short P) (l := long P)]
  · simp
  · simp only [threeShortAddLongRoot_eq, one_smul, add_left_inj]
    norm_cast

中文:
引理 pairingIn_threeShortAddLong_left
  证明: by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 3) (y := 1) (i := short P) (l := long P)]
  · simp
  · simp only [threeShortAddLongRoot_eq, one_smul, add_left_inj]
    norm_cast
-/
@[simp] lemma pairingIn_threeShortAddLong_left :
    P.pairingIn Int (threeShortAddLong P) i =
      3 * P.pairingIn Int (short P) i + P.pairingIn Int (long P) i := by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 3) (y := 1) (i := short P) (l := long P)]
  · simp
  · simp only [threeShortAddLongRoot_eq, one_smul, add_left_inj]
    norm_cast

/--
lemma `pairingIn_threeShortAddLong_right` / 引理 `pairingIn_threeShortAddLong_right`

English:
lemma pairingIn_threeShortAddLong_right
  proof: by
  suffices P.pairing i (threeShortAddLong P) =
      P.pairing i (short P) + P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  apply mul_

中文:
引理 pairingIn_threeShortAddLong_right
  证明: by
  suffices P.pairing i (threeShortAddLong P) =
      P.pairing i (short P) + P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  apply mul_
-/
@[simp] lemma pairingIn_threeShortAddLong_right :
    P.pairingIn Int i (threeShortAddLong P) =
      P.pairingIn Int i (short P) + P.pairingIn Int i (long P) := by
  suffices P.pairing i (threeShortAddLong P) =
      P.pairing i (short P) + P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| threeShortAddLong P)
  calc P.pairing i (threeShortAddLong P) *
          B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P)
    _ = 2 * B.form (P.root i) (threeShortAddLongRoot P) := ?_
    _ = 3 * (2 * B.form (P.root i) (shortRoot P)) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = P.pairing i (short P) * B.form (longRoot P) (longRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + P.pairing i (long P)) *
          B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [threeShortAddLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]; ring
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
  · rw [threeShortAddLongRoot_longRoot]; ring

/--
lemma `pairingIn_threeShortAddTwoLong_left` / 引理 `pairingIn_threeShortAddTwoLong_left`

English:
lemma pairingIn_threeShortAddTwoLong_left
  proof: by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 3) (y := 2) (i := short P) (l := long P)]
  · simp
  · simp only [threeShortAddTwoLongRoot_eq]
    norm_cast

中文:
引理 pairingIn_threeShortAddTwoLong_left
  证明: by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 3) (y := 2) (i := short P) (l := long P)]
  · simp
  · simp only [threeShortAddTwoLongRoot_eq]
    norm_cast
-/
@[simp] lemma pairingIn_threeShortAddTwoLong_left :
    P.pairingIn Int (threeShortAddTwoLong P) i =
      3 * P.pairingIn Int (short P) i + 2 * P.pairingIn Int (long P) i := by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 3) (y := 2) (i := short P) (l := long P)]
  · simp
  · simp only [threeShortAddTwoLongRoot_eq]
    norm_cast

/--
lemma `pairingIn_threeShortAddTwoLong_right` / 引理 `pairingIn_threeShortAddTwoLong_right`

English:
lemma pairingIn_threeShortAddTwoLong_right
  proof: by
  suffices P.pairing i (threeShortAddTwoLong P) =
      P.pairing i (short P) + 2 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  app

中文:
引理 pairingIn_threeShortAddTwoLong_right
  证明: by
  suffices P.pairing i (threeShortAddTwoLong P) =
      P.pairing i (short P) + 2 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  app
-/
@[simp] lemma pairingIn_threeShortAddTwoLong_right :
    P.pairingIn Int i (threeShortAddTwoLong P) =
      P.pairingIn Int i (short P) + 2 * P.pairingIn Int i (long P) := by
  suffices P.pairing i (threeShortAddTwoLong P) =
      P.pairing i (short P) + 2 * P.pairing i (long P) from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| threeShortAddTwoLong P)
  calc P.pairing i (threeShortAddTwoLong P) *
          B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P)
    _ = 2 * B.form (P.root i) (threeShortAddTwoLongRoot P) := ?_
    _ = 3 * (2 * B.form (P.root i) (shortRoot P)) + 2 * (2 * B.form (P.root i) (longRoot P)) := ?_
    _ = P.pairing i (short P) * B.form (longRoot P) (longRoot P) +
          2 * P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + 2 * P.pairing i (long P)) *
          B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · simp only [threeShortAddTwoLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]; ring
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
  · rw [threeShortAddTwoLongRoot_longRoot]; ring

end Pairing

/--
lemma `isOrthogonal_short_and_long_aux` / 引理 `isOrthogonal_short_and_long_aux`

English:
lemma isOrthogonal_short_and_long_aux
  statement: {a b c d e f a' b' c' d' e' f' : Int} {S : Set (Int × Int)}
  proof: by
  simp [S_def] at ha hb hc hd he hf
  omega

中文:
引理 isOrthogonal_short_and_long_aux
  结论: {a b c d e f a' b' c' d' e' f' : 整数} {S : Set (整数 × 整数)}
  证明: by
  simp [S_def] at ha hb hc hd he hf
  omega
-/
private lemma isOrthogonal_short_and_long_aux {a b c d e f a' b' c' d' e' f' : Int} {S : Set (Int × Int)}
    (S_def : S = {(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1),
      (-1, -3), (-3, -1)})
    (ha : (a, a') in S)
    (hb : (b, b') in S)
    (hc : (c, c') in S)
    (hd : (d, d') in S)
    (he : (e, e') in S)
    (hf : (f, f') in S)
    (h₁ : c = a + 3 * b)
    (h₂ : c' = a' + b')
    (h₃ : d = 2 * a + 3 * b)
    (h₄ : d' = 2 * a' + b')
    (h₅ : e = a + b)
    (h₆ : e' = 3 * a' + b')
    (h₇ : f = a + 2 * b)
    (h₈ : f' = 3 * a' + 2 * b') :
    a = 0 ∧ b = 0 := by
  simp [S_def] at ha hb hc hd he hf
  omega

/--
lemma `isOrthogonal_short_and_long` / 引理 `isOrthogonal_short_and_long`

English:
lemma isOrthogonal_short_and_long
  given: {i : ι} (hi : P.root i ∉ allRoots P)
  proof: by
  suffices P.pairingIn Int i (short P) = 0 ∧ P.pairingIn Int i (long P) = 0 by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    simpa [isOrthogonal_iff_pairing_eq_zero, ← P.algebraMap_pairingIn Int]
  simp only [mem_cons, not_mem_nil, or_false, not_or] at hi
  obtain ⟨h₁, h₂,

中文:
引理 isOrthogonal_short_and_long
  条件: {i : ι} (hi : P.root i ∉ allRoots P)
  证明: by
  suffices P.pairingIn Int i (short P) = 0 ∧ P.pairingIn Int i (long P) = 0 by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    simpa [isOrthogonal_iff_pairing_eq_zero, ← P.algebraMap_pairingIn Int]
  simp only [mem_cons, not_mem_nil, or_false, not_or] at hi
  obtain ⟨h₁, h₂,

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, P.algebraMap_pairingIn, P.pairingIn, P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, P.toLinearMap, algebraMap_pairingIn, isOrthogonal_iff_pairing_eq_zero, mem_cons, not_mem_nil, not_or, of_isPerfPair, or_false, pairingIn, pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, toLinearMap
-/
lemma isOrthogonal_short_and_long {i : ι} (hi : P.root i ∉ allRoots P) :
    P.IsOrthogonal i (short P) ∧ P.IsOrthogonal i (long P) := by
  suffices P.pairingIn Int i (short P) = 0 ∧ P.pairingIn Int i (long P) = 0 by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    simpa [isOrthogonal_iff_pairing_eq_zero, ← P.algebraMap_pairingIn Int]
  simp only [mem_cons, not_mem_nil, or_false, not_or] at hi
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := hi
  have ha := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (short P) ‹_› ‹_›
  have hb := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (long P) ‹_› ‹_›
  have hc := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (shortAddLong P) ‹_› ‹_›
  have hd := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (twoShortAddLong P) ‹_› ‹_›
  have he := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (threeShortAddLong P) ‹_› ‹_›
  have hf := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (threeShortAddTwoLong P) ‹_› ‹_›
  apply isOrthogonal_short_and_long_aux rfl ha hb hc hd he hf <;> simp

section IsIrreducible

variable [P.IsIrreducible]

/--
lemma `span_eq_top` / 引理 `span_eq_top`

English:
lemma span_eq_top
  proof: by
  have := P.span_root_image_eq_top_of_forall_orthogonal {long P, short P} (by simp)
  rw [show P.root '' {long P]; rw [short P} = {longRoot P]; rw [shortRoot P} by aesop] at this
  refine this fun k hk ij hij => ?_
  replace hk : P.root k ∉ allRoots P :=
fun contra => hk span_subset_span Int _ _ 

中文:
引理 span_eq_top
  证明: by
  have := P.span_root_image_eq_top_of_forall_orthogonal {long P, short P} (by simp)
  rw [show P.root '' {long P]; rw [short P} = {longRoot P]; rw [shortRoot P} by aesop] at this
  refine this fun k hk ij hij => ?_
  replace hk : P.root k ∉ allRoots P :=
fun contra => hk span_subset_span Int _ _ 
-/
@[simp] lemma span_eq_top :
    span R {longRoot P, shortRoot P} = ⊤ := by
  have := P.span_root_image_eq_top_of_forall_orthogonal {long P, short P} (by simp)
  rw [show P.root '' {long P]; rw [short P} = {longRoot P]; rw [shortRoot P} by aesop] at this
  refine this fun k hk ij hij => ?_
  replace hk : P.root k ∉ allRoots P :=
fun contra => hk span_subset_span Int _ _ mem_span_of_mem_allRoots P contra
  have aux := isOrthogonal_short_and_long P hk
  rcases hij with rfl | rfl <;> tauto

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : Module.Basis (Fin 2) R M
  body: have : LinearIndependent R ![EmbeddedG2.shortRoot P, EmbeddedG2.longRoot P] := by
    have := pairing_long_short P
    refine (IsReduced.linearIndependent_iff P).mpr ⟨fun h => ?_, fun h => ?_⟩
    · norm_num [h] at this
    · simp only [root_eq_neg_iff] at h
      norm_num [h] at this
  Module.Basis

中文:
定义 basis
  签名: : Module.Basis (Fin 2) R M
  定义体: have : LinearIndependent R ![EmbeddedG2.shortRoot P, EmbeddedG2.longRoot P] := by
    have := pairing_long_short P
    refine (IsReduced.linearIndependent_iff P).mpr ⟨fun h => ?_, fun h => ?_⟩
    · norm_num [h] at this
    · simp only [root_eq_neg_iff] at h
      norm_num [h] at this
  Module.Basis

Depends on / 依赖: EmbeddedG2, EmbeddedG2.longRoot, EmbeddedG2.shortRoot, IsReduced, IsReduced.linearIndependent_iff, LinearIndependent, Module, Module.Basis.mk, linearIndependent_iff, longRoot, pairing_long_short, root_eq_neg_iff, shortRoot
-/
def basis : Module.Basis (Fin 2) R M :=
  have : LinearIndependent R ![EmbeddedG2.shortRoot P, EmbeddedG2.longRoot P] := by
    have := pairing_long_short P
    refine (IsReduced.linearIndependent_iff P).mpr ⟨fun h => ?_, fun h => ?_⟩
    · norm_num [h] at this
    · simp only [root_eq_neg_iff] at h
      norm_num [h] at this
  Module.Basis.mk this (by simp)

/--
lemma `mem_allRoots` / 引理 `mem_allRoots`

English:
lemma mem_allRoots
  given: (i : ι)
  proof: by
  by_contra hi
  obtain ⟨h₁, h₂⟩ := isOrthogonal_short_and_long P hi
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [isOrthogonal_iff_pairing_eq_zero]; rw [← B.apply_root_root_zero_iff] 

中文:
引理 mem_allRoots
  条件: (i : ι)
  证明: by
  by_contra hi
  obtain ⟨h₁, h₂⟩ := isOrthogonal_short_and_long P hi
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [isOrthogonal_iff_pairing_eq_zero]; rw [← B.apply_root_root_zero_iff] 

Depends on / 依赖: B.apply_root_root_zero_iff, B.form, Fintype, Fintype.ofFinite, IsReflexive, LinearMap, LinearMap.zero_apply, Module, Module.IsReflexive, P.posRootForm, P.root, P.toLinearMap, Submodule, Submodule.span_induction, apply_root_root_zero_iff, isOrthogonal_iff_pairing_eq_zero, isOrthogonal_short_and_long, longRoot, ofFinite, of_isPerfPair
-/
lemma mem_allRoots (i : ι) :
    P.root i in allRoots P := by
  by_contra hi
  obtain ⟨h₁, h₂⟩ := isOrthogonal_short_and_long P hi
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [isOrthogonal_iff_pairing_eq_zero]; rw [← B.apply_root_root_zero_iff] at h₁ h₂
  have key : B.form (P.root i) = 0 := by
    ext x
    have hx : x in span R {longRoot P, shortRoot P} := by simp
    simp only [LinearMap.zero_apply]
    induction hx using Submodule.span_induction with
    | zero => simp
    | mem => grind
    | add => simp_all
    | smul => simp_all
  simpa using LinearMap.congr_fun key (P.root i)

open scoped Classical in
/--
Definition of `indexEquivAllRoots` / `indexEquivAllRoots` 的定义

English:
definition indexEquivAllRoots
  signature: : ι ≃ (allRoots P).toFinset
  body: { toFun i := ⟨P.root i, List.mem_toFinset.mpr <| mem_allRoots P i⟩
    invFun x := (allRoots_subset_range_root P x.property).choose
    left_inv i := by simp
    right_inv := by
      rintro ⟨x, hx⟩
      simp only [Subtype.mk.injEq]
      exact (allRoots_subset_range_root P hx).choose_spec }

inclu

中文:
定义 indexEquivAllRoots
  签名: : ι ≃ (allRoots P).toFinset
  定义体: { toFun i := ⟨P.root i, List.mem_toFinset.mpr <| mem_allRoots P i⟩
    invFun x := (allRoots_subset_range_root P x.property).choose
    left_inv i := by simp
    right_inv := by
      rintro ⟨x, hx⟩
      simp only [Subtype.mk.injEq]
      exact (allRoots_subset_range_root P hx).choose_spec }

inclu
-/
@[simps] def indexEquivAllRoots : ι ≃ (allRoots P).toFinset :=
  { toFun i := ⟨P.root i, List.mem_toFinset.mpr <| mem_allRoots P i⟩
    invFun x := (allRoots_subset_range_root P x.property).choose
    left_inv i := by simp
    right_inv := by
      rintro ⟨x, hx⟩
      simp only [Subtype.mk.injEq]
      exact (allRoots_subset_range_root P hx).choose_spec }

include P in
/--
lemma `card_index_eq_twelve` / 引理 `card_index_eq_twelve`

English:
lemma card_index_eq_twelve
  proof: by
  classical
  have : Nat.card (allRoots P).toFinset = 12 := by
    rw [Nat.card_eq_fintype_card]; rw [Fintype.card_coe]; rw [toFinset_card_of_nodup (allRoots_nodup P)]
    simp
  rw [← this]
exact Nat.card_congr indexEquivAllRoots P

中文:
引理 card_index_eq_twelve
  证明: by
  classical
  have : Nat.card (allRoots P).toFinset = 12 := by
    rw [Nat.card_eq_fintype_card]; rw [Fintype.card_coe]; rw [toFinset_card_of_nodup (allRoots_nodup P)]
    simp
  rw [← this]
exact Nat.card_congr indexEquivAllRoots P

Depends on / 依赖: Fintype, Fintype.card_coe, Nat.card, Nat.card_congr, Nat.card_eq_fintype_card, allRoots, allRoots_nodup, card_coe, card_congr, card_eq_fintype_card, classical, indexEquivAllRoots, toFinset, toFinset_card_of_nodup
-/
lemma card_index_eq_twelve :
    Nat.card ι = 12 := by
  classical
  have : Nat.card (allRoots P).toFinset = 12 := by
    rw [Nat.card_eq_fintype_card]; rw [Fintype.card_coe]; rw [toFinset_card_of_nodup (allRoots_nodup P)]
    simp
  rw [← this]
exact Nat.card_congr indexEquivAllRoots P

/--
lemma `setOfPred_index_eq_univ` / 引理 `setOfPred_index_eq_univ`

English:
lemma setOfPred_index_eq_univ
  proof: P.indexNeg
    { long P, -long P,
      short P, -short P,
      shortAddLong P, -shortAddLong P,
      twoShortAddLong P, -twoShortAddLong P,
      threeShortAddLong P, -threeShortAddLong P,
      threeShortAddTwoLong P, -threeShortAddTwoLong P } = univ :=
  eq_univ_iff_forall.mpr fun i => by simpa

中文:
引理 setOfPred_index_eq_univ
  证明: P.indexNeg
    { long P, -long P,
      short P, -short P,
      shortAddLong P, -shortAddLong P,
      twoShortAddLong P, -twoShortAddLong P,
      threeShortAddLong P, -threeShortAddLong P,
      threeShortAddTwoLong P, -threeShortAddTwoLong P } = univ :=
  eq_univ_iff_forall.mpr fun i => by simpa

Depends on / 依赖: P.indexNeg, indexNeg
-/
lemma setOfPred_index_eq_univ :
    letI _i := P.indexNeg
    { long P, -long P,
      short P, -short P,
      shortAddLong P, -shortAddLong P,
      twoShortAddLong P, -twoShortAddLong P,
      threeShortAddLong P, -threeShortAddLong P,
      threeShortAddTwoLong P, -threeShortAddTwoLong P } = univ :=
  eq_univ_iff_forall.mpr fun i => by simpa using mem_allRoots P i

@[deprecated (since := "2026-07-09")] alias setOf_index_eq_univ := setOfPred_index_eq_univ

end IsIrreducible

end EmbeddedG2

namespace IsG2

variable {P}
variable [P.IsG2] (b : P.Base) [Finite ι] [CharZero R] [IsDomain R]

/--
lemma `card_base_support_eq_two` / 引理 `card_base_support_eq_two`

English:
lemma card_base_support_eq_two
  proof: by
  have _i : P.EmbeddedG2 := toEmbeddedG2 P
  have _i : Nonempty ι := IsG2.nonempty P
  rw [← Fintype.card_fin 2]; rw [← Module.finrank_eq_card_basis (EmbeddedG2.basis P)]; rw [Module.finrank_eq_card_basis b.toWeightBasis]; rw [Fintype.card_coe]

中文:
引理 card_base_support_eq_two
  证明: by
  have _i : P.EmbeddedG2 := toEmbeddedG2 P
  have _i : Nonempty ι := IsG2.nonempty P
  rw [← Fintype.card_fin 2]; rw [← Module.finrank_eq_card_basis (EmbeddedG2.basis P)]; rw [Module.finrank_eq_card_basis b.toWeightBasis]; rw [Fintype.card_coe]
-/
@[simp] lemma card_base_support_eq_two :
    b.support.card = 2 := by
  have _i : P.EmbeddedG2 := toEmbeddedG2 P
  have _i : Nonempty ι := IsG2.nonempty P
  rw [← Fintype.card_fin 2]; rw [← Module.finrank_eq_card_basis (EmbeddedG2.basis P)]; rw [Module.finrank_eq_card_basis b.toWeightBasis]; rw [Fintype.card_coe]

variable {b} in
/--
lemma `span_eq_rootSpan_int` / 引理 `span_eq_rootSpan_int`

English:
lemma span_eq_rootSpan_int
  given: {i j : ι} (hi : i in b.support) (hj : j in b.support) (h_ne : i != j)
  proof: by
  classical
  have : {i, j} subseteq b.support := by grind
  rw [← image_pair]; rw [← Finset.coe_pair]; rw [Finset.eq_of_subset_of_card_le this (by aesop)]; rw [b.span_int_root_support]

中文:
引理 span_eq_rootSpan_int
  条件: {i j : ι} (hi : i in b.support) (hj : j in b.support) (h_ne : i != j)
  证明: by
  classical
  have : {i, j} subseteq b.support := by grind
  rw [← image_pair]; rw [← Finset.coe_pair]; rw [Finset.eq_of_subset_of_card_le this (by aesop)]; rw [b.span_int_root_support]

Depends on / 依赖: Finset, Finset.coe_pair, Finset.eq_of_subset_of_card_le, b.span_int_root_support, b.support, classical, coe_pair, eq_of_subset_of_card_le, image_pair, span_int_root_support, subseteq, support
-/
lemma span_eq_rootSpan_int {i j : ι} (hi : i in b.support) (hj : j in b.support) (h_ne : i != j) :
    Submodule.span Int {P.root i, P.root j} = P.rootSpan Int := by
  classical
  have : {i, j} subseteq b.support := by grind
  rw [← image_pair]; rw [← Finset.coe_pair]; rw [Finset.eq_of_subset_of_card_le this (by aesop)]; rw [b.span_int_root_support]

end IsG2

end RootPairing
