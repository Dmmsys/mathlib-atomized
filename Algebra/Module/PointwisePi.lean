/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Pointwise actions on sets in Pi types

This file contains lemmas about pointwise actions on sets in Pi types.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication, pi

-/

public section

open scoped Pointwise

open Set

variable {K ι : Type*} {R : ι -> Type*}

@[to_additive]
/--
theorem `smul_pi_subset` / 定理 `smul_pi_subset`

English:
theorem smul_pi_subset
  given: [forall i, SMul K (R i)] (r : K) (s : Set ι) (t : forall i, Set (R i))
  proof: piMap_image_pi_subset _

@[to_additive]

中文:
定理 smul_pi_subset
  条件: [对任意 i, SMul K (R i)] (r : K) (s : Set ι) (t : 对任意 i, Set (R i))
  证明: piMap_image_pi_subset _

@[to_additive]

Depends on / 依赖: piMap_image_pi_subset
-/
theorem smul_pi_subset [forall i, SMul K (R i)] (r : K) (s : Set ι) (t : forall i, Set (R i)) :
    r • pi s t subseteq pi s (r • t) :=
  piMap_image_pi_subset _

@[to_additive]
/--
theorem `smul_univ_pi` / 定理 `smul_univ_pi`

English:
theorem smul_univ_pi
  given: [forall i, SMul K (R i)] (r : K) (t : forall i, Set (R i))
  proof: piMap_image_univ_pi _ _

@[to_additive]

中文:
定理 smul_univ_pi
  条件: [对任意 i, SMul K (R i)] (r : K) (t : 对任意 i, Set (R i))
  证明: piMap_image_univ_pi _ _

@[to_additive]

Depends on / 依赖: piMap_image_univ_pi
-/
theorem smul_univ_pi [forall i, SMul K (R i)] (r : K) (t : forall i, Set (R i)) :
    r • pi (univ : Set ι) t = pi (univ : Set ι) (r • t) :=
  piMap_image_univ_pi _ _

@[to_additive]
/--
theorem `smul_pi` / 定理 `smul_pi`

English:
theorem smul_pi
  given: [Group K] [forall i, MulAction K (R i)] (r : K) (S : Set ι) (t : forall i, Set (R i))
  proof: piMap_image_pi (fun _ _ => MulAction.surjective _) _

中文:
定理 smul_pi
  条件: [Group K] [对任意 i, MulAction K (R i)] (r : K) (S : Set ι) (t : 对任意 i, Set (R i))
  证明: piMap_image_pi (fun _ _ => MulAction.surjective _) _

Depends on / 依赖: MulAction, MulAction.surjective, piMap_image_pi, surjective
-/
theorem smul_pi [Group K] [forall i, MulAction K (R i)] (r : K) (S : Set ι) (t : forall i, Set (R i)) :
    r • S.pi t = S.pi (r • t) :=
  piMap_image_pi (fun _ _ => MulAction.surjective _) _

/--
theorem `smul_pi₀` / 定理 `smul_pi₀`

English:
theorem smul_pi₀
  statement: [GroupWithZero K] [forall i, MulAction K (R i)] {r : K} (S : Set ι) (t : forall i, Set (R i))
  proof: smul_pi (Units.mk0 r hr) S t

中文:
定理 smul_pi₀
  结论: [GroupWithZero K] [对任意 i, MulAction K (R i)] {r : K} (S : Set ι) (t : 对任意 i, Set (R i))
  证明: smul_pi (Units.mk0 r hr) S t

Depends on / 依赖: Units.mk0, smul_pi
-/
theorem smul_pi₀ [GroupWithZero K] [forall i, MulAction K (R i)] {r : K} (S : Set ι) (t : forall i, Set (R i))
    (hr : r != 0) : r • S.pi t = S.pi (r • t) :=
  smul_pi (Units.mk0 r hr) S t
