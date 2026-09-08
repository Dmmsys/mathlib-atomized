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

variable {K ι : Type*} {R : ι → Type*}

@[to_additive]
/-
**smul_pi_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_pi_subset [forall i, SMul K (R i)] (r : K) (s : Set ι) (t : forall i,
 Set (R i)) : r • pi s t subseteq pi s (r • t)
参数：R i；r : K；s : Set ι；t : forall i, Set (R i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piMap_image_pi_subset`：piMap_image_pi_subset {f : forall i, α i -> β
 i} (t : forall i, Set (α i)) : Pi.map f '' s.pi t subseteq s.pi fun i => f i ''
 t i
-/
theorem smul_pi_subset [∀ i, SMul K (R i)] (r : K) (s : Set ι) (t : ∀ i, Set (R i)) :
    r • pi s t ⊆ pi s (r • t) :=
  piMap_image_pi_subset _

@[to_additive]
/-
**smul_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_univ_pi [forall i, SMul K (R i)] (r : K) (t : forall i, Set (R i)) : 
r • pi (univ : Set ι) t = pi (univ : Set ι) (r • t)
参数：R i；r : K；t : forall i, Set (R i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piMap_image_univ_pi`：piMap_image_univ_pi (f : forall i, α i -> β i) 
(t : forall i, Set (α i)) : Pi.map f '' univ.pi t = univ.pi fun i => f i '' t i
-/
theorem smul_univ_pi [∀ i, SMul K (R i)] (r : K) (t : ∀ i, Set (R i)) :
    r • pi (univ : Set ι) t = pi (univ : Set ι) (r • t) :=
  piMap_image_univ_pi _ _

@[to_additive]
/-
**smul_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_pi [Group K] [forall i, MulAction K (R i)] (r : K) (S : Set ι) (t : f
orall i, Set (R i)) : r • S.pi t = S.pi (r • t)
参数：R i；r : K；S : Set ι；t : forall i, Set (R i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piMap_image_pi`：piMap_image_pi {f : forall i, α i -> β i} (hf : fora
ll i ∉ s, Surjective (f i)) (t : forall i, Set (α i)) : Pi.map f '' s.pi t = s.p
i fun i …
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x
-/
theorem smul_pi [Group K] [∀ i, MulAction K (R i)] (r : K) (S : Set ι) (t : ∀ i, Set (R i)) :
    r • S.pi t = S.pi (r • t) :=
  piMap_image_pi (fun _ _ => MulAction.surjective _) _
/-
**smul_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_pi [Group K] [forall i, MulAction K (R i)] (r : K) (S : Set ι) (t : f
orall i, Set (R i)) : r • S.pi t = S.pi (r • t)
参数：R i；r : K；S : Set ι；t : forall i, Set (R i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piMap_image_pi`：piMap_image_pi {f : forall i, α i -> β i} (hf : fora
ll i ∉ s, Surjective (f i)) (t : forall i, Set (α i)) : Pi.map f '' s.pi t = s.p
i fun i …
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x
-/
theorem smul_pi₀ [GroupWithZero K] [∀ i, MulAction K (R i)] {r : K} (S : Set ι) (t : ∀ i, Set (R i))
    (hr : r ≠ 0) : r • S.pi t = S.pi (r • t) :=
  smul_pi (Units.mk0 r hr) S t
