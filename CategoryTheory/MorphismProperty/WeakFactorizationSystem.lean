/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Weak factorization systems

In this file, we introduce the notion of weak factorization system,
which is a property of two classes of morphisms `W₁` and `W₂` in
a category `C`. The type class `IsWeakFactorizationSystem W₁ W₂` asserts
that `W₁` is exactly `W₂.llp`, `W₂` is exactly `W₁.rlp`,
and any morphism in `C` can be factored a `i ≫ p` with `W₁ i` and `W₂ p`.

## References
* https://ncatlab.org/nlab/show/weak+factorization+system

-/

public section

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (W₁ W₂ : MorphismProperty C)

/--
Definition of `IsWeakFactorizationSystem` / `IsWeakFactorizationSystem` 的定义

English:
class IsWeakFactorizationSystem
  parameters: : Prop where
  axioms and operations (3):
    - rlp : W₁.rlp = W₂
    - llp : W₂.llp = W₁
    - hasFactorization : HasFactorization W₁ W₂  [default: by infer_instance]

中文:
类 是WeakFactorizationSystem
  参数: : 命题 where
  公理与运算 (3 个):
    - rlp : W₁.rlp = W₂
    - llp : W₂.llp = W₁
    - hasFactorization : 有分解 W₁ W₂  [默认: by infer_instance]

Depends on / 依赖: WithBotTop, WithBotTop.rec, infer_instance, isGE_of_isZero
-/
class IsWeakFactorizationSystem : Prop where
  rlp : W₁.rlp = W₂
  llp : W₂.llp = W₁
  hasFactorization : HasFactorization W₁ W₂ := by infer_instance

namespace IsWeakFactorizationSystem

attribute [instance] hasFactorization

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  statement: [HasFactorization W₁ W₂]
  proof: rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hp _ _ _ hi => h _ _ hi hp)
  llp := llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hi _ _ _ hp => h _ _ hi hp)

中文:
引理 mk'
  结论: [有分解 W₁ W₂]
  证明: rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hp _ _ _ hi => h _ _ hi hp)
  llp := llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hi _ _ _ hp => h _ _ hi hp)

Depends on / 依赖: rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
-/
lemma mk' [HasFactorization W₁ W₂]
    [W₁.IsStableUnderRetracts] [W₂.IsStableUnderRetracts]
    (h : forall {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),
      W₁ i -> W₂ p -> HasLiftingProperty i p) :
    IsWeakFactorizationSystem W₁ W₂ where
  rlp := rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hp _ _ _ hi => h _ _ hi hp)
  llp := llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
    (fun _ _ _ hi _ _ _ hp => h _ _ hi hp)

end IsWeakFactorizationSystem

section

variable [IsWeakFactorizationSystem W₁ W₂]

/--
lemma `rlp_eq_of_wfs` / 引理 `rlp_eq_of_wfs`

English:
lemma rlp_eq_of_wfs
  statement: W₁.rlp = W₂
  proof: IsWeakFactorizationSystem.rlp

中文:
引理 rlp_eq_of_wfs
  结论: W₁.rlp = W₂
  证明: IsWeakFactorizationSystem.rlp

Depends on / 依赖: IsWeakFactorizationSystem, IsWeakFactorizationSystem.rlp
-/
lemma rlp_eq_of_wfs : W₁.rlp = W₂ := IsWeakFactorizationSystem.rlp

/--
lemma `llp_eq_of_wfs` / 引理 `llp_eq_of_wfs`

English:
lemma llp_eq_of_wfs
  statement: W₂.llp = W₁
  proof: IsWeakFactorizationSystem.llp

中文:
引理 llp_eq_of_wfs
  结论: W₂.llp = W₁
  证明: IsWeakFactorizationSystem.llp

Depends on / 依赖: IsWeakFactorizationSystem, IsWeakFactorizationSystem.llp
-/
lemma llp_eq_of_wfs : W₂.llp = W₁ := IsWeakFactorizationSystem.llp

variable {W₁ W₂} in
/--
lemma `hasLiftingProperty_of_wfs` / 引理 `hasLiftingProperty_of_wfs`

English:
lemma hasLiftingProperty_of_wfs
  statement: {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
  proof: (llp_eq_of_wfs W₁ W₂ ▸ hi) p hp

中文:
引理 hasLiftingProperty_of_wfs
  结论: {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
  证明: (llp_eq_of_wfs W₁ W₂ ▸ hi) p hp

Depends on / 依赖: llp_eq_of_wfs
-/
lemma hasLiftingProperty_of_wfs {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : W₁ i) (hp : W₂ p) : HasLiftingProperty i p :=
  (llp_eq_of_wfs W₁ W₂ ▸ hi) p hp

end

end CategoryTheory.MorphismProperty
