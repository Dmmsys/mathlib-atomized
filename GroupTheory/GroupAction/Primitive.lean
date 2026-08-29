/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Setoid.Partition.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Primitive actions

## Definitions

- `MulAction.IsPreprimitive G X`
  A structure that says that the action of a type `G` on a type `X`
  (defined by an instance `SMul G X`) is *preprimitive*,
  namely, it is pretransitive and the only blocks are ⊤ and subsingletons.
  (The pretransitivity assumption is essentially trivial,
  because orbits are blocks, unless the action itself is trivial.)

  The notion which is introduced in classical books on group theory
  is restricted to group actions.
  In fact, it may be irrelevant if the action is degenerate,
  when “trivial blocks” might not be blocks.
  Moreover, the classical notion is *primitive*,
  which further assumes that `X` is not empty.

- `MulAction.IsQuasiPreprimitive G X`
  A structure that says that the action of the group `G` on the type `X` is *quasipreprimitive*,
  namely, normal subgroups of `G` which act nontrivially act pretransitively.

- We prove some straightforward theorems that relate preprimitivity
  under equivariant maps, for images and preimages.

## Relation with stabilizers

- `MulAction.isSimpleOrderBlockMem_iff_isPreprimitive`
  relates primitivity and the fact that the inclusion order on blocks containing is simple.

- `MulAction.isCoatom_stabilizer_iff_preprimitive`
  An action is preprimitive iff the stabilizers of points are maximal subgroups.

- `MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive`
  Stabilizers of points under a preprimitive action are maximal subgroups.

## Relation with normal subgroups

- `MulAction.IsPreprimitive.isQuasipreprimitive`
  Preprimitive actions are quasipreprimitive.

## Particular results for actions on finite types

- `MulAction.IsPreprimitive.of_prime_card` :
  A pretransitive action on a finite type of prime cardinal is preprimitive.

- `MulAction.IsPreprimitive.of_card_lt`
  Given an equivariant map from a preprimitive action,
  if the image is at least twice the codomain, then the codomain is preprimitive.

- `MulAction.IsPreprimitive.exists_mem_smul_and_notMem_smul` : **Theorem of Rudio**.
  For a preprimitive action, a subset which is neither empty nor full has a translate
  which contains a given point and avoids another one.

-/

public section

open scoped Pointwise

namespace MulAction

variable (G : Type*) (X : Type*)

-- Note : if the action is degenerate, singletons may not be blocks.
/--
Definition of `_root_.AddAction.IsPreprimitive` / `_root_.AddAction.IsPreprimitive` 的定义

English:
class _root_.AddAction.IsPreprimitive
  parameters: [VAdd G X]
  extends: AddAction.IsPretransitive G X
  axioms and operations (1):
    - isTrivialBlock_of_isBlock : forall {B : Set X}, AddAction.IsBlock G B -> AddAction.IsTrivialBlock B

中文:
类 _root_.加法作用.是Preprimitive
  参数: [向量加法 G X]
  继承: 加法作用.是Pretransitive G X
  公理与运算 (1 个):
    - isTrivialBlock_of_isBlock : 对任意 {B : 集合 X}, 加法作用.IsBlock G B -> 加法作用.IsTrivialBlock B
-/
class _root_.AddAction.IsPreprimitive [VAdd G X] : Prop extends AddAction.IsPretransitive G X where
  /-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
  isTrivialBlock_of_isBlock : forall {B : Set X}, AddAction.IsBlock G B -> AddAction.IsTrivialBlock B

/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
@[to_additive]
/--
Definition of `IsPreprimitive` / `IsPreprimitive` 的定义

English:
class IsPreprimitive
  parameters: [SMul G X]
  extends: IsPretransitive G X
  axioms and operations (1):
    - isTrivialBlock_of_isBlock : forall {B : Set X}, IsBlock G B -> IsTrivialBlock B

中文:
类 是Preprimitive
  参数: [标量乘法 G X]
  继承: 是Pretransitive G X
  公理与运算 (1 个):
    - isTrivialBlock_of_isBlock : 对任意 {B : 集合 X}, IsBlock G B -> IsTrivialBlock B
-/
class IsPreprimitive [SMul G X] : Prop extends IsPretransitive G X where
  /-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
  isTrivialBlock_of_isBlock : forall {B : Set X}, IsBlock G B -> IsTrivialBlock B

open IsPreprimitive

/--
Definition of `_root_.AddAction.IsQuasiPreprimitive` / `_root_.AddAction.IsQuasiPreprimitive` 的定义

English:
class _root_.AddAction.IsQuasiPreprimitive
  extends: AddAction.IsPretransitive G X
  axioms and operations (1):
    - isPretransitive_of_normal : forall {N : AddSubgroup G} [N.Normal], AddAction.fixedPoints N X != .univ -> AddAction.IsPretransitive N X

中文:
类 _root_.加法作用.是QuasiPreprimitive
  继承: 加法作用.是Pretransitive G X
  公理与运算 (1 个):
    - isPretransitive_of_normal : 对任意 {N : 加法子群 G} [N.正规], 加法作用.fixedPoints N X != .univ -> 加法作用.是Pretransitive N X
-/
class _root_.AddAction.IsQuasiPreprimitive
    [AddGroup G] [AddAction G X] : Prop extends AddAction.IsPretransitive G X where
  isPretransitive_of_normal :
    forall {N : AddSubgroup G} [N.Normal], AddAction.fixedPoints N X != .univ ->
      AddAction.IsPretransitive N X

/-- An action of a group is quasipreprimitive if any normal subgroup
that has no fixed point acts pretransitively -/
@[to_additive]
/--
Definition of `IsQuasiPreprimitive` / `IsQuasiPreprimitive` 的定义

English:
class IsQuasiPreprimitive
  parameters: [Group G] [MulAction G X]
  extends: IsPretransitive G X
  axioms and operations (1):
    - isPretransitive_of_normal : forall {N : Subgroup G} [N.Normal], fixedPoints N X != .univ -> IsPretransitive N X

中文:
类 是QuasiPreprimitive
  参数: [群 G] [乘法作用 G X]
  继承: 是Pretransitive G X
  公理与运算 (1 个):
    - isPretransitive_of_normal : 对任意 {N : 子群 G} [N.正规], fixedPoints N X != .univ -> 是Pretransitive N X
-/
class IsQuasiPreprimitive [Group G] [MulAction G X] : Prop extends IsPretransitive G X where
  isPretransitive_of_normal :
    forall {N : Subgroup G} [N.Normal], fixedPoints N X != .univ -> IsPretransitive N X

variable {G X}

@[to_additive]
/--
theorem `IsBlock.subsingleton_or_eq_univ` / 定理 `IsBlock.subsingleton_or_eq_univ`

English:
theorem IsBlock.subsingleton_or_eq_univ
  proof: isTrivialBlock_of_isBlock hB

@[to_additive (attr := nontriviality)]

中文:
定理 IsBlock.subsingleton_or_eq_univ
  证明: isTrivialBlock_of_isBlock hB

@[to_additive (attr := nontriviality)]

Depends on / 依赖: isTrivialBlock_of_isBlock
-/
theorem IsBlock.subsingleton_or_eq_univ
    [SMul G X] [IsPreprimitive G X] {B : Set X} (hB : IsBlock G B) :
    B.Subsingleton ∨ B = .univ :=
  isTrivialBlock_of_isBlock hB

@[to_additive (attr := nontriviality)]
/--
theorem `IsPreprimitive.of_subsingleton` / 定理 `IsPreprimitive.of_subsingleton`

English:
theorem IsPreprimitive.of_subsingleton
  given: [SMul G X] [Nonempty G] [Subsingleton X]
  proof: by
    use Classical.arbitrary G
    rw [eq_iff_true_of_subsingleton]
    trivial
  isTrivialBlock_of_isBlock B := by
    left
    exact Set.subsingleton_of_subsingleton

中文:
定理 是Preprimitive.of_subsingleton
  条件: [标量乘法 G X] [非空 G] [子单例 X]
  证明: by
    use Classical.arbitrary G
    rw [eq_iff_true_of_subsingleton]
    trivial
  isTrivialBlock_of_isBlock B := by
    left
    exact Set.subsingleton_of_subsingleton

Depends on / 依赖: Classical, Classical.arbitrary, Set.subsingleton_of_subsingleton, arbitrary, eq_iff_true_of_subsingleton, isTrivialBlock_of_isBlock, subsingleton_of_subsingleton
-/
theorem IsPreprimitive.of_subsingleton [SMul G X] [Nonempty G] [Subsingleton X] :
    IsPreprimitive G X where
  exists_smul_eq (x y) := by
    use Classical.arbitrary G
    rw [eq_iff_true_of_subsingleton]
    trivial
  isTrivialBlock_of_isBlock B := by
    left
    exact Set.subsingleton_of_subsingleton

/--
theorem `isTrivialBlock_of_card_le_two` / 定理 `isTrivialBlock_of_card_le_two`

English:
theorem isTrivialBlock_of_card_le_two
  proof: by
  rw [IsTrivialBlock]; rw [← B.ncard_le_one_iff_subsingleton]; rw [B.eq_univ_iff_ncard]
  have := B.ncard_le_card
  grind

中文:
定理 isTrivialBlock_of_card_le_two
  证明: by
  rw [IsTrivialBlock]; rw [← B.ncard_le_one_iff_subsingleton]; rw [B.eq_univ_iff_ncard]
  have := B.ncard_le_card
  grind

Depends on / 依赖: B.eq_univ_iff_ncard, B.ncard_le_card, B.ncard_le_one_iff_subsingleton, IsTrivialBlock, eq_univ_iff_ncard, ncard_le_card, ncard_le_one_iff_subsingleton
-/
theorem isTrivialBlock_of_card_le_two
    [Finite X] (hX : Nat.card X <= 2) (B : Set X) :
    IsTrivialBlock B := by
  rw [IsTrivialBlock]; rw [← B.ncard_le_one_iff_subsingleton]; rw [B.eq_univ_iff_ncard]
  have := B.ncard_le_card
  grind

variable [Group G] [MulAction G X]

open scoped Pointwise

/-- If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition) -/
@[to_additive
/-- If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition) -/]
/--
theorem `IsPreprimitive.of_isTrivialBlock_base` / 定理 `IsPreprimitive.of_isTrivialBlock_base`

English:
theorem IsPreprimitive.of_isTrivialBlock_base
  statement: [IsPretransitive G X] (a : X)
  proof: by
    obtain rfl | ⟨b, hb⟩ := B.eq_empty_or_nonempty
    · simp [IsTrivialBlock]
    · obtain ⟨g, hg⟩ := exists_smul_eq G b a
      rw [← IsTrivialBlock.smul_iff g]
      apply H _ (hB.translate g)
      rw [← hg]
      use b

中文:
定理 是Preprimitive.of_isTrivialBlock_base
  结论: [是Pretransitive G X] (a : X)
  证明: by
    obtain rfl | ⟨b, hb⟩ := B.eq_empty_or_nonempty
    · simp [IsTrivialBlock]
    · obtain ⟨g, hg⟩ := exists_smul_eq G b a
      rw [← IsTrivialBlock.smul_iff g]
      apply H _ (hB.translate g)
      rw [← hg]
      use b

Depends on / 依赖: B.eq_empty_or_nonempty, IsTrivialBlock, IsTrivialBlock.smul_iff, eq_empty_or_nonempty, exists_smul_eq, hB.translate, smul_iff, translate
-/
theorem IsPreprimitive.of_isTrivialBlock_base [IsPretransitive G X] (a : X)
    (H : forall {B : Set X} (_ : a in B) (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X where
  isTrivialBlock_of_isBlock {B} hB := by
    obtain rfl | ⟨b, hb⟩ := B.eq_empty_or_nonempty
    · simp [IsTrivialBlock]
    · obtain ⟨g, hg⟩ := exists_smul_eq G b a
      rw [← IsTrivialBlock.smul_iff g]
      apply H _ (hB.translate g)
      rw [← hg]
      use b

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) (based condition) -/
@[to_additive
  /-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
  (pretransitivity is automatic) (based condition) -/]
/--
theorem `IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints` / 定理 `IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints`

English:
theorem IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints
  statement: {a : X} (ha : a ∉ fixedPoints G X)
  proof: have : IsPretransitive G X := by
    rw [isPretransitive_iff_base a]
    rcases H (mem_orbit_self a) (IsBlock.orbit a) with H | H
    · exfalso; apply ha
      rw [Set.subsingleton_iff_singleton (mem_orbit_self a)] at H
      simp only [mem_fixedPoints]
      intro g
      rw [← Set.mem_singleton_if

中文:
定理 是Preprimitive.of_isTrivialBlock_of_notMem_fixedPoints
  结论: {a : X} (ha : a ∉ fixedPoints G X)
  证明: have : IsPretransitive G X := by
    rw [isPretransitive_iff_base a]
    rcases H (mem_orbit_self a) (IsBlock.orbit a) with H | H
    · exfalso; apply ha
      rw [Set.subsingleton_iff_singleton (mem_orbit_self a)] at H
      simp only [mem_fixedPoints]
      intro g
      rw [← Set.mem_singleton_if

Depends on / 依赖: B.eq_empty_or_nonempty, IsBlock, IsBlock.orbit, IsPretransitive, IsTrivialBlock, MulAction, MulAction.mem_orbit_iff, Set.mem_singleton_iff, Set.mem_univ, Set.subsingleton_iff_singleton, eq_empty_or_nonempty, isPretransitive_iff_base, isTrivialBlock_of_isBlock, mem_fixedPoints, mem_orbit, mem_orbit_iff, mem_orbit_self, mem_singleton_iff, mem_univ, subsingleton_iff_singleton
-/
theorem IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints {a : X} (ha : a ∉ fixedPoints G X)
    (H : forall ⦃B : Set X⦄, a in B -> IsBlock G B -> IsTrivialBlock B) :
    IsPreprimitive G X :=
  have : IsPretransitive G X := by
    rw [isPretransitive_iff_base a]
    rcases H (mem_orbit_self a) (IsBlock.orbit a) with H | H
    · exfalso; apply ha
      rw [Set.subsingleton_iff_singleton (mem_orbit_self a)] at H
      simp only [mem_fixedPoints]
      intro g
      rw [← Set.mem_singleton_iff]; rw [← H]
      exact mem_orbit a g
    · intro x; rw [← MulAction.mem_orbit_iff, H]; exact Set.mem_univ x
  { isTrivialBlock_of_isBlock {B} hB := by
      obtain rfl | ⟨b, hb⟩ := B.eq_empty_or_nonempty
      · simp [IsTrivialBlock]
      · obtain ⟨g, hg⟩ := exists_smul_eq G b a
        rw [← IsTrivialBlock.smul_iff g]
        exact H ⟨b, hb, hg⟩ (hB.translate g) }

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) -/
@[to_additive
  /-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) -/]
/--
theorem `IsPreprimitive.mk'` / 定理 `IsPreprimitive.mk'`

English:
theorem IsPreprimitive.mk'
  statement: (Hnt : fixedPoints G X != ⊤)
  proof: by
  simp only [Set.top_eq_univ, Set.ne_univ_iff_exists_notMem] at Hnt
  obtain ⟨_, ha⟩ := Hnt
  exact .of_isTrivialBlock_of_notMem_fixedPoints ha fun {B} _ => H

中文:
定理 是Preprimitive.mk'
  结论: (Hnt : fixedPoints G X != ⊤)
  证明: by
  simp only [Set.top_eq_univ, Set.ne_univ_iff_exists_notMem] at Hnt
  obtain ⟨_, ha⟩ := Hnt
  exact .of_isTrivialBlock_of_notMem_fixedPoints ha fun {B} _ => H

Depends on / 依赖: Set.ne_univ_iff_exists_notMem, Set.top_eq_univ, ne_univ_iff_exists_notMem, of_isTrivialBlock_of_notMem_fixedPoints, top_eq_univ
-/
theorem IsPreprimitive.mk' (Hnt : fixedPoints G X != ⊤)
    (H : forall {B : Set X} (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  simp only [Set.top_eq_univ, Set.ne_univ_iff_exists_notMem] at Hnt
  obtain ⟨_, ha⟩ := Hnt
  exact .of_isTrivialBlock_of_notMem_fixedPoints ha fun {B} _ => H

section EquivariantMap

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]
variable {N β : Type*} [Group N] [MulAction N β]
variable {φ : M -> N} {f : α ->ₑ[φ] β}

@[to_additive]
/--
theorem `IsPreprimitive.of_surjective` / 定理 `IsPreprimitive.of_surjective`

English:
theorem IsPreprimitive.of_surjective
  given: [IsPreprimitive M α] (hf : Function.Surjective f)
  proof: toIsPretransitive.of_surjective_map hf
  isTrivialBlock_of_isBlock {B} hB := by
    rw [← Set.image_preimage_eq B hf]
    apply IsTrivialBlock.image hf
    exact isTrivialBlock_of_isBlock (IsBlock.preimage f hB)

@[to_additive]

中文:
定理 是Preprimitive.of_surjective
  条件: [是Preprimitive M α] (hf : 函数.满射 f)
  证明: toIsPretransitive.of_surjective_map hf
  isTrivialBlock_of_isBlock {B} hB := by
    rw [← Set.image_preimage_eq B hf]
    apply IsTrivialBlock.image hf
    exact isTrivialBlock_of_isBlock (IsBlock.preimage f hB)

@[to_additive]

Depends on / 依赖: of_surjective_map, toIsPretransitive, toIsPretransitive.of_surjective_map
-/
theorem IsPreprimitive.of_surjective [IsPreprimitive M α] (hf : Function.Surjective f) :
    IsPreprimitive N β where
  toIsPretransitive := toIsPretransitive.of_surjective_map hf
  isTrivialBlock_of_isBlock {B} hB := by
    rw [← Set.image_preimage_eq B hf]
    apply IsTrivialBlock.image hf
    exact isTrivialBlock_of_isBlock (IsBlock.preimage f hB)

@[to_additive]
/--
theorem `isPreprimitive_congr` / 定理 `isPreprimitive_congr`

English:
theorem isPreprimitive_congr
  given: (hφ : Function.Surjective φ) (hf : Function.Bijective f)
  proof: by
  constructor
  · intro _
    apply IsPreprimitive.of_surjective hf.surjective
  · intro _
    have := (isPretransitive_congr hφ hf).mpr toIsPretransitive
    exact {
      isTrivialBlock_of_isBlock {B} hB := by
        rw [← Set.preimage_image_eq B hf.injective]
        exact IsTrivialBlock.prei

中文:
定理 isPreprimitive_congr
  条件: (hφ : 函数.满射 φ) (hf : 函数.双射 f)
  证明: by
  constructor
  · intro _
    apply IsPreprimitive.of_surjective hf.surjective
  · intro _
    have := (isPretransitive_congr hφ hf).mpr toIsPretransitive
    exact {
      isTrivialBlock_of_isBlock {B} hB := by
        rw [← Set.preimage_image_eq B hf.injective]
        exact IsTrivialBlock.prei

Depends on / 依赖: IsPreprimitive, IsPreprimitive.of_surjective, IsTrivialBlock, IsTrivialBlock.preimage, Set.preimage_image_eq, hB.image, hf.injective, hf.surjective, injective, isPretransitive_congr, isTrivialBlock_of_isBlock, of_surjective, preimage, preimage_image_eq, surjective, toIsPretransitive
-/
theorem isPreprimitive_congr (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPreprimitive M α ↔ IsPreprimitive N β := by
  constructor
  · intro _
    apply IsPreprimitive.of_surjective hf.surjective
  · intro _
    have := (isPretransitive_congr hφ hf).mpr toIsPretransitive
    exact {
      isTrivialBlock_of_isBlock {B} hB := by
        rw [← Set.preimage_image_eq B hf.injective]
        exact IsTrivialBlock.preimage hf.injective
          (isTrivialBlock_of_isBlock (hB.image f hφ hf.injective)) }

end EquivariantMap

section Stabilizer

variable (G : Type*) [Group G] {X : Type*} [MulAction G X]

open scoped Pointwise

/-- A pretransitive action on a nontrivial type is preprimitive iff
the set of blocks containing a given element is a simple order -/
@[to_additive (attr := simp)
  /-- A pretransitive action on a nontrivial type is preprimitive iff
  the set of blocks containing a given element is a simple order -/]
/--
theorem `isSimpleOrder_blockMem_iff_isPreprimitive` / 定理 `isSimpleOrder_blockMem_iff_isPreprimitive`

English:
theorem isSimpleOrder_blockMem_iff_isPreprimitive
  given: [IsPretransitive G X] [Nontrivial X] (a : X)
  proof: by
  constructor
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.of_isTrivialBlock_base a
    intro B haB hB
    rcases h_bot_or_top ⟨B, haB, hB⟩ with hB' | hB' <;>
      simp only [← Subtype.coe_inj] at hB'
    · left; rw [hB']; exact Set.subsingleton_singleton
    · ri

中文:
定理 isSimpleOrder_blockMem_iff_isPreprimitive
  条件: [是Pretransitive G X] [非平凡 X] (a : X)
  证明: by
  constructor
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.of_isTrivialBlock_base a
    intro B haB hB
    rcases h_bot_or_top ⟨B, haB, hB⟩ with hB' | hB' <;>
      simp only [← Subtype.coe_inj] at hB'
    · left; rw [hB']; exact Set.subsingleton_singleton
    · ri

Depends on / 依赖: BlockMem, BlockMem.coe_bot, IsPreprimitive, IsPreprimitive.of_isTrivialBlock_base, IsSimpleOrder, IsSimpleOrder.mk, Set.subsingleton_singleton, Subtype, Subtype.coe_inj, coe_bot, coe_inj, eq_bot_or_eq_top, eq_singleton_of_mem, h.eq_bot_or_eq_top, h.eq_singleton_of_mem, h_bot_or_top, isTrivialBlock_of_isBlock, of_isTrivialBlock_base, subsingleton_singleton
-/
theorem isSimpleOrder_blockMem_iff_isPreprimitive [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsSimpleOrder (BlockMem G a) ↔ IsPreprimitive G X := by
  constructor
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.of_isTrivialBlock_base a
    intro B haB hB
    rcases h_bot_or_top ⟨B, haB, hB⟩ with hB' | hB' <;>
      simp only [← Subtype.coe_inj] at hB'
    · left; rw [hB']; exact Set.subsingleton_singleton
    · right; rw [hB']; rfl
  · intro hGX'; apply IsSimpleOrder.mk
    rintro ⟨B, haB, hB⟩
    simp only [← Subtype.coe_inj]
    cases hGX'.isTrivialBlock_of_isBlock hB with
    | inl h =>
      simp [BlockMem.coe_bot, h.eq_singleton_of_mem haB]
    | inr h =>
      simp [BlockMem.coe_top, h]

/-- A pretransitive action is preprimitive
iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
@[to_additive
  /-- A pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/]
/--
theorem `isCoatom_stabilizer_iff_preprimitive` / 定理 `isCoatom_stabilizer_iff_preprimitive`

English:
theorem isCoatom_stabilizer_iff_preprimitive
  given: [IsPretransitive G X] [Nontrivial X] (a : X)
  proof: by
  rw [← isSimpleOrder_blockMem_iff_isPreprimitive G a]; rw [← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (block_stabilizerOrderIso G a)]; rw [OrderIso.map_bot]

中文:
定理 isCoatom_stabilizer_iff_preprimitive
  条件: [是Pretransitive G X] [非平凡 X] (a : X)
  证明: by
  rw [← isSimpleOrder_blockMem_iff_isPreprimitive G a]; rw [← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (block_stabilizerOrderIso G a)]; rw [OrderIso.map_bot]

Depends on / 依赖: OrderIso, OrderIso.isCoatom_iff, OrderIso.map_bot, Set.isSimpleOrder_Ici_iff_isCoatom, block_stabilizerOrderIso, isCoatom_iff, isSimpleOrder_Ici_iff_isCoatom, isSimpleOrder_blockMem_iff_isPreprimitive, isSimpleOrder_iff_isCoatom_bot, map_bot
-/
theorem isCoatom_stabilizer_iff_preprimitive [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsCoatom (stabilizer G a) ↔ IsPreprimitive G X := by
  rw [← isSimpleOrder_blockMem_iff_isPreprimitive G a]; rw [← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (block_stabilizerOrderIso G a)]; rw [OrderIso.map_bot]

/-- In a preprimitive action, stabilizers are maximal subgroups -/
@[to_additive /-- In a preprimitive action, stabilizers are maximal subgroups. -/]
/--
theorem `IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive` / 定理 `IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive`

English:
theorem IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
  proof: by
  rwa [isCoatom_stabilizer_iff_preprimitive]

中文:
定理 是Preprimitive.isCoatom_stabilizer_of_isPreprimitive
  证明: by
  rwa [isCoatom_stabilizer_iff_preprimitive]

Depends on / 依赖: isCoatom_stabilizer_iff_preprimitive
-/
theorem IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    [Nontrivial X] [IsPreprimitive G X] (a : X) :
    IsCoatom (stabilizer G a) := by
  rwa [isCoatom_stabilizer_iff_preprimitive]

end Stabilizer

section Normal

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]

/-- In a preprimitive action, any normal subgroup that acts nontrivially is pretransitive
(Wielandt, th. 7.1). -/
@[to_additive /-- In a preprimitive additive action,
  any normal subgroup that acts nontrivially is pretransitive (Wielandt, th. 7.1). -/]
-- See note [lower instance priority]
instance (priority := 100) IsPreprimitive.isQuasiPreprimitive [IsPreprimitive M α] :
    IsQuasiPreprimitive M α where
  isPretransitive_of_normal {N} _ hNX := by
    rw [Set.ne_univ_iff_exists_notMem] at hNX
    obtain ⟨a, ha⟩ := hNX
    rw [isPretransitive_iff_orbit_eq_univ a]
    apply Or.resolve_left (isTrivialBlock_of_isBlock (IsBlock.orbit_of_normal a))
    intro h
    apply ha
    simp only [mem_fixedPoints]
    intro n
    rw [← Set.mem_singleton_iff]
    suffices orbit N a = {a} by rw [← this]; use n
    ext b
    rw [Set.Subsingleton.eq_singleton_of_mem h (MulAction.mem_orbit_self a)]

end Normal

section Finite

namespace IsPreprimitive

variable {H Y : Type*} [Group H] [MulAction H Y]

/-- A pretransitive action on a set of prime order is preprimitive -/
@[to_additive /-- A pretransitive action on a set of prime order is preprimitive -/]
/--
theorem `of_prime_card` / 定理 `of_prime_card`

English:
theorem of_prime_card
  given: [hGX : IsPretransitive G X] (hp : Nat.Prime (Nat.card X))
  proof: by
  refine ⟨fun {B} hB => B.subsingleton_or_nontrivial.imp id fun hB' => ?_⟩
  have : Finite X := (Nat.card_ne_zero.mp hp.ne_zero).2
  rw [Set.eq_univ_iff_ncard]; rw [eq_comm]; rw [← hp.dvd_iff_eq ((Set.one_lt_ncard).mpr hB').ne']
  exact hB.ncard_dvd_card hB'.nonempty

中文:
定理 of_prime_card
  条件: [hGX : 是Pretransitive G X] (hp : 自然数.素 (自然数.card X))
  证明: by
  refine ⟨fun {B} hB => B.subsingleton_or_nontrivial.imp id fun hB' => ?_⟩
  have : Finite X := (Nat.card_ne_zero.mp hp.ne_zero).2
  rw [Set.eq_univ_iff_ncard]; rw [eq_comm]; rw [← hp.dvd_iff_eq ((Set.one_lt_ncard).mpr hB').ne']
  exact hB.ncard_dvd_card hB'.nonempty

Depends on / 依赖: B.subsingleton_or_nontrivial.imp, Finite, Nat.card_ne_zero.mp, Set.eq_univ_iff_ncard, Set.one_lt_ncard, card_ne_zero, dvd_iff_eq, eq_comm, eq_univ_iff_ncard, hB.ncard_dvd_card, hp.dvd_iff_eq, hp.ne_zero, ncard_dvd_card, ne_zero, nonempty, one_lt_ncard, subsingleton_or_nontrivial
-/
theorem of_prime_card [hGX : IsPretransitive G X] (hp : Nat.Prime (Nat.card X)) :
    IsPreprimitive G X := by
  refine ⟨fun {B} hB => B.subsingleton_or_nontrivial.imp id fun hB' => ?_⟩
  have : Finite X := (Nat.card_ne_zero.mp hp.ne_zero).2
  rw [Set.eq_univ_iff_ncard]; rw [eq_comm]; rw [← hp.dvd_iff_eq ((Set.one_lt_ncard).mpr hB').ne']
  exact hB.ncard_dvd_card hB'.nonempty

variable {φ : G -> H} {f : X ->ₑ[φ] Y}

/-- The codomain of an equivariant map of large image is preprimitive if the domain is. -/
@[to_additive
/-- The codomain of an equivariant map of large image is preprimitive if the domain is. -/]
/--
theorem `of_card_lt` / 定理 `of_card_lt`

English:
theorem of_card_lt
  statement: [Finite Y] [IsPretransitive H Y] [IsPreprimitive G X]
  proof: by
  refine ⟨fun {B} hB => ?_⟩
  rcases B.eq_empty_or_nonempty with hB' | hB'; · simp [IsTrivialBlock, hB']
  rw [IsTrivialBlock]; rw [or_iff_not_imp_right]
  intro hB_ne_top
  -- we need Set.Subsingleton B ↔ Set.ncard B ≤ 1
  suffices Set.ncard B < 2 by simpa [Nat.lt_succ_iff] using this
  -- We re

中文:
定理 of_card_lt
  结论: [有限 Y] [是Pretransitive H Y] [是Preprimitive G X]
  证明: by
  refine ⟨fun {B} hB => ?_⟩
  rcases B.eq_empty_or_nonempty with hB' | hB'; · simp [IsTrivialBlock, hB']
  rw [IsTrivialBlock]; rw [or_iff_not_imp_right]
  intro hB_ne_top
  -- we need Set.Subsingleton B ↔ Set.ncard B ≤ 1
  suffices Set.ncard B < 2 by simpa [Nat.lt_succ_iff] using this
  -- We re

Depends on / 依赖: B.eq_empty_or_nonempty, IsTrivialBlock, eq_empty_or_nonempty, hB_ne_top, or_iff_not_imp_right
-/
theorem of_card_lt [Finite Y] [IsPretransitive H Y] [IsPreprimitive G X]
    (hf' : Nat.card Y < 2 * (Set.range f).ncard) :
    IsPreprimitive H Y := by
  refine ⟨fun {B} hB => ?_⟩
  rcases B.eq_empty_or_nonempty with hB' | hB'; · simp [IsTrivialBlock, hB']
  rw [IsTrivialBlock]; rw [or_iff_not_imp_right]
  intro hB_ne_top
  -- we need Set.Subsingleton B ↔ Set.ncard B ≤ 1
  suffices Set.ncard B < 2 by simpa [Nat.lt_succ_iff] using this
  -- We reduce to proving that (Set.range f).ncard ≤ (orbit N B).ncard
  apply lt_of_mul_lt_mul_right' (hf'.trans_le' _)
  simp only [← hB.ncard_block_mul_ncard_orbit_eq hB']
  apply Nat.mul_le_mul_left
  -- We reduce to proving that (Set.range f ∩ g • B).ncard ≤ 1 for every g
  have hfin := Fintype.ofFinite (Set.range fun g : H => g • B)
  rw [(hB.isBlockSystem hB').left.ncard_eq_finsum]; rw [finsum_eq_sum_of_fintype]
  apply le_trans (Finset.sum_le_card_nsmul _ _ 1 _)
  · rw [nsmul_one, Finset.card_univ, ← Set.toFinset_card, ← Set.ncard_eq_toFinset_card',
      orbit, Nat.cast_id]
  · rintro ⟨x, ⟨g, rfl⟩⟩ -
    suffices Set.Subsingleton (Set.range f inter g • B) by simpa
    -- It suffices to prove that the preimage is subsingleton
    rw [← Set.image_preimage_eq_range_inter]
    apply Set.Subsingleton.image
    -- Since the action of M on α is primitive, it suffices to prove that
    -- the preimage is a block which is not ⊤
    apply Or.resolve_right (isTrivialBlock_of_isBlock ((hB.translate g).preimage f))
    intro h
    simp only [Set.preimage_eq_univ_iff] at h
    -- We will prove that B is large, which will contradict the assumption that it is not ⊤
    apply hB_ne_top
    apply hB.eq_univ_of_card_lt
    -- It remains to show that Nat.card β < Set.ncard B * 2
    apply lt_of_lt_of_le hf'
    rw [mul_comm]; rw [mul_le_mul_iff_left₀ Nat.succ_pos']
    apply le_trans (Set.ncard_le_ncard h) (Set.ncard_image_le B.toFinite)

/- The finiteness assumption is necessary :
  For G = ℤ acting on itself, no translate of ℕ contains 0 but not 1.
  (See comment before `IsBlock.of_subset`.) -/
/-- Theorem of Rudio (Wielandt, 1964, Th. 8.1)

For a preprimitive action, a subset which is neither empty nor full has a translate
which contains a given point and avoids another one. -/
@[to_additive /-- Theorem of Rudio (Wielandt, 1964, Th. 8.1)

For a preprimitive additive action, a subset which is neither empty nor full has a translate
which contains a given point and avoids another one. -/]
/--
theorem `exists_mem_smul_and_notMem_smul` / 定理 `exists_mem_smul_and_notMem_smul`

English:
theorem exists_mem_smul_and_notMem_smul
  statement: [IsPreprimitive G X]
  proof: by
  let B := ⋂ (g : G) (_ : a in g • A), g • A
  suffices b ∉ B by
    rw [Set.mem_iInter] at this
    simpa only [Set.mem_iInter, not_forall, exists_prop] using this
  suffices B = {a} by rw [this]; rw [Set.mem_singleton_iff]; exact Ne.symm h
  -- B is a block hence is a trivial block
  rcases isT

中文:
定理 存在_mem_smul_and_notMem_smul
  结论: [是Preprimitive G X]
  证明: by
  let B := ⋂ (g : G) (_ : a in g • A), g • A
  suffices b ∉ B by
    rw [Set.mem_iInter] at this
    simpa only [Set.mem_iInter, not_forall, exists_prop] using this
  suffices B = {a} by rw [this]; rw [Set.mem_singleton_iff]; exact Ne.symm h
  -- B is a block hence is a trivial block
  rcases isT

Depends on / 依赖: Ne.symm, Set.mem_iInter, Set.mem_singleton_iff, exists_prop, mem_iInter, mem_singleton_iff, not_forall
-/
theorem exists_mem_smul_and_notMem_smul [IsPreprimitive G X]
    {A : Set X} (hfA : A.Finite) (hA : A.Nonempty) (hA' : A != .univ) {a b : X} (h : a != b) :
    exists g : G, a in g • A ∧ b ∉ g • A := by
  let B := ⋂ (g : G) (_ : a in g • A), g • A
  suffices b ∉ B by
    rw [Set.mem_iInter] at this
    simpa only [Set.mem_iInter, not_forall, exists_prop] using this
  suffices B = {a} by rw [this]; rw [Set.mem_singleton_iff]; exact Ne.symm h
  -- B is a block hence is a trivial block
  rcases isTrivialBlock_of_isBlock (G := G) (IsBlock.of_subset a hfA) with hyp | hyp
  · -- B.subsingleton
    apply Set.Subsingleton.eq_singleton_of_mem hyp
    rw [Set.mem_iInter]; intro g; simp only [Set.mem_iInter, imp_self]
  · -- B = Set.univ: contradiction
    change B = Set.univ at hyp
    exfalso; apply hA'
    suffices exists g : G, a in g • A by
      obtain ⟨g, hg⟩ := this
      have : B subseteq g • A := Set.biInter_subset_of_mem hg
      rw [hyp]; rw [Set.univ_subset_iff]; rw [← eq_inv_smul_iff] at this
      rw [this]; rw [Set.smul_set_univ]
    -- ∃ (g : M), a ∈ g • A
    obtain ⟨x, hx⟩ := hA
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x a
    use g, x

end IsPreprimitive

end Finite

end MulAction
