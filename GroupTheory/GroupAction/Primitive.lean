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
/-- An additive action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
/-
**MulAction._root_.AddAction.IsPreprimitive** 是 Mathlib 中的一个类，位于命名空间 `MulAction`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive action is preprimitive if it is pretransitive and
the only blocks are the trivial ones
-/
class _root_.AddAction.IsPreprimitive [VAdd G X] : Prop extends AddAction.IsPretransitive G X where
  /-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
  isTrivialBlock_of_isBlock : ∀ {B : Set X}, AddAction.IsBlock G B → AddAction.IsTrivialBlock B

/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
@[to_additive]
/-
**MulAction.IsPreprimitive** 是 Mathlib 中的一个归纳类型，位于命名空间 `MulAction`。
形式化陈述：(G : Type u_1) → (X : Type u_2) → [SMul G X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones
-/
class IsPreprimitive [SMul G X] : Prop extends IsPretransitive G X where
  /-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
  isTrivialBlock_of_isBlock : ∀ {B : Set X}, IsBlock G B → IsTrivialBlock B

open IsPreprimitive

/-- An additive action of an additive group is quasipreprimitive if any normal subgroup
that has no fixed point acts pretransitively -/
/-
**MulAction._root_.AddAction.IsQuasiPreprimitive** 是 Mathlib 中的一个类，位于命名空间 `MulAc
tion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive action of an additive group is quasipreprimitive if any normal subgr
oup
that has no fixed point acts pretransitively
-/
class _root_.AddAction.IsQuasiPreprimitive
    [AddGroup G] [AddAction G X] : Prop extends AddAction.IsPretransitive G X where
  isPretransitive_of_normal :
    ∀ {N : AddSubgroup G} [N.Normal], AddAction.fixedPoints N X ≠ .univ →
      AddAction.IsPretransitive N X

/-- An action of a group is quasipreprimitive if any normal subgroup
that has no fixed point acts pretransitively -/
@[to_additive]
/-
**MulAction.IsQuasiPreprimitive** 是 Mathlib 中的一个归纳类型，位于命名空间 `MulAction`。
形式化陈述：(G : Type u_1) → (X : Type u_2) → [inst : Group G] → [MulAction G X] → Pro
p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An action of a group is quasipreprimitive if any normal subgroup
that has no fixed point acts pretransitively
-/
class IsQuasiPreprimitive [Group G] [MulAction G X] : Prop extends IsPretransitive G X where
  isPretransitive_of_normal :
    ∀ {N : Subgroup G} [N.Normal], fixedPoints N X ≠ .univ → IsPretransitive N X

variable {G X}

@[to_additive]
/-
**MulAction.IsBlock.subsingleton_or_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `MulAction
.IsBlock`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] [MulAction.IsPreprimitiv
e G X] {B : Set X},   MulAction.IsBlock G B → B.Subsingleton ∨ B = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
-/
theorem IsBlock.subsingleton_or_eq_univ
    [SMul G X] [IsPreprimitive G X] {B : Set X} (hB : IsBlock G B) :
    B.Subsingleton ∨ B = .univ :=
  isTrivialBlock_of_isBlock hB

@[to_additive (attr := nontriviality)]
/-
**MulAction.IsPreprimitive.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.
IsPreprimitive`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] [Nonempty G] [Subsinglet
on X], MulAction.IsPreprimitive G X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_true_of_subsingleton`：∀ {α : Sort u_1} [Subsingleton α] (x y : α)
, x = y ↔ True
· 使用定理 `Set.subsingleton_of_subsingleton`：subsingleton_of_subsingleton [Subsingl
eton α] {s : Set α} : s.Subsingleton
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
/-
**MulAction.isTrivialBlock_of_card_le_two** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isTrivialBlock_of_card_le_two [Finite X] (hX : Nat.card X <= 2) (B : Set X
) : IsTrivialBlock B
参数：hX : Nat.card X <= 2；B : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.IsTrivialBlock.eq_1`：∀ {X : Type u_2} (B : Set X), MulAction.I
sTrivialBlock B = (B.Subsingleton ∨ B = Set.univ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_le_one_iff_subsingleton`：∀ {α : Type u_1} {s : Set α} [Finite 
↑s], s.ncard ≤ 1 ↔ s.Subsingleton
· 使用定理 `Set.eq_univ_iff_ncard`：eq_univ_iff_ncard [Finite α] (s : Set α) : s = un
iv ↔ ncard s = Nat.card α
· 使用定理 `Set.ncard_le_card`：ncard_le_card [Finite α] (s : Set α) : s.ncard <= Nat
.card α
-/
theorem isTrivialBlock_of_card_le_two
    [Finite X] (hX : Nat.card X ≤ 2) (B : Set X) :
    IsTrivialBlock B := by
  rw [IsTrivialBlock, ← B.ncard_le_one_iff_subsingleton, B.eq_univ_iff_ncard]
  have := B.ncard_le_card
  grind

variable [Group G] [MulAction G X]

open scoped Pointwise

/-- If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition) -/
@[to_additive
/-- If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition) -/]
/-
**MulAction.IsPreprimitive.of_isTrivialBlock_base** 是 Mathlib 中的一个定理，位于命名空间 `Mul
Action.IsPreprimitive`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : Group G] [inst_1 : MulAction G X] 
[MulAction.IsPretransitive G X] (a : X),   (∀ {B : Set X}, a ∈ B → MulAction.IsB
lock G B → MulAction.IsTrivialBlock B) → MulAction.IsPreprimitive G X
参数：a : X；∀ {B : Set X}, a ∈ B → MulAction.IsBlock G B → MulAction.IsTrivialBlock
 B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `MulAction.IsTrivialBlock.smul_iff`：∀ {M : Type u_3} {α : Type u_4} [inst
 : Group M] [inst_1 : MulAction M α] {B : Set α} (g : M),   MulAction.IsTrivialB
lock (g • B) ↔ MulActio…
· 使用定理 `MulAction.IsBlock.translate`：∀ {G : Type u_1} [inst : Group G] {X : Type
 u_2} [inst_1 : MulAction G X] {B : Set X} (g : G),   MulAction.IsBlock G B → Mu
lAction.IsBlock G…
-/
theorem IsPreprimitive.of_isTrivialBlock_base [IsPretransitive G X] (a : X)
    (H : ∀ {B : Set X} (_ : a ∈ B) (_ : IsBlock G B), IsTrivialBlock B) :
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
/-
**MulAction.IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints** 是 Mathlib 中
的一个定理，位于命名空间 `MulAction.IsPreprimitive`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : Group G] [inst_1 : MulAction G X] 
{a : X},   a ∉ MulAction.fixedPoints G X →     (∀ ⦃B : Set X⦄, a ∈ B → MulAction
.IsBlock G B → MulAction.IsTrivialBlock B) → MulAction.IsPreprimitive G X
参数：∀ ⦃B : Set X⦄, a ∈ B → MulAction.IsBlock G B → MulAction.IsTrivialBlock B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.isPretransitive_iff_base`：isPretransitive_iff_base (a : X) : I
sPretransitive G X ↔ forall x : X, exists g : G, g • a = x where mp hG x
· 使用定理 `MulAction.mem_orbit_self`：mem_orbit_self (a : α) : a in orbit M a
· 使用定理 `MulAction.IsBlock.orbit`：∀ {G : Type u_1} [inst : Group G] {X : Type u_2
} [inst_1 : MulAction G X] (a : X),   MulAction.IsBlock G (MulAction.orbit G a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
· 使用定理 `MulAction.mem_orbit_iff`：mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ 
exists x : γ, x • a₁ = a₂
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `MulAction.IsTrivialBlock.smul_iff`：∀ {M : Type u_3} {α : Type u_4} [inst
 : Group M] [inst_1 : MulAction M α] {B : Set α} (g : M),   MulAction.IsTrivialB
lock (g • B) ↔ MulActio…
· 使用定理 `MulAction.IsBlock.translate`：∀ {G : Type u_1} [inst : Group G] {X : Type
 u_2} [inst_1 : MulAction G X] {B : Set X} (g : G),   MulAction.IsBlock G B → Mu
lAction.IsBlock G…
-/
theorem IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints {a : X} (ha : a ∉ fixedPoints G X)
    (H : ∀ ⦃B : Set X⦄, a ∈ B → IsBlock G B → IsTrivialBlock B) :
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
/-
**MulAction.IsPreprimitive.mk'** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsPreprimiti
ve`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : Group G] [inst_1 : MulAction G X],
   MulAction.fixedPoints G X ≠ ⊤ →     (∀ {B : Set X}, MulAction.IsBlock G B → M
ulAction.IsTrivialBlock B) → MulAction.IsPreprimitive G X
参数：∀ {B : Set X}, MulAction.IsBlock G B → MulAction.IsTrivialBlock B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints`：∀ {G :
 Type u_1} {X : Type u_2} [inst : Group G] [inst_1 : MulAction G X] {a : X},   a
 ∉ MulAction.fixedPoints G X →     (∀ ⦃B : Set X⦄, a ∈…
-/
theorem IsPreprimitive.mk' (Hnt : fixedPoints G X ≠ ⊤)
    (H : ∀ {B : Set X} (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  simp only [Set.top_eq_univ, Set.ne_univ_iff_exists_notMem] at Hnt
  obtain ⟨_, ha⟩ := Hnt
  exact .of_isTrivialBlock_of_notMem_fixedPoints ha fun {B} _ ↦ H

section EquivariantMap

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]
variable {N β : Type*} [Group N] [MulAction N β]
variable {φ : M → N} {f : α →ₑ[φ] β}

@[to_additive]
/-
**MulAction.IsPreprimitive.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Is
Preprimitive`。
形式化陈述：∀ {M : Type u_3} [inst : Group M] {α : Type u_4} [inst_1 : MulAction M α] 
{N : Type u_5} {β : Type u_6}   [inst_2 : Group N] [inst_3 : MulAction N β] {φ :
 M → N} {f : α →ₑ[φ] β} [MulAction.IsPreprimitive M α],   Function.Surjective ⇑f
 → MulAction.IsPreprimitive N β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_surjective_map`：∀ {M : Type u_3} {N : Type 
u_4} {α : Type u_5} {β : Type u_6} [inst : Monoid M] [inst_1 : Monoid N]   [inst
_2 : MulAction M α] [inst_3 : Mul…
· 使用定理 `MulAction.IsPreprimitive.toIsPretransitive`：∀ {G : Type u_1} {X : Type u
_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X], MulAction.IsPretran
sitive G X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `MulAction.IsTrivialBlock.image`：∀ {M : Type u_3} {α : Type u_4} {N : Typ
e u_5} {β : Type u_6} [inst : Monoid M] [inst_1 : MulAction M α]   [inst_2 : Mon
oid N] [inst_3 : Mul…
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
· 使用定理 `MulAction.IsBlock.preimage`：∀ {G : Type u_1} [inst : Group G] {X : Type 
u_2} [inst_1 : MulAction G X] {B : Set X} {H : Type u_3} {Y : Type u_4}   [inst_
2 : Group H] [in…
-/
theorem IsPreprimitive.of_surjective [IsPreprimitive M α] (hf : Function.Surjective f) :
    IsPreprimitive N β where
  toIsPretransitive := toIsPretransitive.of_surjective_map hf
  isTrivialBlock_of_isBlock {B} hB := by
    rw [← Set.image_preimage_eq B hf]
    apply IsTrivialBlock.image hf
    exact isTrivialBlock_of_isBlock (IsBlock.preimage f hB)

@[to_additive]
/-
**MulAction.isPreprimitive_congr** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isPreprimitive_congr (hφ : Function.Surjective φ) (hf : Function.Bijective
 f) : IsPreprimitive M α ↔ IsPreprimitive N β
参数：hφ : Function.Surjective φ；hf : Function.Bijective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPreprimitive.of_surjective`：∀ {M : Type u_3} [inst : Group M
] {α : Type u_4} [inst_1 : MulAction M α] {N : Type u_5} {β : Type u_6}   [inst_
2 : Group N] [inst_3 : MulAc…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.isPretransitive_congr`：isPretransitive_congr {φ : M -> N} {f :
 α ->ₑ[φ] β} (hφ : Function.Surjective φ) (hf : Function.Bijective f) : IsPretra
nsitive M α ↔ IsPretr…
· 使用定理 `MulAction.IsPreprimitive.toIsPretransitive`：∀ {G : Type u_1} {X : Type u
_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X], MulAction.IsPretran
sitive G X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `MulAction.IsTrivialBlock.preimage`：∀ {M : Type u_3} {α : Type u_4} {N : 
Type u_5} {β : Type u_6} [inst : Monoid M] [inst_1 : MulAction M α]   [inst_2 : 
Monoid N] [inst_3 : Mul…
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
· 使用定理 `MulAction.IsBlock.image`：∀ {G : Type u_1} [inst : Group G] {X : Type u_2
} [inst_1 : MulAction G X] {B : Set X} {H : Type u_3} {Y : Type u_4}   [inst_2 :
 SMul H Y] {φ…
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
/-
**MulAction.isSimpleOrder_blockMem_iff_isPreprimitive** 是 Mathlib 中的一个定理，位于命名空间 
`MulAction`。
形式化陈述：isSimpleOrder_blockMem_iff_isPreprimitive [IsPretransitive G X] [Nontrivia
l X] (a : X) : IsSimpleOrder (BlockMem G a) ↔ IsPreprimitive G X
参数：a : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `MulAction.IsPreprimitive.of_isTrivialBlock_base`：∀ {G : Type u_1} {X : T
ype u_2} [inst : Group G] [inst_1 : MulAction G X] [MulAction.IsPretransitive G 
X] (a : X),   (∀ {B : Set X}, a ∈ B →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用定理 `MulAction.BlockMem.instNontrivial`：∀ (G : Type u_1) [inst : Group G] {X 
: Type u_2} [inst_1 : MulAction G X] [Nontrivial X] (a : X),   Nontrivial (MulAc
tion.BlockMem G a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
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
/-
**MulAction.isCoatom_stabilizer_iff_preprimitive** 是 Mathlib 中的一个定理，位于命名空间 `MulA
ction`。
形式化陈述：isCoatom_stabilizer_iff_preprimitive [IsPretransitive G X] [Nontrivial X] 
(a : X) : IsCoatom (stabilizer G a) ↔ IsPreprimitive G X
参数：a : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.isSimpleOrder_blockMem_iff_isPreprimitive`：isSimpleOrder_block
Mem_iff_isPreprimitive [IsPretransitive G X] [Nontrivial X] (a : X) : IsSimpleOr
der (BlockMem G a) ↔ IsPreprimitive G X
· 使用定理 `Set.isSimpleOrder_Ici_iff_isCoatom`：isSimpleOrder_Ici_iff_isCoatom [Part
ialOrder α] [OrderTop α] {a : α} : IsSimpleOrder (Ici a) ↔ IsCoatom a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderIso.isCoatom_iff`：isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o 
β) (a : α) : IsCoatom (f a) ↔ IsCoatom a
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCoatom_stabilizer_iff_preprimitive [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsCoatom (stabilizer G a) ↔ IsPreprimitive G X := by
  rw [← isSimpleOrder_blockMem_iff_isPreprimitive G a, ← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (block_stabilizerOrderIso G a), OrderIso.map_bot]

/-- In a preprimitive action, stabilizers are maximal subgroups -/
@[to_additive /-- In a preprimitive action, stabilizers are maximal subgroups. -/]
/-
**MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive** 是 Mathlib 中的一
个定理，位于命名空间 `MulAction.IsPreprimitive`。
形式化陈述：∀ (G : Type u_3) [inst : Group G] {X : Type u_4} [inst_1 : MulAction G X] 
[Nontrivial X] [MulAction.IsPreprimitive G X]   (a : X), IsCoatom (MulAction.sta
bilizer G a)
参数：G : Type u_3；a : X；MulAction.stabilizer G a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.isCoatom_stabilizer_iff_preprimitive`：isCoatom_stabilizer_iff_
preprimitive [IsPretransitive G X] [Nontrivial X] (a : X) : IsCoatom (stabilizer
 G a) ↔ IsPreprimitive G X
· 使用定理 `MulAction.IsPreprimitive.toIsPretransitive`：∀ {G : Type u_1} {X : Type u
_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X], MulAction.IsPretran
sitive G X

--- 原说明 ---
In a preprimitive action, stabilizers are maximal subgroups
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
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
/-
**MulAction.IsPreprimitive.of_prime_card** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Is
Preprimitive`。
形式化陈述：of_prime_card [hGX : IsPretransitive G X] (hp : Nat.Prime (Nat.card X)) : 
IsPreprimitive G X
参数：hp : Nat.Prime (Nat.card X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.card_ne_zero`：card_ne_zero : Nat.card α != 0 ↔ Nonempty α ∧ Finite α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_ncard`：eq_univ_iff_ncard [Finite α] (s : Set α) : s = un
iv ↔ ncard s = Nat.card α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.dvd_iff_eq`：∀ {p a : ℕ}, Nat.Prime p → a ≠ 1 → (a ∣ p ↔ p = a)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.one_lt_ncard`：one_lt_ncard (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `MulAction.IsBlock.ncard_dvd_card`：ncard_dvd_card (hB : IsBlock G B) (hB_
ne : B.Nonempty) : Set.ncard B ∣ Nat.card X
· 使用定理 `Set.Nontrivial.nonempty`：∀ {α : Type u} {s : Set α}, s.Nontrivial → s.No
nempty
· 使用定理 `Set.subsingleton_or_nontrivial`：∀ {α : Type u} (s : Set α), s.Subsinglet
on ∨ s.Nontrivial

--- 原说明 ---
A pretransitive action on a set of prime order is preprimitive
-/
theorem of_prime_card [hGX : IsPretransitive G X] (hp : Nat.Prime (Nat.card X)) :
    IsPreprimitive G X := by
  refine ⟨fun {B} hB ↦ B.subsingleton_or_nontrivial.imp id fun hB' ↦ ?_⟩
  have : Finite X := (Nat.card_ne_zero.mp hp.ne_zero).2
  rw [Set.eq_univ_iff_ncard, eq_comm, ← hp.dvd_iff_eq ((Set.one_lt_ncard).mpr hB').ne']
  exact hB.ncard_dvd_card hB'.nonempty

variable {φ : G → H} {f : X →ₑ[φ] Y}

/-- The codomain of an equivariant map of large image is preprimitive if the domain is. -/
@[to_additive
/-- The codomain of an equivariant map of large image is preprimitive if the domain is. -/]
/-
**MulAction.IsPreprimitive.of_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsPre
primitive`。
形式化陈述：of_card_lt [Finite Y] [IsPretransitive H Y] [IsPreprimitive G X] (hf' : Na
t.card Y < 2 * (Set.range f).ncard) : IsPreprimitive H Y
参数：hf' : Nat.card Y < 2 * (Set.range f).ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MulAction.IsTrivialBlock.eq_1`：∀ {X : Type u_2} (B : Set X), MulAction.I
sTrivialBlock B = (B.Subsingleton ∨ B = Set.univ)
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `lt_of_mul_lt_mul_right'`：lt_of_mul_lt_mul_right' [i : MulRightReflectLT 
α] {a b c : α} (bc : b * a < c * a) : b < c
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq`：ncard_block_mul_ncard_
orbit_eq (hB : IsBlock G B) (hB_ne : B.Nonempty) : Set.ncard B * Set.ncard (orbi
t G B) = Nat.card X
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Setoid.IsPartition.ncard_eq_finsum`：Setoid.IsPartition.ncard_eq_finsum {
α : Type*} {P : Set (Set α)} (hP : Setoid.IsPartition P) (s : Set α) (hs : s.Fin
ite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MulAction.IsBlock.isBlockSystem`：∀ {G : Type u_1} [inst : Group G] {X : 
Type u_2} [inst_1 : MulAction G X] {B : Set X}   [hGX : MulAction.IsPretransitiv
e G X],   MulAction.I…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `finsum_eq_sum_of_fintype`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCom
mMonoid M] [inst_1 : Fintype α] (f : α → M), ∑ᶠ (i : α), f i = ∑ i, f i
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.image_preimage_eq_range_inter`：image_preimage_eq_range_inter {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = range f inter t
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
· 使用定理 `MulAction.IsBlock.preimage`：∀ {G : Type u_1} [inst : Group G] {X : Type 
u_2} [inst_1 : MulAction G X] {B : Set X} {H : Type u_3} {Y : Type u_4}   [inst_
2 : Group H] [in…
· 使用定理 `MulAction.IsBlock.translate`：∀ {G : Type u_1} [inst : Group G] {X : Type
 u_2} [inst_1 : MulAction G X] {B : Set X} (g : G),   MulAction.IsBlock G B → Mu
lAction.IsBlock G…
· 使用定理 `MulAction.IsBlock.eq_univ_of_card_lt`：eq_univ_of_card_lt [hX : Finite X]
 (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2) : B = Set.univ
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
（共 48 条，此处仅展示前 30 条）
-/
theorem of_card_lt [Finite Y] [IsPretransitive H Y] [IsPreprimitive G X]
    (hf' : Nat.card Y < 2 * (Set.range f).ncard) :
    IsPreprimitive H Y := by
  refine ⟨fun {B} hB ↦ ?_⟩
  rcases B.eq_empty_or_nonempty with hB' | hB'; · simp [IsTrivialBlock, hB']
  rw [IsTrivialBlock, or_iff_not_imp_right]
  intro hB_ne_top
  -- we need Set.Subsingleton B ↔ Set.ncard B ≤ 1
  suffices Set.ncard B < 2 by simpa [Nat.lt_succ_iff] using this
  -- We reduce to proving that (Set.range f).ncard ≤ (orbit N B).ncard
  apply lt_of_mul_lt_mul_right' (hf'.trans_le' _)
  simp only [← hB.ncard_block_mul_ncard_orbit_eq hB']
  apply Nat.mul_le_mul_left
  -- We reduce to proving that (Set.range f ∩ g • B).ncard ≤ 1 for every g
  have hfin := Fintype.ofFinite (Set.range fun g : H ↦ g • B)
  rw [(hB.isBlockSystem hB').left.ncard_eq_finsum, finsum_eq_sum_of_fintype]
  apply le_trans (Finset.sum_le_card_nsmul _ _ 1 _)
  · rw [nsmul_one, Finset.card_univ, ← Set.toFinset_card, ← Set.ncard_eq_toFinset_card',
      orbit, Nat.cast_id]
  · rintro ⟨x, ⟨g, rfl⟩⟩ -
    suffices Set.Subsingleton (Set.range f ∩ g • B) by simpa
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
    rw [mul_comm, mul_le_mul_iff_left₀ Nat.succ_pos']
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
/-
**MulAction.IsPreprimitive.exists_mem_smul_and_notMem_smul** 是 Mathlib 中的一个定理，位于
命名空间 `MulAction.IsPreprimitive`。
形式化陈述：exists_mem_smul_and_notMem_smul [IsPreprimitive G X] {A : Set X} (hfA : A.
Finite) (hA : A.Nonempty) (hA' : A != .univ) {a b : X} (h : a != b) : exists g :
 G, a in g • A ∧ b ∉ g • A
参数：hfA : A.Finite；hA : A.Nonempty；hA' : A != .univ；h : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
· 使用定理 `MulAction.IsBlock.of_subset`：of_subset (a : X) (hfB : B.Finite) : IsBloc
k G (⋂ (k : G) (_ : a in k • B), k • B)
· 使用定理 `MulAction.IsQuasiPreprimitive.toIsPretransitive`：∀ {G : Type u_1} {X : T
ype u_2} {inst : Group G} {inst_1 : MulAction G X} [self : MulAction.IsQuasiPrep
rimitive G X],   MulAction.IsPretrans…
· 使用定理 `MulAction.IsPreprimitive.isQuasiPreprimitive`：∀ {M : Type u_3} [inst : G
roup M] {α : Type u_4} [inst_1 : MulAction M α] [MulAction.IsPreprimitive M α], 
  MulAction.IsQuasiPreprimitive M …
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem exists_mem_smul_and_notMem_smul [IsPreprimitive G X]
    {A : Set X} (hfA : A.Finite) (hA : A.Nonempty) (hA' : A ≠ .univ) {a b : X} (h : a ≠ b) :
    ∃ g : G, a ∈ g • A ∧ b ∉ g • A := by
  let B := ⋂ (g : G) (_ : a ∈ g • A), g • A
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
    suffices ∃ g : G, a ∈ g • A by
      obtain ⟨g, hg⟩ := this
      have : B ⊆ g • A := Set.biInter_subset_of_mem hg
      rw [hyp, Set.univ_subset_iff, ← eq_inv_smul_iff] at this
      rw [this, Set.smul_set_univ]
    -- ∃ (g : M), a ∈ g • A
    obtain ⟨x, hx⟩ := hA
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x a
    use g, x

end IsPreprimitive

end Finite

end MulAction

