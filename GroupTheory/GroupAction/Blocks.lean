/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Data.Setoid.Partition
public import Mathlib.GroupTheory.GroupAction.Pointwise
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.IntervalCases

/-! # Blocks

Given `SMul G X`, an action of a type `G` on a type `X`, we define

- the predicate `MulAction.IsBlock G B` states that `B : Set X` is a block,
  which means that the sets `g • B`, for `g ∈ G`, are equal or disjoint.
  Under `Group G` and `MulAction G X`, this is equivalent to the classical
  definition `MulAction.IsBlock.def_one`

- a bunch of lemmas that give examples of “trivial” blocks : ⊥, ⊤, singletons,
  and non-trivial blocks: orbit of the group, orbit of a normal subgroup…

The non-existence of nontrivial blocks is the definition of primitive actions.

## Results for actions on finite sets

- `MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq` : The cardinality of a block
  multiplied by the number of its translates is the cardinal of the ambient type

- `MulAction.IsBlock.eq_univ_of_card_lt` : a too large block is equal to `Set.univ`

- `MulAction.IsBlock.subsingleton_of_card_lt` : a too small block is a subsingleton

- `MulAction.IsBlock.of_subset` : the intersections of the translates of a finite subset
  that contain a given point is a block

- `MulAction.BlockMem` : the type of blocks containing a given element

- `MulAction.BlockMem.instBoundedOrder` :
  the type of blocks containing a given element is a bounded order.

## References

We follow [Wielandt-1964].

-/

@[expose] public section

open Set
open scoped Pointwise

namespace MulAction

section orbits

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

@[to_additive]
/-
**MulAction.orbit.eq_or_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.orbit`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
(a b : X),   MulAction.orbit G a = MulAction.orbit G b ∨ Disjoint (MulAction.orb
it G a) (MulAction.orbit G b)
参数：a b : X；MulAction.orbit G a；MulAction.orbit G b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem orbit.eq_or_disjoint (a b : X) :
    orbit G a = orbit G b ∨ Disjoint (orbit G a) (orbit G b) := by
  apply (em (Disjoint (orbit G a) (orbit G b))).symm.imp _ id
  simp +contextual
    only [Set.not_disjoint_iff, ← orbit_eq_iff, forall_exists_index, eq_comm, implies_true]

@[to_additive]
/-
**MulAction.orbit.pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.orbit`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X],
   (Set.range fun x => MulAction.orbit G x).PairwiseDisjoint id
参数：Set.range fun x => MulAction.orbit G x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `MulAction.orbit.eq_or_disjoint`：∀ {G : Type u_1} [inst : Group G] {X : T
ype u_2} [inst_1 : MulAction G X] (a b : X),   MulAction.orbit G a = MulAction.o
rbit G b ∨ Disjoint …
-/
theorem orbit.pairwiseDisjoint :
    (Set.range fun x : X => orbit G x).PairwiseDisjoint id := by
  rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩ h
  contrapose! h
  exact (orbit.eq_or_disjoint x y).resolve_right h

/-- Orbits of an element form a partition -/
@[to_additive /-- Orbits of an element form a partition -/]
/-
**MulAction.IsPartition.of_orbits** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsPartiti
on`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X],
   Setoid.IsPartition (Set.range fun a => MulAction.orbit G a)
参数：Set.range fun a => MulAction.orbit G a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty`：∀ {α : Type u_2}
 {s : Set (Set α)}, s.PairwiseDisjoint id → (∀ (a : α), ∃ x ∈ s, a ∈ x) → ∅ ∉ s 
→ Setoid.IsPartition s
· 使用定理 `MulAction.orbit.pairwiseDisjoint`：∀ {G : Type u_1} [inst : Group G] {X :
 Type u_2} [inst_1 : MulAction G X],   (Set.range fun x => MulAction.orbit G x).
PairwiseDisjoint id
· 使用定理 `MulAction.mem_orbit_self`：mem_orbit_self (a : α) : a in orbit M a
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `MulAction.nonempty_orbit`：nonempty_orbit (a : α) : Set.Nonempty (orbit M
 a)

--- 原说明 ---
Orbits of an element form a partition
-/
theorem IsPartition.of_orbits :
    Setoid.IsPartition (Set.range fun a : X => orbit G a) := by
  apply orbit.pairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · intro x
    exact ⟨_, ⟨x, rfl⟩, mem_orbit_self x⟩
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact (MulAction.nonempty_orbit a).ne_empty ha

end orbits

section SMul

variable (G : Type*) {X : Type*} [SMul G X] {B : Set X} {a : X}

-- Change terminology to IsFullyInvariant?
/-- A set `B` is a `G`-fixed block if `g • B = B` for all `g : G`. -/
@[to_additive /-- A set `B` is a `G`-fixed block if `g +ᵥ B = B` for all `g : G`. -/]
/-
**MulAction.IsFixedBlock** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：IsFixedBlock (B : Set X)
参数：B : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `B` is a `G`-fixed block if `g • B = B` for all `g : G`.
-/
def IsFixedBlock (B : Set X) := ∀ g : G, g • B = B

/-- A set `B` is a `G`-invariant block if `g • B ⊆ B` for all `g : G`.

Note: It is not necessarily a block when the action is not by a group. -/
@[to_additive
/-- A set `B` is a `G`-invariant block if `g +ᵥ B ⊆ B` for all `g : G`.

Note: It is not necessarily a block when the action is not by a group. -/]
/-
**MulAction.IsInvariantBlock** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：IsInvariantBlock (B : Set X)
参数：B : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsInvariantBlock (B : Set X) := ∀ g : G, g • B ⊆ B

section IsTrivialBlock

/-- A trivial block is a `Set X` which is either a subsingleton or `univ`.

Note: It is not necessarily a block when the action is not by a group. -/
@[to_additive
/-- A trivial block is a `Set X` which is either a subsingleton or `univ`.

Note: It is not necessarily a block when the action is not by a group. -/]
/-
**MulAction.IsTrivialBlock** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：IsTrivialBlock (B : Set X)
参数：B : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsTrivialBlock (B : Set X) := B.Subsingleton ∨ B = univ

variable {M α N β : Type*}

section monoid

variable [Monoid M] [MulAction M α] [Monoid N] [MulAction N β]

@[to_additive]
/-
**MulAction.IsTrivialBlock.image** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsTrivialB
lock`。
形式化陈述：∀ {M : Type u_3} {α : Type u_4} {N : Type u_5} {β : Type u_6} [inst : Mono
id M] [inst_1 : MulAction M α]   [inst_2 : Monoid N] [inst_3 : MulAction N β] {φ
 : M → N} {f : α →ₑ[φ] β},   Function.Surjective ⇑f → ∀ {B : Set α}, MulAction.I
sTrivialBlock B → MulAction.IsTrivialBlock (⇑f '' B)
参数：⇑f '' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem IsTrivialBlock.image {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f) {B : Set α} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f '' B) := by
  obtain hB | hB := hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.image_univ, Set.range_eq_univ, hf]

@[to_additive]
/-
**MulAction.IsTrivialBlock.preimage** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsTrivi
alBlock`。
形式化陈述：∀ {M : Type u_3} {α : Type u_4} {N : Type u_5} {β : Type u_6} [inst : Mono
id M] [inst_1 : MulAction M α]   [inst_2 : Monoid N] [inst_3 : MulAction N β] {φ
 : M → N} {f : α →ₑ[φ] β},   Function.Injective ⇑f → ∀ {B : Set β}, MulAction.Is
TrivialBlock B → MulAction.IsTrivialBlock (⇑f ⁻¹' B)
参数：⇑f ⁻¹' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `Set.Subsingleton.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
s : Set β}, s.Subsingleton → Function.Injective f → (f ⁻¹' s).Subsingleton
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem IsTrivialBlock.preimage {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Injective f) {B : Set β} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f ⁻¹' B) := by
  obtain hB | hB := hB
  · apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  · apply Or.intro_right; simp only [hB]; apply Set.preimage_univ

end monoid

variable [Group M] [MulAction M α] [Monoid N] [MulAction N β]

@[to_additive]
/-
**MulAction.IsTrivialBlock.smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsTrivialBl
ock`。
形式化陈述：∀ {M : Type u_3} {α : Type u_4} [inst : Group M] [inst_1 : MulAction M α] 
{B : Set α},   MulAction.IsTrivialBlock B → ∀ (g : M), MulAction.IsTrivialBlock 
(g • B)
参数：g : M；g • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.subsingleton_image_iff`：∀ {α : Type u_1} {β : Type u_
2} {f : α → β},   Function.Injective f → ∀ {s : Set α}, (f '' s).Subsingleton ↔ 
s.Subsingleton
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β} {a : α}, (fun x => a • x) '' t = a • t
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x
-/
theorem IsTrivialBlock.smul {B : Set α} (hB : IsTrivialBlock B) (g : M) :
    IsTrivialBlock (g • B) := by
  cases hB with
  | inl h =>
    left
    exact (Function.Injective.subsingleton_image_iff (MulAction.injective g)).mpr h
  | inr h =>
    right
    rw [h, ← Set.image_smul, Set.image_univ_of_surjective (MulAction.surjective g)]

@[to_additive]
/-
**MulAction.IsTrivialBlock.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsTrivi
alBlock`。
形式化陈述：∀ {M : Type u_3} {α : Type u_4} [inst : Group M] [inst_1 : MulAction M α] 
{B : Set α} (g : M),   MulAction.IsTrivialBlock (g • B) ↔ MulAction.IsTrivialBlo
ck B
参数：g : M；g • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulAction.IsTrivialBlock.smul`：∀ {M : Type u_3} {α : Type u_4} [inst : G
roup M] [inst_1 : MulAction M α] {B : Set α},   MulAction.IsTrivialBlock B → ∀ (
g : M), MulAction.I…
-/
theorem IsTrivialBlock.smul_iff {B : Set α} (g : M) :
    IsTrivialBlock (g • B) ↔ IsTrivialBlock B := by
  constructor
  · intro H
    convert! IsTrivialBlock.smul H g⁻¹
    simp only [inv_smul_smul]
  · intro H
    exact IsTrivialBlock.smul H g

end IsTrivialBlock

/-- A set `B` is a `G`-block iff the sets of the form `g • B` are pairwise equal or disjoint. -/
@[to_additive
/-- A set `B` is a `G`-block iff the sets of the form `g +ᵥ B` are pairwise equal or disjoint. -/]
/-
**MulAction.IsBlock** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：IsBlock (B : Set X)
参数：B : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsBlock (B : Set X) := ∀ ⦃g₁ g₂ : G⦄, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B)

variable {G} {s : Set G} {g g₁ g₂ : G}

@[to_additive]
/-
**MulAction.isBlock_iff_smul_eq_smul_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `MulA
ction`。
形式化陈述：isBlock_iff_smul_eq_smul_of_nonempty : IsBlock G B ↔ forall ⦃g₁ g₂ : G⦄, (
g₁ • B inter g₂ • B).Nonempty -> g₁ • B = g₂ • B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isBlock_iff_smul_eq_smul_of_nonempty :
    IsBlock G B ↔ ∀ ⦃g₁ g₂ : G⦄, (g₁ • B ∩ g₂ • B).Nonempty → g₁ • B = g₂ • B := by
  simp_rw [IsBlock, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]
/-
**MulAction.isBlock_iff_pairwiseDisjoint_range_smul** 是 Mathlib 中的一个引理，位于命名空间 `M
ulAction`。
形式化陈述：isBlock_iff_pairwiseDisjoint_range_smul : IsBlock G B ↔ (range fun g : G =
> g • B).PairwiseDisjoint id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Set.pairwiseDisjoint_range_iff`：pairwiseDisjoint_range_iff {α β : Type*}
 {f : α -> (Set β)} : (range f).PairwiseDisjoint id ↔ forall x y, f x != f y -> 
Disjoint (f x) (f y)
-/
lemma isBlock_iff_pairwiseDisjoint_range_smul :
    IsBlock G B ↔ (range fun g : G ↦ g • B).PairwiseDisjoint id := pairwiseDisjoint_range_iff.symm

@[to_additive]
/-
**MulAction.isBlock_iff_smul_eq_smul_or_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `MulA
ction`。
形式化陈述：isBlock_iff_smul_eq_smul_or_disjoint : IsBlock G B ↔ forall g₁ g₂ : G, g₁ 
• B = g₂ • B ∨ Disjoint (g₁ • B) (g₂ • B)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
lemma isBlock_iff_smul_eq_smul_or_disjoint :
    IsBlock G B ↔ ∀ g₁ g₂ : G, g₁ • B = g₂ • B ∨ Disjoint (g₁ • B) (g₂ • B) :=
  forall₂_congr fun _ _ ↦ or_iff_not_imp_left.symm

@[to_additive]
/-
**MulAction.IsBlock.smul_eq_smul_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.
IsBlock`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] {B : Set X} {g₁ g₂ : G},
   MulAction.IsBlock G B → g₁ • B ⊆ g₂ • B → g₁ • B = g₂ • B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.eq_bot_of_le`：Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a
 <= b) : a = ⊥
-/
lemma IsBlock.smul_eq_smul_of_subset (hB : IsBlock G B) (hg : g₁ • B ⊆ g₂ • B) :
    g₁ • B = g₂ • B := by
  by_contra! hg'
  obtain rfl : B = ∅ := by simpa using (hB hg').eq_bot_of_le hg
  simp at hg'

@[to_additive]
/-
**MulAction.IsBlock.not_smul_set_ssubset_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Mul
Action.IsBlock`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] {B : Set X} {g₁ g₂ : G},
 MulAction.IsBlock G B → ¬g₁ • B ⊂ g₂ • B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MulAction.IsBlock.smul_eq_smul_of_subset`：∀ {G : Type u_1} {X : Type u_2
} [inst : SMul G X] {B : Set X} {g₁ g₂ : G},   MulAction.IsBlock G B → g₁ • B ⊆ 
g₂ • B → g₁ • B = g₂ • B
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
-/
lemma IsBlock.not_smul_set_ssubset_smul_set (hB : IsBlock G B) : ¬ g₁ • B ⊂ g₂ • B :=
  fun hab ↦ hab.ne <| hB.smul_eq_smul_of_subset hab.subset

@[to_additive]
/-
**MulAction.IsBlock.disjoint_smul_set_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.
IsBlock`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] {B : Set X} {s : Set G} 
{g : G},   MulAction.IsBlock G B → ¬g • B ⊆ s • B → Disjoint (g • B) (s • B)
参数：g • B；s • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.iUnion_smul_set`：iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a in s,
 a • t = s • t
· 使用定理 `Set.disjoint_iUnion₂_right`：disjoint_iUnion₂_right {s : Set α} {t : fora
ll i, κ i -> Set α} : Disjoint s (⋃ (i) (j), t i j) ↔ forall i j, Disjoint s (t 
i j)
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用引理 `Set.smul_set_subset_smul`：smul_set_subset_smul {s : Set α} : a in s -> a
 • t subseteq s • t
-/
lemma IsBlock.disjoint_smul_set_smul (hB : IsBlock G B) (hgs : ¬ g • B ⊆ s • B) :
    Disjoint (g • B) (s • B) := by
  rw [← iUnion_smul_set, disjoint_iUnion₂_right]
  exact fun b hb ↦ hB fun h ↦ hgs <| h.trans_subset <| smul_set_subset_smul hb

@[to_additive]
/-
**MulAction.IsBlock.disjoint_smul_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.
IsBlock`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] {B : Set X} {s : Set G} 
{g : G},   MulAction.IsBlock G B → ¬g • B ⊆ s • B → Disjoint (s • B) (g • B)
参数：s • B；g • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `MulAction.IsBlock.disjoint_smul_set_smul`：∀ {G : Type u_1} {X : Type u_2
} [inst : SMul G X] {B : Set X} {s : Set G} {g : G},   MulAction.IsBlock G B → ¬
g • B ⊆ s • B → Disjoint (g • …
-/
lemma IsBlock.disjoint_smul_smul_set (hB : IsBlock G B) (hgs : ¬ g • B ⊆ s • B) :
    Disjoint (s • B) (g • B) := (hB.disjoint_smul_set_smul hgs).symm

@[to_additive]
alias ⟨IsBlock.smul_eq_smul_of_nonempty, _⟩ := isBlock_iff_smul_eq_smul_of_nonempty
@[to_additive]
alias ⟨IsBlock.pairwiseDisjoint_range_smul, _⟩ := isBlock_iff_pairwiseDisjoint_range_smul
@[to_additive]
alias ⟨IsBlock.smul_eq_smul_or_disjoint, _⟩ := isBlock_iff_smul_eq_smul_or_disjoint

/-- A fixed block is a block. -/
@[to_additive /-- A fixed block is a block. -/]
/-
**MulAction.IsFixedBlock.isBlock** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsFixedBlo
ck`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] {B : Set X}, MulAction.I
sFixedBlock G B → MulAction.IsBlock G B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A fixed block is a block.
-/
lemma IsFixedBlock.isBlock (hfB : IsFixedBlock G B) : IsBlock G B := by simp [IsBlock, hfB _]

/-- The empty set is a block. -/
@[to_additive (attr := simp) /-- The empty set is a block. -/]
/-
**MulAction.IsBlock.empty** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X], MulAction.IsBlock G ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The empty set is a block.
-/
lemma IsBlock.empty : IsBlock G (∅ : Set X) := by simp [IsBlock]

/-- A singleton is a block. -/
@[to_additive /-- A singleton is a block. -/]
/-
**MulAction.IsBlock.singleton** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] {a : X}, MulAction.IsBlo
ck G {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.smul_set_singleton`：smul_set_singleton : a • ({b} : Set β) = {a • b}
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A singleton is a block.
-/
lemma IsBlock.singleton : IsBlock G ({a} : Set X) := by simp [IsBlock]

/-- Subsingletons are (trivial) blocks. -/
@[to_additive /-- Subsingletons are (trivial) blocks. -/]
/-
**MulAction.IsBlock.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock
`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] {B : Set X}, B.Subsingle
ton → MulAction.IsBlock G B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `MulAction.IsBlock.empty`：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G 
X], MulAction.IsBlock G ∅
· 使用定理 `MulAction.IsBlock.singleton`：∀ {G : Type u_1} {X : Type u_2} [inst : SMu
l G X] {a : X}, MulAction.IsBlock G {a}

--- 原说明 ---
Subsingletons are (trivial) blocks.
-/
lemma IsBlock.of_subsingleton (hB : B.Subsingleton) : IsBlock G B :=
  hB.induction_on .empty fun _ ↦ .singleton

/-- A fixed block is an invariant block. -/
@[to_additive /-- A fixed block is an invariant block. -/]
/-
**MulAction.IsFixedBlock.isInvariantBlock** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.I
sFixedBlock`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : SMul G X] {B : Set X},   MulAction
.IsFixedBlock G B → MulAction.IsInvariantBlock G B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
A fixed block is an invariant block.
-/
lemma IsFixedBlock.isInvariantBlock (hB : IsFixedBlock G B) : IsInvariantBlock G B :=
  fun _ ↦ (hB _).le

end SMul

section Monoid
variable {M X : Type*} [Monoid M] [MulAction M X] {B : Set X} {s : Set M}

@[to_additive]
/-
**MulAction.IsBlock.disjoint_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsB
lock`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} [inst : Monoid M] [inst_1 : MulAction M X]
 {B : Set X} {s : Set M},   MulAction.IsBlock M B → ¬B ⊆ s • B → Disjoint B (s •
 B)
参数：s • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MulAction.IsBlock.disjoint_smul_set_smul`：∀ {G : Type u_1} {X : Type u_2
} [inst : SMul G X] {B : Set X} {s : Set G} {g : G},   MulAction.IsBlock G B → ¬
g • B ⊆ s • B → Disjoint (g • …
-/
lemma IsBlock.disjoint_smul_right (hB : IsBlock M B) (hs : ¬ B ⊆ s • B) : Disjoint B (s • B) := by
  simpa using hB.disjoint_smul_set_smul (g := 1) (by simpa using hs)

@[to_additive]
/-
**MulAction.IsBlock.disjoint_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBl
ock`。
形式化陈述：∀ {M : Type u_1} {X : Type u_2} [inst : Monoid M] [inst_1 : MulAction M X]
 {B : Set X} {s : Set M},   MulAction.IsBlock M B → ¬B ⊆ s • B → Disjoint (s • B
) B
参数：s • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `MulAction.IsBlock.disjoint_smul_right`：∀ {M : Type u_1} {X : Type u_2} [
inst : Monoid M] [inst_1 : MulAction M X] {B : Set X} {s : Set M},   MulAction.I
sBlock M B → ¬B ⊆ s • B → D…
-/
lemma IsBlock.disjoint_smul_left (hB : IsBlock M B) (hs : ¬ B ⊆ s • B) : Disjoint (s • B) B :=
  (hB.disjoint_smul_right hs).symm

end Monoid

section Group

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] {B : Set X}

@[to_additive]
/-
**MulAction.isBlock_iff_disjoint_smul_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `MulAction
`。
形式化陈述：isBlock_iff_disjoint_smul_of_ne : IsBlock G B ↔ forall ⦃g : G⦄, g • B != B
 -> Disjoint (g • B) B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
lemma isBlock_iff_disjoint_smul_of_ne :
    IsBlock G B ↔ ∀ ⦃g : G⦄, g • B ≠ B → Disjoint (g • B) B := by
  refine ⟨fun hB g ↦ by simpa using hB (g₂ := 1), fun hB g₁ g₂ h ↦ ?_⟩
  simp only [disjoint_smul_set_right, ne_eq, ← inv_smul_eq_iff, smul_smul] at h ⊢
  exact hB h

@[to_additive]
/-
**MulAction.isBlock_iff_smul_eq_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `MulAction
`。
形式化陈述：isBlock_iff_smul_eq_of_nonempty : IsBlock G B ↔ forall ⦃g : G⦄, (g • B int
er B).Nonempty -> g • B = B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isBlock_iff_smul_eq_of_nonempty :
    IsBlock G B ↔ ∀ ⦃g : G⦄, (g • B ∩ B).Nonempty → g • B = B := by
  simp_rw [isBlock_iff_disjoint_smul_of_ne, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]
/-
**MulAction.isBlock_iff_smul_eq_or_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `MulAction
`。
形式化陈述：isBlock_iff_smul_eq_or_disjoint : IsBlock G B ↔ forall g : G, g • B = B ∨ 
Disjoint (g • B) B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `MulAction.isBlock_iff_disjoint_smul_of_ne`：isBlock_iff_disjoint_smul_of_
ne : IsBlock G B ↔ forall ⦃g : G⦄, g • B != B -> Disjoint (g • B) B
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
lemma isBlock_iff_smul_eq_or_disjoint :
    IsBlock G B ↔ ∀ g : G, g • B = B ∨ Disjoint (g • B) B :=
  isBlock_iff_disjoint_smul_of_ne.trans <| forall_congr' fun _ ↦ or_iff_not_imp_left.symm

@[to_additive]
/-
**MulAction.isBlock_iff_smul_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：isBlock_iff_smul_eq_of_mem : IsBlock G B ↔ forall ⦃g : G⦄ ⦃a : X⦄, a in B 
-> g • a in B -> g • B = B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isBlock_iff_smul_eq_of_mem :
    IsBlock G B ↔ ∀ ⦃g : G⦄ ⦃a : X⦄, a ∈ B → g • a ∈ B → g • B = B := by
  simp [isBlock_iff_smul_eq_of_nonempty, Set.Nonempty, mem_smul_set]

@[to_additive] alias ⟨IsBlock.disjoint_smul_of_ne, _⟩ := isBlock_iff_disjoint_smul_of_ne
@[to_additive] alias ⟨IsBlock.smul_eq_of_nonempty, _⟩ := isBlock_iff_smul_eq_of_nonempty
@[to_additive] alias ⟨IsBlock.smul_eq_or_disjoint, _⟩ := isBlock_iff_smul_eq_or_disjoint
@[to_additive] alias ⟨IsBlock.smul_eq_of_mem, _⟩ := isBlock_iff_smul_eq_of_mem

-- TODO: Generalise to `SubgroupClass`
/-- If `B` is a `G`-block, then it is also a `H`-block for any subgroup `H` of `G`. -/
@[to_additive
/-- If `B` is a `G`-block, then it is also a `H`-block for any subgroup `H` of `G`. -/]
/-
**MulAction.IsBlock.subgroup** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X} {H : Subgroup G},   MulAction.IsBlock G B → MulAction.IsBlock (↥H) B
参数：↥H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsBlock.subgroup {H : Subgroup G} (hB : IsBlock G B) : IsBlock H B := fun _ _ h ↦ hB h

/-- A block of a group action is invariant iff it is fixed. -/
@[to_additive /-- A block of a group action is invariant iff it is fixed. -/]
/-
**MulAction.isInvariantBlock_iff_isFixedBlock** 是 Mathlib 中的一个引理，位于命名空间 `MulActi
on`。
形式化陈述：isInvariantBlock_iff_isFixedBlock : IsInvariantBlock G B ↔ IsFixedBlock G 
B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
· 使用定理 `MulAction.IsFixedBlock.isInvariantBlock`：∀ {G : Type u_1} {X : Type u_2}
 [inst : SMul G X] {B : Set X},   MulAction.IsFixedBlock G B → MulAction.IsInvar
iantBlock G B

--- 原说明 ---
A block of a group action is invariant iff it is fixed.
-/
lemma isInvariantBlock_iff_isFixedBlock : IsInvariantBlock G B ↔ IsFixedBlock G B :=
  ⟨fun hB g ↦ (hB g).antisymm <| subset_smul_set_iff.2 <| hB _, IsFixedBlock.isInvariantBlock⟩

/-- An invariant block of a group action is a fixed block. -/
@[to_additive /-- An invariant block of a group action is a fixed block. -/]
alias ⟨IsInvariantBlock.isFixedBlock, _⟩ := isInvariantBlock_iff_isFixedBlock

/-- An invariant block of a group action is a block. -/
@[to_additive /-- An invariant block of a group action is a block. -/]
/-
**MulAction.IsInvariantBlock.isBlock** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsInva
riantBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X},   MulAction.IsInvariantBlock G B → MulAction.IsBlock G B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsFixedBlock.isBlock`：∀ {G : Type u_1} {X : Type u_2} [inst : 
SMul G X] {B : Set X}, MulAction.IsFixedBlock G B → MulAction.IsBlock G B
· 使用定理 `MulAction.IsInvariantBlock.isFixedBlock`：∀ {G : Type u_1} [inst : Group 
G] {X : Type u_2} [inst_1 : MulAction G X] {B : Set X},   MulAction.IsInvariantB
lock G B → MulAction.IsFixedB…

--- 原说明 ---
An invariant block of a group action is a block.
-/
lemma IsInvariantBlock.isBlock (hB : IsInvariantBlock G B) : IsBlock G B := hB.isFixedBlock.isBlock

/-- The full set is a fixed block. -/
@[to_additive /-- The full set is a fixed block. -/]
/-
**MulAction.IsFixedBlock.univ** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsFixedBlock`
。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X],
 MulAction.IsFixedBlock G Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The full set is a fixed block.
-/
lemma IsFixedBlock.univ : IsFixedBlock G (univ : Set X) := fun _ ↦ by simp

/-- The full set is a block. -/
@[to_additive (attr := simp) /-- The full set is a block. -/]
/-
**MulAction.IsBlock.univ** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X],
 MulAction.IsBlock G Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsFixedBlock.isBlock`：∀ {G : Type u_1} {X : Type u_2} [inst : 
SMul G X] {B : Set X}, MulAction.IsFixedBlock G B → MulAction.IsBlock G B
· 使用定理 `MulAction.IsFixedBlock.univ`：∀ {G : Type u_1} [inst : Group G] {X : Type
 u_2} [inst_1 : MulAction G X], MulAction.IsFixedBlock G Set.univ

--- 原说明 ---
The full set is a block.
-/
lemma IsBlock.univ : IsBlock G (univ : Set X) := IsFixedBlock.univ.isBlock

/-- The intersection of two blocks is a block. -/
@[to_additive /-- The intersection of two blocks is a block. -/]
/-
**MulAction.IsBlock.inter** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B₁ B₂ : Set X},   MulAction.IsBlock G B₁ → MulAction.IsBlock G B₂ → MulAction.I
sBlock G (B₁ ∩ B₂)
参数：B₁ ∩ B₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The intersection of two blocks is a block.
-/
lemma IsBlock.inter {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂) :
    IsBlock G (B₁ ∩ B₂) := by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_inter] at h₁ h₂ ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  rw [h₁ ⟨a, ha₁.1, ha₂.1⟩, h₂ ⟨a, ha₁.2, ha₂.2⟩]

/-- An intersection of blocks is a block. -/
@[to_additive /-- An intersection of blocks is a block. -/]
/-
**MulAction.IsBlock.iInter** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{ι : Sort u_3} {B : ι → Set X},   (∀ (i : ι), MulAction.IsBlock G (B i)) → MulAc
tion.IsBlock G (⋂ i, B i)
参数：∀ (i : ι), MulAction.IsBlock G (B i)；⋂ i, B i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.smul_set_iInter`：smul_set_iInter {ι : Sort*} (a : α) (t : ι -> Set β
) : (a • ⋂ i, t i) = ⋂ i, a • t i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An intersection of blocks is a block.
-/
lemma IsBlock.iInter {ι : Sort*} {B : ι → Set X} (hB : ∀ i, IsBlock G (B i)) :
    IsBlock G (⋂ i, B i) := by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_iInter] at hB ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  simp_rw [fun i ↦ hB i ⟨a, iInter_subset _ i ha₁, iInter_subset _ i ha₂⟩]

/-- A trivial block is a block. -/
@[to_additive /-- A trivial block is a block. -/]
/-
**MulAction.IsTrivialBlock.isBlock** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsTrivia
lBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X},   MulAction.IsTrivialBlock B → MulAction.IsBlock G B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsBlock.of_subsingleton`：∀ {G : Type u_1} {X : Type u_2} [inst
 : SMul G X] {B : Set X}, B.Subsingleton → MulAction.IsBlock G B
· 使用定理 `MulAction.IsBlock.univ`：∀ {G : Type u_1} [inst : Group G] {X : Type u_2}
 [inst_1 : MulAction G X], MulAction.IsBlock G Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A trivial block is a block.
-/
lemma IsTrivialBlock.isBlock (hB : IsTrivialBlock B) : IsBlock G B := by
  obtain hB | rfl := hB
  · exact .of_subsingleton hB
  · exact .univ

/-- An orbit is a fixed block. -/
@[to_additive /-- An orbit is a fixed block. -/]
/-
**MulAction.IsFixedBlock.orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsFixedBlock
`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
(a : X),   MulAction.IsFixedBlock G (MulAction.orbit G a)
参数：a : X；MulAction.orbit G a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.smul_orbit`：smul_orbit (g : G) (a : α) : g • orbit G a = orbit
 G a

--- 原说明 ---
An orbit is a fixed block.
-/
protected lemma IsFixedBlock.orbit (a : X) : IsFixedBlock G (orbit G a) := (smul_orbit · a)

/-- An orbit is a block. -/
@[to_additive /-- An orbit is a block. -/]
/-
**MulAction.IsBlock.orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
(a : X),   MulAction.IsBlock G (MulAction.orbit G a)
参数：a : X；MulAction.orbit G a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsFixedBlock.isBlock`：∀ {G : Type u_1} {X : Type u_2} [inst : 
SMul G X] {B : Set X}, MulAction.IsFixedBlock G B → MulAction.IsBlock G B
· 使用定理 `MulAction.IsFixedBlock.orbit`：∀ {G : Type u_1} [inst : Group G] {X : Typ
e u_2} [inst_1 : MulAction G X] (a : X),   MulAction.IsFixedBlock G (MulAction.o
rbit G a)

--- 原说明 ---
An orbit is a block.
-/
protected lemma IsBlock.orbit (a : X) : IsBlock G (orbit G a) := (IsFixedBlock.orbit a).isBlock

@[to_additive]
/-
**MulAction.isBlock_top** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：isBlock_top : IsBlock (⊤ : Subgroup G) B ↔ IsBlock G B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
-/
lemma isBlock_top : IsBlock (⊤ : Subgroup G) B ↔ IsBlock G B :=
  Subgroup.topEquiv.toEquiv.forall_congr fun _ ↦ Subgroup.topEquiv.toEquiv.forall_congr_left

@[to_additive]
/-
**MulAction.IsBlock.preimage** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X} {H : Type u_3} {Y : Type u_4}   [inst_2 : Group H] [inst_3 : MulActi
on H Y] {φ : H → G} (j : Y →ₑ[φ] X),   MulAction.IsBlock G B → MulAction.IsBlock
 H (⇑j ⁻¹' B)
参数：j : Y →ₑ[φ] X；⇑j ⁻¹' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Group.preimage_smul_setₛₗ`：Group.preimage_smul_setₛₗ {G H α β : Type*} [
Group G] [Group H] (σ : G -> H) [MulAction G α] [MulAction H β] {F : Type*} [Fun
Like F α β] [Mu…
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
lemma IsBlock.preimage {H Y : Type*} [Group H] [MulAction H Y]
    {φ : H → G} (j : Y →ₑ[φ] X) (hB : IsBlock G B) :
    IsBlock H (j ⁻¹' B) := by
  rintro g₁ g₂ hg
  rw [← Group.preimage_smul_setₛₗ, ← Group.preimage_smul_setₛₗ] at hg ⊢
  exact (hB <| ne_of_apply_ne _ hg).preimage _

@[to_additive]
/-
**MulAction.IsBlock.image** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X} {H : Type u_3} {Y : Type u_4}   [inst_2 : SMul H Y] {φ : G → H} (j :
 X →ₑ[φ] Y),   Function.Surjective φ → Function.Injective ⇑j → MulAction.IsBlock
 G B → MulAction.IsBlock H (⇑j '' B)
参数：j : X →ₑ[φ] Y；⇑j '' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.disjoint_image_of_injective`：disjoint_image_of_injective (hf : Injec
tive f) {s t : Set α} (hd : Disjoint s t) : Disjoint (f '' s) (f '' t)
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem IsBlock.image {H Y : Type*} [SMul H Y] {φ : G → H} (j : X →ₑ[φ] Y)
    (hφ : Function.Surjective φ) (hj : Function.Injective j) (hB : IsBlock G B) :
    IsBlock H (j '' B) := by
  simp only [IsBlock, hφ.forall, ← image_smul_setₛₗ]
  exact fun g₁ g₂ hg ↦ disjoint_image_of_injective hj <| hB <| ne_of_apply_ne _ hg

@[to_additive]
/-
**MulAction.IsBlock.subtype_val_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Is
Block`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X} {C : SubMulAction G X},   MulAction.IsBlock G B → MulAction.IsBlock 
G (Subtype.val ⁻¹' B)
参数：Subtype.val ⁻¹' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsBlock.preimage`：∀ {G : Type u_1} [inst : Group G] {X : Type 
u_2} [inst_1 : MulAction G X] {B : Set X} {H : Type u_3} {Y : Type u_4}   [inst_
2 : Group H] [in…
-/
theorem IsBlock.subtype_val_preimage {C : SubMulAction G X} (hB : IsBlock G B) :
    IsBlock G (Subtype.val ⁻¹' B : Set C) :=
  hB.preimage C.inclusion

@[to_additive]
/-
**MulAction.isBlock_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isBlock_subtypeVal {C : SubMulAction G X} {B : Set C} : IsBlock G (Subtype
.val '' B : Set X) ↔ IsBlock G B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubMulAction.inclusion.coe_eq`：∀ {M : Type u_1} {α : Type u_2} [inst : M
onoid M] [inst_1 : MulAction M α] (s : SubMulAction M α),   ⇑s.inclusion = Subty
pe.val
· 使用定理 `image_smul_set`：image_smul_set (f : F) (c : M) (s : Set α) : f '' (c • s
) = c • f '' s
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.image_eq_image`：image_eq_image {f : α -> β} (hf : Injective f) : f '
' s = f '' t ↔ s = t
· 使用引理 `SubMulAction.inclusion_injective`：inclusion_injective (s : SubMulAction 
M α) : Function.Injective s.inclusion
· 使用定理 `Set.disjoint_image_iff`：disjoint_image_iff (hf : Injective f) : Disjoint
 (f '' s) (f '' t) ↔ Disjoint s t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBlock_subtypeVal {C : SubMulAction G X} {B : Set C} :
    IsBlock G (Subtype.val '' B : Set X) ↔ IsBlock G B := by
  refine forall₂_congr fun g₁ g₂ ↦ ?_
  rw [← SubMulAction.inclusion.coe_eq, ← image_smul_set, ← image_smul_set, ne_eq,
    Set.image_eq_image C.inclusion_injective, disjoint_image_iff C.inclusion_injective]

@[to_additive]
/-
**MulAction.IsBlock.of_subgroup_of_conjugate** 是 Mathlib 中的一个定理，位于命名空间 `MulActio
n.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X} {H : Subgroup G},   MulAction.IsBlock (↥H) B →     ∀ (g : G), MulAct
ion.IsBlock (↥(Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) H)) (g • B)
参数：↥H；g : G；↥(Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) H)；g • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.isBlock_iff_smul_eq_or_disjoint`：isBlock_iff_smul_eq_or_disjoi
nt : IsBlock G B ↔ forall g : G, g • B = B ∨ Disjoint (g • B) B
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_map`：mem_map {f : G ->* N} {K : Subgroup G} {y : N} : y in 
K.map f ↔ exists x in K, f x = y
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `MulAction.IsBlock.smul_eq_or_disjoint`：∀ {G : Type u_1} [inst : Group G]
 {X : Type u_2} [inst_1 : MulAction G X] {B : Set X},   MulAction.IsBlock G B → 
∀ (g : G), g • B = B ∨ Disj…
· 使用定理 `Set.disjoint_image_of_injective`：disjoint_image_of_injective (hf : Injec
tive f) {s t : Set α} (hd : Disjoint s t) : Disjoint (f '' s) (f '' t)
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem IsBlock.of_subgroup_of_conjugate {H : Subgroup G} (hB : IsBlock H B) (g : G) :
    IsBlock (H.map (MulAut.conj g).toMonoidHom) (g • B) := by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro h'
  obtain ⟨h, hH, hh⟩ := Subgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hh
  suffices h' • g • B = g • h • B by
    simp only [this]
    apply (hB.smul_eq_or_disjoint ⟨h, hH⟩).imp
    · intro; congr
    · exact Set.disjoint_image_of_injective (MulAction.injective g)
  suffices (h' : G) • g • B = g • h • B by
    rw [← this]; rfl
  rw [← hh, smul_smul (g * h * g⁻¹) g B, smul_smul g h B, inv_mul_cancel_right]

/-- A translate of a block is a block -/
@[to_additive]
/-
**MulAction.IsBlock.translate** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X} (g : G),   MulAction.IsBlock G B → MulAction.IsBlock G (g • B)
参数：g : G；g • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MulAction.isBlock_top`：isBlock_top : IsBlock (⊤ : Subgroup G) B ↔ IsBloc
k G B
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.map_comap_eq_self_of_surjective`：map_comap_eq_self_of_surjectiv
e {f : G ->* N} (h : Function.Surjective f) (H : Subgroup N) : map f (comap f H)
 = H
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `MulAction.IsBlock.of_subgroup_of_conjugate`：∀ {G : Type u_1} [inst : Gro
up G] {X : Type u_2} [inst_1 : MulAction G X] {B : Set X} {H : Subgroup G},   Mu
lAction.IsBlock (↥H) B →     ∀ (…
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤

--- 原说明 ---
A translate of a block is a block
-/
theorem IsBlock.translate (g : G) (hB : IsBlock G B) :
    IsBlock G (g • B) := by
  rw [← isBlock_top] at hB ⊢
  rw [← Subgroup.map_comap_eq_self_of_surjective
          (G := G) (f := MulAut.conj g) (MulAut.conj g).surjective ⊤]
  apply IsBlock.of_subgroup_of_conjugate
  rwa [Subgroup.comap_top]

variable (G) in
/-- For `SMul G X`, a block system of `X` is a partition of `X` into blocks
for the action of `G` -/
@[to_additive /-- For `VAdd G X`, a block system of `X` is a partition of `X` into blocks
for the additive action of `G` -/]
/-
**MulAction.IsBlockSystem** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：IsBlockSystem (ℬ : Set (Set X))
参数：ℬ : Set (Set X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsBlockSystem (ℬ : Set (Set X)) := Setoid.IsPartition ℬ ∧ ∀ ⦃B⦄, B ∈ ℬ → IsBlock G B

/-- Translates of a block form a block system -/
@[to_additive /-- Translates of a block form a block system -/]
/-
**MulAction.IsBlock.isBlockSystem** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X}   [hGX : MulAction.IsPretransitive G X],   MulAction.IsBlock G B → B
.Nonempty → MulAction.IsBlockSystem G (Set.range fun g => g • B)
参数：Set.range fun g => g • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulAction.IsBlock.smul_eq_smul_of_nonempty`：∀ {G : Type u_1} {X : Type u
_2} [inst : SMul G X] {B : Set X},   MulAction.IsBlock G B → ∀ ⦃g₁ g₂ : G⦄, (g₁ 
• B ∩ g₂ • B).Nonempty → g₁ • B …
· 使用定理 `MulAction.IsBlock.translate`：∀ {G : Type u_1} [inst : Group G] {X : Type
 u_2} [inst_1 : MulAction G X] {B : Set X} (g : G),   MulAction.IsBlock G B → Mu
lAction.IsBlock G…

--- 原说明 ---
Translates of a block form a block system
-/
theorem IsBlock.isBlockSystem [hGX : MulAction.IsPretransitive G X]
    (hB : IsBlock G B) (hBe : B.Nonempty) :
    IsBlockSystem G (Set.range fun g : G => g • B) := by
  refine ⟨⟨?nonempty, ?cover⟩, ?mem_blocks⟩
  case mem_blocks => rintro B' ⟨g, rfl⟩; exact hB.translate g
  · simp only [Set.mem_range, not_exists]
    intro g hg
    apply hBe.ne_empty
    simpa only [Set.smul_set_eq_empty] using hg
  · intro a
    obtain ⟨b : X, hb : b ∈ B⟩ := hBe
    obtain ⟨g, rfl⟩ := exists_smul_eq G b a
    use g • B
    simp only [Set.smul_mem_smul_set_iff, hb, Set.mem_range,
      exists_apply_eq_apply, and_imp, forall_exists_index,
      forall_apply_eq_imp_iff, true_and]
    exact fun g' ha ↦ hB.smul_eq_smul_of_nonempty ⟨g • b, ha, ⟨b, hb, rfl⟩⟩

section Normal

@[to_additive]
/-
**MulAction.smul_orbit_eq_orbit_smul** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：smul_orbit_eq_orbit_smul (N : Subgroup G) [nN : N.Normal] (a : X) (g : G) 
: g • orbit N a = orbit N (g • a)
参数：N : Subgroup G；a : X；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.smul_set_range`：smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι
 -> β) : a • range f = range fun i => a • f i
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.Normal.conj_mem'`：conj_mem' (nH : H.Normal) (n : G) (hn : n in 
H) (g : G) : g⁻¹ * n * g in H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_orbit_eq_orbit_smul (N : Subgroup G) [nN : N.Normal] (a : X) (g : G) :
    g • orbit N a = orbit N (g • a) := by
  simp only [orbit, Set.smul_set_range]
  ext
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g * k * g⁻¹, nN.conj_mem k hk g⟩
    simp only [Subgroup.mk_smul]
    rw [smul_smul, inv_mul_cancel_right, ← smul_smul]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g⁻¹ * k * g, nN.conj_mem' k hk g⟩
    simp only [Subgroup.mk_smul]
    simp only [← smul_smul, smul_inv_smul]

/-- An orbit of a normal subgroup is a block -/
@[to_additive /-- An orbit of a normal subgroup is a block -/]
/-
**MulAction.IsBlock.orbit_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock
`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{N : Subgroup G} [N.Normal] (a : X),   MulAction.IsBlock G (MulAction.orbit (↥N)
 a)
参数：a : X；MulAction.orbit (↥N) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.isBlock_iff_smul_eq_or_disjoint`：isBlock_iff_smul_eq_or_disjoi
nt : IsBlock G B ↔ forall g : G, g • B = B ∨ Disjoint (g • B) B
· 使用引理 `MulAction.smul_orbit_eq_orbit_smul`：smul_orbit_eq_orbit_smul (N : Subgro
up G) [nN : N.Normal] (a : X) (g : G) : g • orbit N a = orbit N (g • a)
· 使用定理 `MulAction.orbit.eq_or_disjoint`：∀ {G : Type u_1} [inst : Group G] {X : T
ype u_2} [inst_1 : MulAction G X] (a b : X),   MulAction.orbit G a = MulAction.o
rbit G b ∨ Disjoint …

--- 原说明 ---
An orbit of a normal subgroup is a block
-/
theorem IsBlock.orbit_of_normal {N : Subgroup G} [N.Normal] (a : X) :
    IsBlock G (orbit N a) := by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro g
  rw [smul_orbit_eq_orbit_smul]
  apply orbit.eq_or_disjoint

/-- The orbits of a normal subgroup form a block system -/
@[to_additive /-- The orbits of a normal subgroup form a block system -/]
/-
**MulAction.IsBlockSystem.of_normal** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock
System`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{N : Subgroup G} [N.Normal],   MulAction.IsBlockSystem G (Set.range fun a => Mul
Action.orbit (↥N) a)
参数：Set.range fun a => MulAction.orbit (↥N) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPartition.of_orbits`：∀ {G : Type u_1} [inst : Group G] {X : 
Type u_2} [inst_1 : MulAction G X],   Setoid.IsPartition (Set.range fun a => Mul
Action.orbit G a)
· 使用定理 `MulAction.IsBlock.orbit_of_normal`：∀ {G : Type u_1} [inst : Group G] {X 
: Type u_2} [inst_1 : MulAction G X] {N : Subgroup G} [N.Normal] (a : X),   MulA
ction.IsBlock G (MulAct…

--- 原说明 ---
The orbits of a normal subgroup form a block system
-/
theorem IsBlockSystem.of_normal {N : Subgroup G} [N.Normal] :
    IsBlockSystem G (Set.range fun a : X => orbit N a) := by
  constructor
  · apply IsPartition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact .orbit_of_normal a

section Group
variable {S H : Type*} [Group H] [SetLike S H] [SubgroupClass S H] {s : S} {a : G}

/-!
Annoyingly, it seems like the following two lemmas cannot be unified.
-/

section Left
variable [MulAction G H] [IsScalarTower G H H]

/-- See `MulAction.isBlock_subgroup'` for a version that works for the right action of a group on
itself. -/
@[to_additive /-- See `AddAction.isBlock_subgroup'` for a version that works for the right action
of a group on itself. -/]
/-
**MulAction.isBlock_subgroup** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：isBlock_subgroup : IsBlock G (s : Set H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_coe_set`：smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {
s : S} {a : G} (ha : a in s) : a • (s : Set G) = s
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
lemma isBlock_subgroup : IsBlock G (s : Set H) := by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe_set hc, ← smul_assoc, ← hcd, smul_assoc, smul_coe_set hc, smul_coe_set hd]

end Left

section Right
variable [MulAction G H] [IsScalarTower G Hᵐᵒᵖ H]

open MulOpposite

/-- See `MulAction.isBlock_subgroup` for a version that works for the left action of a group on
itself. -/
@[to_additive /-- See `AddAction.isBlock_subgroup` for a version that works for the left action
of a group on itself. -/]
/-
**MulAction.isBlock_subgroup'** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：isBlock_subgroup' : IsBlock G (s : Set H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `op_smul_coe_set`：op_smul_coe_set [Group G] [SetLike S G] [SubgroupClass 
S G] {s : S} {a : G} (ha : a in s) : MulOpposite.op a • (s : Set G) = s
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `MulOpposite.op_smul`：op_smul [SMul α β] (a : α) (b : β) : op (a • b) = a
 • op b
-/
lemma isBlock_subgroup' : IsBlock G (s : Set H) := by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← op_smul_coe_set hc, ← smul_assoc, ← op_smul, ← hcd, op_smul, smul_assoc, op_smul_coe_set hc,
    op_smul_coe_set hd]

end Right
end Group

end Normal

section Stabilizer

/- For transitive actions, construction of the lattice equivalence
  `block_stabilizerOrderIso` between
  - blocks of `MulAction G X` containing a point `a ∈ X`,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/

/-- The orbit of `a` under a subgroup containing the stabilizer of `a` is a block -/
@[to_additive /-- The orbit of `a` under a subgroup containing the stabilizer of `a` is a block -/]
/-
**MulAction.IsBlock.of_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{H : Subgroup G} {a : X},   MulAction.stabilizer G a ≤ H → MulAction.IsBlock G (
MulAction.orbit (↥H) a)
参数：MulAction.orbit (↥H) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.isBlock_iff_smul_eq_of_nonempty`：isBlock_iff_smul_eq_of_nonemp
ty : IsBlock G B ↔ forall ⦃g : G⦄, (g • B inter B).Nonempty -> g • B = B
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mul_mem_cancel_right`：mul_mem_cancel_right {x y : G} (h : x in H) : y * 
x in H ↔ y in H
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Subgroup.coe_mk`：coe_mk (x : G) (hx : x in H) : ((⟨x, hx⟩ : H) : G) = x
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `MulAction.smul_orbit`：smul_orbit (g : G) (a : α) : g • orbit G a = orbit
 G a

--- 原说明 ---
The orbit of `a` under a subgroup containing the stabilizer of `a` is a block
-/
theorem IsBlock.of_orbit {H : Subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
    IsBlock G (MulAction.orbit H a) := by
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨-, ⟨-, ⟨h₁, rfl⟩, h⟩, h₂, rfl⟩
  suffices g ∈ H by
    rw [← Subgroup.coe_mk H g this, ← H.toSubmonoid.smul_def, smul_orbit (⟨g, this⟩ : H) a]
  rw [← mul_mem_cancel_left h₂⁻¹.2, ← mul_mem_cancel_right h₁.2]
  apply hH
  simpa only [mem_stabilizer_iff, InvMemClass.coe_inv, mul_smul, inv_smul_eq_iff]

/-- If `B` is a block containing `a`, then the stabilizer of `B` contains the stabilizer of `a` -/
@[to_additive
/-- If `B` is a block containing `a`, then the stabilizer of `B` contains the stabilizer of `a` -/]
/-
**MulAction.IsBlock.stabilizer_le** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X},   MulAction.IsBlock G B → ∀ {a : X}, a ∈ B → MulAction.stabilizer G
 a ≤ MulAction.stabilizer G B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsBlock.smul_eq_of_nonempty`：∀ {G : Type u_1} [inst : Group G]
 {X : Type u_2} [inst_1 : MulAction G X] {B : Set X},   MulAction.IsBlock G B → 
∀ ⦃g : G⦄, (g • B ∩ B).None…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
theorem IsBlock.stabilizer_le (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    stabilizer G a ≤ stabilizer G B :=
  fun g hg ↦ hB.smul_eq_of_nonempty ⟨a, by rwa [← hg, smul_mem_smul_set_iff], ha⟩

/-- A block containing `a` is the orbit of `a` under its stabilizer -/
@[to_additive /-- A block containing `a` is the orbit of `a` under its stabilizer -/]
/-
**MulAction.IsBlock.orbit_stabilizer_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsB
lock`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {X : Type u_2} [inst_1 : MulAction G X] 
{B : Set X} [MulAction.IsPretransitive G X],   MulAction.IsBlock G B → ∀ {a : X}
, a ∈ B → MulAction.orbit (↥(MulAction.stabilizer G B)) a = B
参数：↥(MulAction.stabilizer G B)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `MulAction.IsBlock.smul_eq_of_mem`：∀ {G : Type u_1} [inst : Group G] {X :
 Type u_2} [inst_1 : MulAction G X] {B : Set X},   MulAction.IsBlock G B → ∀ ⦃g 
: G⦄ ⦃a : X⦄, a ∈ B → …

--- 原说明 ---
A block containing `a` is the orbit of `a` under its stabilizer
-/
theorem IsBlock.orbit_stabilizer_eq [IsPretransitive G X] (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    MulAction.orbit (stabilizer G B) a = B := by
  ext x
  constructor
  · rintro ⟨⟨k, k_mem⟩, rfl⟩
    simp only [Subgroup.mk_smul]
    rw [← k_mem, Set.smul_mem_smul_set_iff]
    exact ha
  · intro hx
    obtain ⟨k, rfl⟩ := exists_smul_eq G a x
    exact ⟨⟨k, hB.smul_eq_of_mem ha hx⟩, rfl⟩

/-- A subgroup containing the stabilizer of `a`
  is the stabilizer of the orbit of `a` under that subgroup -/
@[to_additive
  /-- A subgroup containing the stabilizer of `a`
  is the stabilizer of the orbit of `a` under that subgroup -/]
/-
**MulAction.stabilizer_orbit_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_orbit_eq {a : X} {H : Subgroup G} (hH : stabilizer G a <= H) : 
stabilizer G (orbit H a) = H
参数：hH : stabilizer G a <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `MulAction.mem_orbit_self`：mem_orbit_self (a : α) : a in orbit M a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_mem_cancel_right`：mul_mem_cancel_right {x y : G} (h : x in H) : y * 
x in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Subgroup.coe_mk`：coe_mk (x : G) (hx : x in H) : ((⟨x, hx⟩ : H) : G) = x
· 使用定理 `MulAction.smul_orbit`：smul_orbit (g : G) (a : α) : g • orbit G a = orbit
 G a
-/
theorem stabilizer_orbit_eq {a : X} {H : Subgroup G} (hH : stabilizer G a ≤ H) :
    stabilizer G (orbit H a) = H := by
  ext g
  constructor
  · intro hg
    obtain ⟨-, ⟨b, rfl⟩, h⟩ := hg.symm ▸ mem_orbit_self a
    simp_rw [H.toSubmonoid.smul_def, ← mul_smul, ← mem_stabilizer_iff] at h
    exact (mul_mem_cancel_right b.2).mp (hH h)
  · intro hg
    rw [mem_stabilizer_iff, ← Subgroup.coe_mk H g hg, ← Submonoid.smul_def (S := H.toSubmonoid)]
    apply smul_orbit (G := H)

variable (G)

/-- Order equivalence between blocks in `X` containing a point `a`
and subgroups of `G` containing the stabilizer of `a` (Wielandt, th. 7.5) -/
@[to_additive
/-- Order equivalence between blocks in `X` containing a point `a`
and subgroups of `G` containing the stabilizer of `a` (Wielandt, th. 7.5) -/]
/-
**MulAction.block_stabilizerOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：block_stabilizerOrderIso [htGX : IsPretransitive G X] (a : X) : { B : Set 
X // a in B ∧ IsBlock G B } ≃o Set.Ici (stabilizer G a) where toFun
参数：a : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsBlock.stabilizer_le`：∀ {G : Type u_1} [inst : Group G] {X : 
Type u_2} [inst_1 : MulAction G X] {B : Set X},   MulAction.IsBlock G B → ∀ {a :
 X}, a ∈ B → MulActio…
-/
def block_stabilizerOrderIso [htGX : IsPretransitive G X] (a : X) :
    { B : Set X // a ∈ B ∧ IsBlock G B } ≃o Set.Ici (stabilizer G a) where
  toFun := fun ⟨B, ha, hB⟩ => ⟨stabilizer G B, hB.stabilizer_le ha⟩
  invFun := fun ⟨H, hH⟩ =>
    ⟨MulAction.orbit H a, MulAction.mem_orbit_self a, IsBlock.of_orbit hH⟩
  left_inv := fun ⟨_, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (hB.orbit_stabilizer_eq ha)
  right_inv := fun ⟨_, hH⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (stabilizer_orbit_eq hH)
  map_rel_iff' := by
    rintro ⟨B, ha, hB⟩; rintro ⟨B', ha', hB'⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk]
    constructor
    · rintro hBB' b hb
      obtain ⟨k, rfl⟩ := htGX.exists_smul_eq a b
      suffices k ∈ stabilizer G B' by
        exact this.symm ▸ (Set.smul_mem_smul_set ha')
      exact hBB' (hB.smul_eq_of_mem ha hb)
    · intro hBB' g hgB
      apply hB'.smul_eq_of_mem ha'
      exact hBB' <| hgB.symm ▸ (Set.smul_mem_smul_set ha)

/-- The type of blocks for a group action containing a given element -/
@[to_additive
/-- The type of blocks for an additive group action containing a given element -/]
/-
**MulAction.BlockMem** 是 Mathlib 中的一个缩写定义，位于命名空间 `MulAction`。
形式化陈述：BlockMem (a : X) : Type _
参数：a : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev BlockMem (a : X) : Type _ := {B : Set X // a ∈ B ∧ IsBlock G B}

namespace BlockMem

/-- The type of blocks for a group action containing a given element is a bounded order. -/
@[to_additive /-- The type of blocks for an additive group action containing a given element is a
bounded order. -/]
/-
**MulAction.BlockMem.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction.BlockMem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : X) : BoundedOrder (BlockMem G a) where
  top := ⟨Set.univ, Set.mem_univ a, .univ⟩
  le_top := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, subset_univ]
  bot := ⟨{a}, Set.mem_singleton a, IsBlock.singleton⟩
  bot_le := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, Set.singleton_subset_iff]
    exact ha

@[to_additive (attr := simp, norm_cast)]
/-
**MulAction.BlockMem.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.BlockMem`。
形式化陈述：coe_top (a : X) : ((⊤ : BlockMem G a) : Set X) = Set.univ
参数：a : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top (a : X) :
    ((⊤ : BlockMem G a) : Set X) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MulAction.BlockMem.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.BlockMem`。
形式化陈述：coe_bot (a : X) : ((⊥ : BlockMem G a) : Set X) = {a}
参数：a : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot (a : X) :
    ((⊥ : BlockMem G a) : Set X) = {a} :=
  rfl

@[to_additive]
/-
**MulAction.BlockMem.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction.BlockMem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial X] (a : X) : Nontrivial (BlockMem G a) := by
  rw [nontrivial_iff]
  use ⊥, ⊤
  intro h
  rw [← Subtype.coe_inj] at h
  simp only [coe_top, coe_bot] at h
  obtain ⟨b, hb⟩ := exists_ne a
  apply hb
  rw [← Set.mem_singleton_iff, h]
  apply Set.mem_univ

end BlockMem

end Stabilizer

section Finite

namespace IsBlock

variable [IsPretransitive G X] {B : Set X}

@[to_additive]
/-
**MulAction.IsBlock.ncard_block_eq_relIndex** 是 Mathlib 中的一个定理，位于命名空间 `MulAction
.IsBlock`。
形式化陈述：ncard_block_eq_relIndex (hB : IsBlock G B) {x : X} (hx : x in B) : B.ncard
 = (stabilizer G x).relIndex (stabilizer G B)
参数：hB : IsBlock G B；hx : x in B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用定理 `MulAction.index_stabilizer`：∀ (G : Type u_1) {X : Type u_2} [inst : Grou
p G] [inst_1 : MulAction G X] (x : X),   (MulAction.stabilizer G x).index = (Mul
Action.orbit G x…
· 使用定理 `MulAction.IsBlock.orbit_stabilizer_eq`：∀ {G : Type u_1} [inst : Group G]
 {X : Type u_2} [inst_1 : MulAction G X] {B : Set X} [MulAction.IsPretransitive 
G X],   MulAction.IsBlock G…
-/
theorem ncard_block_eq_relIndex (hB : IsBlock G B) {x : X} (hx : x ∈ B) :
    B.ncard = (stabilizer G x).relIndex (stabilizer G B) := by
  have key : (stabilizer G x).subgroupOf (stabilizer G B) = stabilizer (stabilizer G B) x := by
    ext; rfl
  rw [Subgroup.relIndex, key, index_stabilizer, hB.orbit_stabilizer_eq hx]

/-- The cardinality of the ambient space is the product of the cardinality of a block
  by the cardinality of the set of translates of that block -/
@[to_additive
  /-- The cardinality of the ambient space is the product of the cardinality of a block
  by the cardinality of the set of translates of that block -/]
/-
**MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mu
lAction.IsBlock`。
形式化陈述：ncard_block_mul_ncard_orbit_eq (hB : IsBlock G B) (hB_ne : B.Nonempty) : S
et.ncard B * Set.ncard (orbit G B) = Nat.card X
参数：hB : IsBlock G B；hB_ne : B.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.IsBlock.ncard_block_eq_relIndex`：ncard_block_eq_relIndex (hB :
 IsBlock G B) {x : X} (hx : x in B) : B.ncard = (stabilizer G x).relIndex (stabi
lizer G B)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.index_stabilizer`：∀ (G : Type u_1) {X : Type u_2} [inst : Grou
p G] [inst_1 : MulAction G X] (x : X),   (MulAction.stabilizer G x).index = (Mul
Action.orbit G x…
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
· 使用定理 `MulAction.IsBlock.stabilizer_le`：∀ {G : Type u_1} [inst : Group G] {X : 
Type u_2} [inst_1 : MulAction G X] {B : Set X},   MulAction.IsBlock G B → ∀ {a :
 X}, a ∈ B → MulActio…
· 使用定理 `MulAction.index_stabilizer_of_transitive`：∀ (G : Type u_1) {X : Type u_2
} [inst : Group G] [inst_1 : MulAction G X] (x : X) [MulAction.IsPretransitive G
 X],   (MulAction.stabilizer G…
-/
theorem ncard_block_mul_ncard_orbit_eq (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B * Set.ncard (orbit G B) = Nat.card X := by
  obtain ⟨x, hx⟩ := hB_ne
  rw [ncard_block_eq_relIndex hB hx, ← index_stabilizer,
      Subgroup.relIndex_mul_index (hB.stabilizer_le hx), index_stabilizer_of_transitive]

/-- The cardinality of a block divides the cardinality of the ambient type -/
@[to_additive /-- The cardinality of a block divides the cardinality of the ambient type -/]
/-
**MulAction.IsBlock.ncard_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`
。
形式化陈述：ncard_dvd_card (hB : IsBlock G B) (hB_ne : B.Nonempty) : Set.ncard B ∣ Nat
.card X
参数：hB : IsBlock G B；hB_ne : B.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq`：ncard_block_mul_ncard_
orbit_eq (hB : IsBlock G B) (hB_ne : B.Nonempty) : Set.ncard B * Set.ncard (orbi
t G B) = Nat.card X

--- 原说明 ---
The cardinality of a block divides the cardinality of the ambient type
-/
theorem ncard_dvd_card (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B ∣ Nat.card X :=
  Dvd.intro _ (hB.ncard_block_mul_ncard_orbit_eq hB_ne)

/-- A too large block is equal to `univ` -/
@[to_additive /-- A too large block is equal to `univ` -/]
/-
**MulAction.IsBlock.eq_univ_of_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBl
ock`。
形式化陈述：eq_univ_of_card_lt [hX : Finite X] (hB : IsBlock G B) (hB' : Nat.card X < 
Set.ncard B * 2) : B = Set.univ
参数：hB : IsBlock G B；hB' : Nat.card X < Set.ncard B * 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq`：ncard_block_mul_ncard_
orbit_eq (hB : IsBlock G B) (hB_ne : B.Nonempty) : Set.ncard B * Set.ncard (orbi
t G B) = Nat.card X
· 使用定理 `Set.eq_of_subset_of_ncard_le`：eq_of_subset_of_ncard_le (h : s subseteq t
) (h' : t.ncard <= s.ncard) (ht : t.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Mathlib.Tactic.IntervalCases.of_lt_right`：of_lt_right [LinearOrder α] (h
 : (a : α) < b) (eq : b = b') : ¬b' <= a
· 使用定理 `mul_lt_mul_iff_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Ze
ro α] [inst_2 : Preorder α] {a b c : α} [PosMulStrictMono α]   [PosMulReflectLT 
α], 0 < a → (a *…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsEmpty.exists_iff`：exists_iff {p : α -> Prop} : (exists a, p a) ↔ False
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Finite.not_infinite`：∀ {α : Sort u_1}, Finite α → ¬Infinite α
· 使用引理 `Nat.card_eq_zero`：card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
A too large block is equal to `univ`
-/
theorem eq_univ_of_card_lt [hX : Finite X] (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2) :
    B = Set.univ := by
  rcases Set.eq_empty_or_nonempty B with rfl | hB_ne
  · simp at hB'
  have key := hB.ncard_block_mul_ncard_orbit_eq hB_ne
  rw [← key, mul_lt_mul_iff_of_pos_left (by rwa [Set.ncard_pos])] at hB'
  interval_cases (orbit G B).ncard
  · rw [mul_zero, eq_comm, Nat.card_eq_zero, or_iff_left hX.not_infinite] at key
    exact (IsEmpty.exists_iff.mp hB_ne).elim
  · rw [mul_one, ← Set.ncard_univ] at key
    rw [Set.eq_of_subset_of_ncard_le (Set.subset_univ B) key.ge]

/-- If a block has too many translates, then it is a (sub)singleton -/
@[to_additive /-- If a block has too many translates, then it is a (sub)singleton -/]
/-
**MulAction.IsBlock.subsingleton_of_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `MulAction
.IsBlock`。
形式化陈述：subsingleton_of_card_lt [Finite X] (hB : IsBlock G B) (hB' : Nat.card X < 
2 * Set.ncard (orbit G B)) : B.Subsingleton
参数：hB : IsBlock G B；hB' : Nat.card X < 2 * Set.ncard (orbit G B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq`：ncard_block_mul_ncard_
orbit_eq (hB : IsBlock G B) (hB_ne : B.Nonempty) : Set.ncard B * Set.ncard (orbi
t G B) = Nat.card X
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k

--- 原说明 ---
If a block has too many translates, then it is a (sub)singleton
-/
theorem subsingleton_of_card_lt [Finite X] (hB : IsBlock G B)
    (hB' : Nat.card X < 2 * Set.ncard (orbit G B)) :
    B.Subsingleton := by
  suffices Set.ncard B < 2 by simp_all
  cases Set.eq_empty_or_nonempty B with
  | inl h => rw [h, Set.ncard_empty]; simp
  | inr h =>
    rw [← hB.ncard_block_mul_ncard_orbit_eq h, lt_iff_not_ge] at hB'
    rw [← not_le]
    exact fun hb ↦ hB' (Nat.mul_le_mul_right _ hb)

/- The assumption `B.Finite` is necessary :
  For G = ℤ acting on itself, a = 0 and B = ℕ, the translates `k • B` of the statement
  are just `k + ℕ`, for `k ≤ 0`, and the corresponding intersection is `ℕ`, which is not a block.
  (Remark by Thomas Browning) -/
/-- The intersection of the translates of a *finite* subset which contain a given point
is a block (Wielandt, th. 7.3). -/
@[to_additive
  /-- The intersection of the translates of a *finite* subset which contain a given point
  is a block (Wielandt, th. 7.3). -/]
/-
**MulAction.IsBlock.of_subset** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsBlock`。
形式化陈述：of_subset (a : X) (hfB : B.Finite) : IsBlock G (⋂ (k : G) (_ : a in k • B)
, k • B)
参数：a : X；hfB : B.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.map`：∀ {α β : Type u_1} {s : Set α} (f : α → β), s.Finite → (
f <$> s).Finite
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用引理 `MulAction.mem_stabilizer_set_iff_subset_smul_set`：mem_stabilizer_set_iff
_subset_smul_set {s : Set α} (hs : s.Finite) : a in stabilizer G s ↔ s subseteq 
a • s
· 使用引理 `MulAction.isBlock_iff_smul_eq_of_nonempty`：isBlock_iff_smul_eq_of_nonemp
ty : IsBlock G B ↔ forall ⦃g : G⦄, (g • B inter B).Nonempty -> g • B = B
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
-/
theorem of_subset (a : X) (hfB : B.Finite) :
    IsBlock G (⋂ (k : G) (_ : a ∈ k • B), k • B) := by
  let B' := ⋂ (k : G) (_ : a ∈ k • B), k • B
  rcases Set.eq_empty_or_nonempty B with hfB_e | hfB_ne
  · simp [hfB_e]
  have hB'₀ : ∀ (k : G) (_ : a ∈ k • B), B' ≤ k • B := by
    intro k hk
    exact Set.biInter_subset_of_mem hk
  have hfB' : B'.Finite := by
    obtain ⟨b, hb : b ∈ B⟩ := hfB_ne
    obtain ⟨k, hk : k • b = a⟩ := exists_smul_eq G b a
    apply Set.Finite.subset (Set.Finite.map _ hfB) (hB'₀ k ⟨b, hb, hk⟩)
  have hag : ∀ g : G, a ∈ g • B' → B' ≤ g • B' := by
    intro g hg x hx
    -- a = g • b; b ∈ B'; a ∈ k • B → b ∈ k • B
    simp only [B', Set.mem_iInter, Set.mem_smul_set_iff_inv_smul_mem,
      smul_smul, ← mul_inv_rev] at hg hx ⊢
    exact fun _ ↦ hx _ ∘ hg _
  have hag' (g : G) (hg : a ∈ g • B') : B' = g • B' := by
    rw [eq_comm, ← mem_stabilizer_iff, mem_stabilizer_set_iff_subset_smul_set hfB']
    exact hag g hg
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨b : X, hb' : b ∈ g • B', hb : b ∈ B'⟩
  obtain ⟨k : G, hk : k • a = b⟩ := exists_smul_eq G a b
  have hak : a ∈ k⁻¹ • B' := by
    refine ⟨b, hb, ?_⟩
    simp only [← hk, inv_smul_smul]
  have hagk : a ∈ (k⁻¹ * g) • B' := by
    rw [mul_smul, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, hk]
    exact hb'
  have hkB' : B' = k⁻¹ • B' := hag' k⁻¹ hak
  have hgkB' : B' = (k⁻¹ * g) • B' := hag' (k⁻¹ * g) hagk
  rw [mul_smul] at hgkB'
  rw [← smul_eq_iff_eq_inv_smul] at hkB' hgkB'
  rw [← hgkB', hkB']

end IsBlock

end Finite

end Group

end MulAction

