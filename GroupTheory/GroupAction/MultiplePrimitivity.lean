/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-! # Multiply preprimitive actions

Let `G` be a group acting on a type `α`.

* `MulAction.IsMultiplyPreprimitive` :
  The action is said to be `n`-primitive if, for every subset `s :
  Set α` with `n` elements, the actions f `stabilizer G s` on the
  complement of `s` is primitive.

* `MulAction.is_zero_preprimitive` : any action is 0-primitive

* `MulAction.is_one_preprimitive_iff` : an action is 1-primitive if and only if it is primitive

* `MulAction.isMultiplyPreprimitive_ofStabilizer`: if an action is `n + 1`-primitive,
  then the action of `stabilizer G a` on the complement of `{a}` is `n`-primitive.

* `MulAction.isMultiplyPreprimitive_succ_iff_ofStabilizer` :
  for `1 ≤ n`, an action is `n + 1`-primitive, then the action
  of `stabilizer G a` on the complement of `{a}` is `n`-primitive.
  ofFixingSubgroup.isMultiplyPreprimitive

* `MulAction.ofFixingSubgroup.isMultiplyPreprimitive`:
  If an action is `s.ncard + m`-primitive, then
  the action of `FixingSubgroup G s` on the complement of `s`
  is `m`-primitive.

-/

public section

open scoped Pointwise Cardinal

namespace MulAction

open SubMulAction

section Preprimitive

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

-- Rewriting lemmas for transitivity or primitivity

@[to_additive]
/-
**MulAction.isPreprimitive_of_fixingSubgroup_empty_iff** 是 Mathlib 中的一个定理，位于命名空间
 `MulAction`。
形式化陈述：isPreprimitive_of_fixingSubgroup_empty_iff : IsPreprimitive ↥(fixingSubgro
up G (∅ : Set α)) ↥(ofFixingSubgroup G (∅ : Set α)) ↔ IsPreprimitive G α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPreprimitive_congr`：isPreprimitive_congr (hφ : Function.Surj
ective φ) (hf : Function.Bijective f) : IsPreprimitive M α ↔ IsPreprimitive N β
· 使用定理 `SubMulAction.of_fixingSubgroupEmpty_mapScalars_surjective`：of_fixingSubg
roupEmpty_mapScalars_surjective : Surjective (fixingSubgroup M (∅ : Set α)).subt
ype
· 使用定理 `SubMulAction.ofFixingSubgroupEmpty_equivariantMap_bijective`：ofFixingSub
groupEmpty_equivariantMap_bijective : Bijective (ofFixingSubgroup_equivariantMap
 M (∅ : Set α))
-/
theorem isPreprimitive_of_fixingSubgroup_empty_iff :
    IsPreprimitive ↥(fixingSubgroup G (∅ : Set α))
    ↥(ofFixingSubgroup G (∅ : Set α)) ↔ IsPreprimitive G α :=
  isPreprimitive_congr
    of_fixingSubgroupEmpty_mapScalars_surjective
    ofFixingSubgroupEmpty_equivariantMap_bijective

@[to_additive]
/-
**MulAction.isPreprimitive_ofFixingSubgroup_conj_iff** 是 Mathlib 中的一个定理，位于命名空间 `
MulAction`。
形式化陈述：isPreprimitive_ofFixingSubgroup_conj_iff {s : Set α} {g : G} : IsPreprimit
ive (fixingSubgroup G s) (ofFixingSubgroup G s) ↔ IsPreprimitive (fixingSubgroup
 G (g • s)) (ofFixingSubgroup G (g • s))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPreprimitive_congr`：isPreprimitive_congr (hφ : Function.Surj
ective φ) (hf : Function.Bijective f) : IsPreprimitive M α ↔ IsPreprimitive N β
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `SubMulAction.conjMap_ofFixingSubgroup_bijective`：conjMap_ofFixingSubgrou
p_bijective {s t : Set α} {g : M} {hst : g • s = t} : Bijective (conjMap_ofFixin
gSubgroup hst)
-/
theorem isPreprimitive_ofFixingSubgroup_conj_iff {s : Set α} {g : G} :
    IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s) ↔
      IsPreprimitive (fixingSubgroup G (g • s)) (ofFixingSubgroup G (g • s)) :=
  isPreprimitive_congr
    (fixingSubgroupEquivFixingSubgroup rfl).surjective
    conjMap_ofFixingSubgroup_bijective

@[to_additive]
/-
**MulAction.isPreprimitive_fixingSubgroup_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `
MulAction`。
形式化陈述：isPreprimitive_fixingSubgroup_insert_iff {a : α} {t : Set (ofStabilizer G 
a)} : IsPreprimitive ↥(fixingSubgroup G (insert a (Subtype.val '' t))) ↥(ofFixin
gSubgroup G (insert a (Subtype.val '' t))) ↔ IsPreprimitive (fixingSubgroup (sta
bilizer G a) t) (ofFixingSubgroup (stabilizer G a) t)
参数：ofStabilizer G a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPreprimitive_congr`：isPreprimitive_congr (hφ : Function.Surj
ective φ) (hf : Function.Bijective f) : IsPreprimitive M α ↔ IsPreprimitive N β
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `SubMulAction.ofFixingSubgroup_insert_map_bijective`：ofFixingSubgroup_ins
ert_map_bijective {a : α} {s : Set (ofStabilizer M a)} : Bijective (ofFixingSubg
roup_insert_map a s)
-/
theorem isPreprimitive_fixingSubgroup_insert_iff {a : α} {t : Set (ofStabilizer G a)} :
    IsPreprimitive ↥(fixingSubgroup G (insert a (Subtype.val '' t)))
      ↥(ofFixingSubgroup G (insert a (Subtype.val '' t))) ↔
      IsPreprimitive (fixingSubgroup (stabilizer G a) t)
        (ofFixingSubgroup (stabilizer G a) t) :=
  isPreprimitive_congr (fixingSubgroupInsertEquiv a t).surjective
    ofFixingSubgroup_insert_map_bijective

end Preprimitive

/-- An additive action is `n`-multiply preprimitive if it is `n`-multiply pretransitive
  and if, when `n ≥ 1`, for every set `s` of cardinality `n - 1`,
  the action of `fixingAddSubgroup M s` on the complement of `s` is preprimitive. -/
@[mk_iff]
/-
**MulAction._root_.AddAction.IsMultiplyPreprimitive** 是 Mathlib 中的一个类，位于命名空间 `Mu
lAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive action is `n`-multiply preprimitive if it is `n`-multiply pretransit
ive
  and if, when `n ≥ 1`, for every set `s` of cardinality `n - 1`,
  the action of `fixingAddSubgroup M s` on the complement of `s` is preprimitive
.
-/
class _root_.AddAction.IsMultiplyPreprimitive
    (M α : Type*) [AddGroup M] [AddAction M α] (n : ℕ) where
  /-- An `n`-preprimitive action is `n`-pretransitive. -/
  isMultiplyPretransitive (M α n) : AddAction.IsMultiplyPretransitive M α n
  /-- In an `n`-preprimitive action, the action of `fixingAddSubgroup M s`
  on `ofFixingAddSubgroup M s` is preprimitive, for all sets `s` such that `s.encard + 1 = n`. -/
  isPreprimitive_ofFixingAddSubgroup (M n) {s : Set α} (hs : s.encard + 1 = n) :
    AddAction.IsPreprimitive (fixingAddSubgroup M s) (SubAddAction.ofFixingAddSubgroup M s)

/-- A group action is `n`-multiply preprimitive if it is `n`-multiply
pretransitive and if, when `n ≥ 1`, for every set `s` of cardinality
`n - 1`, the action of `fixingSubgroup M s` on the complement of `s`
is preprimitive. -/
@[mk_iff, to_additive existing]
/-
**MulAction.IsMultiplyPreprimitive** 是 Mathlib 中的一个归纳类型，位于命名空间 `MulAction`。
形式化陈述：(M : Type u_1) → (α : Type u_2) → [inst : Group M] → [MulAction M α] → ℕ →
 Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group action is `n`-multiply preprimitive if it is `n`-multiply
pretransitive and if, when `n ≥ 1`, for every set `s` of cardinality
`n - 1`, the action of `fixingSubgroup M s` on the complement of `s`
is preprimitive.
-/
class IsMultiplyPreprimitive (M α : Type*) [Group M] [MulAction M α] (n : ℕ) where
  /-- An `n`-preprimitive action is `n`-pretransitive. -/
  isMultiplyPretransitive (M α n) : IsMultiplyPretransitive M α n
  /-- In an `n`-preprimitive action, the action of `fixingSubgroup M s` on `ofFixingSubgroup M s`
  is preprimitive, for all sets `s` such that `s.encard + 1 = n`. -/
  isPreprimitive_ofFixingSubgroup (M n) {s : Set α} (hs : s.encard + 1 = n) :
    IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s)

variable (M α : Type*) [Group M] [MulAction M α]

@[to_additive]
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) [IsMultiplyPreprimitive M α n] :
    IsMultiplyPretransitive M α n :=
  IsMultiplyPreprimitive.isMultiplyPretransitive M α n

/-- Any action is `0`-preprimitive. -/
@[to_additive /-- Any action is `0`-preprimitive. -/]
/-
**MulAction.is_zero_preprimitive** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：is_zero_preprimitive : IsMultiplyPreprimitive M α 0 where isMultiplyPretra
nsitive
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.is_zero_pretransitive`：is_zero_pretransitive {n : Type*} [IsEm
pty n] : IsPretransitive G (n ↪ α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False

--- 原说明 ---
Any action is `0`-preprimitive.
-/
theorem is_zero_preprimitive : IsMultiplyPreprimitive M α 0 where
  isMultiplyPretransitive := MulAction.is_zero_pretransitive
  isPreprimitive_ofFixingSubgroup hs := by simp at hs

/-- An action is preprimitive iff it is `1`-preprimitive. -/
@[to_additive
/-- An action is preprimitive iff it is `1`-preprimitive. -/]
/-
**MulAction.is_one_preprimitive_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：is_one_preprimitive_iff : IsMultiplyPreprimitive M α 1 ↔ IsPreprimitive M 
α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.isPreprimitive_of_fixingSubgroup_empty_iff`：isPreprimitive_of_
fixingSubgroup_empty_iff : IsPreprimitive ↥(fixingSubgroup G (∅ : Set α)) ↥(ofFi
xingSubgroup G (∅ : Set α)) ↔ IsPreprimiti…
· 使用定理 `MulAction.IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup`：∀ (M :
 Type u_1) {α : Type u_2} {inst : Group M} {inst_1 : MulAction M α} (n : ℕ)   [s
elf : MulAction.IsMultiplyPreprimitive M α n] {s : Set…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulAction.isMultiplyPreprimitive_iff`：∀ (M : Type u_1) (α : Type u_2) [i
nst : Group M] [inst_1 : MulAction M α] (n : ℕ),   MulAction.IsMultiplyPreprimit
ive M α n ↔     MulAction.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.is_one_pretransitive_iff`：is_one_pretransitive_iff : IsMultipl
yPretransitive G α 1 ↔ IsPretransitive G α
· 使用定理 `MulAction.IsPreprimitive.toIsPretransitive`：∀ {G : Type u_1} {X : Type u
_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X], MulAction.IsPretran
sitive G X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem is_one_preprimitive_iff :
    IsMultiplyPreprimitive M α 1 ↔ IsPreprimitive M α := by
  constructor
  · intro H1
    rw [← isPreprimitive_of_fixingSubgroup_empty_iff]
    apply H1.isPreprimitive_ofFixingSubgroup (by simp)
  · intro h
    rw [isMultiplyPreprimitive_iff]
    constructor
    · exact is_one_pretransitive_iff.mpr h.toIsPretransitive
    · simpa using isPreprimitive_of_fixingSubgroup_empty_iff.mpr h

/-- The action of `stabilizer M a` is one-less preprimitive. -/
@[to_additive /-- The action of `stabilizer M a` is one-less preprimitive. -/]
/-
**MulAction.isMultiplyPreprimitive_ofStabilizer** 是 Mathlib 中的一个定理，位于命名空间 `MulAc
tion`。
形式化陈述：isMultiplyPreprimitive_ofStabilizer [IsPretransitive M α] {n : Nat} {a : α
} [IsMultiplyPreprimitive M α n.succ] : IsMultiplyPreprimitive (stabilizer M a) 
(SubMulAction.ofStabilizer M a) n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `MulAction.is_zero_preprimitive`：is_zero_preprimitive : IsMultiplyPreprim
itive M α 0 where isMultiplyPretransitive
· 使用定理 `MulAction.isMultiplyPreprimitive_iff`：∀ (M : Type u_1) (α : Type u_2) [i
nst : Group M] [inst_1 : MulAction M α] (n : ℕ),   MulAction.IsMultiplyPreprimit
ive M α n ↔     MulAction.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubMulAction.ofStabilizer.isMultiplyPretransitive`：isMultiplyPretransiti
ve [IsPretransitive G α] {n : Nat} {a : α} : IsMultiplyPretransitive G α n.succ 
↔ IsMultiplyPretransitive (stabilizer G…
· 使用定理 `MulAction.IsMultiplyPreprimitive.isMultiplyPretransitive`：∀ (M : Type u_
1) (α : Type u_2) {inst : Group M} {inst_1 : MulAction M α} (n : ℕ)   [self : Mu
lAction.IsMultiplyPreprimitive M α n], MulActi…
· 使用定理 `MulAction.IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup`：∀ (M :
 Type u_1) {α : Type u_2} {inst : Group M} {inst_1 : MulAction M α} (n : ℕ)   [s
elf : MulAction.IsMultiplyPreprimitive M α n] {s : Set…
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.encard_image`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β}, Function.Injective f → ∀ (s : Set α), (f '' s).encard = s.encard
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `MulAction.IsPreprimitive.of_surjective`：∀ {M : Type u_3} [inst : Group M
] {α : Type u_4} [inst_1 : MulAction M α] {N : Type u_5} {β : Type u_6}   [inst_
2 : Group N] [inst_3 : MulAc…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Subgroup.instIsScalarTowerSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : Group G] [inst_1 : SMul α β] [inst_2 : MulAction G α]   [in
st_3 : MulAction G β] [IsS…
· 使用定理 `SubMulAction.ofFixingSubgroup_insert_map_bijective`：ofFixingSubgroup_ins
ert_map_bijective {a : α} {s : Set (ofStabilizer M a)} : Bijective (ofFixingSubg
roup_insert_map a s)

--- 原说明 ---
The action of `stabilizer M a` is one-less preprimitive.
-/
theorem isMultiplyPreprimitive_ofStabilizer
    [IsPretransitive M α] {n : ℕ} {a : α} [IsMultiplyPreprimitive M α n.succ] :
    IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · rw [Nat.lt_one_iff] at h0
    rw [h0]
    apply is_zero_preprimitive
  rw [isMultiplyPreprimitive_iff]
  constructor
  · rw [← ofStabilizer.isMultiplyPretransitive]
    exact IsMultiplyPreprimitive.isMultiplyPretransitive M α n.succ
  · intro s hs
    have : IsPreprimitive ↥(fixingSubgroup M (insert a (Subtype.val '' s)))
      ↥(ofFixingSubgroup M (insert a (Subtype.val '' s))) := by
      apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup M n.succ
      rw [Set.encard_insert_of_notMem, Subtype.coe_injective.encard_image, hs, Nat.cast_succ]
      aesop
    exact IsPreprimitive.of_surjective ofFixingSubgroup_insert_map_bijective.surjective

/-- A pretransitive action is `n.succ-`preprimitive
iff the action of stabilizers is `n`-preprimitive. -/
@[to_additive /-- A pretransitive action is `n.succ-`preprimitive
iff the action of stabilizers is `n`-preprimitive. -/]
/-
**MulAction.isMultiplyPreprimitive_succ_iff_ofStabilizer** 是 Mathlib 中的一个定理，位于命名
空间 `MulAction`。
形式化陈述：isMultiplyPreprimitive_succ_iff_ofStabilizer [IsPretransitive M α] {n : Na
t} (hn : 1 <= n) {a : α} : IsMultiplyPreprimitive M α n.succ ↔ IsMultiplyPreprim
itive (stabilizer M a) (SubMulAction.ofStabilizer M a) n
参数：hn : 1 <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isMultiplyPreprimitive_ofStabilizer`：isMultiplyPreprimitive_of
Stabilizer [IsPretransitive M α] {n : Nat} {a : α} [IsMultiplyPreprimitive M α n
.succ] : IsMultiplyPreprimitive (st…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.isMultiplyPreprimitive_iff`：∀ (M : Type u_1) (α : Type u_2) [i
nst : Group M] [inst_1 : MulAction M α] (n : ℕ),   MulAction.IsMultiplyPreprimit
ive M α n ↔     MulAction.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SubMulAction.ofStabilizer.isMultiplyPretransitive`：isMultiplyPretransiti
ve [IsPretransitive G α] {n : Nat} {a : α} : IsMultiplyPretransitive G α n.succ 
↔ IsMultiplyPretransitive (stabilizer G…
· 使用定理 `MulAction.IsMultiplyPreprimitive.isMultiplyPretransitive`：∀ (M : Type u_
1) (α : Type u_2) {inst : Group M} {inst_1 : MulAction M α} (n : ℕ)   [self : Mu
lAction.IsMultiplyPreprimitive M α n], MulActi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.succ_inj`：∀ {a b : ℕ}, a.succ = b.succ ↔ a = b
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `MulAction.isPreprimitive_ofFixingSubgroup_conj_iff`：isPreprimitive_ofFix
ingSubgroup_conj_iff {s : Set α} {g : G} : IsPreprimitive (fixingSubgroup G s) (
ofFixingSubgroup G s) ↔ IsPreprimitive (…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
（共 46 条，此处仅展示前 30 条）
-/
theorem isMultiplyPreprimitive_succ_iff_ofStabilizer
    [IsPretransitive M α] {n : ℕ} (hn : 1 ≤ n) {a : α} :
    IsMultiplyPreprimitive M α n.succ ↔
      IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  constructor
  · apply isMultiplyPreprimitive_ofStabilizer
  · intro H
    rw [isMultiplyPreprimitive_iff]
    constructor
    · exact ofStabilizer.isMultiplyPretransitive.mpr H.isMultiplyPretransitive
    · intro s hs
      have : ∃ b : α, b ∈ s := by
        rw [← Set.nonempty_def, Set.nonempty_iff_ne_empty]
        intro h
        apply not_lt.mpr hn
        rw [h, Set.encard_empty, zero_add, ← Nat.cast_one, Nat.cast_inj, Nat.succ_inj] at hs
        simp only [← hs, zero_lt_one]
      obtain ⟨b, hb⟩ := this
      obtain ⟨g, hg : g • b = a⟩ := exists_smul_eq M b a
      rw [isPreprimitive_ofFixingSubgroup_conj_iff (g := g)]
      set s' := g • s with hs'
      let t : Set (SubMulAction.ofStabilizer M a) := Subtype.val ⁻¹' s'
      have hst : s' = insert a (Subtype.val '' t) := by
        ext x
        constructor
        · intro hxs
          by_cases hxa : x = a
          · simp [hxa]
          · exact Set.mem_insert_of_mem _
              ⟨⟨x, hxa⟩, by simp only [t, Set.mem_preimage]; exact hxs, rfl⟩
        · rw [Set.mem_insert_iff]
          rintro (⟨rfl⟩ | ⟨y, hy, rfl⟩)
          · simpa [s', ← hg]
          · simpa only using! hy
      rw [hst, isPreprimitive_fixingSubgroup_insert_iff]
      apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
      apply ENat.add_left_injective_of_ne_top ENat.one_ne_top
      simp only
      rw [← Nat.cast_one, ← Nat.cast_add, ← hs]
      apply congr_arg₂ _ _ rfl
      rw [show s = g⁻¹ • s' by simp [hs'],
        ← Set.image_smul, (MulAction.injective g⁻¹).encard_image, hst]
      rw [Set.encard_insert_of_notMem, Subtype.coe_injective.encard_image, ENat.natCast_one]
      exact notMem_val_image M t

/-- The fixator of a subset of cardinal `d` in an `n`-primitive action
acts `n-d`-primitively on the remaining (`d ≤ n`). -/
@[to_additive
/-- The fixator of a subset of cardinal `d` in an `n`-primitive action
acts `n-d`-primitively on the remaining (`d ≤ n`). -/]
/-
**MulAction.ofFixingSubgroup.isMultiplyPreprimitive** 是 Mathlib 中的一个定理，位于命名空间 `M
ulAction.ofFixingSubgroup`。
形式化陈述：∀ (M : Type u_1) (α : Type u_2) [inst : Group M] [inst_1 : MulAction M α] 
{m n : ℕ}   [MulAction.IsMultiplyPreprimitive M α n] {s : Set α} [Finite ↑s],   
s.ncard + m = n → MulAction.IsMultiplyPreprimitive (↥(fixingSubgroup M s)) (↥(Su
bMulAction.ofFixingSubgroup M s)) m
参数：M : Type u_1；α : Type u_2；↥(fixingSubgroup M s)；↥(SubMulAction.ofFixingSubgro
up M s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.ofFixingSubgroup.isMultiplyPretransitive`：∀ (G : Type u_1) 
{α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] {m n : ℕ}   [Hn : MulAc
tion.IsMultiplyPretransitive G α n] (s : Se…
· 使用定理 `MulAction.instIsMultiplyPretransitiveOfIsMultiplyPreprimitive`：∀ (M : Ty
pe u_1) (α : Type u_2) [inst : Group M] [inst_1 : MulAction M α] (n : ℕ)   [MulA
ction.IsMultiplyPreprimitive M α n], MulAction.IsMu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup`：∀ (M :
 Type u_1) {α : Type u_2} {inst : Group M} {inst_1 : MulAction M α} (n : ℕ)   [s
elf : MulAction.IsMultiplyPreprimitive M α n] {s : Set…
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用定理 `SubMulAction.disjoint_val_image`：disjoint_val_image {t : Set (ofFixingSu
bgroup M s)} : Disjoint s (Subtype.val '' t)
· 使用定理 `Function.Injective.encard_image`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β}, Function.Injective f → ∀ (s : Set α), (f '' s).encard = s.encard
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `MulAction.IsPreprimitive.of_surjective`：∀ {M : Type u_3} [inst : Group M
] {α : Type u_4} [inst_1 : MulAction M α] {N : Type u_5} {β : Type u_6}   [inst_
2 : Group N] [inst_3 : MulAc…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Subgroup.instIsScalarTowerSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : Group G] [inst_1 : SMul α β] [inst_2 : MulAction G α]   [in
st_3 : MulAction G β] [IsS…
· 使用定理 `SubMulAction.map_ofFixingSubgroupUnion_bijective`：map_ofFixingSubgroupUn
ion_bijective : Bijective (map_ofFixingSubgroupUnion M s t)
-/
theorem ofFixingSubgroup.isMultiplyPreprimitive
    {m n : ℕ} [IsMultiplyPreprimitive M α n] {s : Set α} [Finite s] (hs : s.ncard + m = n) :
    IsMultiplyPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m where
  isMultiplyPretransitive := by
    apply ofFixingSubgroup.isMultiplyPretransitive _ s hs
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let t' : Set α := Subtype.val '' t
    have htt' : t = Subtype.val ⁻¹' t' :=
      (Set.preimage_image_eq _ Subtype.coe_injective).symm
    rw [htt']
    suffices IsPreprimitive (fixingSubgroup M (s ∪ t')) (ofFixingSubgroup M (s ∪ t')) by
      apply IsPreprimitive.of_surjective map_ofFixingSubgroupUnion_bijective.surjective
    apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
    rw [Set.encard_union_eq _]
    · rw [Subtype.coe_injective.encard_image, add_assoc, ht,
        ← hs, Nat.cast_add, Set.Finite.cast_ncard_eq]
      exact Set.toFinite s
    · apply disjoint_val_image

/-- `n.succ`-pretransitivity implies `n`-preprimitivity. -/
@[to_additive /-- `n.succ`-pretransitivity implies `n`-preprimitivity. -/]
/-
**MulAction.isMultiplyPreprimitive_of_isMultiplyPretransitive_succ** 是 Mathlib 中
的一个定理，位于命名空间 `MulAction`。
形式化陈述：isMultiplyPreprimitive_of_isMultiplyPretransitive_succ {n : Nat} (hα : ↑n.
succ <= ENat.card α) [IsMultiplyPretransitive M α n.succ] : IsMultiplyPreprimiti
ve M α n
参数：hα : ↑n.succ <= ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.is_zero_preprimitive`：is_zero_preprimitive : IsMultiplyPreprim
itive M α 0 where isMultiplyPretransitive
· 使用定理 `MulAction.isMultiplyPreprimitive_iff`：∀ (M : Type u_1) (α : Type u_2) [i
nst : Group M] [inst_1 : MulAction M α] (n : ℕ),   MulAction.IsMultiplyPreprimit
ive M α n ↔     MulAction.…
· 使用定理 `MulAction.isMultiplyPretransitive_of_le'`：isMultiplyPretransitive_of_le'
 {m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= ENat.card
 α) : IsMultiplyPretransitive …
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `MulAction.isPreprimitive_of_is_two_pretransitive`：isPreprimitive_of_is_t
wo_pretransitive (h2 : IsMultiplyPretransitive G α 2) : IsPreprimitive G α
· 使用引理 `ENat.add_left_injective_of_ne_top`：add_left_injective_of_ne_top {n : Nat
∞} (hn : n != ⊤) : Function.Injective (· + n)
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Set.finite_of_encard_eq_coe`：finite_of_encard_eq_coe {k : Nat} (h : s.en
card = k) : s.Finite
· 使用定理 `SubMulAction.ofFixingSubgroup.isMultiplyPretransitive`：∀ (G : Type u_1) 
{α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] {m n : ℕ}   [Hn : MulAc
tion.IsMultiplyPretransitive G α n] (s : Se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`n.succ`-pretransitivity implies `n`-preprimitivity.
-/
theorem isMultiplyPreprimitive_of_isMultiplyPretransitive_succ {n : ℕ}
    (hα : ↑n.succ ≤ ENat.card α) [IsMultiplyPretransitive M α n.succ] :
    IsMultiplyPreprimitive M α n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]
    exact is_zero_preprimitive M α
  rw [isMultiplyPreprimitive_iff]
  constructor
  · exact isMultiplyPretransitive_of_le' (Nat.le_succ n) hα
  · intro s hs
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    apply isPreprimitive_of_is_two_pretransitive
    have hs' : s.encard = m := by
      simp only [hm, Nat.succ_eq_add_one, zero_add, add_comm 1] at hs
      exact ENat.add_left_injective_of_ne_top ENat.one_ne_top hs
    have : Finite s := Set.finite_of_encard_eq_coe hs'
    apply ofFixingSubgroup.isMultiplyPretransitive (G := M) s (n := n.succ)
    simp [Set.ncard, hs', hm, add_comm 1]

/-- An `n`-preprimitive action is `m`-preprimitive for `m ≤ n`. -/
@[to_additive /-- An `n`-preprimitive action is `m`-preprimitive for `m ≤ n`. -/]
/-
**MulAction.isMultiplyPreprimitive_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isMultiplyPreprimitive_of_le {n : Nat} (hn : IsMultiplyPreprimitive M α n)
 {m : Nat} (hmn : m <= n) (hα : ↑n <= ENat.card α) : IsMultiplyPreprimitive M α 
m
参数：hn : IsMultiplyPreprimitive M α n；hmn : m <= n；hα : ↑n <= ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Nat.eq_or_lt_of_le`：∀ {n m : ℕ}, n ≤ m → n = m ∨ n < m
· 使用定理 `MulAction.isMultiplyPreprimitive_of_isMultiplyPretransitive_succ`：isMult
iplyPreprimitive_of_isMultiplyPretransitive_succ {n : Nat} (hα : ↑n.succ <= ENat
.card α) [IsMultiplyPretransitive M α n.succ] : IsMult…
· 使用定理 `MulAction.instIsMultiplyPretransitiveOfIsMultiplyPreprimitive`：∀ (M : Ty
pe u_1) (α : Type u_2) [inst : Group M] [inst_1 : MulAction M α] (n : ℕ)   [MulA
ction.IsMultiplyPreprimitive M α n], MulAction.IsMu…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
An `n`-preprimitive action is `m`-preprimitive for `m ≤ n`.
-/
theorem isMultiplyPreprimitive_of_le
    {n : ℕ} (hn : IsMultiplyPreprimitive M α n)
    {m : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ ENat.card α) :
    IsMultiplyPreprimitive M α m := by
  induction n with
  | zero => rw [Nat.eq_zero_of_le_zero hmn]; exact hn
  | succ n hrec =>
    rcases Nat.eq_or_lt_of_le hmn with hmn | hmn'
    · rw [hmn]; exact hn
    · apply hrec
        (isMultiplyPreprimitive_of_isMultiplyPretransitive_succ M α hα)
        (Nat.lt_succ_iff.mp hmn')
      · refine le_trans ?_ hα; rw [ENat.natCast_le_natCast]; exact Nat.le_succ n

variable {M α}

@[to_additive]
/-
**MulAction.IsMultiplyPreprimitive.of_bijective_map** 是 Mathlib 中的一个定理，位于命名空间 `M
ulAction.IsMultiplyPreprimitive`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Group M] [inst_1 : MulAction M α] 
{N : Type u_3} {β : Type u_4}   [inst_2 : Group N] [inst_3 : MulAction N β] {φ :
 M → N} {f : α →ₑ[φ] β},   Function.Bijective ⇑f → ∀ {n : ℕ}, MulAction.IsMultip
lyPreprimitive M α n → MulAction.IsMultiplyPreprimitive N β n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_embedding`：∀ {G : Type u_1} {α : Type u_2} 
[inst : Group G] [inst_1 : MulAction G α] {H : Type u_3} {β : Type u_4}   [inst_
2 : Group H] [inst_3 : MulAc…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulAction.instIsMultiplyPretransitiveOfIsMultiplyPreprimitive`：∀ (M : Ty
pe u_1) (α : Type u_2) [inst : Group M] [inst_1 : MulAction M α] (n : ℕ)   [MulA
ction.IsMultiplyPreprimitive M α n], MulAction.IsMu…
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mem_fixingSubgroup_iff`：mem_fixingSubgroup_iff {s : Set α} {m : M} : m i
n fixingSubgroup M s ↔ forall y in s, m • y = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
· 使用定理 `MulActionHom.map_smul'`：∀ {M : Type u_2} {N : Type u_3} {φ : M → N} {X :
 Type u_5} [inst : SMul M X] {Y : Type u_6} [inst_1 : SMul N Y]   (self : X →ₑ[φ
] Y) (m : M)…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MulAction.IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup`：∀ (M :
 Type u_1) {α : Type u_2} {inst : Group M} {inst_1 : MulAction M α} (n : ℕ)   [s
elf : MulAction.IsMultiplyPreprimitive M α n] {s : Set…
· 使用定理 `Function.Injective.encard_image`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β}, Function.Injective f → ∀ (s : Set α), (f '' s).encard = s.encard
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `MulAction.IsPreprimitive.of_surjective`：∀ {M : Type u_3} [inst : Group M
] {α : Type u_4} [inst_1 : MulAction M α] {N : Type u_5} {β : Type u_6}   [inst_
2 : Group N] [inst_3 : MulAc…
-/
theorem IsMultiplyPreprimitive.of_bijective_map
    {N β : Type*} [Group N] [MulAction N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hf : Function.Bijective f) {n : ℕ}
    (h : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive N β n where
  isMultiplyPretransitive := IsPretransitive.of_embedding hf.surjective
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let s := f ⁻¹' t
    have hs' : f '' s = t := Set.image_preimage_eq t hf.surjective
    let φ' : fixingSubgroup M s → fixingSubgroup N t := fun ⟨m, hm⟩ ↦
      ⟨φ m, fun ⟨y, hy⟩ => by
        rw [← hs', Set.mem_image] at hy
        obtain ⟨x, hx, hx'⟩ := hy
        simp only
        rw [← hx', ← map_smulₛₗ]
        apply congr_arg
        rw [mem_fixingSubgroup_iff] at hm
        exact hm x hx⟩
    let f' : SubMulAction.ofFixingSubgroup M s →ₑ[φ'] SubMulAction.ofFixingSubgroup N t :=
      { toFun := fun ⟨x, hx⟩ => ⟨f.toFun x, fun h => hx (Set.mem_preimage.mp h)⟩
        map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ =>
          by
          rw [← SetLike.coe_eq_coe]
          exact f.map_smul' m x }
    have hf' : Function.Surjective f' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hf.right y
      use ⟨x, ?_⟩
      · simpa only [f', ← Subtype.coe_inj] using! hx
      · intro h
        apply hy
        rw [← hs']
        exact ⟨x, h, hx⟩
    have : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s) :=
      IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
        (by rw [← ht, ← hs', hf.injective.encard_image])
    exact IsPreprimitive.of_surjective (f := f') (φ := φ') hf'

@[to_additive]
/-
**MulAction.isMultiplyPreprimitive_congr** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isMultiplyPreprimitive_congr {N β : Type*} [Group N] [MulAction N β] {φ : 
M -> N} (hφ : Function.Surjective φ) {f : α ->ₑ[φ] β} (hf : Function.Bijective f
) {n : Nat} : IsMultiplyPreprimitive M α n ↔ IsMultiplyPreprimitive N β n
参数：hφ : Function.Surjective φ；hf : Function.Bijective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsMultiplyPreprimitive.of_bijective_map`：∀ {M : Type u_1} {α :
 Type u_2} [inst : Group M] [inst_1 : MulAction M α] {N : Type u_3} {β : Type u_
4}   [inst_2 : Group N] [inst_3 : MulAc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.isMultiplyPreprimitive_iff`：∀ (M : Type u_1) (α : Type u_2) [i
nst : Group M] [inst_1 : MulAction M α] (n : ℕ),   MulAction.IsMultiplyPreprimit
ive M α n ↔     MulAction.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.IsPretransitive.of_embedding_congr`：∀ {G : Type u_1} {α : Type
 u_2} [inst : Group G] [inst_1 : MulAction G α] {H : Type u_3} {β : Type u_4}   
[inst_2 : Group H] [inst_3 : MulAc…
· 使用定理 `MulAction.IsMultiplyPreprimitive.isMultiplyPretransitive`：∀ (M : Type u_
1) (α : Type u_2) {inst : Group M} {inst_1 : MulAction M α} (n : ℕ)   [self : Mu
lAction.IsMultiplyPreprimitive M α n], MulActi…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `SubMulAction.instSMulMemClass`：∀ {R : Type u} {M : Type v} [inst : SMul 
R M], SMulMemClass (SubMulAction R M) R M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulAction.isPreprimitive_congr`：isPreprimitive_congr (hφ : Function.Surj
ective φ) (hf : Function.Bijective f) : IsPreprimitive M α ↔ IsPreprimitive N β
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulAction.IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup`：∀ (M :
 Type u_1) {α : Type u_2} {inst : Group M} {inst_1 : MulAction M α} (n : ℕ)   [s
elf : MulAction.IsMultiplyPreprimitive M α n] {s : Set…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem isMultiplyPreprimitive_congr
    {N β : Type*} [Group N] [MulAction N β] {φ : M → N} (hφ : Function.Surjective φ)
    {f : α →ₑ[φ] β} (hf : Function.Bijective f) {n : ℕ} :
    IsMultiplyPreprimitive M α n ↔ IsMultiplyPreprimitive N β n := by
  refine ⟨IsMultiplyPreprimitive.of_bijective_map hf, ?_⟩
  intro H
  rw [isMultiplyPreprimitive_iff]
  constructor
  · exact (IsPretransitive.of_embedding_congr hφ hf).mpr H.isMultiplyPretransitive
  · intro s hs
    let t := f '' s
    let ψ : fixingSubgroup M s → fixingSubgroup N t := fun ⟨g, hg⟩ ↦ ⟨φ g, by
      simp only [mem_fixingSubgroup_iff] at hg ⊢
      intro y hy
      suffices ∃ x ∈ s, y = f x by
        obtain ⟨x, hx, rfl⟩ := this
        rwa [← map_smulₛₗ, hg]
      obtain ⟨x, rfl⟩ := hf.surjective y
      simpa only [Set.mem_image, t, eq_comm] using! hy⟩
    let g : ofFixingSubgroup M s →ₑ[ψ] ofFixingSubgroup N t := {
      toFun x := ⟨f x.val, by
        simp only [mem_ofFixingSubgroup_iff, Set.mem_image, hf.injective.eq_iff, exists_eq_right, t]
        exact x.prop⟩
      map_smul' m x := by simp [subgroup_smul_def, map_smulₛₗ, ψ] }
    rw [isPreprimitive_congr (f := g)]
    · apply H.isPreprimitive_ofFixingSubgroup
      simp [← hs, t, hf.injective.injOn.encard_image]
    · rintro ⟨k, hk⟩
      obtain ⟨k, rfl⟩ := hφ k
      suffices k ∈ fixingSubgroup M s by
        use ⟨k, this⟩
      simp only [mem_fixingSubgroup_iff, t] at hk ⊢
      intro y hy
      apply hf.injective
      rw [map_smulₛₗ, hk]
      exact Set.mem_image_of_mem (⇑f) hy
    · constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        suffices f x = f y by
          simpa [← Subtype.coe_inj, hf.injective.eq_iff] using! this
        simpa only [g, ← Subtype.coe_inj] using! h
      · rintro ⟨x, hx⟩
        obtain ⟨y, rfl⟩ := hf.surjective x
        suffices y ∈ ofFixingSubgroup M s by
          exact ⟨⟨y, this⟩, rfl⟩
        simp only [mem_ofFixingSubgroup_iff, Set.mem_image, not_exists, not_and, t] at hx ⊢
        exact fun hy ↦ hx y hy rfl

end MulAction

