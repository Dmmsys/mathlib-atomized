/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Lattice.Nat

/-!
# Definition of nilpotent elements

This file proves basic facts about nilpotent elements.
For results that require further theory, see `Mathlib/RingTheory/Nilpotent/Basic.lean`
and `Mathlib/RingTheory/Nilpotent/Lemmas.lean`.

## Main definitions

  * `Commute.isNilpotent_mul_left`
  * `Commute.isNilpotent_mul_right`
  * `nilpotencyClass`

-/

@[expose] public section

open Set

variable {R S : Type*} {x y : R}

/-
**IsNilpotent.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*} 
[FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) : Is
Nilpotent (f r)
参数：hr : IsNilpotent r；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) :
    IsNilpotent (f r) := by
  use hr.choose
  rw [← map_pow, hr.choose_spec, map_zero]
/-
**IsNilpotent.map_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Typ
e*} [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F} (hf : Function.Inject
ive f) : IsNilpotent (f r) ↔ IsNilpotent r
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
-/
lemma IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F} (hf : Function.Injective f) :
    IsNilpotent (f r) ↔ IsNilpotent r :=
  ⟨fun ⟨k, hk⟩ ↦ ⟨k, (map_eq_zero_iff f hf).mp <| by rwa [map_pow]⟩, fun h ↦ h.map f⟩
/-
**IsUnit.isNilpotent_mul_unit_of_commute_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.isNilpotent_mul_unit_of_commute_iff [MonoidWithZero R] {r u : R} (h
u : IsUnit u) (h_comm : Commute r u) : IsNilpotent (r * u) ↔ IsNilpotent r
参数：hu : IsUnit u；h_comm : Commute r u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsUnit.isNilpotent_mul_unit_of_commute_iff [MonoidWithZero R] {r u : R}
    (hu : IsUnit u) (h_comm : Commute r u) :
    IsNilpotent (r * u) ↔ IsNilpotent r :=
  exists_congr fun n ↦ by rw [h_comm.mul_pow, (hu.pow n).mul_left_eq_zero]
/-
**IsUnit.isNilpotent_unit_mul_of_commute_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.isNilpotent_unit_mul_of_commute_iff [MonoidWithZero R] {r u : R} (h
u : IsUnit u) (h_comm : Commute r u) : IsNilpotent (u * r) ↔ IsNilpotent r
参数：hu : IsUnit u；h_comm : Commute r u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.isNilpotent_mul_unit_of_commute_iff`：IsUnit.isNilpotent_mul_unit_
of_commute_iff [MonoidWithZero R] {r u : R} (hu : IsUnit u) (h_comm : Commute r 
u) : IsNilpotent (r * u) ↔ IsNil…
-/
theorem IsUnit.isNilpotent_unit_mul_of_commute_iff [MonoidWithZero R] {r u : R}
    (hu : IsUnit u) (h_comm : Commute r u) :
    IsNilpotent (u * r) ↔ IsNilpotent r :=
  h_comm ▸ hu.isNilpotent_mul_unit_of_commute_iff h_comm

section NilpotencyClass

section ZeroPow

variable [Zero R] [Pow R ℕ]

variable (x) in
/-- If `x` is nilpotent, the nilpotency class is the smallest natural number `k` such that
`x ^ k = 0`. If `x` is not nilpotent, the nilpotency class takes the junk value `0`. -/
/-
**nilpotencyClass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nilpotencyClass : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` is nilpotent, the nilpotency class is the smallest natural number `k` suc
h that
`x ^ k = 0`. If `x` is not nilpotent, the nilpotency class takes the junk value 
`0`.
-/
noncomputable def nilpotencyClass : ℕ := sInf {k | x ^ k = 0}
/-
**nilpotencyClass_eq_zero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {x : R} [inst : Zero R] [inst_1 : Pow R ℕ] [Subsingleton 
R], nilpotencyClass x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csInf_univ`：csInf_univ [ConditionallyCompleteLattice α] [OrderBot α] : s
Inf (univ : Set α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nilpotencyClass_eq_zero_of_subsingleton [Subsingleton R] :
    nilpotencyClass x = 0 := by
  let s : Set ℕ := {k | x ^ k = 0}
  suffices s = univ by change sInf _ = 0; simp [s] at this; simp [this]
  exact eq_univ_iff_forall.mpr fun k ↦ Subsingleton.elim _ _
/-
**isNilpotent_of_pos_nilpotencyClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isNilpotent_of_pos_nilpotencyClass (hx : 0 < nilpotencyClass x) : IsNilpot
ent x
参数：hx : 0 < nilpotencyClass x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Nat.sInf_empty`：sInf_empty : sInf ∅ = 0
-/
lemma isNilpotent_of_pos_nilpotencyClass (hx : 0 < nilpotencyClass x) :
    IsNilpotent x := by
  let s : Set ℕ := {k | x ^ k = 0}
  change s.Nonempty
  change 0 < sInf s at hx
  by_contra contra
  simp [not_nonempty_iff_eq_empty.mp contra] at hx
/-
**pow_nilpotencyClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nilpotencyClass x) = 0
参数：hx : IsNilpotent x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
-/
lemma pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nilpotencyClass x) = 0 :=
  Nat.sInf_mem hx

end ZeroPow

section MonoidWithZero

variable [MonoidWithZero R]

/-
**nilpotencyClass_eq_succ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nilpotencyClass_eq_succ_iff {k : Nat} : nilpotencyClass x = k + 1 ↔ x ^ (k
 + 1) = 0 ∧ x ^ k != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sInf_upward_closed_eq_succ_iff`：sInf_upward_closed_eq_succ_iff {s : 
Set Nat} (hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s) (k : Nat) : s
Inf s = k + 1 ↔ k + 1 in…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nilpotencyClass_eq_succ_iff {k : ℕ} :
    nilpotencyClass x = k + 1 ↔ x ^ (k + 1) = 0 ∧ x ^ k ≠ 0 := by
  let s : Set ℕ := {k | x ^ k = 0}
  have : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := fun k₁ k₂ h_le hk₁ ↦ pow_eq_zero_of_le h_le hk₁
  simp [s, nilpotencyClass, Nat.sInf_upward_closed_eq_succ_iff this]
/-
**nilpotencyClass_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : MonoidWithZero R] [Nontrivial R], nilpotencyClass
 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `nilpotencyClass_eq_succ_iff`：nilpotencyClass_eq_succ_iff {k : Nat} : nil
potencyClass x = k + 1 ↔ x ^ (k + 1) = 0 ∧ x ^ k != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma nilpotencyClass_zero [Nontrivial R] :
    nilpotencyClass (0 : R) = 1 :=
  nilpotencyClass_eq_succ_iff.mpr <| by constructor <;> simp
/-
**pos_nilpotencyClass_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {x : R} [inst : MonoidWithZero R] [Nontrivial R], 0 < nil
potencyClass x ↔ IsNilpotent x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isNilpotent_of_pos_nilpotencyClass`：isNilpotent_of_pos_nilpotencyClass (
hx : 0 < nilpotencyClass x) : IsNilpotent x
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用引理 `pow_nilpotencyClass`：pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nil
potencyClass x) = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
@[simp] lemma pos_nilpotencyClass_iff [Nontrivial R] :
    0 < nilpotencyClass x ↔ IsNilpotent x := by
  refine ⟨isNilpotent_of_pos_nilpotencyClass, fun hx ↦ Nat.pos_of_ne_zero fun hx' ↦ ?_⟩
  replace hx := pow_nilpotencyClass hx
  rw [hx', pow_zero] at hx
  exact one_ne_zero hx
/-
**pow_pred_nilpotencyClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_pred_nilpotencyClass [Nontrivial R] (hx : IsNilpotent x) : x ^ (nilpot
encyClass x - 1) != 0
参数：hx : IsNilpotent x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `nilpotencyClass_eq_succ_iff`：nilpotencyClass_eq_succ_iff {k : Nat} : nil
potencyClass x = k + 1 ↔ x ^ (k + 1) = 0 ∧ x ^ k != 0
· 使用定理 `Nat.eq_add_of_sub_eq`：∀ {a b c : ℕ}, b ≤ a → a - b = c → a = c + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_nilpotencyClass_iff`：∀ {R : Type u_1} {x : R} [inst : MonoidWithZero
 R] [Nontrivial R], 0 < nilpotencyClass x ↔ IsNilpotent x
-/
lemma pow_pred_nilpotencyClass [Nontrivial R] (hx : IsNilpotent x) :
    x ^ (nilpotencyClass x - 1) ≠ 0 :=
  (nilpotencyClass_eq_succ_iff.mp <| Nat.eq_add_of_sub_eq (pos_nilpotencyClass_iff.mpr hx) rfl).2
/-
**eq_zero_of_nilpotencyClass_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_zero_of_nilpotencyClass_eq_one (hx : nilpotencyClass x = 1) : x = 0
参数：hx : nilpotencyClass x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isNilpotent_of_pos_nilpotencyClass`：isNilpotent_of_pos_nilpotencyClass (
hx : 0 < nilpotencyClass x) : IsNilpotent x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_nilpotencyClass`：pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nil
potencyClass x) = 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma eq_zero_of_nilpotencyClass_eq_one (hx : nilpotencyClass x = 1) :
    x = 0 := by
  have : IsNilpotent x := isNilpotent_of_pos_nilpotencyClass (hx ▸ Nat.one_pos)
  rw [← pow_nilpotencyClass this, hx, pow_one]
/-
**nilpotencyClass_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {x : R} [inst : MonoidWithZero R] [Nontrivial R], nilpote
ncyClass x = 1 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_zero_of_nilpotencyClass_eq_one`：eq_zero_of_nilpotencyClass_eq_one (hx
 : nilpotencyClass x = 1) : x = 0
· 使用定理 `nilpotencyClass_zero`：∀ {R : Type u_1} [inst : MonoidWithZero R] [Nontri
vial R], nilpotencyClass 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma nilpotencyClass_eq_one [Nontrivial R] :
    nilpotencyClass x = 1 ↔ x = 0 :=
  ⟨eq_zero_of_nilpotencyClass_eq_one, fun hx ↦ hx ▸ nilpotencyClass_zero⟩

end MonoidWithZero

end NilpotencyClass

/-
**isReduced_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isReduced_of_injective [MonoidWithZero R] [MonoidWithZero S] {F : Type*} [
FunLike F R S] [MonoidWithZeroHomClass F R S] (f : F) (hf : Function.Injective f
) [IsReduced S] : IsReduced R
参数：f : F；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
-/
theorem isReduced_of_injective [MonoidWithZero R] [MonoidWithZero S] {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S]
    (f : F) (hf : Function.Injective f) [IsReduced S] :
    IsReduced R := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ι) (R : ι → Type*) [∀ i, Zero (R i)] [∀ i, Pow (R i) ℕ]
    [∀ i, IsReduced (R i)] : IsReduced (∀ i, R i) where
  eq_zero _ := fun ⟨n, hn⟩ ↦ funext fun i ↦ IsReduced.eq_zero _ ⟨n, congr_fun hn i⟩

/-- An element `y` in a monoid is radical if for any element `x`, `y` divides `x` whenever it
  divides a power of `x`. -/
/-
**IsRadical** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsRadical [Dvd R] [Pow R Nat] (y : R) : Prop
参数：y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `y` in a monoid is radical if for any element `x`, `y` divides `x` wh
enever it
  divides a power of `x`.
-/
def IsRadical [Dvd R] [Pow R ℕ] (y : R) : Prop :=
  ∀ (n : ℕ) (x), y ∣ x ^ n → y ∣ x
/-
**isRadical_iff_pow_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRadical_iff_pow_one_lt [Monoid R] (k : Nat) (hk : 1 < k) : IsRadical y ↔
 forall x, y ∣ x ^ k -> y ∣ x
参数：k : Nat；hk : 1 < k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_imp_self_of_one_lt`：Nat.pow_imp_self_of_one_lt {M} [Monoid M] (k
 : Nat) (hk : 1 < k) (P : M -> Prop) (hmul : forall x y, P x -> P (x * y) ∨ P (y
 * x)) (hpow : f…
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
-/
theorem isRadical_iff_pow_one_lt [Monoid R] (k : ℕ) (hk : 1 < k) :
    IsRadical y ↔ ∀ x, y ∣ x ^ k → y ∣ x :=
  ⟨(· k), k.pow_imp_self_of_one_lt hk _ fun _ _ h ↦ .inl (dvd_mul_of_dvd_left h _)⟩

namespace Commute

section Semiring

variable [Semiring R]

/-
**Commute.isNilpotent_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：isNilpotent_mul_right (h_comm : Commute x y) (h : IsNilpotent x) : IsNilpo
tent (x * y)
参数：h_comm : Commute x y；h : IsNilpotent x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem isNilpotent_mul_right (h_comm : Commute x y) (h : IsNilpotent x) : IsNilpotent (x * y) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow, hn, zero_mul]
/-
**Commute.isNilpotent_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：isNilpotent_mul_left (h_comm : Commute x y) (h : IsNilpotent y) : IsNilpot
ent (x * y)
参数：h_comm : Commute x y；h : IsNilpotent y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.isNilpotent_mul_right`：isNilpotent_mul_right (h_comm : Commute x
 y) (h : IsNilpotent x) : IsNilpotent (x * y)
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
-/
theorem isNilpotent_mul_left (h_comm : Commute x y) (h : IsNilpotent y) : IsNilpotent (x * y) := by
  rw [h_comm.eq]
  exact h_comm.symm.isNilpotent_mul_right h

end Semiring

end Commute

