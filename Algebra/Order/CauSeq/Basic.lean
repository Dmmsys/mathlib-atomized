/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.GCongr

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.
There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `IsCauSeq`: a predicate that says `f : ℕ → β` is Cauchy.
* `CauSeq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/

@[expose] public section

assert_not_exists Finset Module Submonoid FloorRing

variable {α β : Type*}

open IsAbsoluteValue

section

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  (abv : β -> α) [IsAbsoluteValue abv]

/--
theorem `rat_add_continuous_lemma` / 定理 `rat_add_continuous_lemma`

English:
theorem rat_add_continuous_lemma
  given: {ε : α} (ε0 : 0 < ε)
  proof: ⟨ε / 2, half_pos ε0, fun {a₁ a₂ b₁ b₂} h₁ h₂ => by
    grw [add_sub_add_comm, abv_add abv, h₁, h₂, add_halves]⟩

中文:
定理 rat_add_continuous_lemma
  条件: {ε : α} (ε0 : 0 < ε)
  证明: ⟨ε / 2, half_pos ε0, fun {a₁ a₂ b₁ b₂} h₁ h₂ => by
    grw [add_sub_add_comm, abv_add abv, h₁, h₂, add_halves]⟩

Depends on / 依赖: abv_add, add_halves, add_sub_add_comm, half_pos
-/
theorem rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) :
    exists δ > 0, forall {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ -> abv (a₂ - b₂) < δ ->
      abv (a₁ + a₂ - (b₁ + b₂)) < ε :=
  ⟨ε / 2, half_pos ε0, fun {a₁ a₂ b₁ b₂} h₁ h₂ => by
    grw [add_sub_add_comm, abv_add abv, h₁, h₂, add_halves]⟩

/--
theorem `rat_mul_continuous_lemma` / 定理 `rat_mul_continuous_lemma`

English:
theorem rat_mul_continuous_lemma
  given: {ε K₁ K₂ : α} (ε0 : 0 < ε)
  proof: by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have εK := div_pos (half_pos ε0) K0
  refine ⟨_, εK, fun {a₁ a₂ b₁ b₂} ha₁ hb₂ h₁ h₂ => ?_⟩
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))
  replace hb₂ := lt_of_lt_of_l

中文:
定理 rat_mul_continuous_lemma
  条件: {ε K₁ K₂ : α} (ε0 : 0 < ε)
  证明: by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have εK := div_pos (half_pos ε0) K0
  refine ⟨_, εK, fun {a₁ a₂ b₁ b₂} ha₁ hb₂ h₁ h₂ => ?_⟩
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))
  replace hb₂ := lt_of_lt_of_l

Depends on / 依赖: add_left_comm, add_mul, div_pos, half_pos, le_max_left, le_max_right, le_trans, lt_of_lt_of_le, mul_add, replace, sub_eq_add_neg, zero_lt_one
-/
theorem rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) :
    exists δ > 0, forall {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ -> abv b₂ < K₂ -> abv (a₁ - b₁) < δ ->
      abv (a₂ - b₂) < δ -> abv (a₁ * a₂ - b₁ * b₂) < ε := by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have εK := div_pos (half_pos ε0) K0
  refine ⟨_, εK, fun {a₁ a₂ b₁ b₂} ha₁ hb₂ h₁ h₂ => ?_⟩
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))
  replace hb₂ := lt_of_lt_of_le hb₂ (le_trans (le_max_right K₁ _) (le_max_right 1 _))
  set M := max 1 (max K₁ K₂)
  suffices abv ((a₁ - b₁) * b₂ + a₁ * (a₂ - b₂)) < ε by
    simpa [sub_eq_add_neg, mul_add, add_mul, add_left_comm] using this
  grw [abv_add abv, abv_mul abv, abv_mul abv, h₁.le, h₂.le, ha₁, hb₂, mul_comm M,
    div_mul_cancel₀ _ (ne_of_gt K0), add_halves]

/--
theorem `rat_inv_continuous_lemma` / 定理 `rat_inv_continuous_lemma`

English:
theorem rat_inv_continuous_lemma
  statement: {β : Type*} [DivisionRing β] (abv : β -> α) [IsAbsoluteValue abv]
  proof: by
  refine ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, fun {a b} ha hb h => ?_⟩
  have a0 := K0.trans_le ha
  have b0 := K0.trans_le hb
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0)]; rw [abv_mul abv]; rw [abv_mul abv]; rw [abv_inv abv]; rw [abv_inv abv]; rw [abv_sub abv]
  grw [← ha, mu

中文:
定理 rat_inv_continuous_lemma
  结论: {β : 类型} [除环 β] (abv : β -> α) [是绝对值 abv]
  证明: by
  refine ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, fun {a b} ha hb h => ?_⟩
  have a0 := K0.trans_le ha
  have b0 := K0.trans_le hb
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0)]; rw [abv_mul abv]; rw [abv_mul abv]; rw [abv_inv abv]; rw [abv_inv abv]; rw [abv_sub abv]
  grw [← ha, mu

Depends on / 依赖: K0.ne, K0.trans_le, abv_inv, abv_mul, abv_pos, abv_sub, inv_sub_inv, mul_assoc, mul_pos, trans_le
-/
theorem rat_inv_continuous_lemma {β : Type*} [DivisionRing β] (abv : β -> α) [IsAbsoluteValue abv]
    {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
    exists δ > 0, forall {a b : β}, K <= abv a -> K <= abv b -> abv (a - b) < δ -> abv (a⁻¹ - b⁻¹) < ε := by
  refine ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, fun {a b} ha hb h => ?_⟩
  have a0 := K0.trans_le ha
  have b0 := K0.trans_le hb
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0)]; rw [abv_mul abv]; rw [abv_mul abv]; rw [abv_inv abv]; rw [abv_inv abv]; rw [abv_sub abv]
  grw [← ha, mul_assoc, ← hb, h]
  simp [K0.ne']

end

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
@[nolint unusedArguments]
/--
Definition of `IsCauSeq` / `IsCauSeq` 的定义

English:
definition IsCauSeq
  signature: {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  body: forall ε > 0, exists i, forall j >= i, abv (f j - f i) < ε

中文:
定义 IsCauSeq
  签名: {α : 类型} [域 α] [线性序 α] [是StrictOrdered环 α]
  定义体: forall ε > 0, exists i, forall j >= i, abv (f j - f i) < ε
-/
def IsCauSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {β : Type*} [Ring β] (abv : β -> α) (f : Nat -> β) :
    Prop :=
  forall ε > 0, exists i, forall j >= i, abv (f j - f i) < ε

namespace IsCauSeq

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β -> α} [IsAbsoluteValue abv] {f g : Nat -> β}

/--
theorem `cauchy₂` / 定理 `cauchy₂`

English:
theorem cauchy₂
  given: (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε)
  proof: by
  refine (hf _ (half_pos ε0)).imp fun i hi j ij k ik => ?_
  rw [← add_halves ε]
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) ?_)
  rw [abv_sub abv]; exact hi _ ik

中文:
定理 cauchy₂
  条件: (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε)
  证明: by
  refine (hf _ (half_pos ε0)).imp fun i hi j ij k ik => ?_
  rw [← add_halves ε]
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) ?_)
  rw [abv_sub abv]; exact hi _ ik

Depends on / 依赖: abv_sub, abv_sub_le, add_halves, add_lt_add, half_pos, lt_of_le_of_lt
-/
theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    exists i, forall j >= i, forall k >= i, abv (f j - f k) < ε := by
  refine (hf _ (half_pos ε0)).imp fun i hi j ij k ik => ?_
  rw [← add_halves ε]
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) ?_)
  rw [abv_sub abv]; exact hi _ ik

/--
theorem `cauchy₃` / 定理 `cauchy₃`

English:
theorem cauchy₃
  given: (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε)
  proof: let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun _ ij _ jk => H _ (le_trans ij jk) _ ij⟩

中文:
定理 cauchy₃
  条件: (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε)
  证明: let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun _ ij _ jk => H _ (le_trans ij jk) _ ij⟩

Depends on / 依赖: hf.cauchy, le_trans
-/
theorem cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    exists i, forall j >= i, forall k >= j, abv (f k - f j) < ε :=
  let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun _ ij _ jk => H _ (le_trans ij jk) _ ij⟩

/--
lemma `bounded` / 引理 `bounded`

English:
lemma bounded
  given: (hf : IsCauSeq abv f)
  statement: exists r, forall i, abv (f i) < r
  proof: by
  obtain ⟨i, h⟩ := hf _ zero_lt_one
  set R : Nat -> α := @Nat.rec (fun _ => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  have : forall i, forall j <= i, abv (f j) <= R i := by
    refine Nat.rec (by simp [hR]) ?_
    rintro i hi j (rfl | hj)
    · simp [R]
    · exact (hi j hj).tra

中文:
引理 bounded
  条件: (hf : IsCauSeq abv f)
  结论: 存在 r, 对任意 i, abv (f i) < r
  证明: by
  obtain ⟨i, h⟩ := hf _ zero_lt_one
  set R : Nat -> α := @Nat.rec (fun _ => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  have : forall i, forall j <= i, abv (f j) <= R i := by
    refine Nat.rec (by simp [hR]) ?_
    rintro i hi j (rfl | hj)
    · simp [R]
    · exact (hi j hj).tra

Depends on / 依赖: Nat.rec, abv_add, add_lt_add_of_le_of_lt, i.succ, le_max_left, le_rfl, le_total, lt_add_one, trans_lt, zero_lt_one
-/
lemma bounded (hf : IsCauSeq abv f) : exists r, forall i, abv (f i) < r := by
  obtain ⟨i, h⟩ := hf _ zero_lt_one
  set R : Nat -> α := @Nat.rec (fun _ => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  have : forall i, forall j <= i, abv (f j) <= R i := by
    refine Nat.rec (by simp [hR]) ?_
    rintro i hi j (rfl | hj)
    · simp [R]
    · exact (hi j hj).trans (le_max_left _ _)
  refine ⟨R i + 1, fun j => ?_⟩
  obtain hji | hij := le_total j i
  · exact (this i _ hji).trans_lt (lt_add_one _)
· simpa using (abv_add abv _ _).trans_lt add_lt_add_of_le_of_lt (this i _ le_rfl) (h _ hij)

/--
lemma `bounded'` / 引理 `bounded'`

English:
lemma bounded'
  given: (hf : IsCauSeq abv f) (x : α)
  statement: exists r > x, forall i, abv (f i) < r
  proof: let ⟨r, h⟩ := hf.bounded
  ⟨max r (x + 1), (lt_add_one x).trans_le (le_max_right _ _),
    fun i => (h i).trans_le (le_max_left _ _)⟩

中文:
引理 bounded'
  条件: (hf : IsCauSeq abv f) (x : α)
  结论: 存在 r > x, 对任意 i, abv (f i) < r
  证明: let ⟨r, h⟩ := hf.bounded
  ⟨max r (x + 1), (lt_add_one x).trans_le (le_max_right _ _),
    fun i => (h i).trans_le (le_max_left _ _)⟩

Depends on / 依赖: bounded, hf.bounded, le_max_left, le_max_right, lt_add_one, trans_le
-/
lemma bounded' (hf : IsCauSeq abv f) (x : α) : exists r > x, forall i, abv (f i) < r :=
  let ⟨r, h⟩ := hf.bounded
  ⟨max r (x + 1), (lt_add_one x).trans_le (le_max_right _ _),
    fun i => (h i).trans_le (le_max_left _ _)⟩

/--
lemma `const` / 引理 `const`

English:
lemma const
  given: (x : β)
  statement: IsCauSeq abv fun _ => x
  proof: fun ε ε0 => ⟨0, fun j _ => by simpa [abv_zero] using ε0⟩

中文:
引理 const
  条件: (x : β)
  结论: IsCauSeq abv fun _ => x
  证明: fun ε ε0 => ⟨0, fun j _ => by simpa [abv_zero] using ε0⟩

Depends on / 依赖: abv_zero
-/
lemma const (x : β) : IsCauSeq abv fun _ => x :=
  fun ε ε0 => ⟨0, fun j _ => by simpa [abv_zero] using ε0⟩

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hf : IsCauSeq abv f) (hg : IsCauSeq abv g)
  statement: IsCauSeq abv (f + g)
  proof: fun _ ε0 =>
  let ⟨_, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun _ ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (H₁ _ ij) (H₂ _ ij)⟩

中文:
定理 add
  条件: (hf : IsCauSeq abv f) (hg : IsCauSeq abv g)
  结论: IsCauSeq abv (f + g)
  证明: fun _ ε0 =>
  let ⟨_, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun _ ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (H₁ _ ij) (H₂ _ ij)⟩
-/
theorem add (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f + g) := fun _ ε0 =>
  let ⟨_, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun _ ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (H₁ _ ij) (H₂ _ ij)⟩

/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  given: (hf : IsCauSeq abv f) (hg : IsCauSeq abv g)
  statement: IsCauSeq abv (f * g)
  proof: fun _ ε0 =>
  let ⟨_, _, hF⟩ := hf.bounded' 0
  let ⟨_, _, hG⟩ := hg.bounded' 0
  let ⟨_, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun j ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩

中文:
引理 mul
  条件: (hf : IsCauSeq abv f) (hg : IsCauSeq abv g)
  结论: IsCauSeq abv (f * g)
  证明: fun _ ε0 =>
  let ⟨_, _, hF⟩ := hf.bounded' 0
  let ⟨_, _, hG⟩ := hg.bounded' 0
  let ⟨_, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun j ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩
-/
lemma mul (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f * g) := fun _ ε0 =>
  let ⟨_, _, hF⟩ := hf.bounded' 0
  let ⟨_, _, hG⟩ := hg.bounded' 0
  let ⟨_, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun j ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩

/--
lemma `_root_.isCauSeq_neg` / 引理 `_root_.isCauSeq_neg`

English:
lemma _root_.isCauSeq_neg
  statement: IsCauSeq abv (-f) ↔ IsCauSeq abv f
  proof: by
  simp only [IsCauSeq, Pi.neg_apply, ← neg_sub', abv_neg]

protected alias ⟨of_neg, neg⟩ := isCauSeq_neg

中文:
引理 _root_.isCauSeq_neg
  结论: IsCauSeq abv (-f) ↔ IsCauSeq abv f
  证明: by
  simp only [IsCauSeq, Pi.neg_apply, ← neg_sub', abv_neg]

protected alias ⟨of_neg, neg⟩ := isCauSeq_neg
-/
@[simp] lemma _root_.isCauSeq_neg : IsCauSeq abv (-f) ↔ IsCauSeq abv f := by
  simp only [IsCauSeq, Pi.neg_apply, ← neg_sub', abv_neg]

protected alias ⟨of_neg, neg⟩ := isCauSeq_neg

end IsCauSeq

/--
Definition of `CauSeq` / `CauSeq` 的定义

English:
definition CauSeq
  signature: {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  body: { f : Nat -> β // IsCauSeq abv f }

中文:
定义 CauSeq
  签名: {α : 类型} [域 α] [线性序 α] [是StrictOrdered环 α]
  定义体: { f : Nat -> β // IsCauSeq abv f }

Depends on / 依赖: IsCauSeq
-/
def CauSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (β : Type*) [Ring β] (abv : β -> α) : Type _ :=
  { f : Nat -> β // IsCauSeq abv f }

namespace CauSeq

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section Ring

variable [Ring β] {abv : β -> α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (CauSeq β abv) fun _ => Nat -> β
  body: ⟨Subtype.val⟩

@[ext]

中文:
实例 :
  签名: CoeFun (CauSeq β abv) fun _ => 自然数 -> β
  定义体: ⟨Subtype.val⟩

@[ext]

Depends on / 依赖: Subtype, Subtype.val
-/
instance : CoeFun (CauSeq β abv) fun _ => Nat -> β :=
  ⟨Subtype.val⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : CauSeq β abv} (h : forall i, f i = g i)
  statement: f = g
  proof: Subtype.ext (funext h)

中文:
定理 ext
  条件: {f g : CauSeq β abv} (h : 对任意 i, f i = g i)
  结论: f = g
  证明: Subtype.ext (funext h)

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem ext {f g : CauSeq β abv} (h : forall i, f i = g i) : f = g := Subtype.ext (funext h)

/--
theorem `isCauSeq` / 定理 `isCauSeq`

English:
theorem isCauSeq
  given: (f : CauSeq β abv)
  statement: IsCauSeq abv f
  proof: f.2

中文:
定理 isCauSeq
  条件: (f : CauSeq β abv)
  结论: IsCauSeq abv f
  证明: f.2
-/
theorem isCauSeq (f : CauSeq β abv) : IsCauSeq abv f :=
  f.2

/--
theorem `cauchy` / 定理 `cauchy`

English:
theorem cauchy
  given: (f : CauSeq β abv)
  statement: forall {ε}, 0 < ε -> exists i, forall j >= i, abv (f j - f i) < ε
  proof: @f.2

中文:
定理 cauchy
  条件: (f : CauSeq β abv)
  结论: 对任意 {ε}, 0 < ε -> 存在 i, 对任意 j >= i, abv (f j - f i) < ε
  证明: @f.2
-/
theorem cauchy (f : CauSeq β abv) : forall {ε}, 0 < ε -> exists i, forall j >= i, abv (f j - f i) < ε := @f.2

/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (f : CauSeq β abv) (g : Nat -> β) (e : forall i, f i = g i)
  body: ⟨g, fun ε => by rw [show g = f from (funext e).symm]; exact f.cauchy⟩

中文:
定义 ofEq
  签名: (f : CauSeq β abv) (g : 自然数 -> β) (e : 对任意 i, f i = g i)
  定义体: ⟨g, fun ε => by rw [show g = f from (funext e).symm]; exact f.cauchy⟩

Depends on / 依赖: cauchy, f.cauchy
-/
def ofEq (f : CauSeq β abv) (g : Nat -> β) (e : forall i, f i = g i) : CauSeq β abv :=
  ⟨g, fun ε => by rw [show g = f from (funext e).symm]; exact f.cauchy⟩

variable [IsAbsoluteValue abv]

/--
theorem `cauchy₂` / 定理 `cauchy₂`

English:
theorem cauchy₂
  given: (f : CauSeq β abv) {ε}
  proof: f.2.cauchy₂

中文:
定理 cauchy₂
  条件: (f : CauSeq β abv) {ε}
  证明: f.2.cauchy₂
-/
theorem cauchy₂ (f : CauSeq β abv) {ε} :
    0 < ε -> exists i, forall j >= i, forall k >= i, abv (f j - f k) < ε :=
  f.2.cauchy₂

/--
theorem `cauchy₃` / 定理 `cauchy₃`

English:
theorem cauchy₃
  given: (f : CauSeq β abv) {ε}
  statement: 0 < ε -> exists i, forall j >= i, forall k >= j, abv (f k - f j) < ε
  proof: f.2.cauchy₃

中文:
定理 cauchy₃
  条件: (f : CauSeq β abv) {ε}
  结论: 0 < ε -> 存在 i, 对任意 j >= i, 对任意 k >= j, abv (f k - f j) < ε
  证明: f.2.cauchy₃
-/
theorem cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, forall j >= i, forall k >= j, abv (f k - f j) < ε :=
  f.2.cauchy₃

/--
theorem `bounded` / 定理 `bounded`

English:
theorem bounded
  given: (f : CauSeq β abv)
  statement: exists r, forall i, abv (f i) < r
  proof: f.2.bounded

中文:
定理 bounded
  条件: (f : CauSeq β abv)
  结论: 存在 r, 对任意 i, abv (f i) < r
  证明: f.2.bounded

Depends on / 依赖: bounded
-/
theorem bounded (f : CauSeq β abv) : exists r, forall i, abv (f i) < r := f.2.bounded

/--
theorem `bounded'` / 定理 `bounded'`

English:
theorem bounded'
  given: (f : CauSeq β abv) (x : α)
  statement: exists r > x, forall i, abv (f i) < r
  proof: f.2.bounded' x

中文:
定理 bounded'
  条件: (f : CauSeq β abv) (x : α)
  结论: 存在 r > x, 对任意 i, abv (f i) < r
  证明: f.2.bounded' x

Depends on / 依赖: bounded
-/
theorem bounded' (f : CauSeq β abv) (x : α) : exists r > x, forall i, abv (f i) < r := f.2.bounded' x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (CauSeq β abv)
  body: ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 加法 (CauSeq β abv)
  定义体: ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp, norm_cast]
-/
instance : Add (CauSeq β abv) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (f g : CauSeq β abv)
  statement: ⇑(f + g) = (f : Nat -> β) + g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (f g : CauSeq β abv)
  结论: ⇑(f + g) = (f : 自然数 -> β) + g
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : Nat -> β) + g :=
  rfl

@[simp, norm_cast]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (f g : CauSeq β abv) (i : Nat)
  statement: (f + g) i = f i + g i
  proof: rfl

中文:
定理 add_apply
  条件: (f g : CauSeq β abv) (i : 自然数)
  结论: (f + g) i = f i + g i
  证明: rfl
-/
theorem add_apply (f g : CauSeq β abv) (i : Nat) : (f + g) i = f i + g i :=
  rfl

variable (abv) in
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (x : β)
  body: ⟨fun _ => x, IsCauSeq.const _⟩

中文:
定义 const
  签名: (x : β)
  定义体: ⟨fun _ => x, IsCauSeq.const _⟩

Depends on / 依赖: IsCauSeq, IsCauSeq.const
-/
def const (x : β) : CauSeq β abv := ⟨fun _ => x, IsCauSeq.const _⟩

/-- The constant Cauchy sequence -/
local notation "const" => const abv

@[simp, norm_cast]
/--
theorem `coe_const` / 定理 `coe_const`

English:
theorem coe_const
  given: (x : β)
  statement: (const x : Nat -> β) = Function.const Nat x
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_const
  条件: (x : β)
  结论: (const x : 自然数 -> β) = 函数.const 自然数 x
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_const (x : β) : (const x : Nat -> β) = Function.const Nat x :=
  rfl

@[simp, norm_cast]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: (x : β) (i : Nat)
  statement: (const x : Nat -> β) i = x
  proof: rfl

中文:
定理 const_apply
  条件: (x : β) (i : 自然数)
  结论: (const x : 自然数 -> β) i = x
  证明: rfl
-/
theorem const_apply (x : β) (i : Nat) : (const x : Nat -> β) i = x :=
  rfl

/--
theorem `const_inj` / 定理 `const_inj`

English:
theorem const_inj
  given: {x y : β}
  statement: (const x : CauSeq β abv) = const y ↔ x = y
  proof: ⟨fun h => congr_arg (fun f : CauSeq β abv => (f : Nat -> β) 0) h, congr_arg _⟩

中文:
定理 const_inj
  条件: {x y : β}
  结论: (const x : CauSeq β abv) = const y ↔ x = y
  证明: ⟨fun h => congr_arg (fun f : CauSeq β abv => (f : Nat -> β) 0) h, congr_arg _⟩

Depends on / 依赖: CauSeq, congr_arg
-/
theorem const_inj {x y : β} : (const x : CauSeq β abv) = const y ↔ x = y :=
  ⟨fun h => congr_arg (fun f : CauSeq β abv => (f : Nat -> β) 0) h, congr_arg _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (CauSeq β abv)
  body: ⟨const 0⟩

中文:
实例 :
  签名: 零 (CauSeq β abv)
  定义体: ⟨const 0⟩
-/
instance : Zero (CauSeq β abv) :=
  ⟨const 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (CauSeq β abv)
  body: ⟨const 1⟩

中文:
实例 :
  签名: 幺 (CauSeq β abv)
  定义体: ⟨const 1⟩
-/
instance : One (CauSeq β abv) :=
  ⟨const 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CauSeq β abv)
  body: ⟨0⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (CauSeq β abv)
  定义体: ⟨0⟩

@[simp, norm_cast]
-/
instance : Inhabited (CauSeq β abv) :=
  ⟨0⟩

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : CauSeq β abv) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ⇑(0 : CauSeq β abv) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ⇑(0 : CauSeq β abv) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : CauSeq β abv) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ⇑(1 : CauSeq β abv) = 1
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_one : ⇑(1 : CauSeq β abv) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (i)
  statement: (0 : CauSeq β abv) i = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 zero_apply
  条件: (i)
  结论: (0 : CauSeq β abv) i = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem zero_apply (i) : (0 : CauSeq β abv) i = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (i)
  statement: (1 : CauSeq β abv) i = 1
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (i)
  结论: (1 : CauSeq β abv) i = 1
  证明: rfl

@[simp]
-/
theorem one_apply (i) : (1 : CauSeq β abv) i = 1 :=
  rfl

@[simp]
/--
theorem `const_zero` / 定理 `const_zero`

English:
theorem const_zero
  statement: const 0 = 0
  proof: rfl

@[simp]

中文:
定理 const_zero
  结论: const 0 = 0
  证明: rfl

@[simp]
-/
theorem const_zero : const 0 = 0 :=
  rfl

@[simp]
/--
theorem `const_one` / 定理 `const_one`

English:
theorem const_one
  statement: const 1 = 1
  proof: rfl

中文:
定理 const_one
  结论: const 1 = 1
  证明: rfl
-/
theorem const_one : const 1 = 1 :=
  rfl

/--
theorem `const_add` / 定理 `const_add`

English:
theorem const_add
  given: (x y : β)
  statement: const (x + y) = const x + const y
  proof: rfl

中文:
定理 const_add
  条件: (x y : β)
  结论: const (x + y) = const x + const y
  证明: rfl
-/
theorem const_add (x y : β) : const (x + y) = const x + const y :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (CauSeq β abv)
  body: ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 乘法 (CauSeq β abv)
  定义体: ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp, norm_cast]
-/
instance : Mul (CauSeq β abv) := ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : CauSeq β abv)
  statement: ⇑(f * g) = (f : Nat -> β) * g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (f g : CauSeq β abv)
  结论: ⇑(f * g) = (f : 自然数 -> β) * g
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: AddGroup, AddGroup.toOrderedSub, toOrderedSub
-/
theorem coe_mul (f g : CauSeq β abv) : ⇑(f * g) = (f : Nat -> β) * g :=
  rfl

@[simp, norm_cast]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : CauSeq β abv) (i : Nat)
  statement: (f * g) i = f i * g i
  proof: rfl

中文:
定理 mul_apply
  条件: (f g : CauSeq β abv) (i : 自然数)
  结论: (f * g) i = f i * g i
  证明: rfl
-/
theorem mul_apply (f g : CauSeq β abv) (i : Nat) : (f * g) i = f i * g i :=
  rfl

/--
theorem `const_mul` / 定理 `const_mul`

English:
theorem const_mul
  given: (x y : β)
  statement: const (x * y) = const x * const y
  proof: rfl

中文:
定理 const_mul
  条件: (x y : β)
  结论: const (x * y) = const x * const y
  证明: rfl
-/
theorem const_mul (x y : β) : const (x * y) = const x * const y :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (CauSeq β abv)
  body: ⟨fun f => ⟨-f, f.2.neg⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 取负 (CauSeq β abv)
  定义体: ⟨fun f => ⟨-f, f.2.neg⟩⟩

@[simp, norm_cast]
-/
instance : Neg (CauSeq β abv) := ⟨fun f => ⟨-f, f.2.neg⟩⟩

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (f : CauSeq β abv)
  statement: ⇑(-f) = -f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (f : CauSeq β abv)
  结论: ⇑(-f) = -f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg (f : CauSeq β abv) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : CauSeq β abv) (i)
  statement: (-f) i = -f i
  proof: rfl

中文:
定理 neg_apply
  条件: (f : CauSeq β abv) (i)
  结论: (-f) i = -f i
  证明: rfl
-/
theorem neg_apply (f : CauSeq β abv) (i) : (-f) i = -f i :=
  rfl

/--
theorem `const_neg` / 定理 `const_neg`

English:
theorem const_neg
  given: (x : β)
  statement: const (-x) = -const x
  proof: rfl

中文:
定理 const_neg
  条件: (x : β)
  结论: const (-x) = -const x
  证明: rfl
-/
theorem const_neg (x : β) : const (-x) = -const x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (CauSeq β abv)
  body: ⟨fun f g => ofEq (f + -g) (fun x => f x - g x) fun i => by simp [sub_eq_add_neg]⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 减法 (CauSeq β abv)
  定义体: ⟨fun f g => ofEq (f + -g) (fun x => f x - g x) fun i => by simp [sub_eq_add_neg]⟩

@[simp, norm_cast]

Depends on / 依赖: sub_eq_add_neg
-/
instance : Sub (CauSeq β abv) :=
  ⟨fun f g => ofEq (f + -g) (fun x => f x - g x) fun i => by simp [sub_eq_add_neg]⟩

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (f g : CauSeq β abv)
  statement: ⇑(f - g) = (f : Nat -> β) - g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  条件: (f g : CauSeq β abv)
  结论: ⇑(f - g) = (f : 自然数 -> β) - g
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sub (f g : CauSeq β abv) : ⇑(f - g) = (f : Nat -> β) - g :=
  rfl

@[simp, norm_cast]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : CauSeq β abv) (i : Nat)
  statement: (f - g) i = f i - g i
  proof: rfl

中文:
定理 sub_apply
  条件: (f g : CauSeq β abv) (i : 自然数)
  结论: (f - g) i = f i - g i
  证明: rfl
-/
theorem sub_apply (f g : CauSeq β abv) (i : Nat) : (f - g) i = f i - g i :=
  rfl

/--
theorem `const_sub` / 定理 `const_sub`

English:
theorem const_sub
  given: (x y : β)
  statement: const (x - y) = const x - const y
  proof: rfl

中文:
定理 const_sub
  条件: (x y : β)
  结论: const (x - y) = const x - const y
  证明: rfl
-/
theorem const_sub (x y : β) : const (x - y) = const x - const y :=
  rfl

section SMul

variable {G : Type*} [SMul G β] [IsScalarTower G β β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul G (CauSeq β abv)
  body: ⟨fun a f => (ofEq (const (a • (1 : β)) * f) (a • (f : Nat -> β))) fun _ => smul_one_mul _ _⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 标量乘法 G (CauSeq β abv)
  定义体: ⟨fun a f => (ofEq (const (a • (1 : β)) * f) (a • (f : Nat -> β))) fun _ => smul_one_mul _ _⟩

@[simp, norm_cast]

Depends on / 依赖: smul_one_mul
-/
instance : SMul G (CauSeq β abv) :=
  ⟨fun a f => (ofEq (const (a • (1 : β)) * f) (a • (f : Nat -> β))) fun _ => smul_one_mul _ _⟩

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (a : G) (f : CauSeq β abv)
  statement: ⇑(a • f) = a • (f : Nat -> β)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_smul
  条件: (a : G) (f : CauSeq β abv)
  结论: ⇑(a • f) = a • (f : 自然数 -> β)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_smul (a : G) (f : CauSeq β abv) : ⇑(a • f) = a • (f : Nat -> β) :=
  rfl

@[simp, norm_cast]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (a : G) (f : CauSeq β abv) (i : Nat)
  statement: (a • f) i = a • f i
  proof: rfl

中文:
定理 smul_apply
  条件: (a : G) (f : CauSeq β abv) (i : 自然数)
  结论: (a • f) i = a • f i
  证明: rfl
-/
theorem smul_apply (a : G) (f : CauSeq β abv) (i : Nat) : (a • f) i = a • f i :=
  rfl

/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  given: (a : G) (x : β)
  statement: const (a • x) = a • const x
  proof: rfl

中文:
定理 const_smul
  条件: (a : G) (x : β)
  结论: const (a • x) = a • const x
  证明: rfl
-/
theorem const_smul (a : G) (x : β) : const (a • x) = a • const x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower G (CauSeq β abv) (CauSeq β abv)
  body: ⟨fun a f g => Subtype.ext smul_assoc a (f : Nat -> β) (g : Nat -> β)⟩

中文:
实例 :
  签名: 标量塔 G (CauSeq β abv) (CauSeq β abv)
  定义体: ⟨fun a f g => Subtype.ext smul_assoc a (f : Nat -> β) (g : Nat -> β)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance : IsScalarTower G (CauSeq β abv) (CauSeq β abv) :=
⟨fun a f g => Subtype.ext smul_assoc a (f : Nat -> β) (g : Nat -> β)⟩

end SMul

/--
Instance `addGroup` / 实例 `addGroup`

English:
instance addGroup
  signature: : AddGroup (CauSeq β abv)
  body: Function.Injective.addGroup Subtype.val Subtype.val_injective rfl coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

中文:
实例 addGroup
  签名: : 加法群 (CauSeq β abv)
  定义体: Function.Injective.addGroup Subtype.val Subtype.val_injective rfl coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

Depends on / 依赖: Function, Function.Injective.addGroup, Injective, Subtype, Subtype.val, Subtype.val_injective, addGroup, coe_add, coe_neg, coe_smul, coe_sub, val_injective
-/
instance addGroup : AddGroup (CauSeq β abv) :=
  Function.Injective.addGroup Subtype.val Subtype.val_injective rfl coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: : NatCast (CauSeq β abv)
  body: ⟨fun n => const n⟩

中文:
实例 inst自然数Cast
  签名: : 自然数嵌入 (CauSeq β abv)
  定义体: ⟨fun n => const n⟩
-/
instance instNatCast : NatCast (CauSeq β abv) := ⟨fun n => const n⟩

/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: : IntCast (CauSeq β abv)
  body: ⟨fun n => const n⟩

中文:
实例 inst整数Cast
  签名: : 整数嵌入 (CauSeq β abv)
  定义体: ⟨fun n => const n⟩
-/
instance instIntCast : IntCast (CauSeq β abv) := ⟨fun n => const n⟩

/--
Instance `addGroupWithOne` / 实例 `addGroupWithOne`

English:
instance addGroupWithOne
  signature: : AddGroupWithOne (CauSeq β abv)
  body: Function.Injective.addGroupWithOne Subtype.val Subtype.val_injective rfl rfl
  coe_add coe_neg coe_sub
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)

中文:
实例 addGroupWithOne
  签名: : 加法带幺群 (CauSeq β abv)
  定义体: Function.Injective.addGroupWithOne Subtype.val Subtype.val_injective rfl rfl
  coe_add coe_neg coe_sub
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)

Depends on / 依赖: Function, Function.Injective.addGroupWithOne, Injective, Subtype, Subtype.val, Subtype.val_injective, addGroupWithOne, coe_add, coe_neg, coe_sub, intros, val_injective
-/
instance addGroupWithOne : AddGroupWithOne (CauSeq β abv) :=
  Function.Injective.addGroupWithOne Subtype.val Subtype.val_injective rfl rfl
  coe_add coe_neg coe_sub
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (CauSeq β abv) Nat
  body: ⟨fun f n =>
(ofEq (npowRec n f) fun i => f i ^ n) by induction n <;> simp [*, npowRec, pow_succ]⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 幂 (CauSeq β abv) 自然数
  定义体: ⟨fun f n =>
(ofEq (npowRec n f) fun i => f i ^ n) by induction n <;> simp [*, npowRec, pow_succ]⟩

@[simp, norm_cast]

Depends on / 依赖: npowRec, pow_succ
-/
instance : Pow (CauSeq β abv) Nat :=
  ⟨fun f n =>
(ofEq (npowRec n f) fun i => f i ^ n) by induction n <;> simp [*, npowRec, pow_succ]⟩

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (f : CauSeq β abv) (n : Nat)
  statement: ⇑(f ^ n) = (f : Nat -> β) ^ n
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_pow
  条件: (f : CauSeq β abv) (n : 自然数)
  结论: ⇑(f ^ n) = (f : 自然数 -> β) ^ n
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_pow (f : CauSeq β abv) (n : Nat) : ⇑(f ^ n) = (f : Nat -> β) ^ n :=
  rfl

@[simp, norm_cast]
/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: (f : CauSeq β abv) (n i : Nat)
  statement: (f ^ n) i = f i ^ n
  proof: rfl

中文:
定理 pow_apply
  条件: (f : CauSeq β abv) (n i : 自然数)
  结论: (f ^ n) i = f i ^ n
  证明: rfl
-/
theorem pow_apply (f : CauSeq β abv) (n i : Nat) : (f ^ n) i = f i ^ n :=
  rfl

/--
theorem `const_pow` / 定理 `const_pow`

English:
theorem const_pow
  given: (x : β) (n : Nat)
  statement: const (x ^ n) = const x ^ n
  proof: rfl

中文:
定理 const_pow
  条件: (x : β) (n : 自然数)
  结论: const (x ^ n) = const x ^ n
  证明: rfl
-/
theorem const_pow (x : β) (n : Nat) : const (x ^ n) = const x ^ n :=
  rfl

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: : Ring (CauSeq β abv)
  body: Function.Injective.ring Subtype.val Subtype.val_injective rfl rfl coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_smul _ _) (fun _ _ => coe_smul _ _) coe_pow (fun _ => rfl) fun _ => rfl

中文:
实例 ring
  签名: : 环 (CauSeq β abv)
  定义体: Function.Injective.ring Subtype.val Subtype.val_injective rfl rfl coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_smul _ _) (fun _ _ => coe_smul _ _) coe_pow (fun _ => rfl) fun _ => rfl

Depends on / 依赖: Function, Function.Injective.ring, Injective, Subtype, Subtype.val, Subtype.val_injective, coe_add, coe_mul, coe_neg, coe_pow, coe_smul, coe_sub, val_injective
-/
instance ring : Ring (CauSeq β abv) :=
  Function.Injective.ring Subtype.val Subtype.val_injective rfl rfl coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_smul _ _) (fun _ _ => coe_smul _ _) coe_pow (fun _ => rfl) fun _ => rfl

instance {β : Type*} [CommRing β] {abv : β -> α} [IsAbsoluteValue abv] : CommRing (CauSeq β abv) :=
  { CauSeq.ring with
    mul_comm := fun a b => ext fun n => by simp [mul_comm] }

/--
Definition of `LimZero` / `LimZero` 的定义

English:
definition LimZero
  signature: {abv : β -> α} (f : CauSeq β abv)
  body: forall ε > 0, exists i, forall j >= i, abv (f j) < ε

中文:
定义 LimZero
  签名: {abv : β -> α} (f : CauSeq β abv)
  定义体: forall ε > 0, exists i, forall j >= i, abv (f j) < ε
-/
def LimZero {abv : β -> α} (f : CauSeq β abv) : Prop :=
  forall ε > 0, exists i, forall j >= i, abv (f j) < ε

/--
theorem `add_limZero` / 定理 `add_limZero`

English:
theorem add_limZero
  given: {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g)
  statement: LimZero (f + g)
  proof: H _ ij
      simpa [add_halves ε] using lt_of_le_of_lt (abv_add abv _ _) (add_lt_add H₁ H₂)

中文:
定理 add_limZero
  条件: {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g)
  结论: LimZero (f + g)
  证明: H _ ij
      simpa [add_halves ε] using lt_of_le_of_lt (abv_add abv _ _) (add_lt_add H₁ H₂)
-/
theorem add_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f + g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ <| half_pos ε0) (hg _ <| half_pos ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      simpa [add_halves ε] using lt_of_le_of_lt (abv_add abv _ _) (add_lt_add H₁ H₂)

/--
theorem `mul_limZero_right` / 定理 `mul_limZero_right`

English:
theorem mul_limZero_right
  given: (f : CauSeq β abv) {g} (hg : LimZero g)
  statement: LimZero (f * g)
  proof: f.bounded' 0
    (hg _ <| div_pos ε0 F0).imp fun _ H j ij => by
      have := mul_lt_mul' (le_of_lt <| hF j) (H _ ij) (abv_nonneg abv _) F0
      rwa [mul_comm F, div_mul_cancel₀ _ (ne_of_gt F0), ← abv_mul] at this

中文:
定理 mul_limZero_right
  条件: (f : CauSeq β abv) {g} (hg : LimZero g)
  结论: LimZero (f * g)
  证明: f.bounded' 0
    (hg _ <| div_pos ε0 F0).imp fun _ H j ij => by
      have := mul_lt_mul' (le_of_lt <| hF j) (H _ ij) (abv_nonneg abv _) F0
      rwa [mul_comm F, div_mul_cancel₀ _ (ne_of_gt F0), ← abv_mul] at this

Depends on / 依赖: bounded, f.bounded
-/
theorem mul_limZero_right (f : CauSeq β abv) {g} (hg : LimZero g) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨F, F0, hF⟩ := f.bounded' 0
    (hg _ <| div_pos ε0 F0).imp fun _ H j ij => by
      have := mul_lt_mul' (le_of_lt <| hF j) (H _ ij) (abv_nonneg abv _) F0
      rwa [mul_comm F, div_mul_cancel₀ _ (ne_of_gt F0), ← abv_mul] at this

/--
theorem `mul_limZero_left` / 定理 `mul_limZero_left`

English:
theorem mul_limZero_left
  given: {f} (g : CauSeq β abv) (hg : LimZero f)
  statement: LimZero (f * g)
  proof: g.bounded' 0
    (hg _ <| div_pos ε0 G0).imp fun _ H j ij => by
      have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _)
      rwa [div_mul_cancel₀ _ (ne_of_gt G0), ← abv_mul] at this

中文:
定理 mul_limZero_left
  条件: {f} (g : CauSeq β abv) (hg : LimZero f)
  结论: LimZero (f * g)
  证明: g.bounded' 0
    (hg _ <| div_pos ε0 G0).imp fun _ H j ij => by
      have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _)
      rwa [div_mul_cancel₀ _ (ne_of_gt G0), ← abv_mul] at this

Depends on / 依赖: bounded, g.bounded
-/
theorem mul_limZero_left {f} (g : CauSeq β abv) (hg : LimZero f) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨G, G0, hG⟩ := g.bounded' 0
    (hg _ <| div_pos ε0 G0).imp fun _ H j ij => by
      have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _)
      rwa [div_mul_cancel₀ _ (ne_of_gt G0), ← abv_mul] at this

/--
theorem `neg_limZero` / 定理 `neg_limZero`

English:
theorem neg_limZero
  given: {f : CauSeq β abv} (hf : LimZero f)
  statement: LimZero (-f)
  proof: by
  rw [← neg_one_mul f]
  exact mul_limZero_right _ hf

中文:
定理 neg_limZero
  条件: {f : CauSeq β abv} (hf : LimZero f)
  结论: LimZero (-f)
  证明: by
  rw [← neg_one_mul f]
  exact mul_limZero_right _ hf

Depends on / 依赖: mul_limZero_right, neg_one_mul
-/
theorem neg_limZero {f : CauSeq β abv} (hf : LimZero f) : LimZero (-f) := by
  rw [← neg_one_mul f]
  exact mul_limZero_right _ hf

/--
theorem `sub_limZero` / 定理 `sub_limZero`

English:
theorem sub_limZero
  given: {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g)
  statement: LimZero (f - g)
  proof: by
  simpa only [sub_eq_add_neg] using add_limZero hf (neg_limZero hg)

中文:
定理 sub_limZero
  条件: {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g)
  结论: LimZero (f - g)
  证明: by
  simpa only [sub_eq_add_neg] using add_limZero hf (neg_limZero hg)

Depends on / 依赖: add_limZero, neg_limZero, sub_eq_add_neg
-/
theorem sub_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f - g) := by
  simpa only [sub_eq_add_neg] using add_limZero hf (neg_limZero hg)

/--
theorem `limZero_sub_rev` / 定理 `limZero_sub_rev`

English:
theorem limZero_sub_rev
  given: {f g : CauSeq β abv} (hfg : LimZero (f - g))
  statement: LimZero (g - f)
  proof: by
  simpa using neg_limZero hfg

中文:
定理 limZero_sub_rev
  条件: {f g : CauSeq β abv} (hfg : LimZero (f - g))
  结论: LimZero (g - f)
  证明: by
  simpa using neg_limZero hfg

Depends on / 依赖: neg_limZero
-/
theorem limZero_sub_rev {f g : CauSeq β abv} (hfg : LimZero (f - g)) : LimZero (g - f) := by
  simpa using neg_limZero hfg

/--
theorem `zero_limZero` / 定理 `zero_limZero`

English:
theorem zero_limZero
  statement: LimZero (0 : CauSeq β abv)

中文:
定理 zero_limZero
  结论: LimZero (0 : CauSeq β abv)
-/
theorem zero_limZero : LimZero (0 : CauSeq β abv)
  | ε, ε0 => ⟨0, fun j _ => by simpa [abv_zero abv] using ε0⟩

/--
theorem `const_limZero` / 定理 `const_limZero`

English:
theorem const_limZero
  given: {x : β}
  statement: LimZero (const x) ↔ x = 0
  proof: ⟨fun H =>
(abv_eq_zero abv).1
      (eq_of_le_of_forall_lt_imp_le_of_dense (abv_nonneg abv _)) fun _ ε0 =>
        let ⟨_, hi⟩ := H _ ε0
le_of_lt hi _ le_rfl,
    fun e => e.symm ▸ zero_limZero⟩

中文:
定理 const_limZero
  条件: {x : β}
  结论: LimZero (const x) ↔ x = 0
  证明: ⟨fun H =>
(abv_eq_zero abv).1
      (eq_of_le_of_forall_lt_imp_le_of_dense (abv_nonneg abv _)) fun _ ε0 =>
        let ⟨_, hi⟩ := H _ ε0
le_of_lt hi _ le_rfl,
    fun e => e.symm ▸ zero_limZero⟩

Depends on / 依赖: abv_eq_zero, abv_nonneg, e.symm, eq_of_le_of_forall_lt_imp_le_of_dense, le_of_lt, le_rfl, zero_limZero
-/
theorem const_limZero {x : β} : LimZero (const x) ↔ x = 0 :=
  ⟨fun H =>
(abv_eq_zero abv).1
      (eq_of_le_of_forall_lt_imp_le_of_dense (abv_nonneg abv _)) fun _ ε0 =>
        let ⟨_, hi⟩ := H _ ε0
le_of_lt hi _ le_rfl,
    fun e => e.symm ▸ zero_limZero⟩

/--
Instance `equiv` / 实例 `equiv`

English:
instance equiv
  signature: : Setoid (CauSeq β abv)
  body: ⟨fun f g => LimZero (f - g),
    ⟨fun f => by simp [zero_limZero],
    fun f ε hε => by simpa using neg_limZero f ε hε,
    fun fg gh => by simpa using add_limZero fg gh⟩⟩

中文:
实例 equiv
  签名: : 集合等价关系 (CauSeq β abv)
  定义体: ⟨fun f g => LimZero (f - g),
    ⟨fun f => by simp [zero_limZero],
    fun f ε hε => by simpa using neg_limZero f ε hε,
    fun fg gh => by simpa using add_limZero fg gh⟩⟩

Depends on / 依赖: LimZero, add_limZero, neg_limZero, zero_limZero
-/
instance equiv : Setoid (CauSeq β abv) :=
  ⟨fun f g => LimZero (f - g),
    ⟨fun f => by simp [zero_limZero],
    fun f ε hε => by simpa using neg_limZero f ε hε,
    fun fg gh => by simpa using add_limZero fg gh⟩⟩

/--
theorem `add_equiv_add` / 定理 `add_equiv_add`

English:
theorem add_equiv_add
  given: {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2)
  proof: by simpa only [← add_sub_add_comm] using! add_limZero hf hg

中文:
定理 add_equiv_add
  条件: {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2)
  证明: by simpa only [← add_sub_add_comm] using! add_limZero hf hg

Depends on / 依赖: add_limZero, add_sub_add_comm
-/
theorem add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 + g1 ≈ f2 + g2 := by simpa only [← add_sub_add_comm] using! add_limZero hf hg

/--
theorem `neg_equiv_neg` / 定理 `neg_equiv_neg`

English:
theorem neg_equiv_neg
  given: {f g : CauSeq β abv} (hf : f ≈ g)
  statement: -f ≈ -g
  proof: by
  simpa only [neg_sub'] using! neg_limZero hf

中文:
定理 neg_equiv_neg
  条件: {f g : CauSeq β abv} (hf : f ≈ g)
  结论: -f ≈ -g
  证明: by
  simpa only [neg_sub'] using! neg_limZero hf

Depends on / 依赖: neg_limZero, neg_sub
-/
theorem neg_equiv_neg {f g : CauSeq β abv} (hf : f ≈ g) : -f ≈ -g := by
  simpa only [neg_sub'] using! neg_limZero hf

/--
theorem `sub_equiv_sub` / 定理 `sub_equiv_sub`

English:
theorem sub_equiv_sub
  given: {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2)
  proof: by simpa only [sub_eq_add_neg] using add_equiv_add hf (neg_equiv_neg hg)

中文:
定理 sub_equiv_sub
  条件: {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2)
  证明: by simpa only [sub_eq_add_neg] using add_equiv_add hf (neg_equiv_neg hg)

Depends on / 依赖: add_equiv_add, neg_equiv_neg, sub_eq_add_neg
-/
theorem sub_equiv_sub {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 - g1 ≈ f2 - g2 := by simpa only [sub_eq_add_neg] using add_equiv_add hf (neg_equiv_neg hg)

/--
theorem `equiv_def₃` / 定理 `equiv_def₃`

English:
theorem equiv_def₃
  given: {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε)
  proof: (exists_forall_ge_and (h _ <| half_pos ε0) (f.cauchy₃ <| half_pos ε0)).imp fun _ H j ij k jk => by
    let ⟨h₁, h₂⟩ := H _ ij
    have := lt_of_le_of_lt (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk))
    rwa [sub_add_sub_cancel', add_halves] at this

中文:
定理 equiv_def₃
  条件: {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε)
  证明: (exists_forall_ge_and (h _ <| half_pos ε0) (f.cauchy₃ <| half_pos ε0)).imp fun _ H j ij k jk => by
    let ⟨h₁, h₂⟩ := H _ ij
    have := lt_of_le_of_lt (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk))
    rwa [sub_add_sub_cancel', add_halves] at this

Depends on / 依赖: abv_add, add_halves, add_lt_add, exists_forall_ge_and, f.cauchy, half_pos, lt_of_le_of_lt, sub_add_sub_cancel
-/
theorem equiv_def₃ {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) :
    exists i, forall j >= i, forall k >= j, abv (f k - g j) < ε :=
  (exists_forall_ge_and (h _ <| half_pos ε0) (f.cauchy₃ <| half_pos ε0)).imp fun _ H j ij k jk => by
    let ⟨h₁, h₂⟩ := H _ ij
    have := lt_of_le_of_lt (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk))
    rwa [sub_add_sub_cancel', add_halves] at this

/--
theorem `limZero_congr` / 定理 `limZero_congr`

English:
theorem limZero_congr
  given: {f g : CauSeq β abv} (h : f ≈ g)
  statement: LimZero f ↔ LimZero g
  proof: ⟨fun l => by simpa using add_limZero (Setoid.symm h) l, fun l => by simpa using add_limZero h l⟩

中文:
定理 limZero_congr
  条件: {f g : CauSeq β abv} (h : f ≈ g)
  结论: LimZero f ↔ LimZero g
  证明: ⟨fun l => by simpa using add_limZero (Setoid.symm h) l, fun l => by simpa using add_limZero h l⟩

Depends on / 依赖: Setoid, Setoid.symm, add_limZero
-/
theorem limZero_congr {f g : CauSeq β abv} (h : f ≈ g) : LimZero f ↔ LimZero g :=
  ⟨fun l => by simpa using add_limZero (Setoid.symm h) l, fun l => by simpa using add_limZero h l⟩

/--
theorem `abv_pos_of_not_limZero` / 定理 `abv_pos_of_not_limZero`

English:
theorem abv_pos_of_not_limZero
  given: {f : CauSeq β abv} (hf : ¬LimZero f)
  proof: by
  by_contra nk
  refine hf fun ε ε0 => ?_
  simp only [not_exists, not_and, not_forall, not_le] at nk
  obtain ⟨i, hi⟩ := f.cauchy₃ (half_pos ε0)
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k jk => ?_⟩
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
 

中文:
定理 abv_pos_of_not_limZero
  条件: {f : CauSeq β abv} (hf : ¬LimZero f)
  证明: by
  by_contra nk
  refine hf fun ε ε0 => ?_
  simp only [not_exists, not_and, not_forall, not_le] at nk
  obtain ⟨i, hi⟩ := f.cauchy₃ (half_pos ε0)
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k jk => ?_⟩
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
 

Depends on / 依赖: abv_add, add_halves, add_lt_add, f.cauchy, half_pos, lt_of_le_of_lt, not_and, not_exists, not_forall, not_le, sub_add_cancel
-/
theorem abv_pos_of_not_limZero {f : CauSeq β abv} (hf : ¬LimZero f) :
    exists K > 0, exists i, forall j >= i, K <= abv (f j) := by
  by_contra nk
  refine hf fun ε ε0 => ?_
  simp only [not_exists, not_and, not_forall, not_le] at nk
  obtain ⟨i, hi⟩ := f.cauchy₃ (half_pos ε0)
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k jk => ?_⟩
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
  rwa [sub_add_cancel, add_halves] at this

/--
theorem `of_near` / 定理 `of_near`

English:
theorem of_near
  given: (f : Nat -> β) (g : CauSeq β abv) (h : forall ε > 0, exists i, forall j >= i, abv (f j - g j) < ε)
  proof: exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (g.cauchy₃ <| half_pos ε0)
    ⟨i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := hi _ le_rfl; rw [abv_sub abv] at h₁
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add th

中文:
定理 of_near
  条件: (f : 自然数 -> β) (g : CauSeq β abv) (h : 对任意 ε > 0, 存在 i, 对任意 j >= i, abv (f j - g j) < ε)
  证明: exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (g.cauchy₃ <| half_pos ε0)
    ⟨i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := hi _ le_rfl; rw [abv_sub abv] at h₁
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add th

Depends on / 依赖: exists_forall_ge_and, g.cauchy, half_pos
-/
theorem of_near (f : Nat -> β) (g : CauSeq β abv) (h : forall ε > 0, exists i, forall j >= i, abv (f j - g j) < ε) :
    IsCauSeq abv f
  | ε, ε0 =>
    let ⟨i, hi⟩ := exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (g.cauchy₃ <| half_pos ε0)
    ⟨i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := hi _ le_rfl; rw [abv_sub abv] at h₁
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add this (h₂ _ ij))
      rwa [add_halves, add_halves, add_right_comm, sub_add_sub_cancel, sub_add_sub_cancel] at this⟩

/--
theorem `not_limZero_of_not_congr_zero` / 定理 `not_limZero_of_not_congr_zero`

English:
theorem not_limZero_of_not_congr_zero
  given: {f : CauSeq _ abv} (hf : ¬f ≈ 0)
  statement: ¬LimZero f
  proof: by
  intro h
  have : LimZero (f - 0) := by simp [h]
  exact hf this

中文:
定理 not_limZero_of_not_congr_zero
  条件: {f : CauSeq _ abv} (hf : ¬f ≈ 0)
  结论: ¬LimZero f
  证明: by
  intro h
  have : LimZero (f - 0) := by simp [h]
  exact hf this

Depends on / 依赖: LimZero
-/
theorem not_limZero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f := by
  intro h
  have : LimZero (f - 0) := by simp [h]
  exact hf this

/--
theorem `mul_equiv_zero` / 定理 `mul_equiv_zero`

English:
theorem mul_equiv_zero
  given: (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0)
  statement: g * f ≈ 0
  proof: have : LimZero (f - 0) := hf
have : LimZero (g * f) := mul_limZero_right _ by simpa
  show LimZero (g * f - 0) by simpa

中文:
定理 mul_equiv_zero
  条件: (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0)
  结论: g * f ≈ 0
  证明: have : LimZero (f - 0) := hf
have : LimZero (g * f) := mul_limZero_right _ by simpa
  show LimZero (g * f - 0) by simpa

Depends on / 依赖: LimZero, mul_limZero_right
-/
theorem mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : g * f ≈ 0 :=
  have : LimZero (f - 0) := hf
have : LimZero (g * f) := mul_limZero_right _ by simpa
  show LimZero (g * f - 0) by simpa

/--
theorem `mul_equiv_zero'` / 定理 `mul_equiv_zero'`

English:
theorem mul_equiv_zero'
  given: (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0)
  statement: f * g ≈ 0
  proof: have : LimZero (f - 0) := hf
have : LimZero (f * g) := mul_limZero_left _ by simpa
  show LimZero (f * g - 0) by simpa

中文:
定理 mul_equiv_zero'
  条件: (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0)
  结论: f * g ≈ 0
  证明: have : LimZero (f - 0) := hf
have : LimZero (f * g) := mul_limZero_left _ by simpa
  show LimZero (f * g - 0) by simpa

Depends on / 依赖: LimZero, mul_limZero_left
-/
theorem mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : f * g ≈ 0 :=
  have : LimZero (f - 0) := hf
have : LimZero (f * g) := mul_limZero_left _ by simpa
  show LimZero (f * g - 0) by simpa

/--
theorem `mul_not_equiv_zero` / 定理 `mul_not_equiv_zero`

English:
theorem mul_not_equiv_zero
  given: {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0)
  statement: ¬f * g ≈ 0
  proof: fun (this : LimZero (f * g - 0)) => by
  have hlz : LimZero (f * g) := by simpa
  have hf' : ¬LimZero f := by simpa using show ¬LimZero (f - 0) from hf
  have hg' : ¬LimZero g := by simpa using show ¬LimZero (g - 0) from hg
  rcases abv_pos_of_not_limZero hf' with ⟨a1, ha1, N1, hN1⟩
  rcases abv_pos

中文:
定理 mul_not_equiv_zero
  条件: {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0)
  结论: ¬f * g ≈ 0
  证明: fun (this : LimZero (f * g - 0)) => by
  have hlz : LimZero (f * g) := by simpa
  have hf' : ¬LimZero f := by simpa using show ¬LimZero (f - 0) from hf
  have hg' : ¬LimZero g := by simpa using show ¬LimZero (g - 0) from hg
  rcases abv_pos_of_not_limZero hf' with ⟨a1, ha1, N1, hN1⟩
  rcases abv_pos

Depends on / 依赖: LimZero, abv_pos_of_not_limZero, le_max_, le_max_left, le_trans, mul_pos
-/
theorem mul_not_equiv_zero {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0 :=
  fun (this : LimZero (f * g - 0)) => by
  have hlz : LimZero (f * g) := by simpa
  have hf' : ¬LimZero f := by simpa using show ¬LimZero (f - 0) from hf
  have hg' : ¬LimZero g := by simpa using show ¬LimZero (g - 0) from hg
  rcases abv_pos_of_not_limZero hf' with ⟨a1, ha1, N1, hN1⟩
  rcases abv_pos_of_not_limZero hg' with ⟨a2, ha2, N2, hN2⟩
  have : 0 < a1 * a2 := mul_pos ha1 ha2
  obtain ⟨N, hN⟩ := hlz _ this
  let i := max N (max N1 N2)
  have hN' := hN i (le_max_left _ _)
  have hN1' := hN1 i (le_trans (le_max_left _ _) (le_max_right _ _))
  have hN1' := hN2 i (le_trans (le_max_right _ _) (le_max_right _ _))
  apply not_le_of_gt hN'
  change _ <= abv (_ * _)
  rw [abv_mul abv]
  gcongr

/--
theorem `const_equiv` / 定理 `const_equiv`

English:
theorem const_equiv
  given: {x y : β}
  statement: const x ≈ const y ↔ x = y
  proof: show LimZero _ ↔ _ by rw [← const_sub, const_limZero, sub_eq_zero]

中文:
定理 const_equiv
  条件: {x y : β}
  结论: const x ≈ const y ↔ x = y
  证明: show LimZero _ ↔ _ by rw [← const_sub, const_limZero, sub_eq_zero]

Depends on / 依赖: LimZero, const_limZero, const_sub, sub_eq_zero
-/
theorem const_equiv {x y : β} : const x ≈ const y ↔ x = y :=
  show LimZero _ ↔ _ by rw [← const_sub, const_limZero, sub_eq_zero]

/--
theorem `mul_equiv_mul` / 定理 `mul_equiv_mul`

English:
theorem mul_equiv_mul
  given: {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2)
  proof: by
  simpa only [mul_sub, sub_mul, sub_add_sub_cancel]
    using! add_limZero (mul_limZero_left g1 hf) (mul_limZero_right f2 hg)

中文:
定理 mul_equiv_mul
  条件: {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2)
  证明: by
  simpa only [mul_sub, sub_mul, sub_add_sub_cancel]
    using! add_limZero (mul_limZero_left g1 hf) (mul_limZero_right f2 hg)

Depends on / 依赖: add_limZero, mul_limZero_left, mul_limZero_right, mul_sub, sub_add_sub_cancel, sub_mul
-/
theorem mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 * g1 ≈ f2 * g2 := by
  simpa only [mul_sub, sub_mul, sub_add_sub_cancel]
    using! add_limZero (mul_limZero_left g1 hf) (mul_limZero_right f2 hg)

/--
theorem `smul_equiv_smul` / 定理 `smul_equiv_smul`

English:
theorem smul_equiv_smul
  statement: {G : Type*} [SMul G β] [IsScalarTower G β β] {f1 f2 : CauSeq β abv} (c : G)
  proof: by
  simpa [const_smul, smul_one_mul _ _] using
    mul_equiv_mul (const_equiv.mpr <| Eq.refl <| c • (1 : β)) hf

中文:
定理 smul_equiv_smul
  结论: {G : 类型} [标量乘法 G β] [标量塔 G β β] {f1 f2 : CauSeq β abv} (c : G)
  证明: by
  simpa [const_smul, smul_one_mul _ _] using
    mul_equiv_mul (const_equiv.mpr <| Eq.refl <| c • (1 : β)) hf

Depends on / 依赖: Eq.refl, const_equiv, const_equiv.mpr, const_smul, mul_equiv_mul, smul_one_mul
-/
theorem smul_equiv_smul {G : Type*} [SMul G β] [IsScalarTower G β β] {f1 f2 : CauSeq β abv} (c : G)
    (hf : f1 ≈ f2) : c • f1 ≈ c • f2 := by
  simpa [const_smul, smul_one_mul _ _] using
    mul_equiv_mul (const_equiv.mpr <| Eq.refl <| c • (1 : β)) hf

/--
theorem `pow_equiv_pow` / 定理 `pow_equiv_pow`

English:
theorem pow_equiv_pow
  given: {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : Nat)
  statement: f1 ^ n ≈ f2 ^ n
  proof: by
  induction n with
  | zero => simp only [pow_zero, Setoid.refl]
  | succ n ih => simpa only [pow_succ'] using mul_equiv_mul hf ih

中文:
定理 pow_equiv_pow
  条件: {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : 自然数)
  结论: f1 ^ n ≈ f2 ^ n
  证明: by
  induction n with
  | zero => simp only [pow_zero, Setoid.refl]
  | succ n ih => simpa only [pow_succ'] using mul_equiv_mul hf ih

Depends on / 依赖: Setoid, Setoid.refl, mul_equiv_mul, pow_succ, pow_zero
-/
theorem pow_equiv_pow {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : Nat) : f1 ^ n ≈ f2 ^ n := by
  induction n with
  | zero => simp only [pow_zero, Setoid.refl]
  | succ n ih => simpa only [pow_succ'] using mul_equiv_mul hf ih

end Ring

section IsDomain

variable [Ring β] [IsDomain β] (abv : β -> α) [IsAbsoluteValue abv]

/--
theorem `one_not_equiv_zero` / 定理 `one_not_equiv_zero`

English:
theorem one_not_equiv_zero
  statement: ¬const abv 1 ≈ const abv 0
  proof: fun h =>
  have : forall ε > 0, exists i, forall k, i <= k -> abv (1 - 0) < ε := h
  have h1 : abv 1 <= 0 :=
    le_of_not_gt fun h2 : 0 < abv 1 =>
(Exists.elim (this _ h2)) fun i hi => lt_irrefl (abv 1) by simpa using hi _ le_rfl
  have h2 : 0 <= abv 1 := abv_nonneg abv _
  have : abv 1 = 0 := le_a

中文:
定理 one_not_equiv_zero
  结论: ¬const abv 1 ≈ const abv 0
  证明: fun h =>
  have : forall ε > 0, exists i, forall k, i <= k -> abv (1 - 0) < ε := h
  have h1 : abv 1 <= 0 :=
    le_of_not_gt fun h2 : 0 < abv 1 =>
(Exists.elim (this _ h2)) fun i hi => lt_irrefl (abv 1) by simpa using hi _ le_rfl
  have h2 : 0 <= abv 1 := abv_nonneg abv _
  have : abv 1 = 0 := le_a
-/
theorem one_not_equiv_zero : ¬const abv 1 ≈ const abv 0 := fun h =>
  have : forall ε > 0, exists i, forall k, i <= k -> abv (1 - 0) < ε := h
  have h1 : abv 1 <= 0 :=
    le_of_not_gt fun h2 : 0 < abv 1 =>
(Exists.elim (this _ h2)) fun i hi => lt_irrefl (abv 1) by simpa using hi _ le_rfl
  have h2 : 0 <= abv 1 := abv_nonneg abv _
  have : abv 1 = 0 := le_antisymm h1 h2
  have : (1 : β) = 0 := (abv_eq_zero abv).mp this
  absurd this one_ne_zero

end IsDomain

section DivisionRing

variable [DivisionRing β] {abv : β -> α} [IsAbsoluteValue abv]

/--
theorem `inv_aux` / 定理 `inv_aux`

English:
theorem inv_aux
  given: {f : CauSeq β abv} (hf : ¬LimZero f)
  proof: abv_pos_of_not_limZero hf
    let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
    ⟨i, fun _ ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩

中文:
定理 inv_aux
  条件: {f : CauSeq β abv} (hf : ¬LimZero f)
  证明: abv_pos_of_not_limZero hf
    let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
    ⟨i, fun _ ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩

Depends on / 依赖: abv_pos_of_not_limZero
-/
theorem inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) :
    forall ε > 0, exists i, forall j >= i, abv ((f j)⁻¹ - (f i)⁻¹) < ε
  | _, ε0 =>
    let ⟨_, K0, HK⟩ := abv_pos_of_not_limZero hf
    let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
    ⟨i, fun _ ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (f : CauSeq β abv) (hf : ¬LimZero f)
  body: ⟨_, inv_aux hf⟩

@[simp, norm_cast]

中文:
定义 inv
  签名: (f : CauSeq β abv) (hf : ¬LimZero f)
  定义体: ⟨_, inv_aux hf⟩

@[simp, norm_cast]

Depends on / 依赖: inv_aux
-/
def inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩

@[simp, norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: {f : CauSeq β abv} (hf)
  statement: ⇑(inv f hf) = (f : Nat -> β)⁻¹
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inv
  条件: {f : CauSeq β abv} (hf)
  结论: ⇑(inv f hf) = (f : 自然数 -> β)⁻¹
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_inv {f : CauSeq β abv} (hf) : ⇑(inv f hf) = (f : Nat -> β)⁻¹ :=
  rfl

@[simp, norm_cast]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: {f : CauSeq β abv} (hf i)
  statement: inv f hf i = (f i)⁻¹
  proof: rfl

中文:
定理 inv_apply
  条件: {f : CauSeq β abv} (hf i)
  结论: inv f hf i = (f i)⁻¹
  证明: rfl
-/
theorem inv_apply {f : CauSeq β abv} (hf i) : inv f hf i = (f i)⁻¹ :=
  rfl

/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  given: {f : CauSeq β abv} (hf)
  statement: inv f hf * f ≈ 1
  proof: fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩

中文:
定理 inv_mul_cancel
  条件: {f : CauSeq β abv} (hf)
  结论: inv f hf * f ≈ 1
  证明: fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩
-/
theorem inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf * f ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩

/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: {f : CauSeq β abv} (hf)
  statement: f * inv f hf ≈ 1
  proof: fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩

中文:
定理 mul_inv_cancel
  条件: {f : CauSeq β abv} (hf)
  结论: f * inv f hf ≈ 1
  证明: fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩
-/
theorem mul_inv_cancel {f : CauSeq β abv} (hf) : f * inv f hf ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩

/--
theorem `const_inv` / 定理 `const_inv`

English:
theorem const_inv
  given: {x : β} (hx : x != 0)
  proof: rfl

中文:
定理 const_inv
  条件: {x : β} (hx : x != 0)
  证明: rfl
-/
theorem const_inv {x : β} (hx : x != 0) :
    const abv x⁻¹ = inv (const abv x) (by rwa [const_limZero]) :=
  rfl

end DivisionRing

section Abs

/-- The constant Cauchy sequence -/
local notation "const" => const abs

/--
Definition of `Pos` / `Pos` 的定义

English:
definition Pos
  signature: (f : CauSeq α abs)
  body: exists K > 0, exists i, forall j >= i, K <= f j

中文:
定义 Pos
  签名: (f : CauSeq α abs)
  定义体: exists K > 0, exists i, forall j >= i, K <= f j
-/
def Pos (f : CauSeq α abs) : Prop :=
  exists K > 0, exists i, forall j >= i, K <= f j

/--
theorem `not_limZero_of_pos` / 定理 `not_limZero_of_pos`

English:
theorem not_limZero_of_pos
  given: {f : CauSeq α abs}
  statement: Pos f -> ¬LimZero f
  proof: exists_forall_ge_and hF (H _ F0)
    let ⟨h₁, h₂⟩ := h _ le_rfl
    not_lt_of_ge h₁ (abs_lt.1 h₂).2

中文:
定理 not_limZero_of_pos
  条件: {f : CauSeq α abs}
  结论: Pos f -> ¬LimZero f
  证明: exists_forall_ge_and hF (H _ F0)
    let ⟨h₁, h₂⟩ := h _ le_rfl
    not_lt_of_ge h₁ (abs_lt.1 h₂).2

Depends on / 依赖: exists_forall_ge_and
-/
theorem not_limZero_of_pos {f : CauSeq α abs} : Pos f -> ¬LimZero f
  | ⟨_, F0, hF⟩, H =>
    let ⟨_, h⟩ := exists_forall_ge_and hF (H _ F0)
    let ⟨h₁, h₂⟩ := h _ le_rfl
    not_lt_of_ge h₁ (abs_lt.1 h₂).2

/--
theorem `const_pos` / 定理 `const_pos`

English:
theorem const_pos
  given: {x : α}
  statement: Pos (const x) ↔ 0 < x
  proof: ⟨fun ⟨_, K0, _, h⟩ => lt_of_lt_of_le K0 (h _ le_rfl), fun h => ⟨x, h, 0, fun _ _ => le_rfl⟩⟩

中文:
定理 const_pos
  条件: {x : α}
  结论: Pos (const x) ↔ 0 < x
  证明: ⟨fun ⟨_, K0, _, h⟩ => lt_of_lt_of_le K0 (h _ le_rfl), fun h => ⟨x, h, 0, fun _ _ => le_rfl⟩⟩

Depends on / 依赖: le_rfl, lt_of_lt_of_le
-/
theorem const_pos {x : α} : Pos (const x) ↔ 0 < x :=
  ⟨fun ⟨_, K0, _, h⟩ => lt_of_lt_of_le K0 (h _ le_rfl), fun h => ⟨x, h, 0, fun _ _ => le_rfl⟩⟩

/--
theorem `add_pos` / 定理 `add_pos`

English:
theorem add_pos
  given: {f g : CauSeq α abs}
  statement: Pos f -> Pos g -> Pos (f + g)
  proof: exists_forall_ge_and hF hG
    ⟨_, _root_.add_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩

中文:
定理 add_pos
  条件: {f g : CauSeq α abs}
  结论: Pos f -> Pos g -> Pos (f + g)
  证明: exists_forall_ge_and hF hG
    ⟨_, _root_.add_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩

Depends on / 依赖: exists_forall_ge_and
-/
theorem add_pos {f g : CauSeq α abs} : Pos f -> Pos g -> Pos (f + g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, _root_.add_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩

/--
theorem `pos_add_limZero` / 定理 `pos_add_limZero`

English:
theorem pos_add_limZero
  given: {f g : CauSeq α abs}
  statement: Pos f -> LimZero g -> Pos (f + g)
  proof: exists_forall_ge_and hF (H _ (half_pos F0))
    ⟨_, half_pos F0, i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := h j ij
      have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1)
      rwa [← sub_eq_add_neg, sub_self_div_two] at this⟩

中文:
定理 pos_add_limZero
  条件: {f g : CauSeq α abs}
  结论: Pos f -> LimZero g -> Pos (f + g)
  证明: exists_forall_ge_and hF (H _ (half_pos F0))
    ⟨_, half_pos F0, i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := h j ij
      have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1)
      rwa [← sub_eq_add_neg, sub_self_div_two] at this⟩

Depends on / 依赖: exists_forall_ge_and, half_pos
-/
theorem pos_add_limZero {f g : CauSeq α abs} : Pos f -> LimZero g -> Pos (f + g)
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0))
    ⟨_, half_pos F0, i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := h j ij
      have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1)
      rwa [← sub_eq_add_neg, sub_self_div_two] at this⟩

/--
theorem `mul_pos` / 定理 `mul_pos`

English:
theorem mul_pos
  given: {f g : CauSeq α abs}
  statement: Pos f -> Pos g -> Pos (f * g)
  proof: exists_forall_ge_and hF hG
    ⟨_, mul_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩

中文:
定理 mul_pos
  条件: {f g : CauSeq α abs}
  结论: Pos f -> Pos g -> Pos (f * g)
  证明: exists_forall_ge_and hF hG
    ⟨_, mul_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩
-/
protected theorem mul_pos {f g : CauSeq α abs} : Pos f -> Pos g -> Pos (f * g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, mul_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩

/--
theorem `trichotomy` / 定理 `trichotomy`

English:
theorem trichotomy
  given: (f : CauSeq α abs)
  statement: Pos f ∨ LimZero f ∨ Pos (-f)
  proof: by
  rcases Classical.em (LimZero f) with h | h
  · simp [*]
  simp only [false_or, h]
  rcases abv_pos_of_not_limZero h with ⟨K, K0, hK⟩
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩
  refine (le_total 0 (f i)).imp ?_ ?_ <;>
    refine fun h => ⟨K, K0, i, fun j ij => ?_⟩ <;>
    have

中文:
定理 trichotomy
  条件: (f : CauSeq α abs)
  结论: Pos f ∨ LimZero f ∨ Pos (-f)
  证明: by
  rcases Classical.em (LimZero f) with h | h
  · simp [*]
  simp only [false_or, h]
  rcases abv_pos_of_not_limZero h with ⟨K, K0, hK⟩
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩
  refine (le_total 0 (f i)).imp ?_ ?_ <;>
    refine fun h => ⟨K, K0, i, fun j ij => ?_⟩ <;>
    have

Depends on / 依赖: Classical, Classical.em, LimZero, abs_lt, abs_of_nonneg, abv_pos_of_not_limZero, exists_forall_ge_and, f.cauchy, false_or, le_add_iff_nonneg_right, le_of_lt, le_rfl, le_total, le_trans, neg_le_sub_iff_le_add
-/
theorem trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ Pos (-f) := by
  rcases Classical.em (LimZero f) with h | h
  · simp [*]
  simp only [false_or, h]
  rcases abv_pos_of_not_limZero h with ⟨K, K0, hK⟩
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩
  refine (le_total 0 (f i)).imp ?_ ?_ <;>
    refine fun h => ⟨K, K0, i, fun j ij => ?_⟩ <;>
    have := (hi _ ij).1 <;>
    obtain ⟨h₁, h₂⟩ := hi _ le_rfl
  · rwa [abs_of_nonneg] at this
    rw [abs_of_nonneg h] at h₁
    exact
      (le_add_iff_nonneg_right _).1
        (le_trans h₁ <| neg_le_sub_iff_le_add'.1 <| le_of_lt (abs_lt.1 <| h₂ _ ij).1)
  · rwa [abs_of_nonpos] at this
    rw [abs_of_nonpos h] at h₁
    rw [← sub_le_sub_iff_right]; rw [zero_sub]
    exact le_trans (le_of_lt (abs_lt.1 <| h₂ _ ij).2) h₁

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT (CauSeq α abs)
  body: ⟨fun f g => Pos (g - f)⟩

中文:
实例 :
  签名: LT (CauSeq α abs)
  定义体: ⟨fun f g => Pos (g - f)⟩
-/
instance : LT (CauSeq α abs) :=
  ⟨fun f g => Pos (g - f)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (CauSeq α abs)
  body: ⟨fun f g => f < g ∨ f ≈ g⟩

中文:
实例 :
  签名: LE (CauSeq α abs)
  定义体: ⟨fun f g => f < g ∨ f ≈ g⟩
-/
instance : LE (CauSeq α abs) :=
  ⟨fun f g => f < g ∨ f ≈ g⟩

/--
theorem `lt_of_lt_of_eq` / 定理 `lt_of_lt_of_eq`

English:
theorem lt_of_lt_of_eq
  given: {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h)
  statement: f < h
  proof: show Pos (h - f) by
    convert pos_add_limZero fg (neg_limZero gh)
    simp

中文:
定理 lt_of_lt_of_eq
  条件: {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h)
  结论: f < h
  证明: show Pos (h - f) by
    convert pos_add_limZero fg (neg_limZero gh)
    simp

Depends on / 依赖: convert, neg_limZero, pos_add_limZero
-/
theorem lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h :=
  show Pos (h - f) by
    convert pos_add_limZero fg (neg_limZero gh)
    simp

/--
theorem `lt_of_eq_of_lt` / 定理 `lt_of_eq_of_lt`

English:
theorem lt_of_eq_of_lt
  given: {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h)
  statement: f < h
  proof: by
  have := pos_add_limZero gh (neg_limZero fg)
  rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this

中文:
定理 lt_of_eq_of_lt
  条件: {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h)
  结论: f < h
  证明: by
  have := pos_add_limZero gh (neg_limZero fg)
  rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this

Depends on / 依赖: neg_limZero, pos_add_limZero, sub_eq_add_neg, sub_sub_sub_cancel_right
-/
theorem lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h) : f < h := by
  have := pos_add_limZero gh (neg_limZero fg)
  rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this

/--
theorem `lt_trans` / 定理 `lt_trans`

English:
theorem lt_trans
  given: {f g h : CauSeq α abs} (fg : f < g) (gh : g < h)
  statement: f < h
  proof: show Pos (h - f) by
    convert add_pos fg gh
    simp

中文:
定理 lt_trans
  条件: {f g h : CauSeq α abs} (fg : f < g) (gh : g < h)
  结论: f < h
  证明: show Pos (h - f) by
    convert add_pos fg gh
    simp

Depends on / 依赖: add_pos, convert
-/
theorem lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h :=
  show Pos (h - f) by
    convert add_pos fg gh
    simp

/--
theorem `lt_irrefl` / 定理 `lt_irrefl`

English:
theorem lt_irrefl
  given: {f : CauSeq α abs}
  statement: ¬f < f

中文:
定理 lt_irrefl
  条件: {f : CauSeq α abs}
  结论: ¬f < f
-/
theorem lt_irrefl {f : CauSeq α abs} : ¬f < f
  | h => not_limZero_of_pos h (by simp [zero_limZero])

/--
theorem `le_of_eq_of_le` / 定理 `le_of_eq_of_le`

English:
theorem le_of_eq_of_le
  given: {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g <= h)
  statement: f <= h
  proof: hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoid.trans hfg)

中文:
定理 le_of_eq_of_le
  条件: {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g <= h)
  结论: f <= h
  证明: hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoid.trans hfg)

Depends on / 依赖: CauSeq, CauSeq.lt_of_eq_of_lt, Or.inl, Or.inr, Setoid, Setoid.trans, hgh.elim, lt_of_eq_of_lt
-/
theorem le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g <= h) : f <= h :=
  hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoid.trans hfg)

/--
theorem `le_of_le_of_eq` / 定理 `le_of_le_of_eq`

English:
theorem le_of_le_of_eq
  given: {f g h : CauSeq α abs} (hfg : f <= g) (hgh : g ≈ h)
  statement: f <= h
  proof: hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoid.trans h hgh)

中文:
定理 le_of_le_of_eq
  条件: {f g h : CauSeq α abs} (hfg : f <= g) (hgh : g ≈ h)
  结论: f <= h
  证明: hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoid.trans h hgh)

Depends on / 依赖: CauSeq, CauSeq.lt_of_lt_of_eq, Or.inl, Or.inr, Setoid, Setoid.trans, hfg.elim, lt_of_lt_of_eq
-/
theorem le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f <= g) (hgh : g ≈ h) : f <= h :=
  hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoid.trans h hgh)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (CauSeq α abs)
  body: (· < ·)
  le f g := f < g ∨ f ≈ g
  le_refl _ := Or.inr (Setoid.refl _)
  le_trans _ _ _ fg gh :=
    match fg, gh with
| Or.inl fg, Or.inl gh => Or.inl lt_trans fg gh
| Or.inl fg, Or.inr gh => Or.inl lt_of_lt_of_eq fg gh
| Or.inr fg, Or.inl gh => Or.inl lt_of_eq_of_lt fg gh
| Or.inr fg, Or.inr gh =

中文:
实例 :
  签名: 预序 (CauSeq α abs)
  定义体: (· < ·)
  le f g := f < g ∨ f ≈ g
  le_refl _ := Or.inr (Setoid.refl _)
  le_trans _ _ _ fg gh :=
    match fg, gh with
| Or.inl fg, Or.inl gh => Or.inl lt_trans fg gh
| Or.inl fg, Or.inr gh => Or.inl lt_of_lt_of_eq fg gh
| Or.inr fg, Or.inl gh => Or.inl lt_of_eq_of_lt fg gh
| Or.inr fg, Or.inr gh =
-/
instance : Preorder (CauSeq α abs) where
  lt := (· < ·)
  le f g := f < g ∨ f ≈ g
  le_refl _ := Or.inr (Setoid.refl _)
  le_trans _ _ _ fg gh :=
    match fg, gh with
| Or.inl fg, Or.inl gh => Or.inl lt_trans fg gh
| Or.inl fg, Or.inr gh => Or.inl lt_of_lt_of_eq fg gh
| Or.inr fg, Or.inl gh => Or.inl lt_of_eq_of_lt fg gh
| Or.inr fg, Or.inr gh => Or.inr Setoid.trans fg gh
  lt_iff_le_not_ge _ _ :=
    ⟨fun h => ⟨Or.inl h, not_or_intro (mt (lt_trans h) lt_irrefl) (not_limZero_of_pos h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_right (mt (fun h => Or.inr (Setoid.symm h)) h₂)⟩

/--
theorem `le_antisymm` / 定理 `le_antisymm`

English:
theorem le_antisymm
  given: {f g : CauSeq α abs} (fg : f <= g) (gf : g <= f)
  statement: f ≈ g
  proof: fg.resolve_left (not_lt_of_ge gf)

中文:
定理 le_antisymm
  条件: {f g : CauSeq α abs} (fg : f <= g) (gf : g <= f)
  结论: f ≈ g
  证明: fg.resolve_left (not_lt_of_ge gf)

Depends on / 依赖: fg.resolve_left, not_lt_of_ge, resolve_left
-/
theorem le_antisymm {f g : CauSeq α abs} (fg : f <= g) (gf : g <= f) : f ≈ g :=
  fg.resolve_left (not_lt_of_ge gf)

/--
theorem `lt_total` / 定理 `lt_total`

English:
theorem lt_total
  given: (f g : CauSeq α abs)
  statement: f < g ∨ f ≈ g ∨ g < f
  proof: (trichotomy (g - f)).imp_right fun h =>
    h.imp (fun h => Setoid.symm h) fun h => by rwa [neg_sub] at h

中文:
定理 lt_total
  条件: (f g : CauSeq α abs)
  结论: f < g ∨ f ≈ g ∨ g < f
  证明: (trichotomy (g - f)).imp_right fun h =>
    h.imp (fun h => Setoid.symm h) fun h => by rwa [neg_sub] at h

Depends on / 依赖: Setoid, Setoid.symm, h.imp, imp_right, neg_sub, trichotomy
-/
theorem lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f :=
  (trichotomy (g - f)).imp_right fun h =>
    h.imp (fun h => Setoid.symm h) fun h => by rwa [neg_sub] at h

/--
theorem `le_total` / 定理 `le_total`

English:
theorem le_total
  given: (f g : CauSeq α abs)
  statement: f <= g ∨ g <= f
  proof: (or_assoc.2 (lt_total f g)).imp_right Or.inl

中文:
定理 le_total
  条件: (f g : CauSeq α abs)
  结论: f <= g ∨ g <= f
  证明: (or_assoc.2 (lt_total f g)).imp_right Or.inl

Depends on / 依赖: Or.inl, imp_right, lt_total, or_assoc
-/
theorem le_total (f g : CauSeq α abs) : f <= g ∨ g <= f :=
  (or_assoc.2 (lt_total f g)).imp_right Or.inl

/--
theorem `const_lt` / 定理 `const_lt`

English:
theorem const_lt
  given: {x y : α}
  statement: const x < const y ↔ x < y
  proof: show Pos _ ↔ _ by rw [← const_sub, const_pos, sub_pos]

中文:
定理 const_lt
  条件: {x y : α}
  结论: const x < const y ↔ x < y
  证明: show Pos _ ↔ _ by rw [← const_sub, const_pos, sub_pos]

Depends on / 依赖: const_pos, const_sub, sub_pos
-/
theorem const_lt {x y : α} : const x < const y ↔ x < y :=
  show Pos _ ↔ _ by rw [← const_sub, const_pos, sub_pos]

/--
theorem `const_le` / 定理 `const_le`

English:
theorem const_le
  given: {x y : α}
  statement: const x <= const y ↔ x <= y
  proof: by
  rw [le_iff_lt_or_eq]; exact or_congr const_lt const_equiv

中文:
定理 const_le
  条件: {x y : α}
  结论: const x <= const y ↔ x <= y
  证明: by
  rw [le_iff_lt_or_eq]; exact or_congr const_lt const_equiv

Depends on / 依赖: const_equiv, const_lt, le_iff_lt_or_eq, or_congr
-/
theorem const_le {x y : α} : const x <= const y ↔ x <= y := by
  rw [le_iff_lt_or_eq]; exact or_congr const_lt const_equiv

/--
theorem `le_of_exists` / 定理 `le_of_exists`

English:
theorem le_of_exists
  given: {f g : CauSeq α abs} (h : exists i, forall j >= i, f j <= g j)
  statement: f <= g
  proof: let ⟨i, hi⟩ := h
  (or_assoc.2 (CauSeq.lt_total f g)).elim id fun hgf =>
    False.elim
      (let ⟨_, hK0, j, hKj⟩ := hgf
      not_lt_of_ge (hi (max i j) (le_max_left _ _))
        (sub_pos.1 (lt_of_lt_of_le hK0 (hKj _ (le_max_right _ _)))))

中文:
定理 le_of_存在
  条件: {f g : CauSeq α abs} (h : 存在 i, 对任意 j >= i, f j <= g j)
  结论: f <= g
  证明: let ⟨i, hi⟩ := h
  (or_assoc.2 (CauSeq.lt_total f g)).elim id fun hgf =>
    False.elim
      (let ⟨_, hK0, j, hKj⟩ := hgf
      not_lt_of_ge (hi (max i j) (le_max_left _ _))
        (sub_pos.1 (lt_of_lt_of_le hK0 (hKj _ (le_max_right _ _)))))

Depends on / 依赖: CauSeq, CauSeq.lt_total, False.elim, PosMulMono, PosMulStrictMono, PosMulStrictMono.toPosMulMono, le_max_left, le_max_right, lt_of_lt_of_le, lt_total, not_lt_of_ge, or_assoc, sub_pos, toPosMulMono
-/
theorem le_of_exists {f g : CauSeq α abs} (h : exists i, forall j >= i, f j <= g j) : f <= g :=
  let ⟨i, hi⟩ := h
  (or_assoc.2 (CauSeq.lt_total f g)).elim id fun hgf =>
    False.elim
      (let ⟨_, hK0, j, hKj⟩ := hgf
      not_lt_of_ge (hi (max i j) (le_max_left _ _))
        (sub_pos.1 (lt_of_lt_of_le hK0 (hKj _ (le_max_right _ _)))))

/--
theorem `exists_gt` / 定理 `exists_gt`

English:
theorem exists_gt
  given: (f : CauSeq α abs)
  statement: exists a : α, f < const a
  proof: let ⟨K, H⟩ := f.bounded
  ⟨K + 1, 1, zero_lt_one, 0, fun i _ => by
    rw [sub_apply]; rw [const_apply]; rw [le_sub_iff_add_le']; rw [add_le_add_iff_right]
    exact le_of_lt (abs_lt.1 (H _)).2⟩

中文:
定理 存在_gt
  条件: (f : CauSeq α abs)
  结论: 存在 a : α, f < const a
  证明: let ⟨K, H⟩ := f.bounded
  ⟨K + 1, 1, zero_lt_one, 0, fun i _ => by
    rw [sub_apply]; rw [const_apply]; rw [le_sub_iff_add_le']; rw [add_le_add_iff_right]
    exact le_of_lt (abs_lt.1 (H _)).2⟩

Depends on / 依赖: MulPosMono, MulPosStrictMono, MulPosStrictMono.toMulPosMono, abs_lt, add_le_add_iff_right, bounded, const_apply, f.bounded, le_of_lt, le_sub_iff_add_le, sub_apply, toMulPosMono, zero_lt_one
-/
theorem exists_gt (f : CauSeq α abs) : exists a : α, f < const a :=
  let ⟨K, H⟩ := f.bounded
  ⟨K + 1, 1, zero_lt_one, 0, fun i _ => by
    rw [sub_apply]; rw [const_apply]; rw [le_sub_iff_add_le']; rw [add_le_add_iff_right]
    exact le_of_lt (abs_lt.1 (H _)).2⟩

/--
theorem `exists_lt` / 定理 `exists_lt`

English:
theorem exists_lt
  given: (f : CauSeq α abs)
  statement: exists a : α, const a < f
  proof: let ⟨a, h⟩ := (-f).exists_gt
  ⟨-a, show Pos _ by rwa [const_neg, sub_neg_eq_add, add_comm, ← sub_neg_eq_add]⟩

中文:
定理 存在_lt
  条件: (f : CauSeq α abs)
  结论: 存在 a : α, const a < f
  证明: let ⟨a, h⟩ := (-f).exists_gt
  ⟨-a, show Pos _ by rwa [const_neg, sub_neg_eq_add, add_comm, ← sub_neg_eq_add]⟩

Depends on / 依赖: PosMulReflectLE, PosMulReflectLE.toPosMulReflectLT, add_comm, const_neg, exists_gt, sub_neg_eq_add, toPosMulReflectLT
-/
theorem exists_lt (f : CauSeq α abs) : exists a : α, const a < f :=
  let ⟨a, h⟩ := (-f).exists_gt
  ⟨-a, show Pos _ by rwa [const_neg, sub_neg_eq_add, add_comm, ← sub_neg_eq_add]⟩

-- so named to match `rat_add_continuous_lemma`
/--
theorem `rat_sup_continuous_lemma` / 定理 `rat_sup_continuous_lemma`

English:
theorem rat_sup_continuous_lemma
  given: {ε : α} {a₁ a₂ b₁ b₂ : α}
  proof: fun h₁ h₂ =>
  (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

中文:
定理 rat_sup_continuous_lemma
  条件: {ε : α} {a₁ a₂ b₁ b₂ : α}
  证明: fun h₁ h₂ =>
  (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

Depends on / 依赖: MulPosReflectLE, MulPosReflectLE.toMulPosReflectLT, toMulPosReflectLT
-/
theorem rat_sup_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε -> abs (a₂ - b₂) < ε -> abs (a₁ ⊔ a₂ - b₁ ⊔ b₂) < ε := fun h₁ h₂ =>
  (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

-- so named to match `rat_add_continuous_lemma`
/--
theorem `rat_inf_continuous_lemma` / 定理 `rat_inf_continuous_lemma`

English:
theorem rat_inf_continuous_lemma
  given: {ε : α} {a₁ a₂ b₁ b₂ : α}
  proof: fun h₁ h₂ =>
  (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

中文:
定理 rat_inf_continuous_lemma
  条件: {ε : α} {a₁ a₂ b₁ b₂ : α}
  证明: fun h₁ h₂ =>
  (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)
-/
theorem rat_inf_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε -> abs (a₂ - b₂) < ε -> abs (a₁ ⊓ a₂ - b₁ ⊓ b₂) < ε := fun h₁ h₂ =>
  (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (CauSeq α abs)
  body: ⟨fun f g =>
    ⟨f ⊔ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

中文:
实例 :
  签名: 最大值 (CauSeq α abs)
  定义体: ⟨fun f g =>
    ⟨f ⊔ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

Depends on / 依赖: exists_forall_ge_and, f.cauchy, g.cauchy, le_rfl, rat_sup_continuous_lemma
-/
instance : Max (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (CauSeq α abs)
  body: ⟨fun f g =>
    ⟨f ⊓ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 最小值 (CauSeq α abs)
  定义体: ⟨fun f g =>
    ⟨f ⊓ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

@[simp, norm_cast]

Depends on / 依赖: exists_forall_ge_and, f.cauchy, g.cauchy, le_rfl, rat_inf_continuous_lemma
-/
instance : Min (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (f g : CauSeq α abs)
  statement: ⇑(f ⊔ g) = (f : Nat -> α) ⊔ g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sup
  条件: (f g : CauSeq α abs)
  结论: ⇑(f ⊔ g) = (f : 自然数 -> α) ⊔ g
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sup (f g : CauSeq α abs) : ⇑(f ⊔ g) = (f : Nat -> α) ⊔ g :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (f g : CauSeq α abs)
  statement: ⇑(f ⊓ g) = (f : Nat -> α) ⊓ g
  proof: rfl

中文:
定理 coe_inf
  条件: (f g : CauSeq α abs)
  结论: ⇑(f ⊓ g) = (f : 自然数 -> α) ⊓ g
  证明: rfl
-/
theorem coe_inf (f g : CauSeq α abs) : ⇑(f ⊓ g) = (f : Nat -> α) ⊓ g :=
  rfl

/--
theorem `sup_limZero` / 定理 `sup_limZero`

English:
theorem sup_limZero
  given: {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g)
  statement: LimZero (f ⊔ g)
  proof: H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_sup_iff.mpr (Or.inl H₁.1), sup_lt_iff.mpr ⟨H₁.2, H₂.2⟩⟩

中文:
定理 sup_limZero
  条件: {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g)
  结论: LimZero (f ⊔ g)
  证明: H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_sup_iff.mpr (Or.inl H₁.1), sup_lt_iff.mpr ⟨H₁.2, H₂.2⟩⟩
-/
theorem sup_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊔ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_sup_iff.mpr (Or.inl H₁.1), sup_lt_iff.mpr ⟨H₁.2, H₂.2⟩⟩

/--
theorem `inf_limZero` / 定理 `inf_limZero`

English:
theorem inf_limZero
  given: {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g)
  statement: LimZero (f ⊓ g)
  proof: H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_inf_iff.mpr ⟨H₁.1, H₂.1⟩, inf_lt_iff.mpr (Or.inl H₁.2)⟩

中文:
定理 inf_limZero
  条件: {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g)
  结论: LimZero (f ⊓ g)
  证明: H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_inf_iff.mpr ⟨H₁.1, H₂.1⟩, inf_lt_iff.mpr (Or.inl H₁.2)⟩
-/
theorem inf_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊓ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_inf_iff.mpr ⟨H₁.1, H₂.1⟩, inf_lt_iff.mpr (Or.inl H₁.2)⟩

/--
theorem `sup_equiv_sup` / 定理 `sup_equiv_sup`

English:
theorem sup_equiv_sup
  given: {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂)
  proof: by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_max_sub_max_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩

中文:
定理 sup_equiv_sup
  条件: {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂)
  证明: by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_max_sub_max_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩

Depends on / 依赖: abs_max_sub_max_le_max, max_lt, sup_le_iff, sup_le_iff.mp, trans_lt
-/
theorem sup_equiv_sup {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊔ b₁ ≈ a₂ ⊔ b₂ := by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_max_sub_max_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩

/--
theorem `inf_equiv_inf` / 定理 `inf_equiv_inf`

English:
theorem inf_equiv_inf
  given: {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂)
  proof: by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_min_sub_min_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩

中文:
定理 inf_equiv_inf
  条件: {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂)
  证明: by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_min_sub_min_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩

Depends on / 依赖: abs_min_sub_min_le_max, max_lt, sup_le_iff, sup_le_iff.mp, trans_lt
-/
theorem inf_equiv_inf {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊓ b₁ ≈ a₂ ⊓ b₂ := by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_min_sub_min_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩

/--
theorem `sup_lt` / 定理 `sup_lt`

English:
theorem sup_lt
  given: {a b c : CauSeq α abs} (ha : a < c) (hb : b < c)
  statement: a ⊔ b < c
  proof: by
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ha, hb
  refine ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, fun i hi => ?_⟩
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_left _ _ _)

中文:
定理 sup_lt
  条件: {a b c : CauSeq α abs} (ha : a < c) (hb : b < c)
  结论: a ⊔ b < c
  证明: by
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ha, hb
  refine ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, fun i hi => ?_⟩
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_left _ _ _)
-/
protected theorem sup_lt {a b c : CauSeq α abs} (ha : a < c) (hb : b < c) : a ⊔ b < c := by
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ha, hb
  refine ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, fun i hi => ?_⟩
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_left _ _ _)

/--
theorem `lt_inf` / 定理 `lt_inf`

English:
theorem lt_inf
  given: {a b c : CauSeq α abs} (hb : a < b) (hc : a < c)
  statement: a < b ⊓ c
  proof: by
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := hb, hc
  refine ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, fun i hi => ?_⟩
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_right _ _ _)

@[simp]

中文:
定理 lt_inf
  条件: {a b c : CauSeq α abs} (hb : a < b) (hc : a < c)
  结论: a < b ⊓ c
  证明: by
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := hb, hc
  refine ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, fun i hi => ?_⟩
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_right _ _ _)

@[simp]
-/
protected theorem lt_inf {a b c : CauSeq α abs} (hb : a < b) (hc : a < c) : a < b ⊓ c := by
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := hb, hc
  refine ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, fun i hi => ?_⟩
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_right _ _ _)

@[simp]
/--
theorem `sup_idem` / 定理 `sup_idem`

English:
theorem sup_idem
  given: (a : CauSeq α abs)
  statement: a ⊔ a = a
  proof: Subtype.ext (sup_idem _)

@[simp]

中文:
定理 sup_idem
  条件: (a : CauSeq α abs)
  结论: a ⊔ a = a
  证明: Subtype.ext (sup_idem _)

@[simp]
-/
protected theorem sup_idem (a : CauSeq α abs) : a ⊔ a = a := Subtype.ext (sup_idem _)

@[simp]
/--
theorem `inf_idem` / 定理 `inf_idem`

English:
theorem inf_idem
  given: (a : CauSeq α abs)
  statement: a ⊓ a = a
  proof: Subtype.ext (inf_idem _)

中文:
定理 inf_idem
  条件: (a : CauSeq α abs)
  结论: a ⊓ a = a
  证明: Subtype.ext (inf_idem _)
-/
protected theorem inf_idem (a : CauSeq α abs) : a ⊓ a = a := Subtype.ext (inf_idem _)

/--
theorem `sup_comm` / 定理 `sup_comm`

English:
theorem sup_comm
  given: (a b : CauSeq α abs)
  statement: a ⊔ b = b ⊔ a
  proof: Subtype.ext (sup_comm _ _)

中文:
定理 sup_comm
  条件: (a b : CauSeq α abs)
  结论: a ⊔ b = b ⊔ a
  证明: Subtype.ext (sup_comm _ _)
-/
protected theorem sup_comm (a b : CauSeq α abs) : a ⊔ b = b ⊔ a := Subtype.ext (sup_comm _ _)

/--
theorem `inf_comm` / 定理 `inf_comm`

English:
theorem inf_comm
  given: (a b : CauSeq α abs)
  statement: a ⊓ b = b ⊓ a
  proof: Subtype.ext (inf_comm _ _)

中文:
定理 inf_comm
  条件: (a b : CauSeq α abs)
  结论: a ⊓ b = b ⊓ a
  证明: Subtype.ext (inf_comm _ _)
-/
protected theorem inf_comm (a b : CauSeq α abs) : a ⊓ b = b ⊓ a := Subtype.ext (inf_comm _ _)

/--
theorem `sup_eq_right` / 定理 `sup_eq_right`

English:
theorem sup_eq_right
  given: {a b : CauSeq α abs} (h : a <= b)
  statement: a ⊔ b ≈ b
  proof: by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← max_sub_sub_right]
    rwa [sub_self, max_eq_right, abs_zero]
    rw [sub_nonpos]; rw [← sub_nonneg]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (sup_equiv_sup h (Setoid.refl _)) ?_

中文:
定理 sup_eq_right
  条件: {a b : CauSeq α abs} (h : a <= b)
  结论: a ⊔ b ≈ b
  证明: by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← max_sub_sub_right]
    rwa [sub_self, max_eq_right, abs_zero]
    rw [sub_nonpos]; rw [← sub_nonneg]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (sup_equiv_sup h (Setoid.refl _)) ?_
-/
protected theorem sup_eq_right {a b : CauSeq α abs} (h : a <= b) : a ⊔ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← max_sub_sub_right]
    rwa [sub_self, max_eq_right, abs_zero]
    rw [sub_nonpos]; rw [← sub_nonneg]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (sup_equiv_sup h (Setoid.refl _)) ?_
    rw [CauSeq.sup_idem]

/--
theorem `inf_eq_right` / 定理 `inf_eq_right`

English:
theorem inf_eq_right
  given: {a b : CauSeq α abs} (h : b <= a)
  statement: a ⊓ b ≈ b
  proof: by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← min_sub_sub_right]
    rwa [sub_self, min_eq_right, abs_zero]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (inf_equiv_inf (Setoid.symm h) (Setoid.refl _)) ?_
    rw [CauSeq.inf_idem]

中文:
定理 inf_eq_right
  条件: {a b : CauSeq α abs} (h : b <= a)
  结论: a ⊓ b ≈ b
  证明: by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← min_sub_sub_right]
    rwa [sub_self, min_eq_right, abs_zero]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (inf_equiv_inf (Setoid.symm h) (Setoid.refl _)) ?_
    rw [CauSeq.inf_idem]
-/
protected theorem inf_eq_right {a b : CauSeq α abs} (h : b <= a) : a ⊓ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← min_sub_sub_right]
    rwa [sub_self, min_eq_right, abs_zero]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (inf_equiv_inf (Setoid.symm h) (Setoid.refl _)) ?_
    rw [CauSeq.inf_idem]

/--
theorem `sup_eq_left` / 定理 `sup_eq_left`

English:
theorem sup_eq_left
  given: {a b : CauSeq α abs} (h : b <= a)
  statement: a ⊔ b ≈ a
  proof: by
  simpa only [CauSeq.sup_comm] using CauSeq.sup_eq_right h

中文:
定理 sup_eq_left
  条件: {a b : CauSeq α abs} (h : b <= a)
  结论: a ⊔ b ≈ a
  证明: by
  simpa only [CauSeq.sup_comm] using CauSeq.sup_eq_right h
-/
protected theorem sup_eq_left {a b : CauSeq α abs} (h : b <= a) : a ⊔ b ≈ a := by
  simpa only [CauSeq.sup_comm] using CauSeq.sup_eq_right h

/--
theorem `inf_eq_left` / 定理 `inf_eq_left`

English:
theorem inf_eq_left
  given: {a b : CauSeq α abs} (h : a <= b)
  statement: a ⊓ b ≈ a
  proof: by
  simpa only [CauSeq.inf_comm] using CauSeq.inf_eq_right h

中文:
定理 inf_eq_left
  条件: {a b : CauSeq α abs} (h : a <= b)
  结论: a ⊓ b ≈ a
  证明: by
  simpa only [CauSeq.inf_comm] using CauSeq.inf_eq_right h
-/
protected theorem inf_eq_left {a b : CauSeq α abs} (h : a <= b) : a ⊓ b ≈ a := by
  simpa only [CauSeq.inf_comm] using CauSeq.inf_eq_right h

/--
theorem `le_sup_left` / 定理 `le_sup_left`

English:
theorem le_sup_left
  given: {a b : CauSeq α abs}
  statement: a <= a ⊔ b
  proof: le_of_exists ⟨0, fun _ _ => le_sup_left⟩

中文:
定理 le_sup_left
  条件: {a b : CauSeq α abs}
  结论: a <= a ⊔ b
  证明: le_of_exists ⟨0, fun _ _ => le_sup_left⟩
-/
protected theorem le_sup_left {a b : CauSeq α abs} : a <= a ⊔ b :=
  le_of_exists ⟨0, fun _ _ => le_sup_left⟩

/--
theorem `inf_le_left` / 定理 `inf_le_left`

English:
theorem inf_le_left
  given: {a b : CauSeq α abs}
  statement: a ⊓ b <= a
  proof: le_of_exists ⟨0, fun _ _ => inf_le_left⟩

中文:
定理 inf_le_left
  条件: {a b : CauSeq α abs}
  结论: a ⊓ b <= a
  证明: le_of_exists ⟨0, fun _ _ => inf_le_left⟩
-/
protected theorem inf_le_left {a b : CauSeq α abs} : a ⊓ b <= a :=
  le_of_exists ⟨0, fun _ _ => inf_le_left⟩

/--
theorem `le_sup_right` / 定理 `le_sup_right`

English:
theorem le_sup_right
  given: {a b : CauSeq α abs}
  statement: b <= a ⊔ b
  proof: le_of_exists ⟨0, fun _ _ => le_sup_right⟩

中文:
定理 le_sup_right
  条件: {a b : CauSeq α abs}
  结论: b <= a ⊔ b
  证明: le_of_exists ⟨0, fun _ _ => le_sup_right⟩
-/
protected theorem le_sup_right {a b : CauSeq α abs} : b <= a ⊔ b :=
  le_of_exists ⟨0, fun _ _ => le_sup_right⟩

/--
theorem `inf_le_right` / 定理 `inf_le_right`

English:
theorem inf_le_right
  given: {a b : CauSeq α abs}
  statement: a ⊓ b <= b
  proof: le_of_exists ⟨0, fun _ _ => inf_le_right⟩

中文:
定理 inf_le_right
  条件: {a b : CauSeq α abs}
  结论: a ⊓ b <= b
  证明: le_of_exists ⟨0, fun _ _ => inf_le_right⟩
-/
protected theorem inf_le_right {a b : CauSeq α abs} : a ⊓ b <= b :=
  le_of_exists ⟨0, fun _ _ => inf_le_right⟩

/--
theorem `sup_le` / 定理 `sup_le`

English:
theorem sup_le
  given: {a b c : CauSeq α abs} (ha : a <= c) (hb : b <= c)
  statement: a ⊔ b <= c
  proof: by
  obtain ha | ha := ha
  · obtain hb | hb := hb
    · exact Or.inl (CauSeq.sup_lt ha hb)
    · replace ha := le_of_le_of_eq ha.le (Setoid.symm hb)
      refine le_of_le_of_eq (Or.inr ?_) hb
      exact CauSeq.sup_eq_right ha
  · replace hb := le_of_le_of_eq hb (Setoid.symm ha)
    refine le_of_le

中文:
定理 sup_le
  条件: {a b c : CauSeq α abs} (ha : a <= c) (hb : b <= c)
  结论: a ⊔ b <= c
  证明: by
  obtain ha | ha := ha
  · obtain hb | hb := hb
    · exact Or.inl (CauSeq.sup_lt ha hb)
    · replace ha := le_of_le_of_eq ha.le (Setoid.symm hb)
      refine le_of_le_of_eq (Or.inr ?_) hb
      exact CauSeq.sup_eq_right ha
  · replace hb := le_of_le_of_eq hb (Setoid.symm ha)
    refine le_of_le
-/
protected theorem sup_le {a b c : CauSeq α abs} (ha : a <= c) (hb : b <= c) : a ⊔ b <= c := by
  obtain ha | ha := ha
  · obtain hb | hb := hb
    · exact Or.inl (CauSeq.sup_lt ha hb)
    · replace ha := le_of_le_of_eq ha.le (Setoid.symm hb)
      refine le_of_le_of_eq (Or.inr ?_) hb
      exact CauSeq.sup_eq_right ha
  · replace hb := le_of_le_of_eq hb (Setoid.symm ha)
    refine le_of_le_of_eq (Or.inr ?_) ha
    exact CauSeq.sup_eq_left hb

/--
theorem `le_inf` / 定理 `le_inf`

English:
theorem le_inf
  given: {a b c : CauSeq α abs} (hb : a <= b) (hc : a <= c)
  statement: a <= b ⊓ c
  proof: by
  obtain hb | hb := hb
  · obtain hc | hc := hc
    · exact Or.inl (CauSeq.lt_inf hb hc)
    · replace hb := le_of_eq_of_le (Setoid.symm hc) hb.le
      refine le_of_eq_of_le hc (Or.inr ?_)
      exact Setoid.symm (CauSeq.inf_eq_right hb)
  · replace hc := le_of_eq_of_le (Setoid.symm hb) hc
    r

中文:
定理 le_inf
  条件: {a b c : CauSeq α abs} (hb : a <= b) (hc : a <= c)
  结论: a <= b ⊓ c
  证明: by
  obtain hb | hb := hb
  · obtain hc | hc := hc
    · exact Or.inl (CauSeq.lt_inf hb hc)
    · replace hb := le_of_eq_of_le (Setoid.symm hc) hb.le
      refine le_of_eq_of_le hc (Or.inr ?_)
      exact Setoid.symm (CauSeq.inf_eq_right hb)
  · replace hc := le_of_eq_of_le (Setoid.symm hb) hc
    r
-/
protected theorem le_inf {a b c : CauSeq α abs} (hb : a <= b) (hc : a <= c) : a <= b ⊓ c := by
  obtain hb | hb := hb
  · obtain hc | hc := hc
    · exact Or.inl (CauSeq.lt_inf hb hc)
    · replace hb := le_of_eq_of_le (Setoid.symm hc) hb.le
      refine le_of_eq_of_le hc (Or.inr ?_)
      exact Setoid.symm (CauSeq.inf_eq_right hb)
  · replace hc := le_of_eq_of_le (Setoid.symm hb) hc
    refine le_of_eq_of_le hb (Or.inr ?_)
    exact Setoid.symm (CauSeq.inf_eq_left hc)



/--
theorem `sup_inf_distrib_left` / 定理 `sup_inf_distrib_left`

English:
theorem sup_inf_distrib_left
  given: (a b c : CauSeq α abs)
  statement: a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
  proof: ext fun _ => max_min_distrib_left _ _ _

中文:
定理 sup_inf_distrib_left
  条件: (a b c : CauSeq α abs)
  结论: a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
  证明: ext fun _ => max_min_distrib_left _ _ _
-/
protected theorem sup_inf_distrib_left (a b c : CauSeq α abs) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  ext fun _ => max_min_distrib_left _ _ _

/--
theorem `sup_inf_distrib_right` / 定理 `sup_inf_distrib_right`

English:
theorem sup_inf_distrib_right
  given: (a b c : CauSeq α abs)
  statement: a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
  proof: ext fun _ => max_min_distrib_right _ _ _

中文:
定理 sup_inf_distrib_right
  条件: (a b c : CauSeq α abs)
  结论: a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
  证明: ext fun _ => max_min_distrib_right _ _ _
-/
protected theorem sup_inf_distrib_right (a b c : CauSeq α abs) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
  ext fun _ => max_min_distrib_right _ _ _

end Abs

end CauSeq
