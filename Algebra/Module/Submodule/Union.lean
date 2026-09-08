/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Unions of `Submodule`s

This file is a home for results about unions of submodules.

## Main results:
* `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`: a finite union of proper submodules is
  a proper subset, provided the coefficients are a sufficiently large field.

-/

public section

open Function Set

variable {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-
**Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (s : Finset ι) (p : ι
 -> Submodule K M) (h₁ : forall i, p i != ⊤) (h₂ : s.card < ENat.card K) : ⋃ i i
n s, (p i : Set M) ⊂ univ
参数：s : Finset ι；p : ι -> Submodule K M；h₁ : forall i, p i != ⊤；h₂ : s.card < ENa
t.card K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
（共 122 条，此处仅展示前 30 条）
-/
lemma Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (s : Finset ι) (p : ι → Submodule K M)
    (h₁ : ∀ i, p i ≠ ⊤) (h₂ : s.card < ENat.card K) :
    ⋃ i ∈ s, (p i : Set M) ⊂ univ := by
  -- Following https://mathoverflow.net/a/14241
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hj' =>
    simp only [ssubset_univ_iff] at hj' ⊢
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using! h₁ j
    replace h₂ : s.card + 1 < ENat.card K := by simpa [Finset.card_insert_of_notMem hj] using! h₂
    specialize hj' (lt_trans ENat.natCast_lt_succ h₂)
    contrapose hj'
    replace hj' : (p j : Set M) ∪ (⋃ i ∈ s, p i) = univ := by
      simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using! hj'
    suffices (p j : Set M) ⊆ ⋃ i ∈ s, p i by rwa [union_eq_right.mpr this] at hj'
    intro x (hx : x ∈ p j)
    rcases eq_or_ne x 0 with rfl | hx₀
    · simpa using! hs
    obtain ⟨y, hy⟩ : ∃ y, y ∉ p j := by specialize h₁ j; contrapose! h₁; ext; simp [h₁]
    have hy₀ : y ≠ 0 := by aesop
    let sxy := {x + t • y | (t : K) (ht : t ≠ 0)}
    have hsxy : sxy ⊆ ⋃ i ∈ s, p i := by
      suffices Disjoint sxy (p j) from this.subset_right_of_subset_union <| hj' ▸ sxy.subset_univ
      rw [Set.disjoint_iff]
      rintro - ⟨⟨t, ht₀, rfl⟩, ht : x + t • y ∈ p j⟩
      rw [(p j).add_mem_iff_right hx, (p j).smul_mem_iff ht₀] at ht
      contradiction
    obtain ⟨k, hk, t₁, t₂, ht, ht₁, ht₂⟩ : ∃ᵉ (k ∈ s) (t₁ : K) (t₂ : K),
        t₁ ≠ t₂ ∧ x + t₁ • y ∈ p k ∧ x + t₂ • y ∈ p k := by
      suffices ∃ᵉ (k ∈ s) (z₁ ∈ sxy) (z₂ ∈ sxy), z₁ ≠ z₂ ∧ z₁ ∈ p k ∧ z₂ ∈ p k by
        obtain ⟨k, hk, -, ⟨t₁, -, rfl⟩, -, ⟨t₂, -, rfl⟩, htne, ht₁, ht₂⟩ := this
        exact ⟨k, hk, t₁, t₂, by aesop, ht₁, ht₂⟩
      choose f hf using fun z : sxy ↦ mem_iUnion.mp (hsxy z.property)
      have hf' : MapsTo f univ s := fun z _ ↦ by specialize hf z; aesop
      suffices ∃ z₁ z₂, z₁ ≠ z₂ ∧ f z₁ = f z₂ by
        obtain ⟨z₁, z₂, hne, heq⟩ := this
        exact ⟨f z₁, hf' (mem_univ _), z₁, z₁.property, z₂, z₂.property,
          Subtype.coe_ne_coe.mpr hne, by specialize hf z₁; simp_all, by specialize hf z₂; aesop⟩
      have key : s.card < sxy.encard := by
        refine lt_of_add_lt_add_right <| lt_of_lt_of_le h₂ ?_
        have : Injective (fun t : K ↦ x + t • y) :=
          fun t₁ t₂ ht ↦ smul_left_injective K hy₀ <| by simpa using! ht
        have aux : sxy = ((fun t : K ↦ x + t • y) '' {t | t ≠ 0}) := by ext; simp [sxy]
        rw [aux, this.encard_image, encard_ne_add_one]
      obtain ⟨z₁, -, z₂, -, h⟩ := exists_ne_map_eq_of_encard_lt_of_maps_to (by simpa) hf'
      exact ⟨z₁, z₂, h⟩
    replace ht : y ∈ p k := by
      have : (t₁ - t₂) • y ∈ p k := by convert sub_mem ht₁ ht₂; module
      refine ((p k).smul_mem_iff ?_).mp this
      rwa [sub_ne_zero]
    replace ht : x ∈ p k := by convert sub_mem ht₁ ((p k).smul_mem t₁ ht); simp
    simpa using! ⟨k, hk, ht⟩

variable [Finite ι] [Infinite K]
/-
**Submodule.exists_forall_notMem_of_forall_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.exists_forall_notMem_of_forall_ne_top (p : ι -> Submodule K M) (
h : forall i, p i != ⊤) : exists x, forall i, x ∉ p i
参数：p : ι -> Submodule K M；h : forall i, p i != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用引理 `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`：Submodule.iUnion_s
subset_of_forall_ne_top_of_card_lt (s : Finset ι) (p : ι -> Submodule K M) (h₁ :
 forall i, p i != ⊤) (h₂ : s.card < ENat.c…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma Submodule.exists_forall_notMem_of_forall_ne_top (p : ι → Submodule K M) (h : ∀ i, p i ≠ ⊤) :
    ∃ x, ∀ i, x ∉ p i := by
  let _i : Fintype ι := Fintype.ofFinite ι
  suffices ⋃ i, (p i : Set M) ⊂ univ by simpa [ssubset_univ_iff, iUnion_eq_univ_iff] using this
  simpa using iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p h (by simp)
/-
**Module.Dual.exists_forall_ne_zero_of_forall_exists** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：Module.Dual.exists_forall_ne_zero_of_forall_exists (f : ι -> Dual K M) (h 
: forall i, exists x, f i x != 0) : exists x, forall i, f i x != 0
参数：f : ι -> Dual K M；h : forall i, exists x, f i x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `Submodule.exists_forall_notMem_of_forall_ne_top`：Submodule.exists_forall
_notMem_of_forall_ne_top (p : ι -> Submodule K M) (h : forall i, p i != ⊤) : exi
sts x, forall i, x ∉ p i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma Module.Dual.exists_forall_ne_zero_of_forall_exists
    (f : ι → Dual K M) (h : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ x, ∀ i, f i x ≠ 0 := by
  let p i := LinearMap.ker (f i)
  replace h i : p i ≠ ⊤ := by specialize h i; aesop
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p h
  exact ⟨x, by simpa [p] using hx⟩

/-- A convenience variation of `Module.Dual.exists_forall_ne_zero_of_forall_exists` where we are
concerned only about behaviour on a fixed submodule. -/
/-
**Module.Dual.exists_forall_mem_ne_zero_of_forall_exists** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：Module.Dual.exists_forall_mem_ne_zero_of_forall_exists (p : Submodule K M)
 (f : ι -> Dual K M) (h : forall i, exists x in p, f i x != 0) : exists x in p, 
forall i, f i x != 0
参数：p : Submodule K M；f : ι -> Dual K M；h : forall i, exists x in p, f i x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Dual.exists_forall_ne_zero_of_forall_exists`：Module.Dual.exists_f
orall_ne_zero_of_forall_exists (f : ι -> Dual K M) (h : forall i, exists x, f i 
x != 0) : exists x, forall i, f i x != 0

--- 原说明 ---
A convenience variation of `Module.Dual.exists_forall_ne_zero_of_forall_exists` 
where we are
concerned only about behaviour on a fixed submodule.
-/
lemma Module.Dual.exists_forall_mem_ne_zero_of_forall_exists (p : Submodule K M)
    (f : ι → Dual K M) (h : ∀ i, ∃ x ∈ p, f i x ≠ 0) :
    ∃ x ∈ p, ∀ i, f i x ≠ 0 := by
  let f' (i : ι) : Dual K p := (f i).domRestrict p
  replace h (i : ι) : ∃ x : p, f' i x ≠ 0 := by obtain ⟨x, hxp, hx₀⟩ := h i; exact ⟨⟨x, hxp⟩, hx₀⟩
  obtain ⟨⟨x, hxp⟩, hx₀⟩ := exists_forall_ne_zero_of_forall_exists f' h
  exact ⟨x, hxp, hx₀⟩
/-
**Module.exists_dual_forall_apply_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.exists_dual_forall_apply_ne_zero (v : ι -> M) (hv : forall i, v i !
= 0) : exists f : Dual K M, forall i, f (v i) != 0
参数：v : ι -> M；hv : forall i, v i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Dual.exists_forall_ne_zero_of_forall_exists`：Module.Dual.exists_f
orall_ne_zero_of_forall_exists (f : ι -> Dual K M) (h : forall i, exists x, f i 
x != 0) : exists x, forall i, f i x != 0
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma Module.exists_dual_forall_apply_ne_zero (v : ι → M) (hv : ∀ i, v i ≠ 0) :
    ∃ f : Dual K M, ∀ i, f (v i) ≠ 0 := by
  refine Dual.exists_forall_ne_zero_of_forall_exists (fun i ↦ Dual.eval K M (v i)) fun i ↦ ?_
  by_contra! contra
  simp_rw [Dual.eval_apply, forall_dual_apply_eq_zero_iff] at contra
  exact hv i contra
