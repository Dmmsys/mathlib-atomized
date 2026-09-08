/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Ineq

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Linear independence

This file collects consequences of linear (in)dependence and includes specialized tests for
specific families of vectors, requiring more theory to state.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `linearIndependent_option`, `linearIndependent_finCons`,
  `linearIndependent_finSucc`, `linearIndependent_finSnoc`: type-specific tests for linear
  independence of families of vector fields;
* `linearIndependent_insert`, `linearIndependent_pair`: linear independence tests for set operations

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that, when working over a division ring,
any family of vectors includes a linear independent subfamily spanning the same subspace.

## TODO

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

@[expose] public section


assert_not_exists Cardinal

noncomputable section

open Function Module Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι → M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)

variable {R v}

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` is injective. -/
/-
**Fintype.linearIndependent_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.linearIndependent_iff'ₛ [Fintype ι] [DecidableEq ι] : LinearIndepe
ndent R v ↔ Injective (LinearMap.lsum R (fun _ => R) Nat fun i => LinearMap.id.s
mulRight (v i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A finite family of vectors `v i` is linear independent iff the linear map that s
ends
`c : ι → R` to `∑ i, c i • v i` is injective.
-/
theorem Fintype.linearIndependent_iff'ₛ [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      Injective (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) := by
  simp [Fintype.linearIndependent_iffₛ, Injective, funext_iff]
/-
**LinearIndependent.pair_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.pair_iff : LinearIndependent R ![x, y] ↔ forall (s t : R
), s • x + t • y = 0 -> s = 0 ∧ t = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndepOn_univ_iff`：linearIndepOn_univ_iff : LinearIndepOn R v univ 
↔ LinearIndependent R v
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用引理 `LinearIndepOn.pair_iff`：LinearIndepOn.pair_iff {i j : ι} (f : ι -> M) (h
ij : i != j) : LinearIndepOn R f {i,j} ↔ forall c d : R, c • f i + d • f j = 0 -
> c = 0 ∧ d …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma LinearIndependent.pair_iffₛ {x y : M} :
    LinearIndependent R ![x, y] ↔
      ∀ (s t s' t' : R), s • x + t • y = s' • x + t' • y → s = s' ∧ t = t' := by
  simp [Fintype.linearIndependent_iffₛ, Fin.forall_fin_two, ← FinVec.forall_iff]; rfl
/-
**LinearIndependent.eq_of_pair** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.eq_of_pair {x y : M} (h : LinearIndependent R ![x, y]) {
s t s' t' : R} (h' : s • x + t • y = s' • x + t' • y) : s = s' ∧ t = t'
参数：h : LinearIndependent R ![x, y]；h' : s • x + t • y = s' • x + t' • y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearIndependent.pair_iffₛ`：LinearIndependent.pair_iffₛ {x y : M} : Lin
earIndependent R ![x, y] ↔ forall (s t s' t' : R), s • x + t • y = s' • x + t' •
 y -> s = s' ∧ t …
-/
lemma LinearIndependent.eq_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t s' t' : R} (h' : s • x + t • y = s' • x + t' • y) : s = s' ∧ t = t' :=
  pair_iffₛ.mp h _ _ _ _ h'
/-
**LinearIndependent.eq_zero_of_pair'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.eq_zero_of_pair' {x y : M} (h : LinearIndependent R ![x,
 y]) {s t : R} (h' : s • x = t • y) : s = 0 ∧ t = 0
参数：h : LinearIndependent R ![x, y]；h' : s • x = t • y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndependent.eq_of_pair`：LinearIndependent.eq_of_pair {x y : M} (h 
: LinearIndependent R ![x, y]) {s t s' t' : R} (h' : s • x + t • y = s' • x + t'
 • y) : s = s' ∧ t…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma LinearIndependent.eq_zero_of_pair' {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x = t • y) : s = 0 ∧ t = 0 := by
  suffices H : s = 0 ∧ 0 = t from ⟨H.1, H.2.symm⟩
  exact h.eq_of_pair (by simpa using h')
/-
**LinearIndependent.eq_zero_of_pair** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.eq_zero_of_pair {x y : M} (h : LinearIndependent R ![x, 
y]) {s t : R} (h' : s • x + t • y = 0) : s = 0 ∧ t = 0
参数：h : LinearIndependent R ![x, y]；h' : s • x + t • y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma LinearIndependent.eq_zero_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x + t • y = 0) : s = 0 ∧ t = 0 := by
  replace h := @h (.single 0 s + .single 1 t) 0 ?_
  · exact ⟨by simpa using congr($h 0), by simpa using congr($h 1)⟩
  simpa

section Indexed

/-
**linearIndepOn_iUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_iUnion_of_directed {η : Type*} {s : η -> Set ι} (hs : Direct
ed (· subseteq ·) s) (h : forall i, LinearIndepOn R v (s i)) : LinearIndepOn R v
 (⋃ i, s i)
参数：hs : Directed (· subseteq ·) s；h : forall i, LinearIndepOn R v (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndepOn_of_finite`：linearIndepOn_of_finite (s : Set ι) (H : forall
 t subseteq s, Set.Finite t -> LinearIndepOn R v t) : LinearIndepOn R v s
· 使用定理 `Set.finite_subset_iUnion`：finite_subset_iUnion {s : Set α} (hs : s.Finit
e) {ι} {t : ι -> Set α} (h : s subseteq ⋃ i, t i) : exists I : Set ι, I.Finite ∧
 s subseteq ⋃ …
· 使用定理 `Directed.finset_le`：Directed.finset_le {r : α -> α -> Prop} [IsTrans α r
] {ι} [hι : Nonempty ι] {f : ι -> α} (D : Directed r f) (s : Finset ι) : exists 
z, foral…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `linearIndepOn_empty`：linearIndepOn_empty : LinearIndepOn R v ∅
-/
theorem linearIndepOn_iUnion_of_directed {η : Type*} {s : η → Set ι} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, LinearIndepOn R v (s i)) : LinearIndepOn R v (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · refine linearIndepOn_of_finite (⋃ i, s i) fun t ht ft => ?_
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · refine (linearIndepOn_empty R v).mono (t := iUnion (s ·)) ?_
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩
/-
**linearIndepOn_sUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_sUnion_of_directed {s : Set (Set ι)} (hs : DirectedOn (· sub
seteq ·) s) (h : forall a in s, LinearIndepOn R v a) : LinearIndepOn R v (⋃₀ s)
参数：Set ι；hs : DirectedOn (· subseteq ·) s；h : forall a in s, LinearIndepOn R v a
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `linearIndepOn_iUnion_of_directed`：linearIndepOn_iUnion_of_directed {η : 
Type*} {s : η -> Set ι} (hs : Directed (· subseteq ·) s) (h : forall i, LinearIn
depOn R v (s i)) : Lin…
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
-/
theorem linearIndepOn_sUnion_of_directed {s : Set (Set ι)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, LinearIndepOn R v a) : LinearIndepOn R v (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed hs.directed_val (by simpa using h)
/-
**linearIndepOn_biUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_biUnion_of_directed {η} {s : Set η} {t : η -> Set ι} (hs : D
irectedOn (t ⁻¹'o (· subseteq ·)) s) (h : forall a in s, LinearIndepOn R v (t a)
) : LinearIndepOn R v (⋃ a in s, t a)
参数：hs : DirectedOn (t ⁻¹'o (· subseteq ·)) s；h : forall a in s, LinearIndepOn R 
v (t a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `linearIndepOn_iUnion_of_directed`：linearIndepOn_iUnion_of_directed {η : 
Type*} {s : η -> Set ι} (hs : Directed (· subseteq ·) s) (h : forall i, LinearIn
depOn R v (s i)) : Lin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `directed_comp`：directed_comp {ι} {f : ι -> β} {g : β -> α} : Directed r 
(g ∘ f) ↔ Directed (g ⁻¹'o r) f
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
-/
theorem linearIndepOn_biUnion_of_directed {η} {s : Set η} {t : η → Set ι}
    (hs : DirectedOn (t ⁻¹'o (· ⊆ ·)) s) (h : ∀ a ∈ s, LinearIndepOn R v (t a)) :
    LinearIndepOn R v (⋃ a ∈ s, t a) := by
  rw [biUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)

end Indexed

section repr

variable (ι R M) in
/-
**iSupIndep_range_lsingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_range_lsingle : iSupIndep fun i : ι => LinearMap.range (Finsupp.
lsingle (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_supported`：mem_supported {s : Set α} (p : α ->₀ M) : p in su
pported M R s ↔ ↑p.support subseteq s
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem iSupIndep_range_lsingle :
    iSupIndep fun i : ι ↦ LinearMap.range (Finsupp.lsingle (R := R) (M := M) i) := by
  refine fun i ↦ disjoint_iff_inf_le.mpr ?_
  rintro x ⟨⟨m, rfl⟩, hm⟩
  suffices ⨆ j ≠ i, LinearMap.range (Finsupp.lsingle j) ≤ Finsupp.supported M R {i}ᶜ by
    have := (Finsupp.mem_supported ..).mp (this hm); simp_all
  refine iSup₂_le fun j ne ↦ ?_
  rintro _ ⟨m, rfl⟩
  simp [Finsupp.mem_supported, ne]
/-
**LinearMap.iSupIndep_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.iSupIndep_map (f : M ->ₗ[R] M') (inj : Injective f) {m : ι -> Su
bmodule R M} (ind : iSupIndep m) : iSupIndep fun i => (m i).map f
参数：f : M ->ₗ[R] M'；inj : Injective f；ind : iSupIndep m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem LinearMap.iSupIndep_map (f : M →ₗ[R] M') (inj : Injective f) {m : ι → Submodule R M}
    (ind : iSupIndep m) : iSupIndep fun i ↦ (m i).map f := by
  simp_rw [iSupIndep, disjoint_iff_inf_le] at ind ⊢
  rintro i _ ⟨⟨x, hxi, rfl⟩, hx⟩
  rw [ind i ⟨hxi, _⟩]; · simp
  simp_rw [← Submodule.map_iSup] at hx
  have ⟨y, hy, eq⟩ := hx
  simpa [← inj eq]

variable (hv : LinearIndependent R v)

/-- See also `iSupIndep_iff_linearIndependent_of_ne_zero`. -/
/-
**LinearIndependent.iSupIndep_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.iSupIndep_span_singleton (hv : LinearIndependent R v) : 
iSupIndep fun i => R ∙ v i
参数：hv : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `LinearMap.iSupIndep_map`：LinearMap.iSupIndep_map (f : M ->ₗ[R] M') (inj 
: Injective f) {m : ι -> Submodule R M} (ind : iSupIndep m) : iSupIndep fun i =>
 (m i).map f
· 使用定理 `iSupIndep_range_lsingle`：iSupIndep_range_lsingle : iSupIndep fun i : ι =
> LinearMap.range (Finsupp.lsingle (R

--- 原说明 ---
See also `iSupIndep_iff_linearIndependent_of_ne_zero`.
-/
theorem LinearIndependent.iSupIndep_span_singleton (hv : LinearIndependent R v) :
    iSupIndep fun i => R ∙ v i := by
  convert! LinearMap.iSupIndep_map _ hv (iSupIndep_range_lsingle ι R R)
  ext; simp [mem_span_singleton]

end repr

section union

open LinearMap Finsupp

/-
**linearIndependent_inl_union_inr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_inl_union_inr' {v : ι -> M} {v' : ι' -> M'} (hv : Linear
Independent R v) (hv' : LinearIndependent R v') : LinearIndependent R (Sum.elim 
(inl R M M' ∘ v) (inr R M M' ∘ v'))
参数：hv : LinearIndependent R v；hv' : LinearIndependent R v'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finsupp.sumFinsuppLEquivProdFinsupp_apply`：∀ {M : Type u_2} (R : Type u_
5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]  
 {α : Type u_7} {β : Type u_8} …
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_apply`：∀ {M : Type u_5} [inst : Ad
dMonoid M] {α : Type u_12} {β : Type u_13} (f : α ⊕ β →₀ M),   Finsupp.sumFinsup
pAddEquivProdFinsupp f = (Finsupp…
· 使用定理 `Finsupp.comapDomain_single`：comapDomain_single (f : α -> β) (a : α) (m :
 M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) : comapDomain f (Finsup
p.single (f a) m…
· 使用引理 `Finsupp.comapDomain_single_of_not_mem_range`：comapDomain_single_of_not_m
em_range [Zero M] {f : α -> β} {b : β} (hb : b ∉ Set.range f) (m : M) (hf) : com
apDomain f (single b m) hf = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem linearIndependent_inl_union_inr' {v : ι → M} {v' : ι' → M'}
    (hv : LinearIndependent R v) (hv' : LinearIndependent R v') :
    LinearIndependent R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) := by
  have : linearCombination R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) =
      .prodMap (linearCombination R v) (linearCombination R v') ∘ₗ
      (sumFinsuppLEquivProdFinsupp R).toLinearMap := by ext (_ | _) <;> simp
  rw [LinearIndependent, this]
  simpa [LinearMap.coe_prodMap] using ⟨hv, hv'⟩
/-
**LinearIndependent.inl_union_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.inl_union_inr {s : Set M} {t : Set M'} (hs : LinearIndep
endent R (fun x => x : s -> M)) (ht : LinearIndependent R (fun x => x : t -> M')
) : LinearIndependent R (fun x => x : ↥(inl R M M' '' s union inr R M M' '' t) -
> M × M')
参数：hs : LinearIndependent R (fun x => x : s -> M)；ht : LinearIndependent R (fun 
x => x : t -> M')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_equiv'`：linearIndependent_equiv' (e : ι ≃ ι') {f : ι' 
-> M} {g : ι -> M} (h : f ∘ e = g) : LinearIndependent R g ↔ LinearIndependent R
 f
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `linearIndependent_inl_union_inr'`：linearIndependent_inl_union_inr' {v : 
ι -> M} {v' : ι' -> M'} (hv : LinearIndependent R v) (hv' : LinearIndependent R 
v') : LinearIndependen…
-/
theorem LinearIndependent.inl_union_inr {s : Set M} {t : Set M'}
    (hs : LinearIndependent R (fun x => x : s → M))
    (ht : LinearIndependent R (fun x => x : t → M')) :
    LinearIndependent R (fun x => x : ↥(inl R M M' '' s ∪ inr R M M' '' t) → M × M') := by
  nontriviality R
  let e : s ⊕ t ≃ ↥(inl R M M' '' s ∪ inr R M M' '' t) :=
    .ofBijective (Sum.elim (fun i ↦ ⟨_, .inl ⟨_, i.2, rfl⟩⟩) fun i ↦ ⟨_, .inr ⟨_, i.2, rfl⟩⟩)
      ⟨by rintro (_ | _) (_ | _) eq <;> simp [hs.ne_zero, ht.ne_zero] at eq <;> aesop,
        by rintro ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩ <;> aesop⟩
  refine (linearIndependent_equiv' e ?_).mp (linearIndependent_inl_union_inr' hs ht)
  ext (_ | _) <;> rfl

end union

section Maximal

universe v w

variable (R)

/-- TODO : refactor to use `Maximal`. -/
/-
**exists_maximal_linearIndepOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_maximal_linearIndepOn' (v : ι -> M) : exists s : Set ι, (LinearInde
pOn R v s) ∧ forall t : Set ι, s subseteq t -> (LinearIndepOn R v t) -> s = t
参数：v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndepOn_iffₛ`：linearIndepOn_iffₛ : LinearIndepOn R v s ↔ forall f 
in Finsupp.supported R R s, forall g in Finsupp.supported R R s, Finsupp.linearC
ombinati…
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Finsupp.supported_empty`：supported_empty : supported M R (∅ : Set α) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `DirectedOn.exists_mem_subset_of_finset_subset_biUnion`：DirectedOn.exists
_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι -> Set α} {c : Set ι} 
(hn : c.Nonempty) (hc : DirectedOn (fun i j…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `exists_maximal_of_chains_bounded`：exists_maximal_of_chains_bounded (h : 
forall c, IsChain r c -> exists ub, forall a in c, a ≺ ub) (trans : forall {a b 
c}, a ≺ b -> b ≺ c -> …
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b

--- 原说明 ---
TODO : refactor to use `Maximal`.
-/
theorem exists_maximal_linearIndepOn' (v : ι → M) :
    ∃ s : Set ι, (LinearIndepOn R v s) ∧ ∀ t : Set ι, s ⊆ t → (LinearIndepOn R v t) → s = t := by
  let indep : Set ι → Prop := fun s => LinearIndepOn R v s
  let X := { I : Set ι // indep I }
  let r : X → X → Prop := fun I J => I.1 ⊆ J.1
  have key : ∀ c : Set X, IsChain r c → indep (⋃ (I : X) (_ : I ∈ c), I) := by
    intro c hc
    dsimp [indep]
    rw [linearIndepOn_iffₛ]
    intro f hfsupp g hgsupp hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · rw [show f = 0 by simpa using! hfsupp, show g = 0 by simpa using! hgsupp]
    have : Std.Refl r := ⟨fun _ => Set.Subset.refl _⟩
    classical
    obtain ⟨I, _I_mem, hI⟩ : ∃ I ∈ c, (f.support ∪ g.support : Set ι) ⊆ I :=
      f.support.coe_union _ ▸ hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn <| by
        simpa using! And.intro hfsupp hgsupp
    exact linearIndepOn_iffₛ.mp I.2 f (subset_union_left.trans hI)
      g (subset_union_right.trans hI) hsum
  obtain ⟨⟨I, hli : indep I⟩, hmax : ∀ a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩⟩ :=
    exists_maximal_of_chains_bounded (r := r)
      (fun c hc => ⟨⟨⋃ I ∈ c, (I : Set ι), key c hc⟩, fun I => Set.subset_biUnion_of_mem⟩)
      Set.Subset.trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩

end Maximal

/-
**Submodule.codisjoint_span_image_of_codisjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.codisjoint_span_image_of_codisjoint (hv : Submodule.span R (Set.
range v) = ⊤) {s t : Set ι} (hst : Codisjoint s t) : Codisjoint (Submodule.span 
R (v '' s)) (Submodule.span R (v '' t))
参数：hv : Submodule.span R (Set.range v) = ⊤；hst : Codisjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.span_image_eq_map_linearCombination`：span_image_eq_map_linearCom
bination (s : Set α) : span R (v '' s) = Submodule.map (linearCombination R v) (
supported R R s)
· 使用引理 `Submodule.codisjoint_map`：codisjoint_map [RingHomSurjective τ₁₂] {f : M 
->ₛₗ[τ₁₂] M₂} (hf : Function.Surjective f) {p q : Submodule R M} (hpq : Codisjoi
nt p q) : Codi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用引理 `Finsupp.codisjoint_supported_supported`：codisjoint_supported_supported {
s t : Set α} (h : Codisjoint s t) : Codisjoint (supported M R s) (supported M R 
t)
-/
lemma Submodule.codisjoint_span_image_of_codisjoint (hv : Submodule.span R (Set.range v) = ⊤)
    {s t : Set ι} (hst : Codisjoint s t) :
    Codisjoint (Submodule.span R (v '' s)) (Submodule.span R (v '' t)) := by
  rw [Finsupp.span_image_eq_map_linearCombination, Finsupp.span_image_eq_map_linearCombination]
  refine Submodule.codisjoint_map ?_ (Finsupp.codisjoint_supported_supported hst)
  rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
/-
**LinearIndependent.isCompl_span_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.isCompl_span_image (h₁ : LinearIndependent R v) (h₂ : Su
bmodule.span R (Set.range v) = ⊤) {s t : Set ι} (hst : IsCompl s t) : IsCompl (S
ubmodule.span R (v '' s)) (Submodule.span R (v '' t))
参数：h₁ : LinearIndependent R v；h₂ : Submodule.span R (Set.range v) = ⊤；hst : IsCo
mpl s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.disjoint_span_image`：LinearIndependent.disjoint_span_i
mage (hv : LinearIndependent R v) {s t : Set ι} (hs : Disjoint s t) : Disjoint (
Submodule.span R <| v '' s)…
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用引理 `Submodule.codisjoint_span_image_of_codisjoint`：Submodule.codisjoint_span
_image_of_codisjoint (hv : Submodule.span R (Set.range v) = ⊤) {s t : Set ι} (hs
t : Codisjoint s t) : Codisjoint (S…
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
lemma LinearIndependent.isCompl_span_image (h₁ : LinearIndependent R v)
    (h₂ : Submodule.span R (Set.range v) = ⊤) {s t : Set ι} (hst : IsCompl s t) :
    IsCompl (Submodule.span R (v '' s)) (Submodule.span R (v '' t)) :=
  ⟨h₁.disjoint_span_image hst.1, Submodule.codisjoint_span_image_of_codisjoint h₂ hst.2⟩

end Semiring

section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` has the trivial kernel. -/
/-
**Fintype.linearIndependent_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.linearIndependent_iff'ₛ [Fintype ι] [DecidableEq ι] : LinearIndepe
ndent R v ↔ Injective (LinearMap.lsum R (fun _ => R) Nat fun i => LinearMap.id.s
mulRight (v i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A finite family of vectors `v i` is linear independent iff the linear map that s
ends
`c : ι → R` to `∑ i, c i • v i` has the trivial kernel.
-/
theorem Fintype.linearIndependent_iff' [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      LinearMap.ker (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) = ⊥ := by
  simp [Fintype.linearIndependent_iff, LinearMap.ker_eq_bot', funext_iff]

/-- `linearIndepOn_pair_iff` is a simpler version over fields. -/
/-
**LinearIndepOn.pair_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndepOn.pair_iff {i j : ι} (f : ι -> M) (hij : i != j) : LinearIndep
On R f {i,j} ↔ forall c d : R, c • f i + d • f j = 0 -> c = 0 ∧ d = 0
参数：f : ι -> M；hij : i != j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `linearIndepOn_iff''`：linearIndepOn_iff'' : LinearIndepOn R v s ↔ forall 
(t : Finset ι) (g : ι -> R), (t : Set ι) subseteq s -> (forall i ∉ t, g i = 0) -
> ∑ i in …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.sum_pair`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] {f : ι → M} [inst_1 : DecidableEq ι] {a b : ι},   a ≠ b → ∑ x ∈ {a, b}, f x = 
f a +…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`linearIndepOn_pair_iff` is a simpler version over fields.
-/
lemma LinearIndepOn.pair_iff {i j : ι} (f : ι → M) (hij : i ≠ j) :
    LinearIndepOn R f {i,j} ↔ ∀ c d : R, c • f i + d • f j = 0 → c = 0 ∧ d = 0 := by
  classical
  rw [linearIndepOn_iff'']
  refine ⟨fun h c d hcd ↦ ?_, fun h t g ht hg0 h0 ↦ ?_⟩
  · specialize h {i, j} (Pi.single i c + Pi.single j d)
    simpa +contextual [Finset.sum_pair, Pi.single_apply, hij, hij.symm, hcd] using h
  have ht' : t ⊆ {i, j} := by simpa [← Finset.coe_subset]
  rw [Finset.sum_subset ht', Finset.sum_pair hij] at h0
  · obtain ⟨hi0, hj0⟩ := h _ _ h0
    exact fun k hkt ↦ Or.elim (ht hkt) (fun h ↦ h ▸ hi0) (fun h ↦ h ▸ hj0)
  simp +contextual [hg0]

section Pair

variable {x y : M}

/-- Also see `LinearIndependent.pair_iff'` for a simpler version over fields. -/
/-
**LinearIndependent.pair_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.pair_iff : LinearIndependent R ![x, y] ↔ forall (s t : R
), s • x + t • y = 0 -> s = 0 ∧ t = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndepOn_univ_iff`：linearIndepOn_univ_iff : LinearIndepOn R v univ 
↔ LinearIndependent R v
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用引理 `LinearIndepOn.pair_iff`：LinearIndepOn.pair_iff {i j : ι} (f : ι -> M) (h
ij : i != j) : LinearIndepOn R f {i,j} ↔ forall c d : R, c • f i + d • f j = 0 -
> c = 0 ∧ d …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Also see `LinearIndependent.pair_iff'` for a simpler version over fields.
-/
lemma LinearIndependent.pair_iff :
    LinearIndependent R ![x, y] ↔ ∀ (s t : R), s • x + t • y = 0 → s = 0 ∧ t = 0 := by
  rw [← linearIndepOn_univ_iff, ← Finset.coe_univ, show @Finset.univ (Fin 2) _ = {0,1} from rfl,
    Finset.coe_insert, Finset.coe_singleton, LinearIndepOn.pair_iff _ (by trivial)]
  simp
/-
**LinearIndependent.pair_symm_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.pair_symm_iff : LinearIndependent R ![x, y] ↔ LinearInde
pendent R ![y, x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
lemma LinearIndependent.pair_symm_iff :
    LinearIndependent R ![x, y] ↔ LinearIndependent R ![y, x] := by
  suffices ∀ x y : M, LinearIndependent R ![x, y] → LinearIndependent R ![y, x] by tauto
  simp only [LinearIndependent.pair_iff]
  intro x y h s t
  specialize h t s
  rwa [add_comm, and_comm]
/-
**LinearIndependent.pair_neg_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndepende
nt`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {x y : M},   LinearIndependent R ![-x, y] ↔ LinearI
ndependent R ![x, y]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearIndependent.pair_iff`：LinearIndependent.pair_iff : LinearIndepende
nt R ![x, y] ↔ forall (s t : R), s • x + t • y = 0 -> s = 0 ∧ t = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma LinearIndependent.pair_neg_left_iff :
    LinearIndependent R ![-x, y] ↔ LinearIndependent R ![x, y] := by
  rw [pair_iff, pair_iff]
  refine ⟨fun h s t hst ↦ ?_, fun h s t hst ↦ ?_⟩ <;> simpa using h (-s) t (by simpa using hst)
/-
**LinearIndependent.pair_neg_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndepend
ent`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {x y : M},   LinearIndependent R ![x, -y] ↔ LinearI
ndependent R ![x, y]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearIndependent.pair_symm_iff`：LinearIndependent.pair_symm_iff : Linea
rIndependent R ![x, y] ↔ LinearIndependent R ![y, x]
· 使用定理 `LinearIndependent.pair_neg_left_iff`：∀ {R : Type u_2} {M : Type u_4} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {x y : M},  
 LinearIndependent R ![-x…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma LinearIndependent.pair_neg_right_iff :
    LinearIndependent R ![x, -y] ↔ LinearIndependent R ![x, y] := by
  rw [pair_symm_iff, pair_neg_left_iff, pair_symm_iff]

variable {S : Type*} [CommRing S] [IsDomain S] [Module S R] [Module S M]
  [SMulCommClass S R M] [IsScalarTower S R M] [IsTorsionFree S R]
  (a b c d : S)
/-
**LinearIndependent.pair_smul_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.pair_smul_smul_iff {u v : R} (hu : IsUnit u) (hv : IsUni
t v) : LinearIndependent R ![u • x, v • y] ↔ LinearIndependent R ![x, y]
参数：hu : IsUnit u；hv : IsUnit v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
lemma LinearIndependent.pair_smul_smul_iff {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    LinearIndependent R ![u • x, v • y] ↔ LinearIndependent R ![x, y] := by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst ↦ ?_, fun h s t hst ↦ ?_⟩
  · specialize h (s * hu.unit⁻¹) (t * hv.unit⁻¹)
    simp only [Units.mul_left_eq_zero] at h
    apply h
    simpa [← mul_smul, mul_assoc]
  · specialize h (s * hu.unit) (t * hv.unit)
    simp only [Units.mul_left_eq_zero] at h
    apply h
    simpa [mul_smul]
/-
**LinearIndependent.pair_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.pair_smul_iff {u : S} (hu : u != 0) : LinearIndependent 
R ![u • x, u • y] ↔ LinearIndependent R ![x, y]
参数：hu : u != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma LinearIndependent.pair_smul_iff {u : S} (hu : u ≠ 0) :
    LinearIndependent R ![u • x, u • y] ↔ LinearIndependent R ![x, y] := by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst ↦ ?_, fun h s t hst ↦ ?_⟩
  · exact h s t (by rw [← smul_comm u s, ← smul_comm u t, ← smul_add, hst, smul_zero])
  · specialize h (u • s) (u • t) (by rw [smul_assoc, smul_assoc, smul_comm u s, smul_comm u t, hst])
    exact ⟨(smul_eq_zero_iff_right hu).mp h.1, (smul_eq_zero_iff_right hu).mp h.2⟩
/-
**LinearIndependent.pair_add_smul_add_smul_iff_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma LinearIndependent.pair_add_smul_add_smul_iff_aux (h : a * d ≠ b * c)
    (h' : LinearIndependent R ![x, y]) :
    LinearIndependent R ![a • x + b • y, c • x + d • y] := by
  simp only [LinearIndependent.pair_iff] at h' ⊢
  intro s t hst
  specialize h' (a • s + c • t) (b • s + d • t) (by simp only [← hst, smul_add, add_smul,
    smul_assoc, smul_comm a s, smul_comm c t, smul_comm b s, smul_comm d t]; abel)
  obtain ⟨h₁, h₂⟩ := h'
  constructor
  · suffices (a * d) • s = (b * c) • s by
      by_contra hs; exact h (_root_.smul_left_injective S hs ‹_›)
    calc (a * d) • s
        = d • a • s := by rw [mul_comm, mul_smul]
      _ = -(d • c • t) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, h₁, smul_zero]
      _ = (b * c) • s := ?_
    · rw [mul_comm, mul_smul, neg_eq_iff_add_eq_zero, add_comm, smul_comm d c, ← smul_add, h₂,
        smul_zero]
  · suffices (a * d) • t = (b * c) • t by
      by_contra ht; exact h (_root_.smul_left_injective S ht ‹_›)
    calc (a * d) • t
        = a • d • t := by rw [mul_smul]
      _ = -(a • b • s) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, add_comm, h₂, smul_zero]
      _ = (b * c) • t := ?_
    · rw [mul_smul, neg_eq_iff_add_eq_zero, smul_comm a b, ← smul_add, h₁, smul_zero]
/-
**LinearIndependent.pair_add_smul_add_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Independent`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {x y : M}   {S : Type u_6} [inst_3 : CommRing S] [I
sDomain S] [inst_5 : _root_.Module S R] [inst_6 : _root_.Module S M]   [SMulComm
Class S R M] [IsScalarTower S R M] [Module.IsTorsionFree S R] (a b c d : S) [Non
trivial R],   LinearIndependent R ![a • x + b • y, c • x + d • y] ↔ LinearIndepe
ndent R ![x, y] ∧ a * d ≠ b * c
参数：a b c d : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearIndependent.pair_iff`：LinearIndependent.pair_iff : LinearIndepende
nt R ![x, y] ↔ forall (s t : R), s • x + t • y = 0 -> s = 0 ∧ t = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.neg_eq_eval`：neg_eq_eval [AddCommGroup M] [Semi
ring S] [Module S M] [Ring R] [Module R M] {l : NF R M} {l₀ : NF S M} (hl : l.ev
al = l₀.eval) {x : M} (h :…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.zero_eq_eval`：zero_eq_eval [AddMonoid M] : (0:M
) = NF.eval (R
（共 100 条，此处仅展示前 30 条）
-/
@[simp] lemma LinearIndependent.pair_add_smul_add_smul_iff [Nontrivial R] :
    LinearIndependent R ![a • x + b • y, c • x + d • y] ↔
      LinearIndependent R ![x, y] ∧ a * d ≠ b * c := by
  rcases eq_or_ne (a * d) (b * c) with h | h
  · suffices ¬ LinearIndependent R ![a • x + b • y, c • x + d • y] by simpa [h]
    rw [pair_iff]
    push Not
    by_cases hbd : b = 0 ∧ d = 0
    · simp only [hbd.1, hbd.2, zero_smul, add_zero]
      by_cases hac : a = 0 ∧ c = 0; · exact ⟨1, 0, by simp [hac.1, hac.2], by simp⟩
      refine ⟨c • 1, -a • 1, ?_, by aesop⟩
      simp only [smul_assoc, one_smul, neg_smul]
      module
    refine ⟨d • 1, -b • 1, ?_, by contrapose! hbd; simp_all⟩
    simp only [smul_add, smul_assoc, one_smul, smul_smul, mul_comm d, h]
    module
  refine ⟨fun h' ↦ ⟨?_, h⟩, fun ⟨h₁, h₂⟩ ↦ pair_add_smul_add_smul_iff_aux _ _ _ _ h₂ h₁⟩
  suffices LinearIndependent R ![(a * d - b * c) • x, (a * d - b * c) • y] by
    rwa [pair_smul_iff (sub_ne_zero_of_ne h)] at this
  convert! pair_add_smul_add_smul_iff_aux d (-b) (-c) a (by simpa [mul_comm d a]) h' using 1
  ext i; fin_cases i <;> simp <;> module
/-
**LinearIndependent.pair_add_smul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearInd
ependent`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {x y : M}   {S : Type u_6} [inst_3 : CommRing S] [I
sDomain S] [inst_5 : _root_.Module S R] [inst_6 : _root_.Module S M]   [SMulComm
Class S R M] [IsScalarTower S R M] [Module.IsTorsionFree S R] (c : S),   LinearI
ndependent R ![x, c • x + y] ↔ LinearIndependent R ![x, y]
参数：c : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LinearIndependent.pair_add_smul_add_smul_iff`：∀ {R : Type u_2} {M : Type
 u_4} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {x 
y : M}   {S : Type u_6} [inst_3 : …
-/
@[simp] lemma LinearIndependent.pair_add_smul_right_iff :
    LinearIndependent R ![x, c • x + y] ↔ LinearIndependent R ![x, y] := by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim c 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 0 c 1
/-
**LinearIndependent.pair_add_smul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearInde
pendent`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {x y : M}   {S : Type u_6} [inst_3 : CommRing S] [I
sDomain S] [inst_5 : _root_.Module S R] [inst_6 : _root_.Module S M]   [SMulComm
Class S R M] [IsScalarTower S R M] [Module.IsTorsionFree S R] (b : S),   LinearI
ndependent R ![x + b • y, y] ↔ LinearIndependent R ![x, y]
参数：b : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LinearIndependent.pair_add_smul_add_smul_iff`：∀ {R : Type u_2} {M : Type
 u_4} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {x 
y : M}   {S : Type u_6} [inst_3 : …
-/
@[simp] lemma LinearIndependent.pair_add_smul_left_iff :
    LinearIndependent R ![x + b • y, y] ↔ LinearIndependent R ![x, y] := by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim b 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 b 0 1
/-
**LinearIndependent.pair_add_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndepend
ent`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {x y : M},   LinearIndependent R ![x, x + y] ↔ Line
arIndependent R ![x, y]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.LinearAlgebra.LinearIndependent.Lemmas.0.LinearIndepend
ent.pair_add_right_iff._abel_1_2`：∀ {R : Type u_2} {M : Type u_1} [inst : Ring R
] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (x y : M)   (s t : R), 
s • x - t • x …
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
-/
@[simp] lemma LinearIndependent.pair_add_right_iff :
    LinearIndependent R ![x, x + y] ↔ LinearIndependent R ![x, y] := by
  suffices ∀ x y : M, LinearIndependent R ![x, x + y] → LinearIndependent R ![x, y] from
    ⟨this x y, fun h ↦ by simpa using this (-x) (x + y) (by simpa)⟩
  simp only [LinearIndependent.pair_iff]
  intro x y h s t h'
  obtain ⟨h₁, h₂⟩ := h (s - t) t (by rw [sub_smul, smul_add, ← h']; abel)
  rw [h₂, sub_zero] at h₁
  tauto
/-
**LinearIndependent.pair_add_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndepende
nt`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {x y : M},   LinearIndependent R ![x + y, y] ↔ Line
arIndependent R ![x, y]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearIndependent.pair_symm_iff`：LinearIndependent.pair_symm_iff : Linea
rIndependent R ![x, y] ↔ LinearIndependent R ![y, x]
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LinearIndependent.pair_add_right_iff`：∀ {R : Type u_2} {M : Type u_4} [i
nst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {x y : M}, 
  LinearIndependent R ![x,…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma LinearIndependent.pair_add_left_iff :
    LinearIndependent R ![x + y, y] ↔ LinearIndependent R ![x, y] := by
  rw [← pair_symm_iff, add_comm, pair_add_right_iff, pair_symm_iff]

end Pair

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

/-
**linearIndepOn_id_iUnion_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_id_iUnion_finite {f : ι -> Set M} (hl : forall i, LinearInde
pOn R id (f i)) (hd : forall i, forall t : Set ι, t.Finite -> i ∉ t -> Disjoint 
(span R (f i)) (⨆ i in t, span R (f i))) : LinearIndepOn R id (⋃ i, f i)
参数：hl : forall i, LinearIndepOn R id (f i)；hd : forall i, forall t : Set ι, t.Fi
nite -> i ∉ t -> Disjoint (span R (f i)) (⨆ i in t, span R (f i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_eq_iUnion_finset`：iUnion_eq_iUnion_finset (s : ι -> Set α) : 
⋃ i, s i = ⋃ t : Finset ι, ⋃ i in t, s i
· 使用定理 `linearIndepOn_iUnion_of_directed`：linearIndepOn_iUnion_of_directed {η : 
Type*} {s : η -> Set ι} (hs : Directed (· subseteq ·) s) (h : forall i, LinearIn
depOn R v (s i)) : Lin…
· 使用定理 `directed_of_isDirected_le`：directed_of_isDirected_le [LE α] [IsDirectedO
rder α] {f : α -> β} {r : β -> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (
f j)) : Directe…
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Set.iUnion_subset_iUnion_const`：iUnion_subset_iUnion_const {s : Set α} (
h : ι -> ι₂) : ⋃ _ : ι, s subseteq ⋃ _ : ι₂, s
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Finset.set_biUnion_insert`：set_biUnion_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `LinearIndepOn.id_union`：LinearIndepOn.id_union {s t : Set M} (hs : Linea
rIndepOn R id s) (ht : LinearIndepOn R id t) (hdj : Disjoint (span R s) (span R 
t)) : Linear…
· 使用定理 `Submodule.span_iUnion₂`：span_iUnion₂ {ι} {κ : ι -> Sort*} (s : forall i,
 κ i -> Set M) : span R (⋃ (i) (j), s i j) = ⨆ (i) (j), span R (s i j)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem linearIndepOn_id_iUnion_finite {f : ι → Set M} (hl : ∀ i, LinearIndepOn R id (f i))
    (hd : ∀ i, ∀ t : Set ι, t.Finite → i ∉ t → Disjoint (span R (f i)) (⨆ i ∈ t, span R (f i))) :
    LinearIndepOn R id (⋃ i, f i) := by
  classical
  rw [iUnion_eq_iUnion_finset f]
  apply linearIndepOn_iUnion_of_directed
  · apply directed_of_isDirected_le
    exact fun t₁ t₂ ht => iUnion_mono fun i => iUnion_subset_iUnion_const fun h => ht h
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.set_biUnion_insert]
    refine (hl _).id_union ih ?_
    rw [span_iUnion₂]
    exact hd i s s.finite_toSet his
/-
**linearIndependent_iUnion_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iUnion_finite {η : Type*} {ιs : η -> Type*} {f : forall 
j : η, ιs j -> M} (hindep : forall j, LinearIndependent R (f j)) (hd : forall i,
 forall t : Set η, t.Finite -> i ∉ t -> Disjoint (span R (range (f i))) (⨆ i in 
t, span R (range (f i)))) : LinearIndependent R fun ji : Σ j, ιs j => f ji.1 ji.
2
参数：hindep : forall j, LinearIndependent R (f j)；hd : forall i, forall t : Set η,
 t.Finite -> i ∉ t -> Disjoint (span R (range (f i))) (⨆ i in t, span R (range (
f i)))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearIndependent.of_linearIndepOn_id_range`：∀ {R : Type u_2} {M : Type 
u_4} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   {ι : Type u_6} {f : ι → M}, Fu…
· 使用定理 `Sigma.eq`：∀ {α : Type u_7} {β : α → Type u_8} {p₁ p₂ : (a : α) × β a} (h
₁ : p₁.fst = p₂.fst),   Eq.recOn h₁ p₁.snd = p₂.snd → p₁ = p₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `iSup_singleton`：iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton 
b : Set β), f x = f b
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `Set.range_sigma_eq_iUnion_range`：range_sigma_eq_iUnion_range {γ : α -> T
ype*} (f : Sigma γ -> β) : range f = ⋃ a, range fun b => f ⟨a, b⟩
· 使用定理 `linearIndepOn_id_iUnion_finite`：linearIndepOn_id_iUnion_finite {f : ι ->
 Set M} (hl : forall i, LinearIndepOn R id (f i)) (hd : forall i, forall t : Set
 ι, t.Finite -> i ∉ …
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
-/
theorem linearIndependent_iUnion_finite {η : Type*} {ιs : η → Type*} {f : ∀ j : η, ιs j → M}
    (hindep : ∀ j, LinearIndependent R (f j))
    (hd : ∀ i, ∀ t : Set η,
      t.Finite → i ∉ t → Disjoint (span R (range (f i))) (⨆ i ∈ t, span R (range (f i)))) :
    LinearIndependent R fun ji : Σ j, ιs j => f ji.1 ji.2 := by
  nontriviality R
  apply LinearIndependent.of_linearIndepOn_id_range
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    by_cases h_cases : x₁ = y₁
    · subst h_cases
      refine Sigma.eq rfl ?_
      rw [LinearIndependent.injective (hindep _) hxy]
    · have h0 : f x₁ x₂ = 0 := by
        apply
          disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) fun h => h_cases (eq_of_mem_singleton h))
            (f x₁ x₂) (subset_span (mem_range_self _))
        rw [iSup_singleton]
        simp only at hxy
        rw [hxy]
        exact subset_span (mem_range_self y₂)
      exact False.elim ((hindep x₁).ne_zero _ h0)
  rw [range_sigma_eq_iUnion_range]
  apply linearIndepOn_id_iUnion_finite (fun j => (hindep j).linearIndepOn_id) hd

open LinearMap

variable (R) in
/-
**exists_maximal_linearIndepOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_maximal_linearIndepOn (v : ι -> M) : exists s : Set ι, (LinearIndep
On R v s) ∧ forall i ∉ s, exists a : R, a != 0 ∧ a • v i in span R (v '' s)
参数：v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_maximal_linearIndepOn'`：exists_maximal_linearIndepOn' (v : ι -> M
) : exists s : Set ι, (LinearIndepOn R v s) ∧ forall t : Set ι, s subseteq t -> 
(LinearIndepOn R v …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearDepOn_iff`：linearDepOn_iff : ¬LinearIndepOn R v s ↔ exists f : ι -
>₀ R, f in Finsupp.supported R R s ∧ ∑ i in f.support, f i • v i = 0 ∧ f != 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
-/
theorem exists_maximal_linearIndepOn (v : ι → M) :
    ∃ s : Set ι, (LinearIndepOn R v s) ∧ ∀ i ∉ s, ∃ a : R, a ≠ 0 ∧ a • v i ∈ span R (v '' s) := by
  classical
    rcases exists_maximal_linearIndepOn' R v with ⟨I, hIlinind, hImaximal⟩
    use I, hIlinind
    intro i hi
    specialize hImaximal (I ∪ {i}) (by simp)
    set J := I ∪ {i} with hJ
    have memJ : ∀ {x}, x ∈ J ↔ x = i ∨ x ∈ I := by simp [hJ]
    have hiJ : i ∈ J := by simp [J]
    have h := by
      refine mt hImaximal ?_
      · intro h2
        rw [h2] at hi
        exact absurd hiJ hi
    obtain ⟨f, supp_f, sum_f, f_ne⟩ := linearDepOn_iff.mp h
    have hfi : f i ≠ 0 := by
      contrapose hIlinind
      refine linearDepOn_iff.mpr ⟨f, ?_, sum_f, f_ne⟩
      simp only [Finsupp.mem_supported, hJ] at supp_f ⊢
      rintro x hx
      refine (memJ.mp (supp_f hx)).resolve_left ?_
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hx) hIlinind
    use f i, hfi
    have hfi' : i ∈ f.support := Finsupp.mem_support_iff.mpr hfi
    rw [← Finset.insert_erase hfi', Finset.sum_insert (Finset.notMem_erase _ _),
      add_eq_zero_iff_eq_neg] at sum_f
    rw [sum_f]
    refine neg_mem (sum_mem fun c hc => smul_mem _ _ (subset_span ⟨c, ?_, rfl⟩))
    exact (memJ.mp (supp_f (Finset.erase_subset _ _ hc))).resolve_left (Finset.ne_of_mem_erase hc)

@[stacks 0CKM]
/-
**linearIndependent_algHom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndependent_algHom_toLinearMap (K M L) [CommSemiring K] [Semiring M]
 [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] : LinearIndependent L (Al
gHom.toLinearMap : (M ->ₐ[K] L) -> M ->ₗ[K] L)
参数：K M L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `linearIndependent_monoidHom`：linearIndependent_monoidHom (G : Type*) [Mu
lOneClass G] (L : Type*) [CommRing L] [IsDomain L] : LinearIndependent L (M
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
lemma linearIndependent_algHom_toLinearMap
    (K M L) [CommSemiring K] [Semiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] :
    LinearIndependent L (AlgHom.toLinearMap : (M →ₐ[K] L) → M →ₗ[K] L) := by
  apply LinearIndependent.of_comp (LinearMap.ltoFun K M L L)
  exact (linearIndependent_monoidHom M L).comp
    (RingHom.toMonoidHom ∘ AlgHom.toRingHom)
    (fun _ _ e ↦ AlgHom.ext (DFunLike.congr_fun e :))
/-
**linearIndependent_algHom_toLinearMap'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndependent_algHom_toLinearMap' (K M L) [CommRing K] [IsDomain K] [S
emiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] [IsTorsionFree 
K L] : LinearIndependent K (AlgHom.toLinearMap : (M ->ₐ[K] L) -> M ->ₗ[K] L)
参数：K M L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `linearIndependent_algHom_toLinearMap`：linearIndependent_algHom_toLinearM
ap (K M L) [CommSemiring K] [Semiring M] [Algebra K M] [CommRing L] [IsDomain L]
 [Algebra K L] : LinearInd…
-/
lemma linearIndependent_algHom_toLinearMap' (K M L) [CommRing K] [IsDomain K]
    [Semiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] [IsTorsionFree K L] :
    LinearIndependent K (AlgHom.toLinearMap : (M →ₐ[K] L) → M →ₗ[K] L) :=
  (linearIndependent_algHom_toLinearMap K M L).restrict_scalars' K

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.injective_of_linearIndependent** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.injective_of_linearIndependent {N : Type*} [AddCommGroup N] [Mod
ule R N] {f : M ->ₗ[R] N} {ι : Type*} {v : ι -> M} (hv : Submodule.span R (.rang
e v) = ⊤) (hli : LinearIndependent R (f ∘ v)) : Function.Injective f
参数：hv : Submodule.span R (.range v) = ⊤；hli : LinearIndependent R (f ∘ v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_span_range_iff_exists_finsupp`：mem_span_range_iff_exists_fin
supp {v : α -> M} {x : M} : x in span R (range v) ↔ exists c : α ->₀ R, (c.sum f
un i a => a • v i) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
lemma LinearMap.injective_of_linearIndependent {N : Type*} [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} {ι : Type*} {v : ι → M}
    (hv : Submodule.span R (.range v) = ⊤) (hli : LinearIndependent R (f ∘ v)) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  have : x ∈ Submodule.span R (.range v) := by rw [hv]; exact mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [map_finsuppSum, map_smul] at hx
  obtain rfl := linearIndependent_iff.mp hli c hx
  simp
/-
**LinearMap.bijective_of_linearIndependent_of_span_eq_top** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：LinearMap.bijective_of_linearIndependent_of_span_eq_top {N : Type*} [AddCo
mmGroup N] [Module R N] {f : M ->ₗ[R] N} {ι : Type*} {v : ι -> M} (hv : Submodul
e.span R (Set.range v) = ⊤) (hli : LinearIndependent R (f ∘ v)) (hsp : Submodule
.span R (Set.range <| f ∘ v) = ⊤) : Function.Bijective f
参数：hv : Submodule.span R (Set.range v) = ⊤；hli : LinearIndependent R (f ∘ v)；hsp
 : Submodule.span R (Set.range <| f ∘ v) = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.injective_of_linearIndependent`：LinearMap.injective_of_linearI
ndependent {N : Type*} [AddCommGroup N] [Module R N] {f : M ->ₗ[R] N} {ι : Type*
} {v : ι -> M} (hv : Submodule…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
lemma LinearMap.bijective_of_linearIndependent_of_span_eq_top {N : Type*} [AddCommGroup N]
    [Module R N] {f : M →ₗ[R] N} {ι : Type*} {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤)
    (hli : LinearIndependent R (f ∘ v)) (hsp : Submodule.span R (Set.range <| f ∘ v) = ⊤) :
    Function.Bijective f := by
  refine ⟨LinearMap.injective_of_linearIndependent hv hli, ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top] at hsp
  rwa [← range_eq_top]

/-- Version of `LinearIndepOn.insert` that works when the scalars are not a field. -/
/-
**LinearIndepOn.insert'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndepOn.insert' {s : Set ι} {i : ι} (hs : LinearIndepOn R v s) (hx :
 forall r : R, r • v i in Submodule.span R (v '' s) -> r = 0) : LinearIndepOn R 
v (insert i s)
参数：hs : LinearIndepOn R v s；hx : forall r : R, r • v i in Submodule.span R (v ''
 s) -> r = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `LinearIndepOn.union`：LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn
 R v s) (ht : LinearIndepOn R v t) (hdj : Disjoint (span R (v '' s)) (span R (v 
'' t))) :…
· 使用引理 `LinearIndepOn.singleton'`：LinearIndepOn.singleton' (hi : forall r : R, r
 • v i = 0 -> r = 0) : LinearIndepOn R v {i}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Version of `LinearIndepOn.insert` that works when the scalars are not a field.
-/
lemma LinearIndepOn.insert' {s : Set ι} {i : ι} (hs : LinearIndepOn R v s)
    (hx : ∀ r : R, r • v i ∈ Submodule.span R (v '' s) → r = 0) :
    LinearIndepOn R v (insert i s) := by
  rw [← Set.union_singleton]
  refine hs.union (.singleton' fun r hr ↦ hx _ <| by simp [hr]) ?_
  simp +contextual [disjoint_span_singleton'', hx]

/-- Version of `LinearIndepOn.id_insert` that works when the scalars are not a field. -/
/-
**LinearIndepOn.id_insert'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndepOn.id_insert' {s : Set M} {x : M} (hs : LinearIndepOn R id s) (
hx : forall r : R, r • x in Submodule.span R s -> r = 0) : LinearIndepOn R id (i
nsert x s)
参数：hs : LinearIndepOn R id s；hx : forall r : R, r • x in Submodule.span R s -> r
 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndepOn.insert'`：LinearIndepOn.insert' {s : Set ι} {i : ι} (hs : L
inearIndepOn R v s) (hx : forall r : R, r • v i in Submodule.span R (v '' s) -> 
r = 0) : Li…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s

--- 原说明 ---
Version of `LinearIndepOn.id_insert` that works when the scalars are not a field
.
-/
lemma LinearIndepOn.id_insert' {s : Set M} {x : M} (hs : LinearIndepOn R id s)
    (hx : ∀ r : R, r • x ∈ Submodule.span R s → r = 0) : LinearIndepOn R id (insert x s) :=
  hs.insert' <| by simpa

/-- If `v : ι → M` is a family of vectors and there exists a family of linear forms
`f : ι → Dual R M` such that `f i (v j)` is `1` for `i = j` and `0` for `i ≠ j`, then
`v` is linearly independent. -/
/-
**LinearIndependent.of_pairwise_dual_eq_zero_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.of_pairwise_dual_eq_zero_one (v : ι -> M) (f : ι -> Dual
 R M) (h1 : Pairwise fun i j => f i (v j) = 0) (h2 : forall i, (f i) (v i) = 1) 
: LinearIndependent R v
参数：v : ι -> M；f : ι -> Dual R M；h1 : Pairwise fun i j => f i (v j) = 0；h2 : fora
ll i, (f i) (v i) = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `v : ι → M` is a family of vectors and there exists a family of linear forms
`f : ι → Dual R M` such that `f i (v j)` is `1` for `i = j` and `0` for `i ≠ j`,
 then
`v` is linearly independent.
-/
theorem LinearIndependent.of_pairwise_dual_eq_zero_one (v : ι → M) (f : ι → Dual R M)
    (h1 : Pairwise fun i j ↦ f i (v j) = 0)
    (h2 : ∀ i, (f i) (v i) = 1) :
    LinearIndependent R v := by
  refine linearIndependent_iff'.mpr fun s g hrel i hi ↦ ?_
  have aux (j : ι) (hjs : j ∈ s) (hji : j ≠ i) : g j * (f i) (v j) = 0 := by simp [h1 hji.symm]
  simpa [s.sum_eq_single i aux (by lia), h2 i] using congr_arg (f i) hrel

end Module

open Finsupp in
/-- A linearly independent family of vectors `f` remains linearly independent when we substitute one
of the terms with a vector `m` provided there exists a non-zero divisor `r`, such that `r • m`
belongs to the span of `f` with non-zero-divisor coefficients. -/
/-
**LinearIndependent.update** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.update [DecidableEq ι] [CommRing R] [AddCommGroup M] [Mo
dule R M] {f : ι -> M} (hf : LinearIndependent R f) (i : ι) (m : M) (hg : exists
 r in nonZeroDivisors R, exists l : ι ->₀ R, l i in nonZeroDivisors R ∧ r • m = 
linearCombination R f l) : LinearIndependent R (Function.update f i m)
参数：hf : LinearIndependent R f；i : ι；m : M；hg : exists r in nonZeroDivisors R, ex
ists l : ι ->₀ R, l i in nonZeroDivisors R ∧ r • m = linearCombination R f l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finsupp.linearCombination_single_index`：linearCombination_single_index (
c : M) (a : α) (f : α ->₀ R) [DecidableEq α] : linearCombination R (Pi.single a 
c) f = f a • c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.bilinearCombination_apply`：bilinearCombination_apply : bilinearC
ombination R S v = linearCombination R v
· 使用定理 `Pi.update_eq_sub_add_single`：∀ {I : Type u} {f : I → Type v} (i : I) [in
st : DecidableEq I] [inst_1 : (i : I) → AddGroup (f i)] (g : (i : I) → f i)   (x
 : f i), Function…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A linearly independent family of vectors `f` remains linearly independent when w
e substitute one
of the terms with a vector `m` provided there exists a non-zero divisor `r`, suc
h that `r • m`
belongs to the span of `f` with non-zero-divisor coefficients.
-/
lemma LinearIndependent.update [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
    {f : ι → M} (hf : LinearIndependent R f) (i : ι) (m : M)
    (hg : ∃ r ∈ nonZeroDivisors R, ∃ l : ι →₀ R,
      l i ∈ nonZeroDivisors R ∧ r • m = linearCombination R f l) :
    LinearIndependent R (Function.update f i m) := by
  rw [linearIndependent_iff] at hf ⊢
  obtain ⟨r, hr, l, hl, hg⟩ := hg
  intros l' hl'
  apply_fun (r • ·) at hl'
  simp_rw [Pi.update_eq_sub_add_single, ← bilinearCombination_apply _ (S := R), map_add, map_sub,
    bilinearCombination_apply, LinearMap.add_apply, LinearMap.sub_apply,
    linearCombination_single_index, smul_add, smul_sub, smul_zero, smul_comm r (l' i) m,
    hg, ← LinearMap.map_smul, smul_smul, ← linearCombination_single, ← map_sub, ← map_add] at hl'
  replace hl' : ∀ j, (r * l' j - (single i (r * l' i)) j) + l' i * l j = 0 :=
    fun j ↦ DFunLike.congr_fun (hf _ hl') j
  grind [mem_nonZeroDivisors_iff]

/-!
### Properties which require `DivisionRing K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι → V} {s t : Set V} {x y : V}

open Submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
(instead of a data containing type class) -/

/-
**mem_span_insert_exchange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_span_insert_exchange : x in span K (insert y s) -> x ∉ span K s -> y i
n span K (insert x s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Module.NF.eq_const_cons`：eq_const_cons [AddCommMonoid M] 
[Semiring R] [Module R M] {r : R} (m : M) {n : M} {l : NF R M} (h1 : 0 = r) (h2 
: n = l.eval) : n = ((r, m) …
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0

--- 原说明 ---
TODO: some of the following proofs can generalized with a zero_ne_one predicate 
type class
(instead of a data containing type class)
-/
theorem mem_span_insert_exchange :
    x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s) := by
  simp only [mem_span_insert, forall_exists_index, and_imp]
  rintro a z hz rfl h
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, ?_⟩
  have a0 : a ≠ 0 := by
    rintro rfl
    simp_all
  match_scalars <;> simp [a0]
/-
**LinearIndepOn.insert** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndepOn`。
形式化陈述：∀ {ι : Type u'} {K : Type u_3} {V : Type u} [inst : DivisionRing K] [inst_
1 : AddCommGroup V]   [inst_2 : _root_.Module K V] {v : ι → V} {s : Set ι} {x : 
ι},   LinearIndepOn K v s → v x ∉ Submodule.span K (v '' s) → LinearIndepOn K v 
(insert x s)
参数：v '' s；insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `LinearIndepOn.union`：LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn
 R v s) (ht : LinearIndepOn R v t) (hdj : Disjoint (span R (v '' s)) (span R (v 
'' t))) :…
· 使用引理 `LinearIndepOn.singleton`：LinearIndepOn.singleton (hi : v i != 0) : Linea
rIndepOn R v {i}
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Submodule.disjoint_span_singleton'`：disjoint_span_singleton' (hx : x != 
0) : Disjoint s (K ∙ x) ↔ x ∉ s
-/
protected theorem LinearIndepOn.insert {s : Set ι} {x : ι} (hs : LinearIndepOn K v s)
    (hx : v x ∉ span K (v '' s)) : LinearIndepOn K v (insert x s) := by
  rw [← union_singleton]
  have x0 : v x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  apply hs.union (LinearIndepOn.singleton x0)
  rwa [image_singleton, disjoint_span_singleton' x0]
/-
**LinearIndepOn.id_insert** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndepOn`。
形式化陈述：∀ {K : Type u_3} {V : Type u} [inst : DivisionRing K] [inst_1 : AddCommGro
up V] [inst_2 : _root_.Module K V] {s : Set V}   {x : V}, LinearIndepOn K id s →
 x ∉ Submodule.span K s → LinearIndepOn K id (insert x s)
参数：insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.insert`：∀ {ι : Type u'} {K : Type u_3} {V : Type u} [inst 
: DivisionRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] {v : 
ι → V} {s …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
protected theorem LinearIndepOn.id_insert (hs : LinearIndepOn K id s) (hx : x ∉ span K s) :
    LinearIndepOn K id (insert x s) :=
  hs.insert ((image_id s).symm ▸ hx)
/-
**linearIndependent_option'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_option' : LinearIndependent K (fun o => Option.casesOn' 
o x v : Option ι -> V) ↔ LinearIndependent K v ∧ x ∉ Submodule.span K (range v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `linearIndependent_sum`：linearIndependent_sum {v : ι oplus ι' -> M} : Lin
earIndependent R v ↔ LinearIndependent R (v ∘ Sum.inl) ∧ LinearIndependent R (v 
∘ Sum.inr) …
· 使用定理 `Set.range_unique`：range_unique [Unique ι] : range f = {f default}
· 使用引理 `linearIndependent_unique_iff`：linearIndependent_unique_iff [Unique ι] : 
LinearIndependent R v ↔ v default != 0
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `Submodule.disjoint_span_singleton`：disjoint_span_singleton : Disjoint s 
(K ∙ x) ↔ x in s -> x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem linearIndependent_option' :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  -- Porting note: Explicit universe level is required in `Equiv.optionEquivSumPUnit`.
  rw [← linearIndependent_equiv (Equiv.optionEquivSumPUnit.{u'} ι).symm, linearIndependent_sum,
    @range_unique _ PUnit, @linearIndependent_unique_iff PUnit, disjoint_span_singleton]
  dsimp [(· ∘ ·)]
  refine ⟨fun h => ⟨h.1, fun hx => h.2.1 <| h.2.2 hx⟩, fun h => ⟨h.1, ?_, fun hx => (h.2 hx).elim⟩⟩
  rintro rfl
  exact h.2 (zero_mem _)
/-
**LinearIndependent.option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.option (hv : LinearIndependent K v) (hx : x ∉ Submodule.
span K (range v)) : LinearIndependent K (fun o => Option.casesOn' o x v : Option
 ι -> V)
参数：hv : LinearIndependent K v；hx : x ∉ Submodule.span K (range v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
· 使用定理 `linearIndependent_option'`：linearIndependent_option' : LinearIndependent
 K (fun o => Option.casesOn' o x v : Option ι -> V) ↔ LinearIndependent K v ∧ x 
∉ Submodule.spa…
-/
theorem LinearIndependent.option (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) :=
  linearIndependent_option'.2 ⟨hv, hx⟩
/-
**linearIndependent_option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_option {v : Option ι -> V} : LinearIndependent K v ↔ Lin
earIndependent K (v ∘ (↑) : ι -> V) ∧ v none ∉ Submodule.span K (range (v ∘ (↑) 
: ι -> V))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.casesOn'_none_coe`：∀ {α : Type u_1} {β : Type u_2} (f : Option α 
→ β) (o : Option α), o.casesOn' (f none) (f ∘ fun a => some a) = f o
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem linearIndependent_option {v : Option ι → V} : LinearIndependent K v ↔
    LinearIndependent K (v ∘ (↑) : ι → V) ∧
      v none ∉ Submodule.span K (range (v ∘ (↑) : ι → V)) := by
  simp only [← linearIndependent_option', Option.casesOn'_none_coe]
/-
**linearIndepOn_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_insert {s : Set ι} {a : ι} {f : ι -> V} (has : a ∉ s) : Line
arIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉ Submodule.span K (f '' 
s)
参数：has : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `linearIndependent_option`：linearIndependent_option {v : Option ι -> V} :
 LinearIndependent K v ↔ LinearIndependent K (v ∘ (↑) : ι -> V) ∧ v none ∉ Submo
dule.span K (r…
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem linearIndepOn_insert {s : Set ι} {a : ι} {f : ι → V} (has : a ∉ s) :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉ Submodule.span K (f '' s) := by
  classical
  rw [LinearIndepOn, LinearIndepOn, ← linearIndependent_equiv
    ((Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm), linearIndependent_option]
  simp only [comp_def]
  rw [range_comp']
  simp
/-
**linearIndepOn_id_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_id_insert (hxs : x ∉ s) : LinearIndepOn K id (insert x s) ↔ 
LinearIndepOn K id s ∧ x ∉ Submodule.span K s
参数：hxs : x ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndepOn_insert`：linearIndepOn_insert {s : Set ι} {a : ι} {f : ι ->
 V} (has : a ∉ s) : LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉
 Submodule…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem linearIndepOn_id_insert (hxs : x ∉ s) :
    LinearIndepOn K id (insert x s) ↔ LinearIndepOn K id s ∧ x ∉ Submodule.span K s :=
  (linearIndepOn_insert (f := id) hxs).trans <| by simp
/-
**linearIndepOn_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_insert_iff {s : Set ι} {a : ι} {f : ι -> V} : LinearIndepOn 
K f (insert a s) ↔ LinearIndepOn K f s ∧ (f a in span K (f '' s) -> a in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `linearIndepOn_insert`：linearIndepOn_insert {s : Set ι} {a : ι} {f : ι ->
 V} (has : a ∉ s) : LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉
 Submodule…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem linearIndepOn_insert_iff {s : Set ι} {a : ι} {f : ι → V} :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ (f a ∈ span K (f '' s) → a ∈ s) := by
  by_cases has : a ∈ s
  · simp [insert_eq_of_mem has, has]
  simp [linearIndepOn_insert has, has]
/-
**linearIndepOn_id_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_id_insert_iff {a : V} {s : Set V} : LinearIndepOn K id (inse
rt a s) ↔ LinearIndepOn K id s ∧ (a in span K s -> a in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `linearIndepOn_insert_iff`：linearIndepOn_insert_iff {s : Set ι} {a : ι} {
f : ι -> V} : LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ (f a in spa
n K (f '' s) -…
-/
theorem linearIndepOn_id_insert_iff {a : V} {s : Set V} :
    LinearIndepOn K id (insert a s) ↔ LinearIndepOn K id s ∧ (a ∈ span K s → a ∈ s) := by
  simpa using linearIndepOn_insert_iff (a := a) (f := id)
/-
**LinearIndepOn.mem_span_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.mem_span_iff {s : Set ι} {a : ι} {f : ι -> V} (h : LinearInd
epOn K f s) : f a in Submodule.span K (f '' s) ↔ (LinearIndepOn K f (insert a s)
 -> a in s)
参数：h : LinearIndepOn K f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem LinearIndepOn.mem_span_iff {s : Set ι} {a : ι} {f : ι → V} (h : LinearIndepOn K f s) :
    f a ∈ Submodule.span K (f '' s) ↔ (LinearIndepOn K f (insert a s) → a ∈ s) := by
  by_cases has : a ∈ s
  · exact iff_of_true (subset_span <| mem_image_of_mem f has) fun _ ↦ has
  simp [linearIndepOn_insert_iff, h, has]

/-- A shortcut to a convenient form for the negation in `LinearIndepOn.mem_span_iff`. -/
/-
**LinearIndepOn.notMem_span_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.notMem_span_iff {s : Set ι} {a : ι} {f : ι -> V} (h : Linear
IndepOn K f s) : f a ∉ Submodule.span K (f '' s) ↔ LinearIndepOn K f (insert a s
) ∧ a ∉ s
参数：h : LinearIndepOn K f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndepOn.mem_span_iff`：LinearIndepOn.mem_span_iff {s : Set ι} {a : 
ι} {f : ι -> V} (h : LinearIndepOn K f s) : f a in Submodule.span K (f '' s) ↔ (
LinearIndepOn K …
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A shortcut to a convenient form for the negation in `LinearIndepOn.mem_span_iff`
.
-/
theorem LinearIndepOn.notMem_span_iff {s : Set ι} {a : ι} {f : ι → V} (h : LinearIndepOn K f s) :
    f a ∉ Submodule.span K (f '' s) ↔ LinearIndepOn K f (insert a s) ∧ a ∉ s := by
  rw [h.mem_span_iff, Classical.not_imp]
/-
**LinearIndepOn.mem_span_iff_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.mem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K id 
s) : a in Submodule.span K s ↔ (LinearIndepOn K id (insert a s) -> a in s)
参数：h : LinearIndepOn K id s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `LinearIndepOn.mem_span_iff`：LinearIndepOn.mem_span_iff {s : Set ι} {a : 
ι} {f : ι -> V} (h : LinearIndepOn K f s) : f a in Submodule.span K (f '' s) ↔ (
LinearIndepOn K …
-/
theorem LinearIndepOn.mem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K id s) :
    a ∈ Submodule.span K s ↔ (LinearIndepOn K id (insert a s) → a ∈ s) := by
  simpa using h.mem_span_iff (a := a)
/-
**LinearIndepOn.notMem_span_iff_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.notMem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K 
id s) : a ∉ Submodule.span K s ↔ LinearIndepOn K id (insert a s) ∧ a ∉ s
参数：h : LinearIndepOn K id s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndepOn.mem_span_iff_id`：LinearIndepOn.mem_span_iff_id {s : Set V}
 {a : V} (h : LinearIndepOn K id s) : a in Submodule.span K s ↔ (LinearIndepOn K
 id (insert a s) ->…
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem LinearIndepOn.notMem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K id s) :
    a ∉ Submodule.span K s ↔ LinearIndepOn K id (insert a s) ∧ a ∉ s := by
  rw [h.mem_span_iff_id, Classical.not_imp]
/-
**linearIndepOn_id_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_id_pair {x y : V} (hx : x != 0) (hy : forall a : K, a • x !=
 y) : LinearIndepOn K id {x, y}
参数：hx : x != 0；hy : forall a : K, a • x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `LinearIndepOn.id_insert`：∀ {K : Type u_3} {V : Type u} [inst : DivisionR
ing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {s : Set V}   {x :
 V}, LinearIn…
· 使用引理 `LinearIndepOn.singleton`：LinearIndepOn.singleton (hi : v i != 0) : Linea
rIndepOn R v {i}
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem linearIndepOn_id_pair {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, a • x ≠ y) :
    LinearIndepOn K id {x, y} := by
  rw [pair_comm]; exact .id_insert (.singleton hx) <| by simpa [mem_span_singleton]

/-- `LinearIndepOn.pair_iff` is a version that works over arbitrary rings. -/
/-
**linearIndepOn_pair_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_pair_iff {i j : ι} (v : ι -> V) (hij : i != j) (hi : v i != 
0) : LinearIndepOn K v {i, j} ↔ forall (c : K), c • v i != v j
参数：v : ι -> V；hij : i != j；hi : v i != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `linearIndepOn_insert`：linearIndepOn_insert {s : Set ι} {a : ι} {f : ι ->
 V} (has : a ∉ s) : LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉
 Submodule…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
`LinearIndepOn.pair_iff` is a version that works over arbitrary rings.
-/
theorem linearIndepOn_pair_iff {i j : ι} (v : ι → V) (hij : i ≠ j) (hi : v i ≠ 0) :
    LinearIndepOn K v {i, j} ↔ ∀ (c : K), c • v i ≠ v j := by
  rw [pair_comm]
  convert! linearIndepOn_insert (s := { i }) (a := j) hij.symm
  simp [hi, mem_span_singleton]

/-- Also see `LinearIndependent.pair_iff` for the version over arbitrary rings. -/
/-
**LinearIndependent.pair_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.pair_iff' {x y : V} (hx : x != 0) : LinearIndependent K 
![x, y] ↔ forall a : K, a • x != y
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndepOn_univ_iff`：linearIndepOn_univ_iff : LinearIndepOn R v univ 
↔ LinearIndependent R v
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `linearIndepOn_pair_iff`：linearIndepOn_pair_iff {i j : ι} (v : ι -> V) (h
ij : i != j) (hi : v i != 0) : LinearIndepOn K v {i, j} ↔ forall (c : K), c • v 
i != v j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Also see `LinearIndependent.pair_iff` for the version over arbitrary rings.
-/
theorem LinearIndependent.pair_iff' {x y : V} (hx : x ≠ 0) :
    LinearIndependent K ![x, y] ↔ ∀ a : K, a • x ≠ y := by
  rw [← linearIndepOn_univ_iff, ← Finset.coe_univ, show @Finset.univ (Fin 2) _ = {0,1} from rfl,
    Finset.coe_insert, Finset.coe_singleton, linearIndepOn_pair_iff _ (by simp) (by simpa)]
  simp
/-
**linearIndependent_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_finCons {n} {v : Fin n -> V} : LinearIndependent K (Fin.
cons x v : Fin (n + 1) -> V) ↔ LinearIndependent K v ∧ x ∉ Submodule.span K (ran
ge v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `linearIndependent_option`：linearIndependent_option {v : Option ι -> V} :
 LinearIndependent K v ↔ LinearIndependent K (v ∘ (↑) : ι -> V) ∧ v none ∉ Submo
dule.span K (r…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_finCons {n} {v : Fin n → V} :
    LinearIndependent K (Fin.cons x v : Fin (n + 1) → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [← linearIndependent_equiv (finSuccEquiv n).symm, linearIndependent_option]
  rfl

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_cons := linearIndependent_finCons
/-
**linearIndependent_finSnoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_finSnoc {n} {v : Fin n -> V} : LinearIndependent K (Fin.
snoc v x : Fin (n + 1) -> V) ↔ LinearIndependent K v ∧ x ∉ Submodule.span K (ran
ge v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_eq_cons_rotate`：Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n 
-> α) (a : α) : @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α)
 a v (finRota…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `linearIndependent_finCons`：linearIndependent_finCons {n} {v : Fin n -> V
} : LinearIndependent K (Fin.cons x v : Fin (n + 1) -> V) ↔ LinearIndependent K 
v ∧ x ∉ Submodu…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_finSnoc {n} {v : Fin n → V} :
    LinearIndependent K (Fin.snoc v x : Fin (n + 1) → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [Fin.snoc_eq_cons_rotate, ← Function.comp_def, linearIndependent_equiv,
    linearIndependent_finCons]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_snoc := linearIndependent_finSnoc

/-- See `LinearIndependent.finCons'` for an uglier version that works if you
only have a module over a semiring. -/
/-
**LinearIndependent.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.finCons {n} {v : Fin n -> V} (hv : LinearIndependent K v
) (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.cons x v : Fi
n (n + 1) -> V)
参数：hv : LinearIndependent K v；hx : x ∉ Submodule.span K (range v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_finCons`：linearIndependent_finCons {n} {v : Fin n -> V
} : LinearIndependent K (Fin.cons x v : Fin (n + 1) -> V) ↔ LinearIndependent K 
v ∧ x ∉ Submodu…

--- 原说明 ---
See `LinearIndependent.finCons'` for an uglier version that works if you
only have a module over a semiring.
-/
theorem LinearIndependent.finCons {n} {v : Fin n → V} (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.cons x v : Fin (n + 1) → V) :=
  linearIndependent_finCons.2 ⟨hv, hx⟩

@[deprecated (since := "2026-04-07")]
alias LinearIndependent.fin_cons := LinearIndependent.finCons

/-- See `LinearIndependent.finSnoc'` for an uglier version that works if you
only have a module over a semiring, and `LinearIndependent.finSnoc_of_not_mem_span_over` for a
version over a subring of a division ring. -/
/-
**LinearIndependent.finSnoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.finSnoc {n} {v : Fin n -> V} (hv : LinearIndependent K v
) (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.snoc v x : Fi
n (n + 1) -> V)
参数：hv : LinearIndependent K v；hx : x ∉ Submodule.span K (range v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_finSnoc`：linearIndependent_finSnoc {n} {v : Fin n -> V
} : LinearIndependent K (Fin.snoc v x : Fin (n + 1) -> V) ↔ LinearIndependent K 
v ∧ x ∉ Submodu…

--- 原说明 ---
See `LinearIndependent.finSnoc'` for an uglier version that works if you
only have a module over a semiring, and `LinearIndependent.finSnoc_of_not_mem_sp
an_over` for a
version over a subring of a division ring.
-/
lemma LinearIndependent.finSnoc {n} {v : Fin n → V} (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.snoc v x : Fin (n + 1) → V) :=
  linearIndependent_finSnoc.2 ⟨hv, hx⟩

/-- If `v` is `R`-linearly independent and `x` is not in the `K`-span of `range v` (where `K` is a
division ring extending `R` and acting on the same module), then `Fin.snoc v x` is `R`-linearly
independent.

This is useful when proving `ℤ`-linear independence using the fact that an element is outside the
`ℝ`-span, which arises naturally in lattice theory and geometry of numbers. -/
/-
**LinearIndependent.finSnoc_of_not_mem_span_over** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.finSnoc_of_not_mem_span_over {R : Type*} {K : Type*} {M 
: Type*} [CommRing R] [DivisionRing K] [AddCommGroup M] [Algebra R K] [Module K 
M] [Module R M] [IsScalarTower R K M] [FaithfulSMul R K] {n : Nat} {v : Fin n ->
 M} (hv : LinearIndependent R v) {x : M} (hx : x ∉ Submodule.span K (Set.range v
)) : LinearIndependent R (Fin.snoc v x)
参数：hv : LinearIndependent R v；hx : x ∉ Submodule.span K (Set.range v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.finSnoc'`：LinearIndependent.finSnoc' {m : Nat} (v : Fi
n m -> M) (x : M) (hli : LinearIndependent R v) (x_ortho : forall (c : R) (y : M
), y in Submodul…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `FaithfulSMul.algebraMap_eq_zero_iff`：algebraMap_eq_zero_iff {r : R} : al
gebraMap R A r = 0 ↔ r = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `eq_inv_smul_iff₀`：eq_inv_smul_iff₀ (ha : a != 0) {x y : β} : x = a⁻¹ • y
 ↔ a • x = y
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.span_subset_span`：span_subset_span : ↑(span R s) subseteq (spa
n S s : Set M)

--- 原说明 ---
If `v` is `R`-linearly independent and `x` is not in the `K`-span of `range v` (
where `K` is a
division ring extending `R` and acting on the same module), then `Fin.snoc v x` 
is `R`-linearly
independent.

This is useful when proving `ℤ`-linear independence using the fact that an eleme
nt is outside the
`ℝ`-span, which arises naturally in lattice theory and geometry of numbers.
-/
theorem LinearIndependent.finSnoc_of_not_mem_span_over
    {R : Type*} {K : Type*} {M : Type*}
    [CommRing R] [DivisionRing K] [AddCommGroup M]
    [Algebra R K] [Module K M] [Module R M] [IsScalarTower R K M] [FaithfulSMul R K]
    {n : ℕ} {v : Fin n → M} (hv : LinearIndependent R v) {x : M}
    (hx : x ∉ Submodule.span K (Set.range v)) :
    LinearIndependent R (Fin.snoc v x) := by
  apply hv.finSnoc' v x
  intro c y hcy heq
  by_contra hc
  apply hx
  have hc' : algebraMap R K c ≠ 0 := by
    rwa [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← algebraMap_smul K c x] at heq
  rw [(eq_inv_smul_iff₀ hc').mpr (eq_neg_of_add_eq_zero_left heq), smul_neg]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.span_subset_span R K _ hcy))
/-
**linearIndependent_finSucc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_finSucc {n} {v : Fin (n + 1) -> V} : LinearIndependent K
 v ↔ LinearIndependent K (Fin.tail v) ∧ v 0 ∉ Submodule.span K (range <| Fin.tai
l v)
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_finCons`：linearIndependent_finCons {n} {v : Fin n -> V
} : LinearIndependent K (Fin.cons x v : Fin (n + 1) -> V) ↔ LinearIndependent K 
v ∧ x ∉ Submodu…
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_finSucc {n} {v : Fin (n + 1) → V} :
    LinearIndependent K v ↔
      LinearIndependent K (Fin.tail v) ∧ v 0 ∉ Submodule.span K (range <| Fin.tail v) := by
  rw [← linearIndependent_finCons, Fin.cons_self_tail]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_succ := linearIndependent_finSucc
/-
**linearIndependent_finSucc'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_finSucc' {n} {v : Fin (n + 1) -> V} : LinearIndependent 
K v ↔ LinearIndependent K (Fin.init v) ∧ v (Fin.last _) ∉ Submodule.span K (rang
e <| Fin.init v)
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_finSnoc`：linearIndependent_finSnoc {n} {v : Fin n -> V
} : LinearIndependent K (Fin.snoc v x : Fin (n + 1) -> V) ↔ LinearIndependent K 
v ∧ x ∉ Submodu…
· 使用定理 `Fin.snoc_init_self`：snoc_init_self : snoc (init q) (q (last n)) = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_finSucc' {n} {v : Fin (n + 1) → V} : LinearIndependent K v ↔
    LinearIndependent K (Fin.init v) ∧ v (Fin.last _) ∉ Submodule.span K (range <| Fin.init v) := by
  rw [← linearIndependent_finSnoc, Fin.snoc_init_self]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_succ' := linearIndependent_finSucc'

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between `k + 1` vectors of length `n` and `k` vectors of length `n` along with a
vector in the complement of their span.
-/
/-
**equiv_linearIndependent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：equiv_linearIndependent (n : Nat) : { s : Fin (n + 1) -> V // LinearIndepe
ndent K s } ≃ Σ s : { s : Fin n -> V // LinearIndependent K s }, ((Submodule.spa
n K (Set.range (s : Fin n -> V)))ᶜ : Set V) where toFun s
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `k + 1` vectors of length `n` and `k` vectors of length `n` 
along with a
vector in the complement of their span.
-/
def equiv_linearIndependent (n : ℕ) :
    { s : Fin (n + 1) → V // LinearIndependent K s } ≃
      Σ s : { s : Fin n → V // LinearIndependent K s },
        ((Submodule.span K (Set.range (s : Fin n → V)))ᶜ : Set V) where
  toFun s := ⟨⟨Fin.tail s.val, (linearIndependent_finSucc.mp s.property).left⟩,
    ⟨s.val 0, (linearIndependent_finSucc.mp s.property).right⟩⟩
  invFun s := ⟨Fin.cons s.2.val s.1.val,
    linearIndependent_finCons.mpr ⟨s.1.property, s.2.property⟩⟩
  left_inv _ := by simp only [Fin.cons_self_tail, Subtype.coe_eta]
  right_inv := fun ⟨_, _⟩ => by simp only [Fin.cons_zero, Subtype.coe_eta, Sigma.mk.inj_iff,
    Fin.tail_cons, heq_eq_eq, and_self]
/-
**linearIndependent_fin2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_fin2 {f : Fin 2 -> V} : LinearIndependent K f ↔ f 1 != 0
 ∧ forall a : K, a • f 1 != f 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_finSucc`：linearIndependent_finSucc {n} {v : Fin (n + 1
) -> V} : LinearIndependent K v ↔ LinearIndependent K (Fin.tail v) ∧ v 0 ∉ Submo
dule.span K (ra…
· 使用引理 `linearIndependent_unique_iff`：linearIndependent_unique_iff [Unique ι] : 
LinearIndependent R v ↔ v default != 0
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `Set.range_unique`：range_unique [Unique ι] : range f = {f default}
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_zero_eq_one`：∀ {n : ℕ}, Fin.succ 0 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_fin2 {f : Fin 2 → V} :
    LinearIndependent K f ↔ f 1 ≠ 0 ∧ ∀ a : K, a • f 1 ≠ f 0 := by
  rw [linearIndependent_finSucc, linearIndependent_unique_iff, range_unique, mem_span_singleton,
    not_exists, show Fin.tail f default = f 1 by rw [← Fin.succ_zero_eq_one]; rfl]
/-
**exists_linearIndepOn_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndepOn_extension {s t : Set ι} (hs : LinearIndepOn K v s) (h
st : s subseteq t) : exists b subseteq t, s subseteq b ∧ v '' t subseteq span K 
(v '' b) ∧ LinearIndepOn K v b
参数：hs : LinearIndepOn K v s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset_nonempty`：zorn_subset_nonempty (S : Set (Set α)) (H : forall
 c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall 
s in c, s …
· 使用定理 `Set.sUnion_subset`：sUnion_subset {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t' subseteq t) : ⋃₀ S subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `linearIndepOn_sUnion_of_directed`：linearIndepOn_sUnion_of_directed {s : 
Set (Set ι)} (hs : DirectedOn (· subseteq ·) s) (h : forall a in s, LinearIndepO
n R v a) : LinearIndep…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Maximal.mem_of_prop_insert`：Maximal.mem_of_prop_insert (h : Maximal P s)
 (hx : P (insert x s)) : x in s
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `LinearIndepOn.insert`：∀ {ι : Type u'} {K : Type u_3} {V : Type u} [inst 
: DivisionRing K] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module K V] {v : 
ι → V} {s …
-/
theorem exists_linearIndepOn_extension {s t : Set ι} (hs : LinearIndepOn K v s) (hst : s ⊆ t) :
    ∃ b ⊆ t, s ⊆ b ∧ v '' t ⊆ span K (v '' b) ∧ LinearIndepOn K v b := by
  obtain ⟨b, sb, h⟩ := by
    refine zorn_subset_nonempty { b | b ⊆ t ∧ LinearIndepOn K v b} ?_ _ ⟨hst, hs⟩
    · refine fun c hc cc _c0 => ⟨⋃₀ c, ⟨?_, ?_⟩, fun x => ?_⟩
      · exact sUnion_subset fun x xc => (hc xc).1
      · exact linearIndepOn_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2
      · exact subset_sUnion_of_mem
  refine ⟨b, h.prop.1, sb, fun _ ⟨x, hx, hvx⟩ => by_contra fun hn ↦ hn ?_, h.prop.2⟩
  subst hvx
  exact subset_span <| mem_image_of_mem v <| h.mem_of_prop_insert
    ⟨insert_subset hx h.prop.1, h.prop.2.insert hn⟩
/-
**exists_linearIndepOn_id_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndepOn_id_extension (hs : LinearIndepOn K id s) (hst : s sub
seteq t) : exists b subseteq t, s subseteq b ∧ t subseteq span K b ∧ LinearIndep
On K id b
参数：hs : LinearIndepOn K id s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `exists_linearIndepOn_extension`：exists_linearIndepOn_extension {s t : Se
t ι} (hs : LinearIndepOn K v s) (hst : s subseteq t) : exists b subseteq t, s su
bseteq b ∧ v '' t su…
-/
theorem exists_linearIndepOn_id_extension (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    ∃ b ⊆ t, s ⊆ b ∧ t ⊆ span K b ∧ LinearIndepOn K id b := by
  convert! exists_linearIndepOn_extension hs hst <;> simp

variable (K t)
/-
**exists_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndependent : exists b subseteq t, span K b = span K t ∧ Line
arIndependent K ((↑) : b -> V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndepOn_id_extension`：exists_linearIndepOn_id_extension (hs
 : LinearIndepOn K id s) (hst : s subseteq t) : exists b subseteq t, s subseteq 
b ∧ t subseteq span K b…
· 使用定理 `linearIndependent_empty`：linearIndependent_empty : LinearIndependent R (
fun x => x : (∅ : Set M) -> M)
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq_of_le`：span_eq_of_le (h₁ : s subseteq p) (h₂ : p <= sp
an R s) : span R s = p
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
-/
theorem exists_linearIndependent :
    ∃ b ⊆ t, span K b = span K t ∧ LinearIndependent K ((↑) : b → V) := by
  obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
    exists_linearIndepOn_id_extension (linearIndependent_empty K V) (Set.empty_subset t)
  exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩

/-- Indexed version of `exists_linearIndependent`. -/
/-
**exists_linearIndependent'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_linearIndependent' (v : ι -> V) : exists (κ : Type u') (a : κ -> ι)
, Injective a ∧ Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.ran
ge v) ∧ LinearIndependent K (v ∘ a)
参数：v : ι -> V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndependent`：exists_linearIndependent : exists b subseteq t
, span K b = span K t ∧ LinearIndependent K ((↑) : b -> V)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Indexed version of `exists_linearIndependent`.
-/
lemma exists_linearIndependent' (v : ι → V) :
    ∃ (κ : Type u') (a : κ → ι), Injective a ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) ∧
      LinearIndependent K (v ∘ a) := by
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent K (Set.range v)
  choose f hf using ht
  let s : Set ι := Set.range (fun a : t ↦ f a.property)
  have hs {i : ι} (hi : i ∈ s) : v i ∈ t := by obtain ⟨a, rfl⟩ := hi; simp [hf]
  let f' (a : s) : t := ⟨v a.val, hs a.property⟩
  refine ⟨s, Subtype.val, Subtype.val_injective, hsp.symm ▸ by congr; aesop, ?_⟩
  · rw [← show Subtype.val ∘ f' = v ∘ Subtype.val by ext; simp [f']]
    apply hli.comp
    rintro ⟨i, x, rfl⟩ ⟨j, y, rfl⟩ hij
    simp only [Subtype.ext_iff, hf, f'] at hij
    simp [hij]

variable {K} {s t : Set ι}

/-- `LinearIndepOn.extend` adds vectors to a linear independent set `s ⊆ t` until it spans
all elements of `t`. -/
/-
**LinearIndepOn.extend** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIndepOn.extend (hs : LinearIndepOn K v s) (hst : s subseteq t) : Set
 ι
参数：hs : LinearIndepOn K v s；hst : s subseteq t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndepOn_extension`：exists_linearIndepOn_extension {s t : Se
t ι} (hs : LinearIndepOn K v s) (hst : s subseteq t) : exists b subseteq t, s su
bseteq b ∧ v '' t su…

--- 原说明 ---
`LinearIndepOn.extend` adds vectors to a linear independent set `s ⊆ t` until it
 spans
all elements of `t`.
-/
noncomputable def LinearIndepOn.extend (hs : LinearIndepOn K v s) (hst : s ⊆ t) : Set ι :=
  Classical.choose (exists_linearIndepOn_extension hs hst)
/-
**LinearIndepOn.extend_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.extend_subset (hs : LinearIndepOn K v s) (hst : s subseteq t
) : hs.extend hst subseteq t
参数：hs : LinearIndepOn K v s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndepOn_extension`：exists_linearIndepOn_extension {s t : Se
t ι} (hs : LinearIndepOn K v s) (hst : s subseteq t) : exists b subseteq t, s su
bseteq b ∧ v '' t su…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem LinearIndepOn.extend_subset (hs : LinearIndepOn K v s) (hst : s ⊆ t) : hs.extend hst ⊆ t :=
  let ⟨hbt, _hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hbt
/-
**LinearIndepOn.subset_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.subset_extend (hs : LinearIndepOn K v s) (hst : s subseteq t
) : s subseteq hs.extend hst
参数：hs : LinearIndepOn K v s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndepOn_extension`：exists_linearIndepOn_extension {s t : Se
t ι} (hs : LinearIndepOn K v s) (hst : s subseteq t) : exists b subseteq t, s su
bseteq b ∧ v '' t su…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem LinearIndepOn.subset_extend (hs : LinearIndepOn K v s) (hst : s ⊆ t) : s ⊆ hs.extend hst :=
  let ⟨_hbt, hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hsb
/-
**LinearIndepOn.image_subset_span_image_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.image_subset_span_image_extend (hs : LinearIndepOn K v s) (h
st : s subseteq t) : v '' t subseteq span K (v '' hs.extend hst)
参数：hs : LinearIndepOn K v s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndepOn_extension`：exists_linearIndepOn_extension {s t : Se
t ι} (hs : LinearIndepOn K v s) (hst : s subseteq t) : exists b subseteq t, s su
bseteq b ∧ v '' t su…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem LinearIndepOn.image_subset_span_image_extend (hs : LinearIndepOn K v s) (hst : s ⊆ t) :
    v '' t ⊆ span K (v '' hs.extend hst) :=
  let ⟨_hbt, _hsb, htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  htb
/-
**LinearIndepOn.subset_span_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.subset_span_extend {s t : Set V} (hs : LinearIndepOn K id s)
 (hst : s subseteq t) : t subseteq span K (hs.extend hst)
参数：hs : LinearIndepOn K id s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndepOn.image_subset_span_image_extend`：LinearIndepOn.image_subset
_span_image_extend (hs : LinearIndepOn K v s) (hst : s subseteq t) : v '' t subs
eteq span K (v '' hs.extend hst)
-/
theorem LinearIndepOn.subset_span_extend {s t : Set V} (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    t ⊆ span K (hs.extend hst) := by
  convert! hs.image_subset_span_image_extend hst <;> simp
/-
**LinearIndepOn.span_image_extend_eq_span_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.span_image_extend_eq_span_image (hs : LinearIndepOn K v s) (
hst : s subseteq t) : span K (v '' hs.extend hst) = span K (v '' t)
参数：hs : LinearIndepOn K v s；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `LinearIndepOn.extend_subset`：LinearIndepOn.extend_subset (hs : LinearInd
epOn K v s) (hst : s subseteq t) : hs.extend hst subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `LinearIndepOn.image_subset_span_image_extend`：LinearIndepOn.image_subset
_span_image_extend (hs : LinearIndepOn K v s) (hst : s subseteq t) : v '' t subs
eteq span K (v '' hs.extend hst)
-/
theorem LinearIndepOn.span_image_extend_eq_span_image (hs : LinearIndepOn K v s) (hst : s ⊆ t) :
    span K (v '' hs.extend hst) = span K (v '' t) :=
  le_antisymm (span_mono (image_mono (hs.extend_subset hst)))
    (span_le.2 (hs.image_subset_span_image_extend hst))
/-
**LinearIndepOn.span_extend_eq_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.span_extend_eq_span {s t : Set V} (hs : LinearIndepOn K id s
) (hst : s subseteq t) : span K (hs.extend hst) = span K t
参数：hs : LinearIndepOn K id s；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `LinearIndepOn.extend_subset`：LinearIndepOn.extend_subset (hs : LinearInd
epOn K v s) (hst : s subseteq t) : hs.extend hst subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `LinearIndepOn.subset_span_extend`：LinearIndepOn.subset_span_extend {s t 
: Set V} (hs : LinearIndepOn K id s) (hst : s subseteq t) : t subseteq span K (h
s.extend hst)
-/
theorem LinearIndepOn.span_extend_eq_span {s t : Set V} (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    span K (hs.extend hst) = span K t :=
  le_antisymm (span_mono (hs.extend_subset hst)) (span_le.2 (hs.subset_span_extend hst))
/-
**LinearIndepOn.linearIndepOn_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.linearIndepOn_extend (hs : LinearIndepOn K v s) (hst : s sub
seteq t) : LinearIndepOn K v (hs.extend hst)
参数：hs : LinearIndepOn K v s；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndepOn_extension`：exists_linearIndepOn_extension {s t : Se
t ι} (hs : LinearIndepOn K v s) (hst : s subseteq t) : exists b subseteq t, s su
bseteq b ∧ v '' t su…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem LinearIndepOn.linearIndepOn_extend (hs : LinearIndepOn K v s) (hst : s ⊆ t) :
    LinearIndepOn K v (hs.extend hst) :=
  let ⟨_hbt, _hsb, _htb, hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hli

-- TODO(Mario): rewrite?
/-
**exists_of_linearIndepOn_of_finite_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_of_linearIndepOn_of_finite_span {s : Set V} {t : Finset V} (hs : Li
nearIndepOn K id s) (hst : s subseteq (span K ↑t : Submodule K V)) : exists t' :
 Finset V, ↑t' subseteq s union ↑t ∧ s subseteq ↑t' ∧ t'.card = t.card
参数：hs : LinearIndepOn K id s；hst : s subseteq (span K ↑t : Submodule K V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `eq_of_linearIndepOn_id_of_span_subtype`：eq_of_linearIndepOn_id_of_span_s
ubtype [Nontrivial R] {s t : Set M} (hs : LinearIndepOn R id s) (h : t subseteq 
s) (hst : s subseteq span R …
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_empty`：union_empty (s : Finset α) : s union ∅ = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Classical.by_cases`：∀ {p q : Prop}, (p → q) → (¬p → q) → q
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
（共 57 条，此处仅展示前 30 条）
-/
theorem exists_of_linearIndepOn_of_finite_span {s : Set V} {t : Finset V}
    (hs : LinearIndepOn K id s) (hst : s ⊆ (span K ↑t : Submodule K V)) :
    ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card := by
  classical
  have :
    ∀ t : Finset V,
      ∀ s' : Finset V,
        ↑s' ⊆ s →
          s ∩ ↑t = ∅ →
            s ⊆ (span K ↑(s' ∪ t) : Submodule K V) →
              ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
    fun t =>
    Finset.induction_on t
      (fun s' hs' _ hss' =>
        have : s = ↑s' := eq_of_linearIndepOn_id_of_span_subtype hs hs' <| by simpa using hss'
        ⟨s', by simp [this]⟩)
      fun b₁ t hb₁t ih s' hs' hst hss' =>
      have hb₁s : b₁ ∉ s := fun h => by
        have : b₁ ∈ s ∩ ↑(insert b₁ t) := ⟨h, Finset.mem_insert_self _ _⟩
        rwa [hst] at this
      have hb₁s' : b₁ ∉ s' := fun h => hb₁s <| hs' h
      have hst : s ∩ ↑t = ∅ :=
        eq_empty_of_subset_empty <|
          -- Porting note: `-subset_inter_iff` required.
          Subset.trans
            (by simp [inter_subset_inter, -subset_inter_iff])
            (le_of_eq hst)
      Classical.by_cases (p := s ⊆ (span K ↑(s' ∪ t) : Submodule K V))
        (fun this =>
          let ⟨u, hust, hsu, Eq⟩ := ih _ hs' hst this
          have hb₁u : b₁ ∉ u := fun h => (hust h).elim hb₁s hb₁t
          ⟨insert b₁ u, by simp [insert_subset_insert hust], Subset.trans hsu (by simp), by
            simp [Eq, hb₁t, hb₁s', hb₁u]⟩)
        fun this =>
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this
        have hb₂t' : b₂ ∉ s' ∪ t := fun h => hb₂t <| subset_span h
        have : s ⊆ (span K ↑(insert b₂ s' ∪ t) : Submodule K V) := fun b₃ hb₃ => by
          have : ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : Set V) := by
            simp only [insert_eq, union_subset_union, Subset.refl,
              subset_union_right, Finset.union_insert, Finset.coe_insert]
          have hb₃ : b₃ ∈ span K (insert b₁ (insert b₂ ↑(s' ∪ t) : Set V)) :=
            span_mono this (hss' hb₃)
          have : s ⊆ (span K (insert b₁ ↑(s' ∪ t)) : Submodule K V) := by
            simpa [insert_eq, -singleton_union, -union_singleton] using hss'
          have hb₁ : b₁ ∈ span K (insert b₂ ↑(s' ∪ t)) :=
            mem_span_insert_exchange (this hb₂s) hb₂t
          rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset_iff, hb₂s, hs']) hst this
        ⟨u, Subset.trans hust <| union_subset_union (Subset.refl _) (by simp [subset_insert]), hsu,
          by simp [eq, hb₂t', hb₁t, hb₁s']⟩
  have eq : ((t.filter fun x => x ∈ s) ∪ t.filter fun x => x ∉ s) = t := by
    ext1 x
    by_cases x ∈ s <;> simp [*]
  apply
    Exists.elim
      (this (t.filter fun x => x ∉ s) (t.filter fun x => x ∈ s) (by simp [Set.subset_def])
        (by simp +contextual [Set.ext_iff]) (by rwa [eq]))
  intro u h
  exact
    ⟨u, Subset.trans h.1 (by simp +contextual [subset_def, or_imp]),
      h.2.1, by simp only [h.2.2, eq]⟩
/-
**exists_finite_card_le_of_finite_of_linearIndependent_of_span** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：exists_finite_card_le_of_finite_of_linearIndependent_of_span {s t : Set V}
 (ht : t.Finite) (hs : LinearIndepOn K id s) (hst : s subseteq span K t) : exist
s h : s.Finite, h.toFinset.card <= ht.toFinset.card
参数：ht : t.Finite；hs : LinearIndepOn K id s；hst : s subseteq span K t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `exists_of_linearIndepOn_of_finite_span`：exists_of_linearIndepOn_of_finit
e_span {s : Set V} {t : Finset V} (hs : LinearIndepOn K id s) (hst : s subseteq 
(span K ↑t : Submodule K V))…
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem exists_finite_card_le_of_finite_of_linearIndependent_of_span {s t : Set V} (ht : t.Finite)
    (hs : LinearIndepOn K id s) (hst : s ⊆ span K t) :
    ∃ h : s.Finite, h.toFinset.card ≤ ht.toFinset.card :=
  have : s ⊆ (span K ↑ht.toFinset : Submodule K V) := by simpa
  let ⟨u, _hust, hsu, Eq⟩ := exists_of_linearIndepOn_of_finite_span hs this
  have : s.Finite := u.finite_toSet.subset hsu
  ⟨this, by rw [← Eq]; exact Finset.card_le_card <| Finset.coe_subset.mp <| by simp [hsu]⟩

end Module

