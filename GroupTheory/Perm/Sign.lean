/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Data.Finset.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Order.Units
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Data.Finset.Sigma

/-!
# Sign of a permutation

The main definition of this file is `Equiv.Perm.sign`,
associating a `ℤˣ` sign with a permutation.

Other lemmas have been moved to `Mathlib/GroupTheory/Perm/Finite.lean`

-/

@[expose] public section

universe u v

open Equiv Function Fintype Finset

variable {α : Type u} [DecidableEq α] {β : Type v}

namespace Equiv.Perm

/-- `modSwap i j` contains permutations up to swapping `i` and `j`.

We use this to partition permutations in `Matrix.det_zero_of_row_eq`, such that each partition
sums up to `0`.
-/
@[instance_reducible]
/-
**Equiv.Perm.modSwap** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：modSwap (i j : α) : Setoid (Perm α)
参数：i j : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`modSwap i j` contains permutations up to swapping `i` and `j`.

We use this to partition permutations in `Matrix.det_zero_of_row_eq`, such that 
each partition
sums up to `0`.
-/
def modSwap (i j : α) : Setoid (Perm α) :=
  ⟨fun σ τ => σ = τ ∨ σ = swap i j * τ, fun σ => Or.inl (refl σ), fun {σ τ} h =>
    Or.casesOn h (fun h => Or.inl h.symm) fun h => Or.inr (by rw [h, swap_mul_self_mul]),
    fun {σ τ υ} hστ hτυ => by
    rcases hστ with hστ | hστ <;> rcases hτυ with hτυ | hτυ <;>
      (try rw [hστ, hτυ, swap_mul_self_mul]) <;>
      simp [hστ, hτυ]⟩
/-
**Equiv.Perm.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {α : Type*} [Fintype α] [DecidableEq α] (i j : α) :
    DecidableRel (modSwap i j).r :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Given a list `l : List α` and a permutation `f : Perm α` such that the nonfixed points of `f`
  are in `l`, recursively factors `f` as a product of transpositions. -/
/-
**Equiv.Perm.swapFactorsAux** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：swapFactorsAux : forall (l : List α) (f : Perm α), (forall {x}, f x != x -
> x in l) -> { l : List (Perm α) // l.prod = f ∧ forall g in l, IsSwap g } | [] 
=> fun f h => ⟨[], Equiv.ext fun x => by rw [List.prod_nil] exact (Classical.not
_not.1 (mt h List.not_mem_nil)).symm, by simp⟩ | x::l => fun f h => if hfx : x =
 f x then swapFactorsAux l f fun {y} hy => List.mem_of_ne_of_mem (fun h : y = x 
=> by simp [h, hfx.symm] at hy) (h hy) else let m
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a list `l : List α` and a permutation `f : Perm α` such that the nonfixed 
points of `f`
  are in `l`, recursively factors `f` as a product of transpositions.
-/
def swapFactorsAux :
    ∀ (l : List α) (f : Perm α),
      (∀ {x}, f x ≠ x → x ∈ l) → { l : List (Perm α) // l.prod = f ∧ ∀ g ∈ l, IsSwap g }
  | [] => fun f h =>
    ⟨[],
      Equiv.ext fun x => by
        rw [List.prod_nil]
        exact (Classical.not_not.1 (mt h List.not_mem_nil)).symm,
      by simp⟩
  | x::l => fun f h =>
    if hfx : x = f x then
      swapFactorsAux l f fun {y} hy =>
        List.mem_of_ne_of_mem (fun h : y = x => by simp [h, hfx.symm] at hy) (h hy)
    else
      let m :=
        swapFactorsAux l (swap x (f x) * f) fun {y} hy =>
          have : f y ≠ y ∧ y ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hy
          List.mem_of_ne_of_mem this.2 (h this.1)
      ⟨swap x (f x)::m.1, by
        rw [List.prod_cons, m.2.1, ← mul_assoc, mul_def (swap x (f x)), swap_swap, ← one_def,
          one_mul],
        fun {_} hg => ((List.mem_cons).1 hg).elim (fun h => ⟨x, f x, hfx, h⟩) (m.2.2 _)⟩

/-- `swapFactors` represents a permutation as a product of a list of transpositions.
The representation is nonunique and depends on the linear order structure.
For types without linear order `truncSwapFactors` can be used. -/
/-
**Equiv.Perm.swapFactors** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：swapFactors [Fintype α] [LinearOrder α] (f : Perm α) : { l : List (Perm α)
 // l.prod = f ∧ forall g in l, IsSwap g }
参数：f : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`swapFactors` represents a permutation as a product of a list of transpositions.
The representation is nonunique and depends on the linear order structure.
For types without linear order `truncSwapFactors` can be used.
-/
def swapFactors [Fintype α] [LinearOrder α] (f : Perm α) :
    { l : List (Perm α) // l.prod = f ∧ ∀ g ∈ l, IsSwap g } :=
  swapFactorsAux ((@univ α _).sort) f fun {_ _} => (mem_sort _).2 (mem_univ _)

/-- This computably represents the fact that any permutation can be represented as the product of
  a list of transpositions. -/
/-
**Equiv.Perm.truncSwapFactors** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：truncSwapFactors [Fintype α] (f : Perm α) : Trunc { l : List (Perm α) // l
.prod = f ∧ forall g in l, IsSwap g }
参数：f : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This computably represents the fact that any permutation can be represented as t
he product of
  a list of transpositions.
-/
def truncSwapFactors [Fintype α] (f : Perm α) :
    Trunc { l : List (Perm α) // l.prod = f ∧ ∀ g ∈ l, IsSwap g } :=
  Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (swapFactorsAux l f (h _)))
    (show ∀ x, f x ≠ x → x ∈ (@univ α _).1 from fun _ _ => mem_univ _)

/-- An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_elim]
/-
**Equiv.Perm.swap_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：swap_induction_on [Finite α] {motive : Perm α -> Prop} (f : Perm α) (one :
 motive 1) (swap_mul : forall f x y, x != y -> motive f -> motive (swap x y * f)
) : motive f
参数：f : Perm α；one : motive 1；swap_mul : forall f x y, x != y -> motive f -> moti
ve (swap x y * f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l

--- 原说明 ---
An induction principle for permutations. If `P` holds for the identity permutati
on, and
is preserved under composition with a non-trivial swap, then `P` holds for all p
ermutations.
-/
theorem swap_induction_on [Finite α] {motive : Perm α → Prop} (f : Perm α)
    (one : motive 1) (swap_mul : ∀ f x y, x ≠ y → motive f → motive (swap x y * f)) : motive f := by
  cases nonempty_fintype α
  obtain ⟨l, hl⟩ := (truncSwapFactors f).out
  induction l generalizing f with
  | nil =>
    simp only [one, hl.left.symm, List.prod_nil]
  | cons g l ih =>
    rcases hl.2 g (by simp) with ⟨x, y, hxy⟩
    rw [← hl.1, List.prod_cons, hxy.2]
    exact swap_mul _ _ _ hxy.1 (ih _ ⟨rfl, fun v hv => hl.2 _ (List.mem_cons_of_mem _ hv)⟩)
/-
**Equiv.Perm.mclosure_isSwap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mclosure_isSwap [Finite α] : Submonoid.closure { σ : Perm α | IsSwap σ } =
 ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l,
 x in s) : l.prod in s
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem mclosure_isSwap [Finite α] : Submonoid.closure { σ : Perm α | IsSwap σ } = ⊤ := by
  cases nonempty_fintype α
  refine top_unique fun x _ ↦ ?_
  obtain ⟨h1, h2⟩ := (truncSwapFactors x).out.prop
  rw [← h1]
  exact Submonoid.list_prod_mem _ fun y hy ↦ Submonoid.subset_closure (h2 y hy)
/-
**Equiv.Perm.closure_isSwap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：closure_isSwap [Finite α] : Subgroup.closure { σ : Perm α | IsSwap σ } = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.closure_eq_top_of_mclosure_eq_top`：closure_eq_top_of_mclosure_e
q_top {S : Set G} (h : Submonoid.closure S = ⊤) : closure S = ⊤
· 使用定理 `Equiv.Perm.mclosure_isSwap`：mclosure_isSwap [Finite α] : Submonoid.closu
re { σ : Perm α | IsSwap σ } = ⊤
-/
theorem closure_isSwap [Finite α] : Subgroup.closure { σ : Perm α | IsSwap σ } = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_isSwap

/-- Every finite symmetric group is generated by transpositions of adjacent elements. -/
/-
**Equiv.Perm.mclosure_swap_castSucc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mclosure_swap_castSucc_succ (n : Nat) : Submonoid.closure (Set.range fun i
 : Fin n => swap i.castSucc i.succ) = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mclosure_isSwap`：mclosure_isSwap [Finite α] : Submonoid.closu
re { σ : Perm α | IsSwap σ } = ⊤
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Equiv.swap_comm`：swap_comm (a b : α) : swap a b = swap b a
· 使用定理 `Equiv.swap_mul_swap_mul_swap`：∀ {α : Type u_4} [inst : DecidableEq α] {x
 y z : α},   x ≠ y → x ≠ z → Equiv.swap y z * Equiv.swap x y * Equiv.swap y z = 
Equiv.swap z x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a

--- 原说明 ---
Every finite symmetric group is generated by transpositions of adjacent elements
.
-/
theorem mclosure_swap_castSucc_succ (n : ℕ) :
    Submonoid.closure (Set.range fun i : Fin n ↦ swap i.castSucc i.succ) = ⊤ := by
  apply top_unique
  rw [← mclosure_isSwap, Submonoid.closure_le]
  rintro _ ⟨i, j, ne, rfl⟩
  wlog lt : i < j generalizing i j
  · rw [swap_comm]; exact this _ _ ne.symm (ne.lt_or_gt.resolve_left lt)
  induction j using Fin.induction with
  | zero => cases lt
  | succ j ih =>
    have mem : swap j.castSucc j.succ ∈ Submonoid.closure
      (Set.range fun (i : Fin n) ↦ swap i.castSucc i.succ) := Submonoid.subset_closure ⟨_, rfl⟩
    obtain rfl | lts := (Fin.le_castSucc_iff.mpr lt).eq_or_lt
    · exact mem
    rw [swap_comm, ← swap_mul_swap_mul_swap (y := Fin.castSucc j) lts.ne lt.ne]
    exact mul_mem (mul_mem mem <| ih lts.ne lts) mem

/-- Like `swap_induction_on`, but with the composition on the right of `f`.

An induction principle for permutations. If `motive` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `motive` holds for all permutations. -/
@[elab_as_elim]
/-
**Equiv.Perm.swap_induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：swap_induction_on' [Finite α] {motive : Perm α -> Prop} (f : Perm α) (one 
: motive 1) (mul_swap : forall f x y, x != y -> motive f -> motive (f * swap x y
)) : motive f
参数：f : Perm α；one : motive 1；mul_swap : forall f x y, x != y -> motive f -> moti
ve (f * swap x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.swap_induction_on`：swap_induction_on [Finite α] {motive : Per
m α -> Prop} (f : Perm α) (one : motive 1) (swap_mul : forall f x y, x != y -> m
otive f -> motive …
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a

--- 原说明 ---
Like `swap_induction_on`, but with the composition on the right of `f`.

An induction principle for permutations. If `motive` holds for the identity perm
utation, and
is preserved under composition with a non-trivial swap, then `motive` holds for 
all permutations.
-/
theorem swap_induction_on' [Finite α] {motive : Perm α → Prop} (f : Perm α) (one : motive 1)
    (mul_swap : ∀ f x y, x ≠ y → motive f → motive (f * swap x y)) : motive f :=
  inv_inv f ▸ swap_induction_on f⁻¹ one fun f => mul_swap f⁻¹
/-
**Equiv.Perm.isConj_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isConj_swap {w x y z : α} (hwx : w != x) (hyz : y != z) : IsConj (swap w x
) (swap y z)
参数：hwx : w != x；hyz : y != z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Equiv.swap_inv`：∀ {α : Type u_4} [inst : DecidableEq α] (x y : α), (Equi
v.swap x y)⁻¹ = Equiv.swap x y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.swap_mul_swap_mul_swap`：∀ {α : Type u_4} [inst : DecidableEq α] {x
 y z : α},   x ≠ y → x ≠ z → Equiv.swap y z * Equiv.swap x y * Equiv.swap y z = 
Equiv.swap z x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Equiv.swap_comm`：swap_comm (a b : α) : swap a b = swap b a
-/
theorem isConj_swap {w x y z : α} (hwx : w ≠ x) (hyz : y ≠ z) : IsConj (swap w x) (swap y z) :=
  isConj_iff.2
    (have h :
      ∀ {y z : α},
        y ≠ z → w ≠ z → swap w y * swap x z * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
      fun {y z} hyz hwz => by
      rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc (swap w y), mul_assoc (swap w y), ←
        mul_assoc _ (swap x z), swap_mul_swap_mul_swap hwx hwz, ← mul_assoc,
        swap_mul_swap_mul_swap hwz.symm hyz.symm]
    if hwz : w = z then
      have hwy : w ≠ y := by rw [hwz]; exact hyz.symm
      ⟨swap w z * swap x y, by rw [swap_comm y z, h hyz.symm hwy]⟩
    else ⟨swap w y * swap x z, h hyz hwz⟩)

/-- set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a -/
/-
**Equiv.Perm.finPairsLT** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：finPairsLT (n : Nat) : Finset (Σ _ : Fin n, Fin n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a
-/
def finPairsLT (n : ℕ) : Finset (Σ _ : Fin n, Fin n) :=
  (univ : Finset (Fin n)).sigma fun a => (range a).attachFin fun _ hm => (mem_range.1 hm).trans a.2
/-
**Equiv.Perm.mem_finPairsLT** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_finPairsLT {n : Nat} {a : Σ _ : Fin n, Fin n} : a in finPairsLT n ↔ a.
2 < a.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_finPairsLT {n : ℕ} {a : Σ _ : Fin n, Fin n} : a ∈ finPairsLT n ↔ a.2 < a.1 := by
  simp only [finPairsLT, Fin.lt_def, true_and, mem_attachFin, mem_range, mem_univ,
    mem_sigma]

/-- `signAux σ` is the sign of a permutation on `Fin n`, defined as the parity of the number of
  pairs `(x₁, x₂)` such that `x₂ < x₁` but `σ x₁ ≤ σ x₂` -/
/-
**Equiv.Perm.signAux** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux {n : Nat} (a : Perm (Fin n)) : Intˣ
参数：a : Perm (Fin n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`signAux σ` is the sign of a permutation on `Fin n`, defined as the parity of th
e number of
  pairs `(x₁, x₂)` such that `x₂ < x₁` but `σ x₁ ≤ σ x₂`
-/
def signAux {n : ℕ} (a : Perm (Fin n)) : ℤˣ :=
  ∏ x ∈ finPairsLT n, if a x.1 ≤ a x.2 then -1 else 1

@[simp]
/-
**Equiv.Perm.signAux_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux_one (n : Nat) : signAux (1 : Perm (Fin n)) = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_finPairsLT`：mem_finPairsLT {n : Nat} {a : Σ _ : Fin n, Fi
n n} : a in finPairsLT n ↔ a.2 < a.1
-/
theorem signAux_one (n : ℕ) : signAux (1 : Perm (Fin n)) = 1 := by
  unfold signAux
  conv => rhs; rw [← @Finset.prod_const_one _ _ (finPairsLT n)]
  exact Finset.prod_congr rfl fun a ha => if_neg (mem_finPairsLT.1 ha).not_ge

/-- `signBijAux f ⟨a, b⟩` returns the pair consisting of `f a` and `f b` in decreasing order. -/
/-
**Equiv.Perm.signBijAux** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：signBijAux {n : Nat} (f : Perm (Fin n)) (a : Σ _ : Fin n, Fin n) : Σ _ : F
in n, Fin n
参数：f : Perm (Fin n)；a : Σ _ : Fin n, Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`signBijAux f ⟨a, b⟩` returns the pair consisting of `f a` and `f b` in decreasi
ng order.
-/
def signBijAux {n : ℕ} (f : Perm (Fin n)) (a : Σ _ : Fin n, Fin n) : Σ _ : Fin n, Fin n :=
  if _ : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩
/-
**Equiv.Perm.signBijAux_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signBijAux_injOn {n : Nat} {f : Perm (Fin n)} : (finPairsLT n : Set (Σ _, 
Fin n)).InjOn (signBijAux f)
参数：Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_finPairsLT`：mem_finPairsLT {n : Nat} {a : Σ _ : Fin n, Fi
n n} : a in finPairsLT n ↔ a.2 < a.1
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem signBijAux_injOn {n : ℕ} {f : Perm (Fin n)} :
    (finPairsLT n : Set (Σ _, Fin n)).InjOn (signBijAux f) := by
  rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb h
  dsimp [signBijAux] at h
  rw [Finset.mem_coe, mem_finPairsLT] at *
  have : ¬b₁ < b₂ := hb.le.not_gt
  split_ifs at h <;>
  simp_all only [not_lt, Sigma.mk.inj_iff, (Equiv.injective f).eq_iff, heq_eq_eq]
  · exact absurd this (not_le.mpr ha)
  · exact absurd this (not_le.mpr ha)
/-
**Equiv.Perm.signBijAux_surj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signBijAux_surj {n : Nat} {f : Perm (Fin n)} : forall a in finPairsLT n, e
xists b in finPairsLT n, signBijAux f b = a
参数：Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_finPairsLT`：mem_finPairsLT {n : Nat} {a : Σ _ : Fin n, Fi
n n} : a in finPairsLT n ↔ a.2 < a.1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem signBijAux_surj {n : ℕ} {f : Perm (Fin n)} :
    ∀ a ∈ finPairsLT n, ∃ b ∈ finPairsLT n, signBijAux f b = a :=
  fun ⟨a₁, a₂⟩ ha =>
    if hxa : f.symm a₂ < f.symm a₁ then
      ⟨⟨f.symm a₁, f.symm a₂⟩, mem_finPairsLT.2 hxa, by
       simp [signBijAux, if_pos (mem_finPairsLT.1 ha)]⟩
    else
      ⟨⟨f.symm a₂, f.symm a₁⟩,
        mem_finPairsLT.2 <|
          (le_of_not_gt hxa).lt_of_ne fun h => by
            simp [mem_finPairsLT, f⁻¹.injective h] at ha, by
              simp [signBijAux, if_neg (mem_finPairsLT.1 ha).le.not_gt]⟩
/-
**Equiv.Perm.signBijAux_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signBijAux_mem {n : Nat} {f : Perm (Fin n)} : forall a : Σ _ : Fin n, Fin 
n, a in finPairsLT n -> signBijAux f a in finPairsLT n
参数：Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_finPairsLT`：mem_finPairsLT {n : Nat} {a : Σ _ : Fin n, Fi
n n} : a in finPairsLT n ↔ a.2 < a.1
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem signBijAux_mem {n : ℕ} {f : Perm (Fin n)} :
    ∀ a : Σ _ : Fin n, Fin n, a ∈ finPairsLT n → signBijAux f a ∈ finPairsLT n :=
  fun ⟨a₁, a₂⟩ ha => by
    unfold signBijAux
    split_ifs with h
    · exact mem_finPairsLT.2 h
    · exact mem_finPairsLT.2
        ((le_of_not_gt h).lt_of_ne fun h => (mem_finPairsLT.1 ha).ne (f.injective h.symm))

@[simp]
/-
**Equiv.Perm.signAux_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux_inv {n : Nat} (f : Perm (Fin n)) : signAux f⁻¹ = signAux f
参数：f : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_nbij`：prod_nbij (i : ι -> κ) (hi : forall a in s, i a in t) 
(i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) (h : forall a in
 s, f …
· 使用定理 `Equiv.Perm.signBijAux_mem`：signBijAux_mem {n : Nat} {f : Perm (Fin n)} :
 forall a : Σ _ : Fin n, Fin n, a in finPairsLT n -> signBijAux f a in finPairsL
T n
· 使用定理 `Equiv.Perm.signBijAux_injOn`：signBijAux_injOn {n : Nat} {f : Perm (Fin n
)} : (finPairsLT n : Set (Σ _, Fin n)).InjOn (signBijAux f)
· 使用定理 `Equiv.Perm.signBijAux_surj`：signBijAux_surj {n : Nat} {f : Perm (Fin n)}
 : forall a in finPairsLT n, exists b in finPairsLT n, signBijAux f b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_finPairsLT`：mem_finPairsLT {n : Nat} {a : Σ _ : Fin n, Fi
n n} : a in finPairsLT n ↔ a.2 < a.1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem signAux_inv {n : ℕ} (f : Perm (Fin n)) : signAux f⁻¹ = signAux f :=
  prod_nbij (signBijAux f⁻¹) signBijAux_mem signBijAux_injOn signBijAux_surj fun ⟨a, b⟩ hab ↦ by
    by_cases h : f.symm b < f.symm a
    · simp_all [signBijAux, (mem_finPairsLT.1 hab).not_ge]
    · simp_all [signBijAux, dif_neg h, (mem_finPairsLT.1 hab).le]
/-
**Equiv.Perm.signAux_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux_mul {n : Nat} (f g : Perm (Fin n)) : signAux (f * g) = signAux f *
 signAux g
参数：f g : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.signAux_inv`：signAux_inv {n : Nat} (f : Perm (Fin n)) : signA
ux f⁻¹ = signAux f
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用引理 `Finset.prod_nbij`：prod_nbij (i : ι -> κ) (hi : forall a in s, i a in t) 
(i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) (h : forall a in
 s, f …
· 使用定理 `Equiv.Perm.signBijAux_mem`：signBijAux_mem {n : Nat} {f : Perm (Fin n)} :
 forall a : Σ _ : Fin n, Fin n, a in finPairsLT n -> signBijAux f a in finPairsL
T n
· 使用定理 `Equiv.Perm.signBijAux_injOn`：signBijAux_injOn {n : Nat} {f : Perm (Fin n
)} : (finPairsLT n : Set (Σ _, Fin n)).InjOn (signBijAux f)
· 使用定理 `Equiv.Perm.signBijAux_surj`：signBijAux_surj {n : Nat} {f : Perm (Fin n)}
 : forall a in finPairsLT n, exists b in finPairsLT n, signBijAux f b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Equiv.Perm.mem_finPairsLT`：mem_finPairsLT {n : Nat} {a : Σ _ : Fin n, Fi
n n} : a in finPairsLT n ↔ a.2 < a.1
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem signAux_mul {n : ℕ} (f g : Perm (Fin n)) : signAux (f * g) = signAux f * signAux g := by
  rw [← signAux_inv g]
  unfold signAux
  rw [← prod_mul_distrib]
  refine prod_nbij (signBijAux g) signBijAux_mem signBijAux_injOn signBijAux_surj ?_
  rintro ⟨a, b⟩ hab
  dsimp only [signBijAux]
  rw [mul_apply, mul_apply]
  rw [mem_finPairsLT] at hab
  by_cases hg : g b < g a
  · simp [*]
  obtain hf | hf := (f.injective.ne <| g.injective.ne hab.ne).lt_or_gt <;>
    simp_all [le_of_lt, not_le_of_gt, not_lt_of_ge]
/-
**Equiv.Perm.signAux_swap_zero_one'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem signAux_swap_zero_one' (n : ℕ) : signAux (swap (0 : Fin (n + 2)) 1) = -1 :=
  show _ = ∏ x ∈ {(⟨1, 0⟩ : Σ _ : Fin (n + 2), Fin (n + 2))},
      if (Equiv.swap 0 1) x.1 ≤ swap 0 1 x.2 then (-1 : ℤˣ) else 1 by
    refine Eq.symm (prod_subset (fun ⟨x₁, x₂⟩ => by
      simp +contextual [mem_finPairsLT]) fun a ha₁ ha₂ => ?_)
    rcases a with ⟨a₁, a₂⟩
    replace ha₁ : a₂ < a₁ := mem_finPairsLT.1 ha₁
    dsimp only
    rcases a₁.zero_le.eq_or_lt with (rfl | H)
    · exact absurd a₂.zero_le ha₁.not_ge
    rcases a₂.zero_le.eq_or_lt with (rfl | H')
    · simp only [and_true, heq_iff_eq, mem_singleton, Sigma.mk.inj_iff] at ha₂
      have : 1 < a₁ := lt_of_le_of_ne' (Nat.succ_le_of_lt ha₁) ha₂
      have h01 : Equiv.swap (0 : Fin (n + 2)) 1 0 = 1 := by simp
      rw [swap_apply_of_ne_of_ne (ne_of_gt H) ha₂, h01, if_neg this.not_ge]
    · have le : 1 ≤ a₂ := Nat.succ_le_of_lt H'
      have lt : 1 < a₁ := le.trans_lt ha₁
      have h01 : Equiv.swap (0 : Fin (n + 2)) 1 1 = 0 := by simp only [swap_apply_right]
      rcases le.eq_or_lt with (rfl | lt')
      · rw [swap_apply_of_ne_of_ne H.ne' lt.ne', h01, if_neg H.not_ge]
      · rw [swap_apply_of_ne_of_ne (ne_of_gt H) (ne_of_gt lt),
          swap_apply_of_ne_of_ne (ne_of_gt H') (ne_of_gt lt'), if_neg ha₁.not_ge]
/-
**Equiv.Perm.signAux_swap_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem signAux_swap_zero_one {n : ℕ} (hn : 2 ≤ n) :
    signAux (swap (⟨0, lt_of_lt_of_le (by decide) hn⟩ : Fin n) ⟨1, lt_of_lt_of_le (by decide) hn⟩) =
      -1 := by
  rcases n with (_ | _ | n)
  · norm_num at hn
  · norm_num at hn
  · exact signAux_swap_zero_one' n
/-
**Equiv.Perm.signAux_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux_swap : forall {n : Nat} {x y : Fin n} (_hxy : x != y), signAux (sw
ap x y) = -1 | 0, x, y => by intro; exact Fin.elim0 x | 1, x, y => by dsimp [sig
nAux, swap, swapCore] simp only [eq_iff_true_of_subsingleton, not_true, IsEmpty.
forall_iff] | n + 2, x, y => fun hxy => by have h2n : 2 <= n + 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.swapCore_swapCore`：swapCore_swapCore (r a b : α) : swapCore a b (s
wapCore a b r) = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isConj_iff_eq`：isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsCo
nj a b ↔ a = b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `_private.Mathlib.GroupTheory.Perm.Sign.0.Equiv.Perm.signAux_swap_zero_on
e`：∀ {n : ℕ} (hn : 2 ≤ n), (Equiv.swap ⟨0, ⋯⟩ ⟨1, ⋯⟩).signAux = -1
· 使用定理 `MonoidHom.map_isConj`：∀ {α : Type u} {β : Type v} [inst : Monoid α] [ins
t_1 : Monoid β] (f : α →* β) {a b : α},   IsConj a b → IsConj (f a) (f b)
· 使用定理 `Equiv.Perm.signAux_mul`：signAux_mul {n : Nat} (f g : Perm (Fin n)) : sig
nAux (f * g) = signAux f * signAux g
· 使用定理 `Equiv.Perm.isConj_swap`：isConj_swap {w x y z : α} (hwx : w != x) (hyz : 
y != z) : IsConj (swap w x) (swap y z)
-/
theorem signAux_swap : ∀ {n : ℕ} {x y : Fin n} (_hxy : x ≠ y), signAux (swap x y) = -1
  | 0, x, y => by intro; exact Fin.elim0 x
  | 1, x, y => by
    dsimp [signAux, swap, swapCore]
    simp only [eq_iff_true_of_subsingleton, not_true,
               IsEmpty.forall_iff]
  | n + 2, x, y => fun hxy => by
    have h2n : 2 ≤ n + 2 := by exact le_add_self
    rw [← isConj_iff_eq, ← signAux_swap_zero_one h2n]
    exact (MonoidHom.mk' signAux signAux_mul).map_isConj
      (isConj_swap hxy (by exact of_decide_eq_true rfl))

/-- When the list `l : List α` contains all nonfixed points of the permutation `f : Perm α`,
  `signAux2 l f` recursively calculates the sign of `f`. -/
/-
**Equiv.Perm.signAux2** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：{α : Type u} → [DecidableEq α] → List α → Equiv.Perm α → ℤˣ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the list `l : List α` contains all nonfixed points of the permutation `f : 
Perm α`,
  `signAux2 l f` recursively calculates the sign of `f`.
-/
def signAux2 : List α → Perm α → ℤˣ
  | [], _ => 1
  | x::l, f => if x = f x then signAux2 l f else -signAux2 l (swap x (f x) * f)

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.signAux_eq_signAux2** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux_eq_signAux2 {n : Nat} : forall (l : List α) (f : Perm α) (e : α ≃ 
Fin n) (_h : forall x, f x != x -> x in l), signAux ((e.symm.trans f).trans e) =
 signAux2 l f | [], f, e, h => by have : f = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem signAux_eq_signAux2 {n : ℕ} :
    ∀ (l : List α) (f : Perm α) (e : α ≃ Fin n) (_h : ∀ x, f x ≠ x → x ∈ l),
      signAux ((e.symm.trans f).trans e) = signAux2 l f
  | [], f, e, h => by
    have : f = 1 := Equiv.ext fun y => Classical.not_not.1 (mt (h y) List.not_mem_nil)
    rw [this, one_def, Equiv.trans_refl, Equiv.symm_trans_self, ← one_def, signAux_one, signAux2]
  | x::l, f, e, h => by
    rw [signAux2]
    by_cases hfx : x = f x
    · rw [if_pos hfx]
      exact
        signAux_eq_signAux2 l f _ fun y (hy : f y ≠ y) =>
          List.mem_of_ne_of_mem (fun h : y = x => by simp [h, hfx.symm] at hy) (h y hy)
    · have hy : ∀ y : α, (swap x (f x) * f) y ≠ y → y ∈ l := fun y hy =>
        have : f y ≠ y ∧ y ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hy
        List.mem_of_ne_of_mem this.2 (h _ this.1)
      have : (e.symm.trans (swap x (f x) * f)).trans e =
          swap (e x) (e (f x)) * (e.symm.trans f).trans e := by
        ext
        rw [← Equiv.symm_trans_swap_trans, mul_def, Equiv.symm_trans_swap_trans, mul_def]
        repeat (rw [trans_apply])
        simp [swap, swapCore]
        split_ifs <;> rfl
      have hefx : e x ≠ e (f x) := mt e.injective.eq_iff.1 hfx
      rw [if_neg hfx, ← signAux_eq_signAux2 _ _ e hy, this, signAux_mul, signAux_swap hefx]
      simp only [neg_neg, one_mul, neg_mul]

/-- When the multiset `s : Multiset α` contains all nonfixed points of the permutation `f : Perm α`,
  `signAux2 f _` recursively calculates the sign of `f`. -/
/-
**Equiv.Perm.signAux3** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux3 [Finite α] (f : Perm α) {s : Multiset α} : (forall x, x in s) -> 
Intˣ
参数：f : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the multiset `s : Multiset α` contains all nonfixed points of the permutati
on `f : Perm α`,
  `signAux2 f _` recursively calculates the sign of `f`.
-/
def signAux3 [Finite α] (f : Perm α) {s : Multiset α} : (∀ x, x ∈ s) → ℤˣ :=
  Quotient.hrecOn s (fun l _ => signAux2 l f) fun l₁ l₂ h ↦ by
    rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
    refine Function.hfunext (forall_congr fun _ ↦ propext h.mem_iff) fun h₁ h₂ _ ↦ ?_
    rw [← signAux_eq_signAux2 _ _ e fun _ _ => h₁ _, ← signAux_eq_signAux2 _ _ e fun _ _ => h₂ _]
/-
**Equiv.Perm.signAux3_mul_and_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux3_mul_and_swap [Finite α] (f g : Perm α) (s : Multiset α) (hs : for
all x, x in s) : signAux3 (f * g) hs = signAux3 f hs * signAux3 g hs ∧ Pairwise 
fun x y => signAux3 (swap x y) hs = -1
参数：f g : Perm α；s : Multiset α；hs : forall x, x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.signAux_eq_signAux2`：signAux_eq_signAux2 {n : Nat} : forall (
l : List α) (f : Perm α) (e : α ≃ Fin n) (_h : forall x, f x != x -> x in l), si
gnAux ((e.symm.trans…
· 使用定理 `Equiv.Perm.signAux_mul`：signAux_mul {n : Nat} (f g : Perm (Fin n)) : sig
nAux (f * g) = signAux f * signAux g
· 使用定理 `Equiv.symm_trans_swap_trans`：symm_trans_swap_trans [DecidableEq β] (a b 
: α) (e : α ≃ β) : (e.symm.trans (swap a b)).trans e = swap (e a) (e b)
· 使用定理 `Equiv.Perm.signAux_swap`：signAux_swap : forall {n : Nat} {x y : Fin n} (
_hxy : x != y), signAux (swap x y) = -1 | 0, x, y => by intro; exact Fin.elim0 x
 | 1, x, y =>…
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem signAux3_mul_and_swap [Finite α] (f g : Perm α) (s : Multiset α) (hs : ∀ x, x ∈ s) :
    signAux3 (f * g) hs = signAux3 f hs * signAux3 g hs ∧
      Pairwise fun x y => signAux3 (swap x y) hs = -1 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  induction s using Quotient.inductionOn with | _ l => ?_
  change
    signAux2 l (f * g) = signAux2 l f * signAux2 l g ∧
    Pairwise fun x y => signAux2 l (swap x y) = -1
  have hfg : (e.symm.trans (f * g)).trans e = (e.symm.trans f).trans e * (e.symm.trans g).trans e :=
    Equiv.ext fun h => by simp [mul_apply]
  constructor
  · rw [← signAux_eq_signAux2 _ _ e fun _ _ => hs _, ←
      signAux_eq_signAux2 _ _ e fun _ _ => hs _, ← signAux_eq_signAux2 _ _ e fun _ _ => hs _,
      hfg, signAux_mul]
  · intro x y hxy
    rw [← e.injective.ne_iff] at hxy
    rw [← signAux_eq_signAux2 _ _ e fun _ _ => hs _, symm_trans_swap_trans, signAux_swap hxy]
/-
**Equiv.Perm.signAux3_symm_trans_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：signAux3_symm_trans_trans [Finite α] [DecidableEq β] [Finite β] (f : Perm 
α) (e : α ≃ β) {s : Multiset α} {t : Multiset β} (hs : forall x, x in s) (ht : f
orall x, x in t) : signAux3 ((e.symm.trans f).trans e) ht = signAux3 f hs
参数：f : Perm α；e : α ≃ β；hs : forall x, x in s；ht : forall x, x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.signAux_eq_signAux2`：signAux_eq_signAux2 {n : Nat} : forall (
l : List α) (f : Perm α) (e : α ≃ Fin n) (_h : forall x, f x != x -> x in l), si
gnAux ((e.symm.trans…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.trans_assoc`：trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ
) : (ab.trans bc).trans cd = ab.trans (bc.trans cd)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem signAux3_symm_trans_trans [Finite α] [DecidableEq β] [Finite β] (f : Perm α) (e : α ≃ β)
    {s : Multiset α} {t : Multiset β} (hs : ∀ x, x ∈ s) (ht : ∀ x, x ∈ t) :
    signAux3 ((e.symm.trans f).trans e) ht = signAux3 f hs := by
  induction t, s using Quotient.inductionOn₂
  change signAux2 _ _ = signAux2 _ _
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e'⟩⟩
  rw [← signAux_eq_signAux2 _ _ e' fun _ _ => ht _,
    ← signAux_eq_signAux2 _ _ (e.trans e') fun _ _ => hs _]
  simp [trans_assoc]

/-- `SignType.sign` of a permutation returns the signature or parity of a permutation, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homomorphism from
`Perm α` to the group with two elements. -/
/-
**Equiv.Perm.sign** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：sign [Fintype α] : Perm α ->* Intˣ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
`SignType.sign` of a permutation returns the signature or parity of a permutatio
n, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homom
orphism from
`Perm α` to the group with two elements.
-/
def sign [Fintype α] : Perm α →* ℤˣ :=
  MonoidHom.mk' (fun f => signAux3 f mem_univ) fun f g => (signAux3_mul_and_swap f g _ mem_univ).1

section SignType.sign

variable [Fintype α]

@[simp]
/-
**Equiv.Perm.sign_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_mul (f g : Perm α) : sign (f * g) = sign f * sign g
参数：f g : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem sign_mul (f g : Perm α) : sign (f * g) = sign f * sign g :=
  map_mul sign f g

@[simp]
/-
**Equiv.Perm.sign_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_trans (f g : Perm α) : sign (f.trans g) = sign g * sign f
参数：f g : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_def`：mul_def (f g : Perm α) : f * g = g.trans f
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
-/
theorem sign_trans (f g : Perm α) : sign (f.trans g) = sign g * sign f := by
  rw [← mul_def, sign_mul]

@[simp]
/-
**Equiv.Perm.sign_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_one : sign (1 : Perm α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem sign_one : sign (1 : Perm α) = 1 :=
  map_one sign

@[simp]
/-
**Equiv.Perm.sign_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_refl : sign (Equiv.refl α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem sign_refl : sign (Equiv.refl α) = 1 :=
  map_one sign

@[simp]
/-
**Equiv.Perm.sign_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_inv (f : Perm α) : sign f⁻¹ = sign f
参数：f : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `Int.units_inv_eq_self`：units_inv_eq_self (u : Intˣ) : u⁻¹ = u
-/
theorem sign_inv (f : Perm α) : sign f⁻¹ = sign f := by
  rw [map_inv sign f, Int.units_inv_eq_self]

@[simp]
/-
**Equiv.Perm.sign_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_symm (e : Perm α) : sign e.symm = sign e
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
-/
theorem sign_symm (e : Perm α) : sign e.symm = sign e :=
  sign_inv e
/-
**Equiv.Perm.sign_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_swap {x y : α} (h : x != y) : sign (swap x y) = -1
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Equiv.Perm.signAux3_mul_and_swap`：signAux3_mul_and_swap [Finite α] (f g 
: Perm α) (s : Multiset α) (hs : forall x, x in s) : signAux3 (f * g) hs = signA
ux3 f hs * signAux3 g …
-/
theorem sign_swap {x y : α} (h : x ≠ y) : sign (swap x y) = -1 :=
  (signAux3_mul_and_swap 1 1 _ mem_univ).2 h

@[simp]
/-
**Equiv.Perm.sign_swap'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_swap' {x y : α} : sign (swap x y) = if x = y then 1 else -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.sign_swap`：sign_swap {x y : α} (h : x != y) : sign (swap x y)
 = -1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem sign_swap' {x y : α} : sign (swap x y) = if x = y then 1 else -1 :=
  if H : x = y then by simp [H, swap_self] else by simp [sign_swap H, H]
/-
**Equiv.Perm.IsSwap.sign_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsSwap`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] [inst_1 : Fintype α] {f : Equiv.Perm
 α}, f.IsSwap → Equiv.Perm.sign f = -1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sign_swap`：sign_swap {x y : α} (h : x != y) : sign (swap x y)
 = -1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsSwap.sign_eq {f : Perm α} (h : f.IsSwap) : sign f = -1 :=
  let ⟨_, _, hxy⟩ := h
  hxy.2.symm ▸ sign_swap hxy.1

@[simp]
/-
**Equiv.Perm.sign_symm_trans_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_symm_trans_trans [DecidableEq β] [Fintype β] (f : Perm α) (e : α ≃ β)
 : sign ((e.symm.trans f).trans e) = sign f
参数：f : Perm α；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.signAux3_symm_trans_trans`：signAux3_symm_trans_trans [Finite 
α] [DecidableEq β] [Finite β] (f : Perm α) (e : α ≃ β) {s : Multiset α} {t : Mul
tiset β} (hs : forall x, x…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem sign_symm_trans_trans [DecidableEq β] [Fintype β] (f : Perm α) (e : α ≃ β) :
    sign ((e.symm.trans f).trans e) = sign f :=
  signAux3_symm_trans_trans f e mem_univ mem_univ

@[simp]
/-
**Equiv.Perm.sign_trans_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_trans_trans_symm [DecidableEq β] [Fintype β] (f : Perm β) (e : α ≃ β)
 : sign ((e.trans f).trans e.symm) = sign f
参数：f : Perm β；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sign_symm_trans_trans`：sign_symm_trans_trans [DecidableEq β] 
[Fintype β] (f : Perm α) (e : α ≃ β) : sign ((e.symm.trans f).trans e) = sign f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sign_trans_trans_symm [DecidableEq β] [Fintype β] (f : Perm β) (e : α ≃ β) :
    sign ((e.trans f).trans e.symm) = sign f :=
  sign_symm_trans_trans f e.symm
/-
**Equiv.Perm.sign_prod_list_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_prod_list_swap {l : List (Perm α)} (hl : forall g in l, IsSwap g) : s
ign l.prod = (-1) ^ l.length
参数：Perm α；hl : forall g in l, IsSwap g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.eq_replicate_iff`：∀ {α : Type u_1} {a : α} {n : ℕ} {l : List α}, l 
= List.replicate n a ↔ l.length = n ∧ ∀ b ∈ l, b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Equiv.Perm.IsSwap.sign_eq`：∀ {α : Type u} [inst : DecidableEq α] [inst_1
 : Fintype α] {f : Equiv.Perm α}, f.IsSwap → Equiv.Perm.sign f = -1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod
-/
theorem sign_prod_list_swap {l : List (Perm α)} (hl : ∀ g ∈ l, IsSwap g) :
    sign l.prod = (-1) ^ l.length := by
  have h₁ : l.map sign = List.replicate l.length (-1) :=
    List.eq_replicate_iff.2
      ⟨by simp, fun u hu =>
        let ⟨g, hg⟩ := List.mem_map.1 hu
        hg.2 ▸ (hl _ hg.1).sign_eq⟩
  rw [← List.prod_replicate, ← h₁, List.prod_hom _ (@sign α _ _)]

@[simp]
/-
**Equiv.Perm.sign_abs** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_abs (f : Perm α) : |(Equiv.Perm.sign f : Int)| = 1
参数：f : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用引理 `Int.units_natAbs`：units_natAbs (u : Intˣ) : natAbs u = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem sign_abs (f : Perm α) :
    |(Equiv.Perm.sign f : ℤ)| = 1 := by
  rw [Int.abs_eq_natAbs, Int.units_natAbs, Nat.cast_one]

variable (α) in
/-
**Equiv.Perm.sign_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_surjective [Nontrivial α] : Function.Surjective (sign : Perm α -> Int
ˣ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Equiv.Perm.sign_swap`：sign_swap {x y : α} (h : x != y) : sign (swap x y)
 = -1
-/
theorem sign_surjective [Nontrivial α] : Function.Surjective (sign : Perm α → ℤˣ) := fun a =>
  (Int.units_eq_one_or a).elim (fun h => ⟨1, by simp [h]⟩) fun h =>
    let ⟨x, y, hxy⟩ := exists_pair_ne α
    ⟨swap x y, by rw [sign_swap hxy, h]⟩
/-
**Equiv.Perm.eq_sign_of_surjective_hom** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：eq_sign_of_surjective_hom {s : Perm α ->* Intˣ} (hs : Surjective s) : s = 
sign
参数：hs : Surjective s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isConj_iff_eq`：isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsCo
nj a b ↔ a = b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `MonoidHom.map_isConj`：∀ {α : Type u} {β : Type v} [inst : Monoid α] [ins
t_1 : Monoid β] (f : α →* β) {a b : α},   IsConj a b → IsConj (f a) (f b)
· 使用定理 `Equiv.Perm.isConj_swap`：isConj_swap {w x y z : α} (hwx : w != x) (hyz : 
y != z) : IsConj (swap w x) (swap y z)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.eq_replicate_length`：∀ {α : Type u} {a : α} {l : List α}, l = List.
replicate l.length a ↔ ∀ b ∈ l, b = a
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.IsSwap.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [i
nst_1 : DecidableEq α] (f f_1 : Equiv.Perm α), f = f_1 → f.IsSwap = f_1.IsSwap
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `Equiv.Perm.sign_prod_list_swap`：sign_prod_list_swap {l : List (Perm α)} 
(hl : forall g in l, IsSwap g) : sign l.prod = (-1) ^ l.length
-/
theorem eq_sign_of_surjective_hom {s : Perm α →* ℤˣ} (hs : Surjective s) : s = sign :=
  have : ∀ {f}, IsSwap f → s f = -1 := fun {f} ⟨x, y, hxy, hxy'⟩ =>
    hxy'.symm ▸
      by_contradiction fun h => by
        have : ∀ f, IsSwap f → s f = 1 := fun f ⟨a, b, hab, hab'⟩ => by
          rw [← isConj_iff_eq, ← Or.resolve_right (Int.units_eq_one_or _) h, hab']
          exact s.map_isConj (isConj_swap hab hxy)
        let ⟨g, hg⟩ := hs (-1)
        let ⟨l, hl⟩ := (truncSwapFactors g).out
        have : ∀ a ∈ l.map s, a = (1 : ℤˣ) := fun a ha =>
          let ⟨g, hg⟩ := List.mem_map.1 ha
          hg.2 ▸ this _ (hl.2 _ hg.1)
        have : s l.prod = 1 := by
          rw [← l.prod_hom s, List.eq_replicate_length.2 this, List.prod_replicate, one_pow]
        rw [hl.1, hg] at this
        exact absurd this (by simp_all)
  MonoidHom.ext fun f => by
    let ⟨l, hl₁, hl₂⟩ := (truncSwapFactors f).out
    have hsl : ∀ a ∈ l.map s, a = (-1 : ℤˣ) := fun a ha =>
      let ⟨g, hg⟩ := List.mem_map.1 ha
      hg.2 ▸ this (hl₂ _ hg.1)
    rw [← hl₁, ← l.prod_hom s, List.eq_replicate_length.2 hsl, List.length_map, List.prod_replicate,
      sign_prod_list_swap hl₂]
/-
**Equiv.Perm.sign_subtypePerm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_subtypePerm (f : Perm α) {p : α -> Prop} [DecidablePred p] (h₁ : fora
ll x, p (f x) ↔ p x) (h₂ : forall x, f x != x -> p x) : sign (subtypePerm f h₁) 
= sign f
参数：f : Perm α；h₁ : forall x, p (f x) ↔ p x；h₂ : forall x, f x != x -> p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Equiv.Perm.IsSwap.of_subtype_isSwap`：∀ {α : Type u_1} [inst : DecidableE
q α] {p : α → Prop} [inst_1 : DecidablePred p] {f : Equiv.Perm (Subtype p)},   f
.IsSwap → (Equiv.Perm.ofS…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod
· 使用定理 `Equiv.Perm.ofSubtype_subtypePerm`：ofSubtype_subtypePerm {f : Perm α} (h₁
 : forall x, p (f x) ↔ p x) (h₂ : forall x, f x != x -> p x) : ofSubtype (subtyp
ePerm f h₁) = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sign_prod_list_swap`：sign_prod_list_swap {l : List (Perm α)} 
(hl : forall g in l, IsSwap g) : sign l.prod = (-1) ^ l.length
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
-/
theorem sign_subtypePerm (f : Perm α) {p : α → Prop} [DecidablePred p] (h₁ : ∀ x, p (f x) ↔ p x)
    (h₂ : ∀ x, f x ≠ x → p x) : sign (subtypePerm f h₁) = sign f := by
  let l := (truncSwapFactors (subtypePerm f h₁)).out
  have hl' : ∀ g' ∈ l.1.map ofSubtype, IsSwap g' := fun g' hg' =>
    let ⟨g, hg⟩ := List.mem_map.1 hg'
    hg.2 ▸ (l.2.2 _ hg.1).of_subtype_isSwap
  have hl'₂ : (l.1.map ofSubtype).prod = f := by
    rw [l.1.prod_hom ofSubtype, l.2.1, ofSubtype_subtypePerm _ h₂]
  conv =>
    congr
    rw [← l.2.1]
  simp_rw [← hl'₂]
  rw [sign_prod_list_swap l.2.2, sign_prod_list_swap hl', List.length_map]
/-
**Equiv.Perm.sign_eq_sign_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_eq_sign_of_equiv [DecidableEq β] [Fintype β] (f : Perm α) (g : Perm β
) (e : α ≃ β) (h : forall x, e (f x) = g (e x)) : sign f = sign g
参数：f : Perm α；g : Perm β；e : α ≃ β；h : forall x, e (f x) = g (e x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Equiv.Perm.sign_symm_trans_trans`：sign_symm_trans_trans [DecidableEq β] 
[Fintype β] (f : Perm α) (e : α ≃ β) : sign ((e.symm.trans f).trans e) = sign f
-/
theorem sign_eq_sign_of_equiv [DecidableEq β] [Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β)
    (h : ∀ x, e (f x) = g (e x)) : sign f = sign g := by
  have hg : g = (e.symm.trans f).trans e := Equiv.ext <| by simp [h]
  rw [hg, sign_symm_trans_trans]
/-
**Equiv.Perm.sign_bij** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_bij [DecidableEq β] [Fintype β] {f : Perm α} {g : Perm β} (i : forall
 x : α, f x != x -> β) (h : forall x hx hx', i (f x) hx' = g (i x hx)) (hi : for
all x₁ x₂ hx₁ hx₂, i x₁ hx₁ = i x₂ hx₂ -> x₁ = x₂) (hg : forall y, g y != y -> e
xists x hx, i x hx = y) : sign f = sign g
参数：i : forall x : α, f x != x -> β；h : forall x hx hx', i (f x) hx' = g (i x hx)
；hi : forall x₁ x₂ hx₁ hx₂, i x₁ hx₁ = i x₂ hx₂ -> x₁ = x₂；hg : forall y, g y !=
 y -> exists x hx, i x hx = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sign_subtypePerm`：sign_subtypePerm (f : Perm α) {p : α -> Pro
p} [DecidablePred p] (h₁ : forall x, p (f x) ↔ p x) (h₂ : forall x, f x != x -> 
p x) : sign (subt…
· 使用定理 `Equiv.Perm.sign_eq_sign_of_equiv`：sign_eq_sign_of_equiv [DecidableEq β] 
[Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β) (h : forall x, e (f x) = g (e 
x)) : sign f = sign g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
-/
theorem sign_bij [DecidableEq β] [Fintype β] {f : Perm α} {g : Perm β} (i : ∀ x : α, f x ≠ x → β)
    (h : ∀ x hx hx', i (f x) hx' = g (i x hx)) (hi : ∀ x₁ x₂ hx₁ hx₂, i x₁ hx₁ = i x₂ hx₂ → x₁ = x₂)
    (hg : ∀ y, g y ≠ y → ∃ x hx, i x hx = y) : sign f = sign g :=
  calc
    sign f = sign (subtypePerm f <| by simp : Perm { x // f x ≠ x }) :=
      (sign_subtypePerm _ _ fun _ => id).symm
    _ = sign (subtypePerm g <| by simp : Perm { x // g x ≠ x }) :=
      sign_eq_sign_of_equiv _ _
        (Equiv.ofBijective
          (fun x : { x // f x ≠ x } =>
            (⟨i x.1 x.2, by
                have : f (f x) ≠ f x := mt (fun h => f.injective h) x.2
                rw [← h _ x.2 this]
                exact mt (hi _ _ this x.2) x.2⟩ :
              { y // g y ≠ y }))
          ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => Subtype.ext (hi _ _ _ _ (Subtype.mk.inj h)), fun ⟨y, hy⟩ =>
            let ⟨x, hfx, hx⟩ := hg y hy
            ⟨⟨x, hfx⟩, Subtype.ext hx⟩⟩)
        fun ⟨x, _⟩ => Subtype.ext (h x _ _)
    _ = sign g := sign_subtypePerm _ _ fun _ => id

/-- If we apply `prod_extendRight a (σ a)` for all `a : α` in turn,
we get `prod_congrRight σ`. -/
/-
**Equiv.Perm.prod_prodExtendRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：prod_prodExtendRight {α : Type*} [DecidableEq α] (σ : α -> Perm β) {l : Li
st α} (hl : l.Nodup) (mem_l : forall a, a in l) : (l.map fun a => prodExtendRigh
t a (σ a)).prod = prodCongrRight σ
参数：σ : α -> Perm β；hl : l.Nodup；mem_l : forall a, a in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.prod_nil`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α], [].prod =
 1
· 使用定理 `Equiv.Perm.one_apply`：one_apply (x) : (1 : Perm α) x = x
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `Equiv.Perm.prodExtendRight_apply_ne`：prodExtendRight_apply_ne {a a' : α₁
} (h : a' != a) (b : β₁) : prodExtendRight a e (a', b) = (a', b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Equiv.Perm.prodExtendRight_apply_eq`：prodExtendRight_apply_eq (b : β₁) :
 prodExtendRight a e (a, b) = (a, e b)
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `Equiv.prodCongrRight_apply`：prodCongrRight_apply (a : α₁) (b : β₁) : pro
dCongrRight e (a, b) = (a, e a b)

--- 原说明 ---
If we apply `prod_extendRight a (σ a)` for all `a : α` in turn,
we get `prod_congrRight σ`.
-/
theorem prod_prodExtendRight {α : Type*} [DecidableEq α] (σ : α → Perm β) {l : List α}
    (hl : l.Nodup) (mem_l : ∀ a, a ∈ l) :
    (l.map fun a => prodExtendRight a (σ a)).prod = prodCongrRight σ := by
  ext ⟨a, b⟩ : 1
  -- We'll use induction on the list of elements,
  -- but we have to keep track of whether we already passed `a` in the list.
  suffices a ∈ l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b) = (a, σ a b) ∨
      a ∉ l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b) = (a, b) by
    obtain ⟨_, prod_eq⟩ := Or.resolve_right this (not_and.mpr fun h _ => h (mem_l a))
    rw [prod_eq, prodCongrRight_apply]
  clear mem_l
  induction l with
  | nil =>
    refine Or.inr ⟨List.not_mem_nil, ?_⟩
    rw [List.map_nil, List.prod_nil, one_apply]
  | cons a' l ih =>
    rw [List.map_cons, List.prod_cons, mul_apply]
    rcases ih (List.nodup_cons.mp hl).2 with (⟨mem_l, prod_eq⟩ | ⟨notMem_l, prod_eq⟩) <;>
      rw [prod_eq]
    · refine Or.inl ⟨List.mem_cons_of_mem _ mem_l, ?_⟩
      rw [prodExtendRight_apply_ne _ fun h : a = a' => (List.nodup_cons.mp hl).1 (h ▸ mem_l)]
    by_cases ha' : a = a'
    · rw [← ha'] at *
      refine Or.inl ⟨l.mem_cons_self, ?_⟩
      rw [prodExtendRight_apply_eq]
    · refine Or.inr ⟨fun h => not_or_intro ha' notMem_l ((List.mem_cons).mp h), ?_⟩
      rw [prodExtendRight_apply_ne _ ha']

section congr

variable [DecidableEq β] [Fintype β]

@[simp]
/-
**Equiv.Perm.sign_prodExtendRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_prodExtendRight (a : α) (σ : Perm β) : sign (prodExtendRight a σ) = s
ign σ
参数：a : α；σ : Perm β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sign_bij`：sign_bij [DecidableEq β] [Fintype β] {f : Perm α} {
g : Perm β} (i : forall x : α, f x != x -> β) (h : forall x hx hx', i (f x) hx' 
= g (i x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.eq_of_prodExtendRight_ne`：eq_of_prodExtendRight_ne {e : Perm 
β₁} {a a' : α₁} {b : β₁} (h : prodExtendRight a e (a', b) != (a', b)) : a' = a
· 使用定理 `Equiv.Perm.prodExtendRight_apply_eq`：prodExtendRight_apply_eq (b : β₁) :
 prodExtendRight a e (a, b) = (a, e b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem sign_prodExtendRight (a : α) (σ : Perm β) : sign (prodExtendRight a σ) = sign σ :=
  sign_bij (fun (ab : α × β) _ => ab.snd)
    (fun ⟨a', b⟩ hab _ => by simp [eq_of_prodExtendRight_ne hab])
    (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab₁ hab₂ h => by
      simpa [eq_of_prodExtendRight_ne hab₁, eq_of_prodExtendRight_ne hab₂] using h)
    fun y hy => ⟨(a, y), by simpa, by simp⟩
/-
**Equiv.Perm.sign_prodCongrRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_prodCongrRight (σ : α -> Perm β) : sign (prodCongrRight σ) = ∏ k, sig
n (σ k)
参数：σ : α -> Perm β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_univ_list`：Finite.exists_univ_list (α) [Finite α] : exists
 l : List α, l.Nodup ∧ forall x : α, x in l
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.prod_prodExtendRight`：prod_prodExtendRight {α : Type*} [Decid
ableEq α] (σ : α -> Perm β) {l : List α} (hl : l.Nodup) (mem_l : forall a, a in 
l) : (l.map fun a => …
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.prod_toFinset`：prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoi
d M] (f : ι -> M) : forall {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.
map f).p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.sign_prodExtendRight`：sign_prodExtendRight (a : α) (σ : Perm 
β) : sign (prodExtendRight a σ) = sign σ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_prodCongrRight (σ : α → Perm β) : sign (prodCongrRight σ) = ∏ k, sign (σ k) := by
  obtain ⟨l, hl, mem_l⟩ := Finite.exists_univ_list α
  have l_to_finset : l.toFinset = Finset.univ := by
    apply eq_top_iff.mpr
    intro b _
    exact List.mem_toFinset.mpr (mem_l b)
  rw [← prod_prodExtendRight σ hl mem_l, map_list_prod sign, List.map_map, ← l_to_finset,
    List.prod_toFinset _ hl]
  simp_rw [← fun a => sign_prodExtendRight a (σ a), Function.comp_def]
/-
**Equiv.Perm.sign_prodCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_prodCongrLeft (σ : α -> Perm β) : sign (prodCongrLeft σ) = ∏ k, sign 
(σ k)
参数：σ : α -> Perm β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.sign_eq_sign_of_equiv`：sign_eq_sign_of_equiv [DecidableEq β] 
[Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β) (h : forall x, e (f x) = g (e 
x)) : sign f = sign g
· 使用定理 `Equiv.Perm.sign_prodCongrRight`：sign_prodCongrRight (σ : α -> Perm β) : 
sign (prodCongrRight σ) = ∏ k, sign (σ k)
-/
theorem sign_prodCongrLeft (σ : α → Perm β) : sign (prodCongrLeft σ) = ∏ k, sign (σ k) := by
  refine (sign_eq_sign_of_equiv _ _ (prodComm β α) ?_).trans (sign_prodCongrRight σ)
  rintro ⟨b, α⟩
  rfl

@[simp]
/-
**Equiv.Perm.sign_permCongr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_permCongr (e : α ≃ β) (p : Perm α) : sign (e.permCongr p) = sign p
参数：e : α ≃ β；p : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sign_eq_sign_of_equiv`：sign_eq_sign_of_equiv [DecidableEq β] 
[Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β) (h : forall x, e (f x) = g (e 
x)) : sign f = sign g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sign_permCongr (e : α ≃ β) (p : Perm α) : sign (e.permCongr p) = sign p :=
  sign_eq_sign_of_equiv _ _ e.symm (by simp)
/-
**Equiv.Perm.sign_trans_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] {β : Type v} [inst_1 : Fintype α] [i
nst_2 : DecidableEq β] [inst_3 : Fintype β]   (f : β ≃ α) (p : Equiv.Perm α) (g 
: α ≃ β),   Equiv.Perm.sign (f.trans (Equiv.trans p g)) = Equiv.Perm.sign p * Eq
uiv.Perm.sign (f.trans g)
参数：f : β ≃ α；p : Equiv.Perm α；g : α ≃ β；f.trans (Equiv.trans p g)；f.trans g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sign_permCongr`：sign_permCongr (e : α ≃ β) (p : Perm α) : sig
n (e.permCongr p) = sign p
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem sign_trans_trans (f : β ≃ α) (p : Perm α) (g : α ≃ β) :
    sign (f.trans (p.trans g)) = sign p * sign (f.trans g) := by
  rw [← sign_permCongr g, ← sign_mul]; congr; ext; simp
/-
**Equiv.Perm.sign_equivCongr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] {β : Type v} [inst_1 : Fintype α] [i
nst_2 : DecidableEq β] [inst_3 : Fintype β]   (f g : α ≃ β) (p : Equiv.Perm α), 
  Equiv.Perm.sign ((f.equivCongr g) p) = Equiv.Perm.sign p * Equiv.Perm.sign (f.
symm.trans g)
参数：f g : α ≃ β；p : Equiv.Perm α；(f.equivCongr g) p；f.symm.trans g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sign_trans_trans`：∀ {α : Type u} [inst : DecidableEq α] {β : 
Type v} [inst_1 : Fintype α] [inst_2 : DecidableEq β] [inst_3 : Fintype β]   (f 
: β ≃ α) (p : Equ…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem sign_equivCongr (f g : α ≃ β) (p : Perm α) :
    sign (f.equivCongr g p) = sign p * sign (f.symm.trans g) :=
  sign_trans_trans ..

@[simp]
/-
**Equiv.Perm.sign_sumCongr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_sumCongr (σa : Perm α) (σb : Perm β) : sign (sumCongr σa σb) = sign σ
a * sign σb
参数：σa : Perm α；σb : Perm β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.swap_induction_on`：swap_induction_on [Finite α] {motive : Per
m α -> Prop} (f : Perm α) (one : motive 1) (swap_mul : forall f x y, x != y -> m
otive f -> motive …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sumCongr_one`：sumCongr_one {α β : Type*} : sumCongr (1 : Perm
 α) (1 : Perm β) = 1
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Equiv.Perm.sumCongr_mul`：sumCongr_mul {α β : Type*} (e : Perm α) (f : Pe
rm β) (g : Perm α) (h : Perm β) : sumCongr e f * sumCongr g h = sumCongr (e * g)
 (f * h)
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.sumCongr_swap_one`：sumCongr_swap_one {α β : Type*} [Decidable
Eq α] [DecidableEq β] (i j : α) : sumCongr (Equiv.swap i j) (1 : Perm β) = Equiv
.swap (Sum.inl i) …
· 使用定理 `Equiv.Perm.sign_swap`：sign_swap {x y : α} (h : x != y) : sign (swap x y)
 = -1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Equiv.Perm.sumCongr_one_swap`：sumCongr_one_swap {α β : Type*} [Decidable
Eq α] [DecidableEq β] (i j : β) : sumCongr (1 : Perm α) (Equiv.swap i j) = Equiv
.swap (Sum.inr i) …
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem sign_sumCongr (σa : Perm α) (σb : Perm β) : sign (sumCongr σa σb) = sign σa * sign σb := by
  suffices sign (sumCongr σa (1 : Perm β)) = sign σa ∧ sign (sumCongr (1 : Perm α) σb) = sign σb
    by rw [← this.1, ← this.2, ← sign_mul, sumCongr_mul, one_mul, mul_one]
  constructor
  · induction σa using swap_induction_on with
    | one => simp
    | swap_mul σa' a₁ a₂ ha ih =>
      rw [← one_mul (1 : Perm β), ← sumCongr_mul, sign_mul, sign_mul, ih, sumCongr_swap_one,
        sign_swap ha, sign_swap (Sum.inl_injective.ne_iff.mpr ha)]
  · induction σb using swap_induction_on with
    | one => simp
    | swap_mul σb' b₁ b₂ hb ih =>
      rw [← one_mul (1 : Perm α), ← sumCongr_mul, sign_mul, sign_mul, ih, sumCongr_one_swap,
        sign_swap hb, sign_swap (Sum.inr_injective.ne_iff.mpr hb)]

@[simp]
/-
**Equiv.Perm.sign_subtypeCongr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_subtypeCongr {p : α -> Prop} [DecidablePred p] (ep : Perm { a // p a 
}) (en : Perm { a // ¬p a }) : sign (ep.subtypeCongr en) = sign ep * sign en
参数：ep : Perm { a // p a }；en : Perm { a // ¬p a }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_permCongr`：sign_permCongr (e : α ≃ β) (p : Perm α) : sig
n (e.permCongr p) = sign p
· 使用定理 `Equiv.Perm.sign_sumCongr`：sign_sumCongr (σa : Perm α) (σb : Perm β) : si
gn (sumCongr σa σb) = sign σa * sign σb
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_subtypeCongr {p : α → Prop} [DecidablePred p] (ep : Perm { a // p a })
    (en : Perm { a // ¬p a }) : sign (ep.subtypeCongr en) = sign ep * sign en := by
  simp [subtypeCongr]

@[simp]
/-
**Equiv.Perm.sign_extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_extendDomain (e : Perm α) {p : β -> Prop} [DecidablePred p] (f : α ≃ 
Subtype p) : Equiv.Perm.sign (e.extendDomain f) = Equiv.Perm.sign e
参数：e : Perm α；f : α ≃ Subtype p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.Perm.sign_subtypeCongr`：sign_subtypeCongr {p : α -> Prop} [Decidab
lePred p] (ep : Perm { a // p a }) (en : Perm { a // ¬p a }) : sign (ep.subtypeC
ongr en) = sign ep…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.sign_permCongr`：sign_permCongr (e : α ≃ β) (p : Perm α) : sig
n (e.permCongr p) = sign p
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_extendDomain (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) :
    Equiv.Perm.sign (e.extendDomain f) = Equiv.Perm.sign e := by
  simp only [Equiv.Perm.extendDomain, sign_subtypeCongr, sign_permCongr, sign_refl, mul_one]

@[simp]
/-
**Equiv.Perm.sign_ofSubtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sign_ofSubtype {p : α -> Prop} [DecidablePred p] [Fintype (Subtype p)] (f 
: Equiv.Perm (Subtype p)) : sign (ofSubtype f) = sign f
参数：Subtype p；f : Equiv.Perm (Subtype p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sign_extendDomain`：sign_extendDomain (e : Perm α) {p : β -> P
rop} [DecidablePred p] (f : α ≃ Subtype p) : Equiv.Perm.sign (e.extendDomain f) 
= Equiv.Perm.sign …
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem sign_ofSubtype {p : α → Prop} [DecidablePred p] [Fintype (Subtype p)]
    (f : Equiv.Perm (Subtype p)) : sign (ofSubtype f) = sign f :=
  sign_extendDomain f (Equiv.refl (Subtype p))

end congr

end SignType.sign

@[simp]
/-
**Equiv.Perm.viaFintypeEmbedding_sign** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：viaFintypeEmbedding_sign [Fintype α] [Fintype β] [DecidableEq β] (e : Equi
v.Perm α) (f : α ↪ β) : sign (e.viaFintypeEmbedding f) = sign e
参数：e : Equiv.Perm α；f : α ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_extendDomain`：sign_extendDomain (e : Perm α) {p : β -> P
rop} [DecidablePred p] (f : α ≃ Subtype p) : Equiv.Perm.sign (e.extendDomain f) 
= Equiv.Perm.sign …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem viaFintypeEmbedding_sign
    [Fintype α] [Fintype β] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β) :
    sign (e.viaFintypeEmbedding f) = sign e := by
  simp [viaFintypeEmbedding]

section Finset

variable [Fintype α]

/-- Permutations of a given sign. -/
/-
**Equiv.Perm.ofSign** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSign (s : Intˣ) : Finset (Perm α)
参数：s : Intˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Permutations of a given sign.
-/
def ofSign (s : ℤˣ) : Finset (Perm α) := univ.filter (sign · = s)

@[simp]
/-
**Equiv.Perm.mem_ofSign** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_ofSign {s : Intˣ} {σ : Perm α} : σ in ofSign s ↔ σ.sign = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.ofSign.eq_1`：∀ {α : Type u} [inst : DecidableEq α] [inst_1 : 
Fintype α] (s : ℤˣ), Equiv.Perm.ofSign s = {x | Equiv.Perm.sign x = s}
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ofSign {s : ℤˣ} {σ : Perm α} : σ ∈ ofSign s ↔ σ.sign = s := by
  rw [ofSign, mem_filter, and_iff_right (mem_univ σ)]
/-
**Equiv.Perm.ofSign_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSign_disjoint : _root_.Disjoint (ofSign 1 : Finset (Perm α)) (ofSign (-1
))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_iff_ne`：disjoint_iff_ne : Disjoint s t ↔ forall a in s, 
forall b in t, a != b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Equiv.Perm.mem_ofSign`：mem_ofSign {s : Intˣ} {σ : Perm α} : σ in ofSign 
s ↔ σ.sign = s
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
-/
lemma ofSign_disjoint : _root_.Disjoint (ofSign 1 : Finset (Perm α)) (ofSign (-1)) := by
  rw [Finset.disjoint_iff_ne]
  rintro σ hσ τ hτ rfl
  rw [mem_ofSign] at hσ hτ
  have := hσ.symm.trans hτ
  contradiction
/-
**Equiv.Perm.ofSign_disjUnion** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSign_disjUnion : (ofSign 1).disjUnion (ofSign (-1)) ofSign_disjoint = (u
niv : Finset (Perm α))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用引理 `Equiv.Perm.ofSign_disjoint`：ofSign_disjoint : _root_.Disjoint (ofSign 1 
: Finset (Perm α)) (ofSign (-1))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofSign_disjUnion :
    (ofSign 1).disjUnion (ofSign (-1)) ofSign_disjoint = (univ : Finset (Perm α)) := by
  ext σ
  simp_rw [mem_disjUnion, mem_ofSign, Int.units_eq_one_or, mem_univ]

end Finset

end Equiv.Perm

