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
/--
Definition of `modSwap` / `modSwap` 的定义

English:
definition modSwap
  signature: (i j : α)
  body: ⟨fun σ τ => σ = τ ∨ σ = swap i j * τ, fun σ => Or.inl (refl σ), fun {σ τ} h =>
    Or.casesOn h (fun h => Or.inl h.symm) fun h => Or.inr (by rw [h, swap_mul_self_mul]),
    fun {σ τ υ} hστ hτυ => by
    rcases hστ with hστ | hστ <;> rcases hτυ with hτυ | hτυ <;>
      (try rw [hστ, hτυ, swap_mul_sel

中文:
定义 modSwap
  签名: (i j : α)
  定义体: ⟨fun σ τ => σ = τ ∨ σ = swap i j * τ, fun σ => Or.inl (refl σ), fun {σ τ} h =>
    Or.casesOn h (fun h => Or.inl h.symm) fun h => Or.inr (by rw [h, swap_mul_self_mul]),
    fun {σ τ υ} hστ hτυ => by
    rcases hστ with hστ | hστ <;> rcases hτυ with hτυ | hτυ <;>
      (try rw [hστ, hτυ, swap_mul_sel

Depends on / 依赖: Or.casesOn, Or.inl, Or.inr, casesOn, h.symm, swap_mul_self_mul
-/
def modSwap (i j : α) : Setoid (Perm α) :=
  ⟨fun σ τ => σ = τ ∨ σ = swap i j * τ, fun σ => Or.inl (refl σ), fun {σ τ} h =>
    Or.casesOn h (fun h => Or.inl h.symm) fun h => Or.inr (by rw [h, swap_mul_self_mul]),
    fun {σ τ υ} hστ hτυ => by
    rcases hστ with hστ | hστ <;> rcases hτυ with hτυ | hτυ <;>
      (try rw [hστ, hτυ, swap_mul_self_mul]) <;>
      simp [hστ, hτυ]⟩

noncomputable instance {α : Type*} [Fintype α] [DecidableEq α] (i j : α) :
    DecidableRel (modSwap i j).r :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/--
Definition of `swapFactorsAux` / `swapFactorsAux` 的定义

English:
definition swapFactorsAux
  signature: :
  body: swapFactorsAux l (swap x (f x) * f) fun {y} hy =>
          have : f y != y ∧ y != x := ne_and_ne_of_swap_mul_apply_ne_self hy
          List.mem_of_ne_of_mem this.2 (h this.1)
      ⟨swap x (f x)::m.1, by
        rw [List.prod_cons]; rw [m.2.1]; rw [← mul_assoc]; rw [mul_def (swap x (f x))]; rw [sw

中文:
定义 swapFactorsAux
  签名: :
  定义体: swapFactorsAux l (swap x (f x) * f) fun {y} hy =>
          have : f y != y ∧ y != x := ne_and_ne_of_swap_mul_apply_ne_self hy
          List.mem_of_ne_of_mem this.2 (h this.1)
      ⟨swap x (f x)::m.1, by
        rw [List.prod_cons]; rw [m.2.1]; rw [← mul_assoc]; rw [mul_def (swap x (f x))]; rw [sw

Depends on / 依赖: List.mem_cons, List.mem_of_ne_of_mem, List.prod_cons, mem_cons, mem_of_ne_of_mem, mul_assoc, mul_def, ne_and_ne_of_swap_mul_apply_ne_self, one_def, one_mul, prod_cons, swapFactorsAux, swap_swap
-/
def swapFactorsAux :
    forall (l : List α) (f : Perm α),
      (forall {x}, f x != x -> x in l) -> { l : List (Perm α) // l.prod = f ∧ forall g in l, IsSwap g }
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
          have : f y != y ∧ y != x := ne_and_ne_of_swap_mul_apply_ne_self hy
          List.mem_of_ne_of_mem this.2 (h this.1)
      ⟨swap x (f x)::m.1, by
        rw [List.prod_cons]; rw [m.2.1]; rw [← mul_assoc]; rw [mul_def (swap x (f x))]; rw [swap_swap]; rw [← one_def]; rw [one_mul],
        fun {_} hg => ((List.mem_cons).1 hg).elim (fun h => ⟨x, f x, hfx, h⟩) (m.2.2 _)⟩

/--
Definition of `swapFactors` / `swapFactors` 的定义

English:
definition swapFactors
  signature: [Fintype α] [LinearOrder α] (f : Perm α)
  body: swapFactorsAux ((@univ α _).sort) f fun {_ _} => (mem_sort _).2 (mem_univ _)

中文:
定义 swapFactors
  签名: [Fintype α] [LinearOrder α] (f : Perm α)
  定义体: swapFactorsAux ((@univ α _).sort) f fun {_ _} => (mem_sort _).2 (mem_univ _)

Depends on / 依赖: mem_sort, mem_univ, swapFactorsAux
-/
def swapFactors [Fintype α] [LinearOrder α] (f : Perm α) :
    { l : List (Perm α) // l.prod = f ∧ forall g in l, IsSwap g } :=
  swapFactorsAux ((@univ α _).sort) f fun {_ _} => (mem_sort _).2 (mem_univ _)

/--
Definition of `truncSwapFactors` / `truncSwapFactors` 的定义

English:
definition truncSwapFactors
  signature: [Fintype α] (f : Perm α)
  body: Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (swapFactorsAux l f (h _)))
    (show forall x, f x != x -> x in (@univ α _).1 from fun _ _ => mem_univ _)

中文:
定义 truncSwapFactors
  签名: [Fintype α] (f : Perm α)
  定义体: Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (swapFactorsAux l f (h _)))
    (show forall x, f x != x -> x in (@univ α _).1 from fun _ _ => mem_univ _)

Depends on / 依赖: Quotient, Quotient.recOnSubsingleton, Trunc.mk, mem_univ, recOnSubsingleton, swapFactorsAux
-/
def truncSwapFactors [Fintype α] (f : Perm α) :
    Trunc { l : List (Perm α) // l.prod = f ∧ forall g in l, IsSwap g } :=
  Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (swapFactorsAux l f (h _)))
    (show forall x, f x != x -> x in (@univ α _).1 from fun _ _ => mem_univ _)

/-- An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_elim]
/--
theorem `swap_induction_on` / 定理 `swap_induction_on`

English:
theorem swap_induction_on
  statement: [Finite α] {motive : Perm α -> Prop} (f : Perm α)
  proof: by
  cases nonempty_fintype α
  obtain ⟨l, hl⟩ := (truncSwapFactors f).out
  induction l generalizing f with
  | nil =>
    simp only [one, hl.left.symm, List.prod_nil]
  | cons g l ih =>
    rcases hl.2 g (by simp) with ⟨x, y, hxy⟩
    rw [← hl.1]; rw [List.prod_cons]; rw [hxy.2]
    exact swap_mul

中文:
定理 swap_induction_on
  结论: [Finite α] {motive : Perm α -> 命题} (f : Perm α)
  证明: by
  cases nonempty_fintype α
  obtain ⟨l, hl⟩ := (truncSwapFactors f).out
  induction l generalizing f with
  | nil =>
    simp only [one, hl.left.symm, List.prod_nil]
  | cons g l ih =>
    rcases hl.2 g (by simp) with ⟨x, y, hxy⟩
    rw [← hl.1]; rw [List.prod_cons]; rw [hxy.2]
    exact swap_mul

Depends on / 依赖: List.mem_cons_of_mem, List.prod_cons, List.prod_nil, generalizing, hl.left.symm, mem_cons_of_mem, nonempty_fintype, prod_cons, prod_nil, swap_mul, truncSwapFactors
-/
theorem swap_induction_on [Finite α] {motive : Perm α -> Prop} (f : Perm α)
    (one : motive 1) (swap_mul : forall f x y, x != y -> motive f -> motive (swap x y * f)) : motive f := by
  cases nonempty_fintype α
  obtain ⟨l, hl⟩ := (truncSwapFactors f).out
  induction l generalizing f with
  | nil =>
    simp only [one, hl.left.symm, List.prod_nil]
  | cons g l ih =>
    rcases hl.2 g (by simp) with ⟨x, y, hxy⟩
    rw [← hl.1]; rw [List.prod_cons]; rw [hxy.2]
    exact swap_mul _ _ _ hxy.1 (ih _ ⟨rfl, fun v hv => hl.2 _ (List.mem_cons_of_mem _ hv)⟩)

/--
theorem `mclosure_isSwap` / 定理 `mclosure_isSwap`

English:
theorem mclosure_isSwap
  given: [Finite α]
  statement: Submonoid.closure { σ : Perm α | IsSwap σ } = ⊤
  proof: by
  cases nonempty_fintype α
  refine top_unique fun x _ => ?_
  obtain ⟨h1, h2⟩ := (truncSwapFactors x).out.prop
  rw [← h1]
  exact Submonoid.list_prod_mem _ fun y hy => Submonoid.subset_closure (h2 y hy)

中文:
定理 mclosure_isSwap
  条件: [Finite α]
  结论: Submonoid.closure { σ : Perm α | IsSwap σ } = ⊤
  证明: by
  cases nonempty_fintype α
  refine top_unique fun x _ => ?_
  obtain ⟨h1, h2⟩ := (truncSwapFactors x).out.prop
  rw [← h1]
  exact Submonoid.list_prod_mem _ fun y hy => Submonoid.subset_closure (h2 y hy)

Depends on / 依赖: Submonoid, Submonoid.list_prod_mem, Submonoid.subset_closure, list_prod_mem, nonempty_fintype, out.prop, subset_closure, top_unique, truncSwapFactors
-/
theorem mclosure_isSwap [Finite α] : Submonoid.closure { σ : Perm α | IsSwap σ } = ⊤ := by
  cases nonempty_fintype α
  refine top_unique fun x _ => ?_
  obtain ⟨h1, h2⟩ := (truncSwapFactors x).out.prop
  rw [← h1]
  exact Submonoid.list_prod_mem _ fun y hy => Submonoid.subset_closure (h2 y hy)

/--
theorem `closure_isSwap` / 定理 `closure_isSwap`

English:
theorem closure_isSwap
  given: [Finite α]
  statement: Subgroup.closure { σ : Perm α | IsSwap σ } = ⊤
  proof: Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_isSwap

中文:
定理 closure_isSwap
  条件: [Finite α]
  结论: Subgroup.closure { σ : Perm α | IsSwap σ } = ⊤
  证明: Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_isSwap

Depends on / 依赖: Subgroup, Subgroup.closure_eq_top_of_mclosure_eq_top, closure_eq_top_of_mclosure_eq_top, mclosure_isSwap
-/
theorem closure_isSwap [Finite α] : Subgroup.closure { σ : Perm α | IsSwap σ } = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_isSwap

/--
theorem `mclosure_swap_castSucc_succ` / 定理 `mclosure_swap_castSucc_succ`

English:
theorem mclosure_swap_castSucc_succ
  given: (n : Nat)
  proof: by
  apply top_unique
  rw [← mclosure_isSwap]; rw [Submonoid.closure_le]
  rintro _ ⟨i, j, ne, rfl⟩
  wlog lt : i < j generalizing i j
  · rw [swap_comm]; exact this _ _ ne.symm (ne.lt_or_gt.resolve_left lt)
  induction j using Fin.induction with
  | zero => cases lt
  | succ j ih =>
    have mem :

中文:
定理 mclosure_swap_castSucc_succ
  条件: (n : 自然数)
  证明: by
  apply top_unique
  rw [← mclosure_isSwap]; rw [Submonoid.closure_le]
  rintro _ ⟨i, j, ne, rfl⟩
  wlog lt : i < j generalizing i j
  · rw [swap_comm]; exact this _ _ ne.symm (ne.lt_or_gt.resolve_left lt)
  induction j using Fin.induction with
  | zero => cases lt
  | succ j ih =>
    have mem :

Depends on / 依赖: Fin.induction, Fin.le_castSucc_iff.mpr, Set.range, Submonoid, Submonoid.closure, Submonoid.closure_le, Submonoid.subset_closure, castSucc, closure, closure_le, eq_or_lt, generalizing, i.castSucc, i.succ, j.castSucc, j.succ, le_castSucc_iff, lt_or_gt, mclosure_isSwap, ne.lt_or_gt.resolve_left
-/
theorem mclosure_swap_castSucc_succ (n : Nat) :
    Submonoid.closure (Set.range fun i : Fin n => swap i.castSucc i.succ) = ⊤ := by
  apply top_unique
  rw [← mclosure_isSwap]; rw [Submonoid.closure_le]
  rintro _ ⟨i, j, ne, rfl⟩
  wlog lt : i < j generalizing i j
  · rw [swap_comm]; exact this _ _ ne.symm (ne.lt_or_gt.resolve_left lt)
  induction j using Fin.induction with
  | zero => cases lt
  | succ j ih =>
    have mem : swap j.castSucc j.succ in Submonoid.closure
      (Set.range fun (i : Fin n) => swap i.castSucc i.succ) := Submonoid.subset_closure ⟨_, rfl⟩
    obtain rfl | lts := (Fin.le_castSucc_iff.mpr lt).eq_or_lt
    · exact mem
    rw [swap_comm]; rw [← swap_mul_swap_mul_swap (y := Fin.castSucc j) lts.ne lt.ne]
    exact mul_mem (mul_mem mem <| ih lts.ne lts) mem

/-- Like `swap_induction_on`, but with the composition on the right of `f`.

An induction principle for permutations. If `motive` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `motive` holds for all permutations. -/
@[elab_as_elim]
/--
theorem `swap_induction_on'` / 定理 `swap_induction_on'`

English:
theorem swap_induction_on'
  statement: [Finite α] {motive : Perm α -> Prop} (f : Perm α) (one : motive 1)
  proof: inv_inv f ▸ swap_induction_on f⁻¹ one fun f => mul_swap f⁻¹

中文:
定理 swap_induction_on'
  结论: [Finite α] {motive : Perm α -> 命题} (f : Perm α) (one : motive 1)
  证明: inv_inv f ▸ swap_induction_on f⁻¹ one fun f => mul_swap f⁻¹

Depends on / 依赖: EquivLike, EquivLike.comp_surjective, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.surjective_rangeRestrict, coe_coe, coe_comp, comp_surjective, inv_inv, mulMap, mul_swap, simp_rw, surjective_rangeRestrict, swap_induction_on
-/
theorem swap_induction_on' [Finite α] {motive : Perm α -> Prop} (f : Perm α) (one : motive 1)
    (mul_swap : forall f x y, x != y -> motive f -> motive (f * swap x y)) : motive f :=
  inv_inv f ▸ swap_induction_on f⁻¹ one fun f => mul_swap f⁻¹

/--
theorem `isConj_swap` / 定理 `isConj_swap`

English:
theorem isConj_swap
  given: {w x y z : α} (hwx : w != x) (hyz : y != z)
  statement: IsConj (swap w x) (swap y z)
  proof: isConj_iff.2
    (have h :
      forall {y z : α},
        y != z -> w != z -> swap w y * swap x z * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
      fun {y z} hyz hwz => by
      rw [mul_inv_rev]; rw [swap_inv]; rw [swap_inv]; rw [mul_assoc (swap w y)]; rw [mul_assoc (swap w y)]; rw [←
      

中文:
定理 isConj_swap
  条件: {w x y z : α} (hwx : w != x) (hyz : y != z)
  结论: IsConj (swap w x) (swap y z)
  证明: isConj_iff.2
    (have h :
      forall {y z : α},
        y != z -> w != z -> swap w y * swap x z * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
      fun {y z} hyz hwz => by
      rw [mul_inv_rev]; rw [swap_inv]; rw [swap_inv]; rw [mul_assoc (swap w y)]; rw [mul_assoc (swap w y)]; rw [←
      

Depends on / 依赖: hwz.symm, hyz.symm, isConj_iff, mul_assoc, mul_inv_rev, swap_comm, swap_inv, swap_mul_swap_mul_swap
-/
theorem isConj_swap {w x y z : α} (hwx : w != x) (hyz : y != z) : IsConj (swap w x) (swap y z) :=
  isConj_iff.2
    (have h :
      forall {y z : α},
        y != z -> w != z -> swap w y * swap x z * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
      fun {y z} hyz hwz => by
      rw [mul_inv_rev]; rw [swap_inv]; rw [swap_inv]; rw [mul_assoc (swap w y)]; rw [mul_assoc (swap w y)]; rw [←
        mul_assoc _ (swap x z)]; rw [swap_mul_swap_mul_swap hwx hwz]; rw [← mul_assoc]; rw [swap_mul_swap_mul_swap hwz.symm hyz.symm]
    if hwz : w = z then
      have hwy : w != y := by rw [hwz]; exact hyz.symm
      ⟨swap w z * swap x y, by rw [swap_comm y z, h hyz.symm hwy]⟩
    else ⟨swap w y * swap x z, h hyz hwz⟩)

/--
Definition of `finPairsLT` / `finPairsLT` 的定义

English:
definition finPairsLT
  signature: (n : Nat)
  body: (univ : Finset (Fin n)).sigma fun a => (range a).attachFin fun _ hm => (mem_range.1 hm).trans a.2

中文:
定义 finPairsLT
  签名: (n : 自然数)
  定义体: (univ : Finset (Fin n)).sigma fun a => (range a).attachFin fun _ hm => (mem_range.1 hm).trans a.2

Depends on / 依赖: Algebra, Algebra.smul_def, Finset, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, LinearMap, LinearMap.codRestrict_apply, LinearMap.coe_comp, SetLike, SetLike.val_smul, Subtype, Subtype.val_injective, attachFin, codRestrict_apply, coe_coe, coe_comp, coe_ofEq_apply
-/
def finPairsLT (n : Nat) : Finset (Σ _ : Fin n, Fin n) :=
  (univ : Finset (Fin n)).sigma fun a => (range a).attachFin fun _ hm => (mem_range.1 hm).trans a.2

/--
theorem `mem_finPairsLT` / 定理 `mem_finPairsLT`

English:
theorem mem_finPairsLT
  given: {n : Nat} {a : Σ _ : Fin n, Fin n}
  statement: a in finPairsLT n ↔ a.2 < a.1
  proof: by
  simp only [finPairsLT, Fin.lt_def, true_and, mem_attachFin, mem_range, mem_univ,
    mem_sigma]

中文:
定理 mem_finPairsLT
  条件: {n : 自然数} {a : Σ _ : Fin n, Fin n}
  结论: a in finPairsLT n ↔ a.2 < a.1
  证明: by
  simp only [finPairsLT, Fin.lt_def, true_and, mem_attachFin, mem_range, mem_univ,
    mem_sigma]

Depends on / 依赖: Fin.lt_def, _tmul, finPairsLT, lTensorOne, lt_def, mem_attachFin, mem_range, mem_sigma, mem_univ, true_and
-/
theorem mem_finPairsLT {n : Nat} {a : Σ _ : Fin n, Fin n} : a in finPairsLT n ↔ a.2 < a.1 := by
  simp only [finPairsLT, Fin.lt_def, true_and, mem_attachFin, mem_range, mem_univ,
    mem_sigma]

/--
Definition of `signAux` / `signAux` 的定义

English:
definition signAux
  signature: {n : Nat} (a : Perm (Fin n))
  body: ∏ x in finPairsLT n, if a x.1 <= a x.2 then -1 else 1

@[simp]

中文:
定义 signAux
  签名: {n : 自然数} (a : Perm (Fin n))
  定义体: ∏ x in finPairsLT n, if a x.1 <= a x.2 then -1 else 1

@[simp]

Depends on / 依赖: finPairsLT
-/
def signAux {n : Nat} (a : Perm (Fin n)) : Intˣ :=
  ∏ x in finPairsLT n, if a x.1 <= a x.2 then -1 else 1

@[simp]
/--
theorem `signAux_one` / 定理 `signAux_one`

English:
theorem signAux_one
  given: (n : Nat)
  statement: signAux (1 : Perm (Fin n)) = 1
  proof: by
  unfold signAux
  conv => rhs; rw [← @Finset.prod_const_one _ _ (finPairsLT n)]
  exact Finset.prod_congr rfl fun a ha => if_neg (mem_finPairsLT.1 ha).not_ge

中文:
定理 signAux_one
  条件: (n : 自然数)
  结论: signAux (1 : Perm (Fin n)) = 1
  证明: by
  unfold signAux
  conv => rhs; rw [← @Finset.prod_const_one _ _ (finPairsLT n)]
  exact Finset.prod_congr rfl fun a ha => if_neg (mem_finPairsLT.1 ha).not_ge

Depends on / 依赖: Finset, Finset.prod_congr, Finset.prod_const_one, finPairsLT, if_neg, mem_finPairsLT, not_ge, prod_congr, prod_const_one, signAux
-/
theorem signAux_one (n : Nat) : signAux (1 : Perm (Fin n)) = 1 := by
  unfold signAux
  conv => rhs; rw [← @Finset.prod_const_one _ _ (finPairsLT n)]
  exact Finset.prod_congr rfl fun a ha => if_neg (mem_finPairsLT.1 ha).not_ge

/--
Definition of `signBijAux` / `signBijAux` 的定义

English:
definition signBijAux
  signature: {n : Nat} (f : Perm (Fin n)) (a : Σ _ : Fin n, Fin n)
  body: if _ : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩

中文:
定义 signBijAux
  签名: {n : 自然数} (f : Perm (Fin n)) (a : Σ _ : Fin n, Fin n)
  定义体: if _ : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩
-/
def signBijAux {n : Nat} (f : Perm (Fin n)) (a : Σ _ : Fin n, Fin n) : Σ _ : Fin n, Fin n :=
  if _ : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩

/--
theorem `signBijAux_injOn` / 定理 `signBijAux_injOn`

English:
theorem signBijAux_injOn
  given: {n : Nat} {f : Perm (Fin n)}
  proof: by
  rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb h
  dsimp [signBijAux] at h
  rw [Finset.mem_coe]; rw [mem_finPairsLT] at *
  have : ¬b₁ < b₂ := hb.le.not_gt
  split_ifs at h <;>
  simp_all only [not_lt, Sigma.mk.inj_iff, (Equiv.injective f).eq_iff, heq_eq_eq]
  · exact absurd this (not_le.mpr ha)
  · exact abs

中文:
定理 signBijAux_injOn
  条件: {n : 自然数} {f : Perm (Fin n)}
  证明: by
  rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb h
  dsimp [signBijAux] at h
  rw [Finset.mem_coe]; rw [mem_finPairsLT] at *
  have : ¬b₁ < b₂ := hb.le.not_gt
  split_ifs at h <;>
  simp_all only [not_lt, Sigma.mk.inj_iff, (Equiv.injective f).eq_iff, heq_eq_eq]
  · exact absurd this (not_le.mpr ha)
  · exact abs

Depends on / 依赖: Equiv.injective, Finset, Finset.mem_coe, Sigma.mk.inj_iff, absurd, eq_iff, hb.le.not_gt, heq_eq_eq, inj_iff, injective, mem_coe, mem_finPairsLT, not_gt, not_le, not_le.mpr, not_lt, signBijAux, split_ifs
-/
theorem signBijAux_injOn {n : Nat} {f : Perm (Fin n)} :
    (finPairsLT n : Set (Σ _, Fin n)).InjOn (signBijAux f) := by
  rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb h
  dsimp [signBijAux] at h
  rw [Finset.mem_coe]; rw [mem_finPairsLT] at *
  have : ¬b₁ < b₂ := hb.le.not_gt
  split_ifs at h <;>
  simp_all only [not_lt, Sigma.mk.inj_iff, (Equiv.injective f).eq_iff, heq_eq_eq]
  · exact absurd this (not_le.mpr ha)
  · exact absurd this (not_le.mpr ha)

/--
theorem `signBijAux_surj` / 定理 `signBijAux_surj`

English:
theorem signBijAux_surj
  given: {n : Nat} {f : Perm (Fin n)}
  proof: fun ⟨a₁, a₂⟩ ha =>
    if hxa : f.symm a₂ < f.symm a₁ then
      ⟨⟨f.symm a₁, f.symm a₂⟩, mem_finPairsLT.2 hxa, by
       simp [signBijAux, if_pos (mem_finPairsLT.1 ha)]⟩
    else
      ⟨⟨f.symm a₂, f.symm a₁⟩,
mem_finPairsLT.2
          (le_of_not_gt hxa).lt_of_ne fun h => by
            simp [mem_

中文:
定理 signBijAux_surj
  条件: {n : 自然数} {f : Perm (Fin n)}
  证明: fun ⟨a₁, a₂⟩ ha =>
    if hxa : f.symm a₂ < f.symm a₁ then
      ⟨⟨f.symm a₁, f.symm a₂⟩, mem_finPairsLT.2 hxa, by
       simp [signBijAux, if_pos (mem_finPairsLT.1 ha)]⟩
    else
      ⟨⟨f.symm a₂, f.symm a₁⟩,
mem_finPairsLT.2
          (le_of_not_gt hxa).lt_of_ne fun h => by
            simp [mem_

Depends on / 依赖: f.symm, if_neg, if_pos, injective, le.not_gt, le_of_not_gt, lt_of_ne, mem_finPairsLT, not_gt, signBijAux
-/
theorem signBijAux_surj {n : Nat} {f : Perm (Fin n)} :
    forall a in finPairsLT n, exists b in finPairsLT n, signBijAux f b = a :=
  fun ⟨a₁, a₂⟩ ha =>
    if hxa : f.symm a₂ < f.symm a₁ then
      ⟨⟨f.symm a₁, f.symm a₂⟩, mem_finPairsLT.2 hxa, by
       simp [signBijAux, if_pos (mem_finPairsLT.1 ha)]⟩
    else
      ⟨⟨f.symm a₂, f.symm a₁⟩,
mem_finPairsLT.2
          (le_of_not_gt hxa).lt_of_ne fun h => by
            simp [mem_finPairsLT, f⁻¹.injective h] at ha, by
              simp [signBijAux, if_neg (mem_finPairsLT.1 ha).le.not_gt]⟩

/--
theorem `signBijAux_mem` / 定理 `signBijAux_mem`

English:
theorem signBijAux_mem
  given: {n : Nat} {f : Perm (Fin n)}
  proof: fun ⟨a₁, a₂⟩ ha => by
    unfold signBijAux
    split_ifs with h
    · exact mem_finPairsLT.2 h
    · exact mem_finPairsLT.2
        ((le_of_not_gt h).lt_of_ne fun h => (mem_finPairsLT.1 ha).ne (f.injective h.symm))

@[simp]

中文:
定理 signBijAux_mem
  条件: {n : 自然数} {f : Perm (Fin n)}
  证明: fun ⟨a₁, a₂⟩ ha => by
    unfold signBijAux
    split_ifs with h
    · exact mem_finPairsLT.2 h
    · exact mem_finPairsLT.2
        ((le_of_not_gt h).lt_of_ne fun h => (mem_finPairsLT.1 ha).ne (f.injective h.symm))

@[simp]

Depends on / 依赖: f.injective, h.symm, injective, le_of_not_gt, lt_of_ne, mem_finPairsLT, signBijAux, split_ifs
-/
theorem signBijAux_mem {n : Nat} {f : Perm (Fin n)} :
    forall a : Σ _ : Fin n, Fin n, a in finPairsLT n -> signBijAux f a in finPairsLT n :=
  fun ⟨a₁, a₂⟩ ha => by
    unfold signBijAux
    split_ifs with h
    · exact mem_finPairsLT.2 h
    · exact mem_finPairsLT.2
        ((le_of_not_gt h).lt_of_ne fun h => (mem_finPairsLT.1 ha).ne (f.injective h.symm))

@[simp]
/--
theorem `signAux_inv` / 定理 `signAux_inv`

English:
theorem signAux_inv
  given: {n : Nat} (f : Perm (Fin n))
  statement: signAux f⁻¹ = signAux f
  proof: prod_nbij (signBijAux f⁻¹) signBijAux_mem signBijAux_injOn signBijAux_surj fun ⟨a, b⟩ hab => by
    by_cases h : f.symm b < f.symm a
    · simp_all [signBijAux, (mem_finPairsLT.1 hab).not_ge]
    · simp_all [signBijAux, dif_neg h, (mem_finPairsLT.1 hab).le]

中文:
定理 signAux_inv
  条件: {n : 自然数} (f : Perm (Fin n))
  结论: signAux f⁻¹ = signAux f
  证明: prod_nbij (signBijAux f⁻¹) signBijAux_mem signBijAux_injOn signBijAux_surj fun ⟨a, b⟩ hab => by
    by_cases h : f.symm b < f.symm a
    · simp_all [signBijAux, (mem_finPairsLT.1 hab).not_ge]
    · simp_all [signBijAux, dif_neg h, (mem_finPairsLT.1 hab).le]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, LinearMap, LinearMap.codRestrict_apply, LinearMap.coe_comp, SetLike, SetLike.val_smul, Subtype, Subtype.val_injective, codRestrict_apply, coe_coe, coe_comp, coe_ofEq_apply, commutes
-/
theorem signAux_inv {n : Nat} (f : Perm (Fin n)) : signAux f⁻¹ = signAux f :=
  prod_nbij (signBijAux f⁻¹) signBijAux_mem signBijAux_injOn signBijAux_surj fun ⟨a, b⟩ hab => by
    by_cases h : f.symm b < f.symm a
    · simp_all [signBijAux, (mem_finPairsLT.1 hab).not_ge]
    · simp_all [signBijAux, dif_neg h, (mem_finPairsLT.1 hab).le]

/--
theorem `signAux_mul` / 定理 `signAux_mul`

English:
theorem signAux_mul
  given: {n : Nat} (f g : Perm (Fin n))
  statement: signAux (f * g) = signAux f * signAux g
  proof: by
  rw [← signAux_inv g]
  unfold signAux
  rw [← prod_mul_distrib]
  refine prod_nbij (signBijAux g) signBijAux_mem signBijAux_injOn signBijAux_surj ?_
  rintro ⟨a, b⟩ hab
  dsimp only [signBijAux]
  rw [mul_apply]; rw [mul_apply]
  rw [mem_finPairsLT] at hab
  by_cases hg : g b < g a
  · simp [*]

中文:
定理 signAux_mul
  条件: {n : 自然数} (f g : Perm (Fin n))
  结论: signAux (f * g) = signAux f * signAux g
  证明: by
  rw [← signAux_inv g]
  unfold signAux
  rw [← prod_mul_distrib]
  refine prod_nbij (signBijAux g) signBijAux_mem signBijAux_injOn signBijAux_surj ?_
  rintro ⟨a, b⟩ hab
  dsimp only [signBijAux]
  rw [mul_apply]; rw [mul_apply]
  rw [mem_finPairsLT] at hab
  by_cases hg : g b < g a
  · simp [*]

Depends on / 依赖: _tmul, f.injective.ne, g.injective.ne, hab.ne, injective, le_of_lt, lt_or_gt, mem_finPairsLT, mul_apply, not_le_of_gt, not_lt_of_ge, prod_mul_distrib, prod_nbij, rTensorOne, signAux, signAux_inv, signBijAux, signBijAux_injOn, signBijAux_mem, signBijAux_surj
-/
theorem signAux_mul {n : Nat} (f g : Perm (Fin n)) : signAux (f * g) = signAux f * signAux g := by
  rw [← signAux_inv g]
  unfold signAux
  rw [← prod_mul_distrib]
  refine prod_nbij (signBijAux g) signBijAux_mem signBijAux_injOn signBijAux_surj ?_
  rintro ⟨a, b⟩ hab
  dsimp only [signBijAux]
  rw [mul_apply]; rw [mul_apply]
  rw [mem_finPairsLT] at hab
  by_cases hg : g b < g a
  · simp [*]
  obtain hf | hf := (f.injective.ne <| g.injective.ne hab.ne).lt_or_gt <;>
    simp_all [le_of_lt, not_le_of_gt, not_lt_of_ge]

/--
theorem `signAux_swap_zero_one'` / 定理 `signAux_swap_zero_one'`

English:
theorem signAux_swap_zero_one'
  given: (n : Nat)
  statement: signAux (swap (0 : Fin (n + 2)) 1) = -1
  proof: show _ = ∏ x in {(⟨1, 0⟩ : Σ _ : Fin (n + 2), Fin (n + 2))},
      if (Equiv.swap 0 1) x.1 <= swap 0 1 x.2 then (-1 : Intˣ) else 1 by
    refine Eq.symm (prod_subset (fun ⟨x₁, x₂⟩ => by
      simp +contextual [mem_finPairsLT]) fun a ha₁ ha₂ => ?_)
    rcases a with ⟨a₁, a₂⟩
    replace ha₁ : a₂ < a₁

中文:
定理 signAux_swap_zero_one'
  条件: (n : 自然数)
  结论: signAux (swap (0 : Fin (n + 2)) 1) = -1
  证明: show _ = ∏ x in {(⟨1, 0⟩ : Σ _ : Fin (n + 2), Fin (n + 2))},
      if (Equiv.swap 0 1) x.1 <= swap 0 1 x.2 then (-1 : Intˣ) else 1 by
    refine Eq.symm (prod_subset (fun ⟨x₁, x₂⟩ => by
      simp +contextual [mem_finPairsLT]) fun a ha₁ ha₂ => ?_)
    rcases a with ⟨a₁, a₂⟩
    replace ha₁ : a₂ < a₁
-/
private theorem signAux_swap_zero_one' (n : Nat) : signAux (swap (0 : Fin (n + 2)) 1) = -1 :=
  show _ = ∏ x in {(⟨1, 0⟩ : Σ _ : Fin (n + 2), Fin (n + 2))},
      if (Equiv.swap 0 1) x.1 <= swap 0 1 x.2 then (-1 : Intˣ) else 1 by
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
      rw [swap_apply_of_ne_of_ne (ne_of_gt H) ha₂]; rw [h01]; rw [if_neg this.not_ge]
    · have le : 1 <= a₂ := Nat.succ_le_of_lt H'
      have lt : 1 < a₁ := le.trans_lt ha₁
      have h01 : Equiv.swap (0 : Fin (n + 2)) 1 1 = 0 := by simp only [swap_apply_right]
      rcases le.eq_or_lt with (rfl | lt')
      · rw [swap_apply_of_ne_of_ne H.ne' lt.ne', h01, if_neg H.not_ge]
      · rw [swap_apply_of_ne_of_ne (ne_of_gt H) (ne_of_gt lt),
          swap_apply_of_ne_of_ne (ne_of_gt H') (ne_of_gt lt'), if_neg ha₁.not_ge]

/--
theorem `signAux_swap_zero_one` / 定理 `signAux_swap_zero_one`

English:
theorem signAux_swap_zero_one
  given: {n : Nat} (hn : 2 <= n)
  proof: by
  rcases n with (_ | _ | n)
  · norm_num at hn
  · norm_num at hn
  · exact signAux_swap_zero_one' n

中文:
定理 signAux_swap_zero_one
  条件: {n : 自然数} (hn : 2 <= n)
  证明: by
  rcases n with (_ | _ | n)
  · norm_num at hn
  · norm_num at hn
  · exact signAux_swap_zero_one' n
-/
private theorem signAux_swap_zero_one {n : Nat} (hn : 2 <= n) :
    signAux (swap (⟨0, lt_of_lt_of_le (by decide) hn⟩ : Fin n) ⟨1, lt_of_lt_of_le (by decide) hn⟩) =
      -1 := by
  rcases n with (_ | _ | n)
  · norm_num at hn
  · norm_num at hn
  · exact signAux_swap_zero_one' n

/--
theorem `signAux_swap` / 定理 `signAux_swap`

English:
theorem signAux_swap
  statement: forall {n : Nat} {x y : Fin n} (_hxy : x != y), signAux (swap x y) = -1
  proof: by exact le_add_self
    rw [← isConj_iff_eq]; rw [← signAux_swap_zero_one h2n]
    exact (MonoidHom.mk' signAux signAux_mul).map_isConj
      (isConj_swap hxy (by exact of_decide_eq_true rfl))

中文:
定理 signAux_swap
  结论: 对任意 {n : 自然数} {x y : Fin n} (_hxy : x != y), signAux (swap x y) = -1
  证明: by exact le_add_self
    rw [← isConj_iff_eq]; rw [← signAux_swap_zero_one h2n]
    exact (MonoidHom.mk' signAux signAux_mul).map_isConj
      (isConj_swap hxy (by exact of_decide_eq_true rfl))

Depends on / 依赖: MonoidHom, MonoidHom.mk, isConj_iff_eq, isConj_swap, le_add_self, map_isConj, of_decide_eq_true, signAux, signAux_mul, signAux_swap_zero_one
-/
theorem signAux_swap : forall {n : Nat} {x y : Fin n} (_hxy : x != y), signAux (swap x y) = -1
  | 0, x, y => by intro; exact Fin.elim0 x
  | 1, x, y => by
    dsimp [signAux, swap, swapCore]
    simp only [eq_iff_true_of_subsingleton, not_true,
               IsEmpty.forall_iff]
  | n + 2, x, y => fun hxy => by
    have h2n : 2 <= n + 2 := by exact le_add_self
    rw [← isConj_iff_eq]; rw [← signAux_swap_zero_one h2n]
    exact (MonoidHom.mk' signAux signAux_mul).map_isConj
      (isConj_swap hxy (by exact of_decide_eq_true rfl))

/--
Definition of `signAux2` / `signAux2` 的定义

English:
definition signAux2
  signature: : List α -> Perm α -> Intˣ

中文:
定义 signAux2
  签名: : List α -> Perm α -> 整数ˣ
-/
def signAux2 : List α -> Perm α -> Intˣ
  | [], _ => 1
  | x::l, f => if x = f x then signAux2 l f else -signAux2 l (swap x (f x) * f)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `signAux_eq_signAux2` / 定理 `signAux_eq_signAux2`

English:
theorem signAux_eq_signAux2
  given: {n : Nat}
  proof: Equiv.ext fun y => Classical.not_not.1 (mt (h y) List.not_mem_nil)
    rw [this]; rw [one_def]; rw [Equiv.trans_refl]; rw [Equiv.symm_trans_self]; rw [← one_def]; rw [signAux_one]; rw [signAux2]
  | x::l, f, e, h => by
    rw [signAux2]
    by_cases hfx : x = f x
    · rw [if_pos hfx]
      exact
  

中文:
定理 signAux_eq_signAux2
  条件: {n : 自然数}
  证明: Equiv.ext fun y => Classical.not_not.1 (mt (h y) List.not_mem_nil)
    rw [this]; rw [one_def]; rw [Equiv.trans_refl]; rw [Equiv.symm_trans_self]; rw [← one_def]; rw [signAux_one]; rw [signAux2]
  | x::l, f, e, h => by
    rw [signAux2]
    by_cases hfx : x = f x
    · rw [if_pos hfx]
      exact
  

Depends on / 依赖: Classical, Classical.not_not, Equiv.ext, List.not_mem_nil, not_mem_nil, not_not
-/
theorem signAux_eq_signAux2 {n : Nat} :
    forall (l : List α) (f : Perm α) (e : α ≃ Fin n) (_h : forall x, f x != x -> x in l),
      signAux ((e.symm.trans f).trans e) = signAux2 l f
  | [], f, e, h => by
    have : f = 1 := Equiv.ext fun y => Classical.not_not.1 (mt (h y) List.not_mem_nil)
    rw [this]; rw [one_def]; rw [Equiv.trans_refl]; rw [Equiv.symm_trans_self]; rw [← one_def]; rw [signAux_one]; rw [signAux2]
  | x::l, f, e, h => by
    rw [signAux2]
    by_cases hfx : x = f x
    · rw [if_pos hfx]
      exact
        signAux_eq_signAux2 l f _ fun y (hy : f y != y) =>
          List.mem_of_ne_of_mem (fun h : y = x => by simp [h, hfx.symm] at hy) (h y hy)
    · have hy : forall y : α, (swap x (f x) * f) y != y -> y in l := fun y hy =>
        have : f y != y ∧ y != x := ne_and_ne_of_swap_mul_apply_ne_self hy
        List.mem_of_ne_of_mem this.2 (h _ this.1)
      have : (e.symm.trans (swap x (f x) * f)).trans e =
          swap (e x) (e (f x)) * (e.symm.trans f).trans e := by
        ext
        rw [← Equiv.symm_trans_swap_trans]; rw [mul_def]; rw [Equiv.symm_trans_swap_trans]; rw [mul_def]
        repeat (rw [trans_apply])
        simp [swap, swapCore]
        split_ifs <;> rfl
      have hefx : e x != e (f x) := mt e.injective.eq_iff.1 hfx
      rw [if_neg hfx]; rw [← signAux_eq_signAux2 _ _ e hy]; rw [this]; rw [signAux_mul]; rw [signAux_swap hefx]
      simp only [neg_neg, one_mul, neg_mul]

/--
Definition of `signAux3` / `signAux3` 的定义

English:
definition signAux3
  signature: [Finite α] (f : Perm α) {s : Multiset α}
  body: Quotient.hrecOn s (fun l _ => signAux2 l f) fun l₁ l₂ h => by
    rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
    refine Function.hfunext (forall_congr fun _ => propext h.mem_iff) fun h₁ h₂ _ => ?_
    rw [← signAux_eq_signAux2 _ _ e fun _ _ => h₁ _]; rw [← signAux_eq_signAux2 _ _ e fun _ _ => h₂

中文:
定义 signAux3
  签名: [Finite α] (f : Perm α) {s : Multiset α}
  定义体: Quotient.hrecOn s (fun l _ => signAux2 l f) fun l₁ l₂ h => by
    rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
    refine Function.hfunext (forall_congr fun _ => propext h.mem_iff) fun h₁ h₂ _ => ?_
    rw [← signAux_eq_signAux2 _ _ e fun _ _ => h₁ _]; rw [← signAux_eq_signAux2 _ _ e fun _ _ => h₂

Depends on / 依赖: Finite, Finite.exists_equiv_fin, Function, Function.hfunext, Quotient, Quotient.hrecOn, exists_equiv_fin, forall_congr, h.mem_iff, hfunext, hrecOn, mem_iff, propext, signAux2, signAux_eq_signAux2
-/
def signAux3 [Finite α] (f : Perm α) {s : Multiset α} : (forall x, x in s) -> Intˣ :=
  Quotient.hrecOn s (fun l _ => signAux2 l f) fun l₁ l₂ h => by
    rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
    refine Function.hfunext (forall_congr fun _ => propext h.mem_iff) fun h₁ h₂ _ => ?_
    rw [← signAux_eq_signAux2 _ _ e fun _ _ => h₁ _]; rw [← signAux_eq_signAux2 _ _ e fun _ _ => h₂ _]

/--
theorem `signAux3_mul_and_swap` / 定理 `signAux3_mul_and_swap`

English:
theorem signAux3_mul_and_swap
  given: [Finite α] (f g : Perm α) (s : Multiset α) (hs : forall x, x in s)
  proof: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  induction s using Quotient.inductionOn with | _ l => ?_
  change
    signAux2 l (f * g) = signAux2 l f * signAux2 l g ∧
    Pairwise fun x y => signAux2 l (swap x y) = -1
  have hfg : (e.symm.trans (f * g)).trans e = (e.symm.trans f).trans e * (e.s

中文:
定理 signAux3_mul_and_swap
  条件: [Finite α] (f g : Perm α) (s : Multiset α) (hs : 对任意 x, x in s)
  证明: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  induction s using Quotient.inductionOn with | _ l => ?_
  change
    signAux2 l (f * g) = signAux2 l f * signAux2 l g ∧
    Pairwise fun x y => signAux2 l (swap x y) = -1
  have hfg : (e.symm.trans (f * g)).trans e = (e.symm.trans f).trans e * (e.s

Depends on / 依赖: Equiv.ext, Finite, Finite.exists_equiv_fin, Pairwise, Quotient, Quotient.inductionOn, e.symm.trans, exists_equiv_fin, inductionOn, mul_apply, signAux2, signAux_eq_signAux2
-/
theorem signAux3_mul_and_swap [Finite α] (f g : Perm α) (s : Multiset α) (hs : forall x, x in s) :
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
    rw [← signAux_eq_signAux2 _ _ e fun _ _ => hs _]; rw [symm_trans_swap_trans]; rw [signAux_swap hxy]

/--
theorem `signAux3_symm_trans_trans` / 定理 `signAux3_symm_trans_trans`

English:
theorem signAux3_symm_trans_trans
  statement: [Finite α] [DecidableEq β] [Finite β] (f : Perm α) (e : α ≃ β)
  proof: by
  induction t, s using Quotient.inductionOn₂
  change signAux2 _ _ = signAux2 _ _
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e'⟩⟩
  rw [← signAux_eq_signAux2 _ _ e' fun _ _ => ht _]; rw [← signAux_eq_signAux2 _ _ (e.trans e') fun _ _ => hs _]
  simp [trans_assoc]

中文:
定理 signAux3_symm_trans_trans
  结论: [Finite α] [DecidableEq β] [Finite β] (f : Perm α) (e : α ≃ β)
  证明: by
  induction t, s using Quotient.inductionOn₂
  change signAux2 _ _ = signAux2 _ _
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e'⟩⟩
  rw [← signAux_eq_signAux2 _ _ e' fun _ _ => ht _]; rw [← signAux_eq_signAux2 _ _ (e.trans e') fun _ _ => hs _]
  simp [trans_assoc]

Depends on / 依赖: Finite, Finite.exists_equiv_fin, Quotient, Quotient.inductionOn, e.trans, exists_equiv_fin, signAux2, signAux_eq_signAux2, trans_assoc
-/
theorem signAux3_symm_trans_trans [Finite α] [DecidableEq β] [Finite β] (f : Perm α) (e : α ≃ β)
    {s : Multiset α} {t : Multiset β} (hs : forall x, x in s) (ht : forall x, x in t) :
    signAux3 ((e.symm.trans f).trans e) ht = signAux3 f hs := by
  induction t, s using Quotient.inductionOn₂
  change signAux2 _ _ = signAux2 _ _
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e'⟩⟩
  rw [← signAux_eq_signAux2 _ _ e' fun _ _ => ht _]; rw [← signAux_eq_signAux2 _ _ (e.trans e') fun _ _ => hs _]
  simp [trans_assoc]

/--
Definition of `sign` / `sign` 的定义

English:
definition sign
  signature: [Fintype α]
  body: MonoidHom.mk' (fun f => signAux3 f mem_univ) fun f g => (signAux3_mul_and_swap f g _ mem_univ).1

中文:
定义 sign
  签名: [Fintype α]
  定义体: MonoidHom.mk' (fun f => signAux3 f mem_univ) fun f g => (signAux3_mul_and_swap f g _ mem_univ).1

Depends on / 依赖: MonoidHom, MonoidHom.mk, mem_univ, signAux3, signAux3_mul_and_swap
-/
def sign [Fintype α] : Perm α ->* Intˣ :=
  MonoidHom.mk' (fun f => signAux3 f mem_univ) fun f g => (signAux3_mul_and_swap f g _ mem_univ).1

section SignType.sign

variable [Fintype α]

@[simp]
/--
theorem `sign_mul` / 定理 `sign_mul`

English:
theorem sign_mul
  given: (f g : Perm α)
  statement: sign (f * g) = sign f * sign g
  proof: map_mul sign f g

@[simp]

中文:
定理 sign_mul
  条件: (f g : Perm α)
  结论: sign (f * g) = sign f * sign g
  证明: map_mul sign f g

@[simp]

Depends on / 依赖: map_mul
-/
theorem sign_mul (f g : Perm α) : sign (f * g) = sign f * sign g :=
  map_mul sign f g

@[simp]
/--
theorem `sign_trans` / 定理 `sign_trans`

English:
theorem sign_trans
  given: (f g : Perm α)
  statement: sign (f.trans g) = sign g * sign f
  proof: by
  rw [← mul_def]; rw [sign_mul]

@[simp]

中文:
定理 sign_trans
  条件: (f g : Perm α)
  结论: sign (f.trans g) = sign g * sign f
  证明: by
  rw [← mul_def]; rw [sign_mul]

@[simp]

Depends on / 依赖: mul_def, sign_mul
-/
theorem sign_trans (f g : Perm α) : sign (f.trans g) = sign g * sign f := by
  rw [← mul_def]; rw [sign_mul]

@[simp]
/--
theorem `sign_one` / 定理 `sign_one`

English:
theorem sign_one
  statement: sign (1 : Perm α) = 1
  proof: map_one sign

@[simp]

中文:
定理 sign_one
  结论: sign (1 : Perm α) = 1
  证明: map_one sign

@[simp]

Depends on / 依赖: map_one
-/
theorem sign_one : sign (1 : Perm α) = 1 :=
  map_one sign

@[simp]
/--
theorem `sign_refl` / 定理 `sign_refl`

English:
theorem sign_refl
  statement: sign (Equiv.refl α) = 1
  proof: map_one sign

@[simp]

中文:
定理 sign_refl
  结论: sign (Equiv.refl α) = 1
  证明: map_one sign

@[simp]

Depends on / 依赖: map_one
-/
theorem sign_refl : sign (Equiv.refl α) = 1 :=
  map_one sign

@[simp]
/--
theorem `sign_inv` / 定理 `sign_inv`

English:
theorem sign_inv
  given: (f : Perm α)
  statement: sign f⁻¹ = sign f
  proof: by
  rw [map_inv sign f]; rw [Int.units_inv_eq_self]

@[simp]

中文:
定理 sign_inv
  条件: (f : Perm α)
  结论: sign f⁻¹ = sign f
  证明: by
  rw [map_inv sign f]; rw [Int.units_inv_eq_self]

@[simp]

Depends on / 依赖: Int.units_inv_eq_self, map_inv, units_inv_eq_self
-/
theorem sign_inv (f : Perm α) : sign f⁻¹ = sign f := by
  rw [map_inv sign f]; rw [Int.units_inv_eq_self]

@[simp]
/--
theorem `sign_symm` / 定理 `sign_symm`

English:
theorem sign_symm
  given: (e : Perm α)
  statement: sign e.symm = sign e
  proof: sign_inv e

中文:
定理 sign_symm
  条件: (e : Perm α)
  结论: sign e.symm = sign e
  证明: sign_inv e

Depends on / 依赖: sign_inv
-/
theorem sign_symm (e : Perm α) : sign e.symm = sign e :=
  sign_inv e

/--
theorem `sign_swap` / 定理 `sign_swap`

English:
theorem sign_swap
  given: {x y : α} (h : x != y)
  statement: sign (swap x y) = -1
  proof: (signAux3_mul_and_swap 1 1 _ mem_univ).2 h

@[simp]

中文:
定理 sign_swap
  条件: {x y : α} (h : x != y)
  结论: sign (swap x y) = -1
  证明: (signAux3_mul_and_swap 1 1 _ mem_univ).2 h

@[simp]

Depends on / 依赖: mem_univ, signAux3_mul_and_swap
-/
theorem sign_swap {x y : α} (h : x != y) : sign (swap x y) = -1 :=
  (signAux3_mul_and_swap 1 1 _ mem_univ).2 h

@[simp]
/--
theorem `sign_swap'` / 定理 `sign_swap'`

English:
theorem sign_swap'
  given: {x y : α}
  statement: sign (swap x y) = if x = y then 1 else -1
  proof: if H : x = y then by simp [H, swap_self] else by simp [sign_swap H, H]

中文:
定理 sign_swap'
  条件: {x y : α}
  结论: sign (swap x y) = if x = y then 1 else -1
  证明: if H : x = y then by simp [H, swap_self] else by simp [sign_swap H, H]

Depends on / 依赖: sign_swap, swap_self
-/
theorem sign_swap' {x y : α} : sign (swap x y) = if x = y then 1 else -1 :=
  if H : x = y then by simp [H, swap_self] else by simp [sign_swap H, H]

/--
theorem `IsSwap.sign_eq` / 定理 `IsSwap.sign_eq`

English:
theorem IsSwap.sign_eq
  given: {f : Perm α} (h : f.IsSwap)
  statement: sign f = -1
  proof: let ⟨_, _, hxy⟩ := h
  hxy.2.symm ▸ sign_swap hxy.1

@[simp]

中文:
定理 IsSwap.sign_eq
  条件: {f : Perm α} (h : f.IsSwap)
  结论: sign f = -1
  证明: let ⟨_, _, hxy⟩ := h
  hxy.2.symm ▸ sign_swap hxy.1

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.ext, lcurry, lift_tmul, ofLinearMap, sign_swap, uncurry
-/
theorem IsSwap.sign_eq {f : Perm α} (h : f.IsSwap) : sign f = -1 :=
  let ⟨_, _, hxy⟩ := h
  hxy.2.symm ▸ sign_swap hxy.1

@[simp]
/--
theorem `sign_symm_trans_trans` / 定理 `sign_symm_trans_trans`

English:
theorem sign_symm_trans_trans
  given: [DecidableEq β] [Fintype β] (f : Perm α) (e : α ≃ β)
  proof: signAux3_symm_trans_trans f e mem_univ mem_univ

@[simp]

中文:
定理 sign_symm_trans_trans
  条件: [DecidableEq β] [Fintype β] (f : Perm α) (e : α ≃ β)
  证明: signAux3_symm_trans_trans f e mem_univ mem_univ

@[simp]

Depends on / 依赖: mem_univ, signAux3_symm_trans_trans
-/
theorem sign_symm_trans_trans [DecidableEq β] [Fintype β] (f : Perm α) (e : α ≃ β) :
    sign ((e.symm.trans f).trans e) = sign f :=
  signAux3_symm_trans_trans f e mem_univ mem_univ

@[simp]
/--
theorem `sign_trans_trans_symm` / 定理 `sign_trans_trans_symm`

English:
theorem sign_trans_trans_symm
  given: [DecidableEq β] [Fintype β] (f : Perm β) (e : α ≃ β)
  proof: sign_symm_trans_trans f e.symm

中文:
定理 sign_trans_trans_symm
  条件: [DecidableEq β] [Fintype β] (f : Perm β) (e : α ≃ β)
  证明: sign_symm_trans_trans f e.symm

Depends on / 依赖: e.symm, sign_symm_trans_trans
-/
theorem sign_trans_trans_symm [DecidableEq β] [Fintype β] (f : Perm β) (e : α ≃ β) :
    sign ((e.trans f).trans e.symm) = sign f :=
  sign_symm_trans_trans f e.symm

/--
theorem `sign_prod_list_swap` / 定理 `sign_prod_list_swap`

English:
theorem sign_prod_list_swap
  given: {l : List (Perm α)} (hl : forall g in l, IsSwap g)
  proof: by
  have h₁ : l.map sign = List.replicate l.length (-1) :=
    List.eq_replicate_iff.2
      ⟨by simp, fun u hu =>
        let ⟨g, hg⟩ := List.mem_map.1 hu
        hg.2 ▸ (hl _ hg.1).sign_eq⟩
  rw [← List.prod_replicate]; rw [← h₁]; rw [List.prod_hom _ (@sign α _ _)]

@[simp]

中文:
定理 sign_prod_list_swap
  条件: {l : List (Perm α)} (hl : 对任意 g in l, IsSwap g)
  证明: by
  have h₁ : l.map sign = List.replicate l.length (-1) :=
    List.eq_replicate_iff.2
      ⟨by simp, fun u hu =>
        let ⟨g, hg⟩ := List.mem_map.1 hu
        hg.2 ▸ (hl _ hg.1).sign_eq⟩
  rw [← List.prod_replicate]; rw [← h₁]; rw [List.prod_hom _ (@sign α _ _)]

@[simp]

Depends on / 依赖: List.eq_replicate_iff, List.mem_map, List.prod_hom, List.prod_replicate, List.replicate, eq_replicate_iff, l.length, l.map, length, mem_map, prod_hom, prod_replicate, replicate, sign_eq
-/
theorem sign_prod_list_swap {l : List (Perm α)} (hl : forall g in l, IsSwap g) :
    sign l.prod = (-1) ^ l.length := by
  have h₁ : l.map sign = List.replicate l.length (-1) :=
    List.eq_replicate_iff.2
      ⟨by simp, fun u hu =>
        let ⟨g, hg⟩ := List.mem_map.1 hu
        hg.2 ▸ (hl _ hg.1).sign_eq⟩
  rw [← List.prod_replicate]; rw [← h₁]; rw [List.prod_hom _ (@sign α _ _)]

@[simp]
/--
theorem `sign_abs` / 定理 `sign_abs`

English:
theorem sign_abs
  given: (f : Perm α)
  proof: by
  rw [Int.abs_eq_natAbs]; rw [Int.units_natAbs]; rw [Nat.cast_one]

中文:
定理 sign_abs
  条件: (f : Perm α)
  证明: by
  rw [Int.abs_eq_natAbs]; rw [Int.units_natAbs]; rw [Nat.cast_one]

Depends on / 依赖: Int.abs_eq_natAbs, Int.units_natAbs, Nat.cast_one, abs_eq_natAbs, cast_one, units_natAbs
-/
theorem sign_abs (f : Perm α) :
    |(Equiv.Perm.sign f : Int)| = 1 := by
  rw [Int.abs_eq_natAbs]; rw [Int.units_natAbs]; rw [Nat.cast_one]

variable (α) in
/--
theorem `sign_surjective` / 定理 `sign_surjective`

English:
theorem sign_surjective
  given: [Nontrivial α]
  statement: Function.Surjective (sign : Perm α -> Intˣ)
  proof: fun a =>
  (Int.units_eq_one_or a).elim (fun h => ⟨1, by simp [h]⟩) fun h =>
    let ⟨x, y, hxy⟩ := exists_pair_ne α
    ⟨swap x y, by rw [sign_swap hxy, h]⟩

中文:
定理 sign_surjective
  条件: [Nontrivial α]
  结论: Function.Surjective (sign : Perm α -> 整数ˣ)
  证明: fun a =>
  (Int.units_eq_one_or a).elim (fun h => ⟨1, by simp [h]⟩) fun h =>
    let ⟨x, y, hxy⟩ := exists_pair_ne α
    ⟨swap x y, by rw [sign_swap hxy, h]⟩
-/
theorem sign_surjective [Nontrivial α] : Function.Surjective (sign : Perm α -> Intˣ) := fun a =>
  (Int.units_eq_one_or a).elim (fun h => ⟨1, by simp [h]⟩) fun h =>
    let ⟨x, y, hxy⟩ := exists_pair_ne α
    ⟨swap x y, by rw [sign_swap hxy, h]⟩

/--
theorem `eq_sign_of_surjective_hom` / 定理 `eq_sign_of_surjective_hom`

English:
theorem eq_sign_of_surjective_hom
  given: {s : Perm α ->* Intˣ} (hs : Surjective s)
  statement: s = sign
  proof: have : forall {f}, IsSwap f -> s f = -1 := fun {f} ⟨x, y, hxy, hxy'⟩ =>
    hxy'.symm ▸
      by_contradiction fun h => by
        have : forall f, IsSwap f -> s f = 1 := fun f ⟨a, b, hab, hab'⟩ => by
          rw [← isConj_iff_eq]; rw [← Or.resolve_right (Int.units_eq_one_or _) h]; rw [hab']
      

中文:
定理 eq_sign_of_surjective_hom
  条件: {s : Perm α ->* 整数ˣ} (hs : Surjective s)
  结论: s = sign
  证明: have : forall {f}, IsSwap f -> s f = -1 := fun {f} ⟨x, y, hxy, hxy'⟩ =>
    hxy'.symm ▸
      by_contradiction fun h => by
        have : forall f, IsSwap f -> s f = 1 := fun f ⟨a, b, hab, hab'⟩ => by
          rw [← isConj_iff_eq]; rw [← Or.resolve_right (Int.units_eq_one_or _) h]; rw [hab']
      

Depends on / 依赖: Int.units_eq_one_or, IsSwap, List.mem_map, Or.resolve_right, by_contradiction, isConj_iff_eq, isConj_swap, l.map, map_isConj, mem_map, resolve_right, s.map_isConj, truncSwapFactors, units_eq_one_or
-/
theorem eq_sign_of_surjective_hom {s : Perm α ->* Intˣ} (hs : Surjective s) : s = sign :=
  have : forall {f}, IsSwap f -> s f = -1 := fun {f} ⟨x, y, hxy, hxy'⟩ =>
    hxy'.symm ▸
      by_contradiction fun h => by
        have : forall f, IsSwap f -> s f = 1 := fun f ⟨a, b, hab, hab'⟩ => by
          rw [← isConj_iff_eq]; rw [← Or.resolve_right (Int.units_eq_one_or _) h]; rw [hab']
          exact s.map_isConj (isConj_swap hab hxy)
        let ⟨g, hg⟩ := hs (-1)
        let ⟨l, hl⟩ := (truncSwapFactors g).out
        have : forall a in l.map s, a = (1 : Intˣ) := fun a ha =>
          let ⟨g, hg⟩ := List.mem_map.1 ha
          hg.2 ▸ this _ (hl.2 _ hg.1)
        have : s l.prod = 1 := by
          rw [← l.prod_hom s]; rw [List.eq_replicate_length.2 this]; rw [List.prod_replicate]; rw [one_pow]
        rw [hl.1]; rw [hg] at this
        exact absurd this (by simp_all)
  MonoidHom.ext fun f => by
    let ⟨l, hl₁, hl₂⟩ := (truncSwapFactors f).out
    have hsl : forall a in l.map s, a = (-1 : Intˣ) := fun a ha =>
      let ⟨g, hg⟩ := List.mem_map.1 ha
      hg.2 ▸ this (hl₂ _ hg.1)
    rw [← hl₁]; rw [← l.prod_hom s]; rw [List.eq_replicate_length.2 hsl]; rw [List.length_map]; rw [List.prod_replicate]; rw [sign_prod_list_swap hl₂]

/--
theorem `sign_subtypePerm` / 定理 `sign_subtypePerm`

English:
theorem sign_subtypePerm
  statement: (f : Perm α) {p : α -> Prop} [DecidablePred p] (h₁ : forall x, p (f x) ↔ p x)
  proof: by
  let l := (truncSwapFactors (subtypePerm f h₁)).out
  have hl' : forall g' in l.1.map ofSubtype, IsSwap g' := fun g' hg' =>
    let ⟨g, hg⟩ := List.mem_map.1 hg'
    hg.2 ▸ (l.2.2 _ hg.1).of_subtype_isSwap
  have hl'₂ : (l.1.map ofSubtype).prod = f := by
    rw [l.1.prod_hom ofSubtype]; rw [l.2.

中文:
定理 sign_subtypePerm
  结论: (f : Perm α) {p : α -> 命题} [DecidablePred p] (h₁ : 对任意 x, p (f x) ↔ p x)
  证明: by
  let l := (truncSwapFactors (subtypePerm f h₁)).out
  have hl' : forall g' in l.1.map ofSubtype, IsSwap g' := fun g' hg' =>
    let ⟨g, hg⟩ := List.mem_map.1 hg'
    hg.2 ▸ (l.2.2 _ hg.1).of_subtype_isSwap
  have hl'₂ : (l.1.map ofSubtype).prod = f := by
    rw [l.1.prod_hom ofSubtype]; rw [l.2.

Depends on / 依赖: IsSwap, List.length_map, List.mem_map, length_map, mem_map, ofSubtype, ofSubtype_subtypePerm, of_subtype_isSwap, prod_hom, sign_prod_list_swap, simp_rw, subtypePerm, truncSwapFactors
-/
theorem sign_subtypePerm (f : Perm α) {p : α -> Prop} [DecidablePred p] (h₁ : forall x, p (f x) ↔ p x)
    (h₂ : forall x, f x != x -> p x) : sign (subtypePerm f h₁) = sign f := by
  let l := (truncSwapFactors (subtypePerm f h₁)).out
  have hl' : forall g' in l.1.map ofSubtype, IsSwap g' := fun g' hg' =>
    let ⟨g, hg⟩ := List.mem_map.1 hg'
    hg.2 ▸ (l.2.2 _ hg.1).of_subtype_isSwap
  have hl'₂ : (l.1.map ofSubtype).prod = f := by
    rw [l.1.prod_hom ofSubtype]; rw [l.2.1]; rw [ofSubtype_subtypePerm _ h₂]
  conv =>
    congr
    rw [← l.2.1]
  simp_rw [← hl'₂]
  rw [sign_prod_list_swap l.2.2]; rw [sign_prod_list_swap hl']; rw [List.length_map]

/--
theorem `sign_eq_sign_of_equiv` / 定理 `sign_eq_sign_of_equiv`

English:
theorem sign_eq_sign_of_equiv
  statement: [DecidableEq β] [Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β)
  proof: by
have hg : g = (e.symm.trans f).trans e := Equiv.ext by simp [h]
  rw [hg]; rw [sign_symm_trans_trans]

中文:
定理 sign_eq_sign_of_equiv
  结论: [DecidableEq β] [Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β)
  证明: by
have hg : g = (e.symm.trans f).trans e := Equiv.ext by simp [h]
  rw [hg]; rw [sign_symm_trans_trans]

Depends on / 依赖: Equiv.ext, e.symm.trans, sign_symm_trans_trans
-/
theorem sign_eq_sign_of_equiv [DecidableEq β] [Fintype β] (f : Perm α) (g : Perm β) (e : α ≃ β)
    (h : forall x, e (f x) = g (e x)) : sign f = sign g := by
have hg : g = (e.symm.trans f).trans e := Equiv.ext by simp [h]
  rw [hg]; rw [sign_symm_trans_trans]

/--
theorem `sign_bij` / 定理 `sign_bij`

English:
theorem sign_bij
  statement: [DecidableEq β] [Fintype β] {f : Perm α} {g : Perm β} (i : forall x : α, f x != x -> β)
  proof: calc
    sign f = sign (subtypePerm f <| by simp : Perm { x // f x != x }) :=
      (sign_subtypePerm _ _ fun _ => id).symm
    _ = sign (subtypePerm g <| by simp : Perm { x // g x != x }) :=
      sign_eq_sign_of_equiv _ _
        (Equiv.ofBijective
          (fun x : { x // f x != x } =>
         

中文:
定理 sign_bij
  结论: [DecidableEq β] [Fintype β] {f : Perm α} {g : Perm β} (i : 对任意 x : α, f x != x -> β)
  证明: calc
    sign f = sign (subtypePerm f <| by simp : Perm { x // f x != x }) :=
      (sign_subtypePerm _ _ fun _ => id).symm
    _ = sign (subtypePerm g <| by simp : Perm { x // g x != x }) :=
      sign_eq_sign_of_equiv _ _
        (Equiv.ofBijective
          (fun x : { x // f x != x } =>
         

Depends on / 依赖: Equiv.ofBijective, Subtype, Subtype.ext, Subtype.mk.inj, f.injective, injective, ofBijective, sign_eq_sign_of_equiv, sign_subtypePerm, subtypePerm
-/
theorem sign_bij [DecidableEq β] [Fintype β] {f : Perm α} {g : Perm β} (i : forall x : α, f x != x -> β)
    (h : forall x hx hx', i (f x) hx' = g (i x hx)) (hi : forall x₁ x₂ hx₁ hx₂, i x₁ hx₁ = i x₂ hx₂ -> x₁ = x₂)
    (hg : forall y, g y != y -> exists x hx, i x hx = y) : sign f = sign g :=
  calc
    sign f = sign (subtypePerm f <| by simp : Perm { x // f x != x }) :=
      (sign_subtypePerm _ _ fun _ => id).symm
    _ = sign (subtypePerm g <| by simp : Perm { x // g x != x }) :=
      sign_eq_sign_of_equiv _ _
        (Equiv.ofBijective
          (fun x : { x // f x != x } =>
            (⟨i x.1 x.2, by
                have : f (f x) != f x := mt (fun h => f.injective h) x.2
                rw [← h _ x.2 this]
                exact mt (hi _ _ this x.2) x.2⟩ :
              { y // g y != y }))
          ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => Subtype.ext (hi _ _ _ _ (Subtype.mk.inj h)), fun ⟨y, hy⟩ =>
            let ⟨x, hfx, hx⟩ := hg y hy
            ⟨⟨x, hfx⟩, Subtype.ext hx⟩⟩)
        fun ⟨x, _⟩ => Subtype.ext (h x _ _)
    _ = sign g := sign_subtypePerm _ _ fun _ => id

/--
theorem `prod_prodExtendRight` / 定理 `prod_prodExtendRight`

English:
theorem prod_prodExtendRight
  statement: {α : Type*} [DecidableEq α] (σ : α -> Perm β) {l : List α}
  proof: by
  ext ⟨a, b⟩ : 1
  -- We'll use induction on the list of elements,
  -- but we have to keep track of whether we already passed `a` in the list.
  suffices a in l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b) = (a, σ a b) ∨
      a ∉ l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b

中文:
定理 prod_prodExtendRight
  结论: {α : 类型} [DecidableEq α] (σ : α -> Perm β) {l : List α}
  证明: by
  ext ⟨a, b⟩ : 1
  -- We'll use induction on the list of elements,
  -- but we have to keep track of whether we already passed `a` in the list.
  suffices a in l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b) = (a, σ a b) ∨
      a ∉ l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b
-/
theorem prod_prodExtendRight {α : Type*} [DecidableEq α] (σ : α -> Perm β) {l : List α}
    (hl : l.Nodup) (mem_l : forall a, a in l) :
    (l.map fun a => prodExtendRight a (σ a)).prod = prodCongrRight σ := by
  ext ⟨a, b⟩ : 1
  -- We'll use induction on the list of elements,
  -- but we have to keep track of whether we already passed `a` in the list.
  suffices a in l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b) = (a, σ a b) ∨
      a ∉ l ∧ (l.map fun a => prodExtendRight a (σ a)).prod (a, b) = (a, b) by
    obtain ⟨_, prod_eq⟩ := Or.resolve_right this (not_and.mpr fun h _ => h (mem_l a))
    rw [prod_eq]; rw [prodCongrRight_apply]
  clear mem_l
  induction l with
  | nil =>
    refine Or.inr ⟨List.not_mem_nil, ?_⟩
    rw [List.map_nil]; rw [List.prod_nil]; rw [one_apply]
  | cons a' l ih =>
    rw [List.map_cons]; rw [List.prod_cons]; rw [mul_apply]
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
/--
theorem `sign_prodExtendRight` / 定理 `sign_prodExtendRight`

English:
theorem sign_prodExtendRight
  given: (a : α) (σ : Perm β)
  statement: sign (prodExtendRight a σ) = sign σ
  proof: sign_bij (fun (ab : α × β) _ => ab.snd)
    (fun ⟨a', b⟩ hab _ => by simp [eq_of_prodExtendRight_ne hab])
    (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab₁ hab₂ h => by
      simpa [eq_of_prodExtendRight_ne hab₁, eq_of_prodExtendRight_ne hab₂] using h)
    fun y hy => ⟨(a, y), by simpa, by simp⟩

中文:
定理 sign_prodExtendRight
  条件: (a : α) (σ : Perm β)
  结论: sign (prodExtendRight a σ) = sign σ
  证明: sign_bij (fun (ab : α × β) _ => ab.snd)
    (fun ⟨a', b⟩ hab _ => by simp [eq_of_prodExtendRight_ne hab])
    (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab₁ hab₂ h => by
      simpa [eq_of_prodExtendRight_ne hab₁, eq_of_prodExtendRight_ne hab₂] using h)
    fun y hy => ⟨(a, y), by simpa, by simp⟩

Depends on / 依赖: ab.snd, eq_of_prodExtendRight_ne, sign_bij
-/
theorem sign_prodExtendRight (a : α) (σ : Perm β) : sign (prodExtendRight a σ) = sign σ :=
  sign_bij (fun (ab : α × β) _ => ab.snd)
    (fun ⟨a', b⟩ hab _ => by simp [eq_of_prodExtendRight_ne hab])
    (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab₁ hab₂ h => by
      simpa [eq_of_prodExtendRight_ne hab₁, eq_of_prodExtendRight_ne hab₂] using h)
    fun y hy => ⟨(a, y), by simpa, by simp⟩

/--
theorem `sign_prodCongrRight` / 定理 `sign_prodCongrRight`

English:
theorem sign_prodCongrRight
  given: (σ : α -> Perm β)
  statement: sign (prodCongrRight σ) = ∏ k, sign (σ k)
  proof: by
  obtain ⟨l, hl, mem_l⟩ := Finite.exists_univ_list α
  have l_to_finset : l.toFinset = Finset.univ := by
    apply eq_top_iff.mpr
    intro b _
    exact List.mem_toFinset.mpr (mem_l b)
  rw [← prod_prodExtendRight σ hl mem_l]; rw [map_list_prod sign]; rw [List.map_map]; rw [← l_to_finset]; rw [L

中文:
定理 sign_prodCongrRight
  条件: (σ : α -> Perm β)
  结论: sign (prodCongrRight σ) = ∏ k, sign (σ k)
  证明: by
  obtain ⟨l, hl, mem_l⟩ := Finite.exists_univ_list α
  have l_to_finset : l.toFinset = Finset.univ := by
    apply eq_top_iff.mpr
    intro b _
    exact List.mem_toFinset.mpr (mem_l b)
  rw [← prod_prodExtendRight σ hl mem_l]; rw [map_list_prod sign]; rw [List.map_map]; rw [← l_to_finset]; rw [L

Depends on / 依赖: Finite, Finite.exists_univ_list, Finset, Finset.univ, Function, Function.comp_def, List.map_map, List.mem_toFinset.mpr, List.prod_toFinset, comp_def, eq_top_iff, eq_top_iff.mpr, exists_univ_list, l.toFinset, l_to_finset, map_list_prod, map_map, mem_l, mem_toFinset, prod_prodExtendRight
-/
theorem sign_prodCongrRight (σ : α -> Perm β) : sign (prodCongrRight σ) = ∏ k, sign (σ k) := by
  obtain ⟨l, hl, mem_l⟩ := Finite.exists_univ_list α
  have l_to_finset : l.toFinset = Finset.univ := by
    apply eq_top_iff.mpr
    intro b _
    exact List.mem_toFinset.mpr (mem_l b)
  rw [← prod_prodExtendRight σ hl mem_l]; rw [map_list_prod sign]; rw [List.map_map]; rw [← l_to_finset]; rw [List.prod_toFinset _ hl]
  simp_rw [← fun a => sign_prodExtendRight a (σ a), Function.comp_def]

/--
theorem `sign_prodCongrLeft` / 定理 `sign_prodCongrLeft`

English:
theorem sign_prodCongrLeft
  given: (σ : α -> Perm β)
  statement: sign (prodCongrLeft σ) = ∏ k, sign (σ k)
  proof: by
  refine (sign_eq_sign_of_equiv _ _ (prodComm β α) ?_).trans (sign_prodCongrRight σ)
  rintro ⟨b, α⟩
  rfl

@[simp]

中文:
定理 sign_prodCongrLeft
  条件: (σ : α -> Perm β)
  结论: sign (prodCongrLeft σ) = ∏ k, sign (σ k)
  证明: by
  refine (sign_eq_sign_of_equiv _ _ (prodComm β α) ?_).trans (sign_prodCongrRight σ)
  rintro ⟨b, α⟩
  rfl

@[simp]

Depends on / 依赖: prodComm, sign_eq_sign_of_equiv, sign_prodCongrRight
-/
theorem sign_prodCongrLeft (σ : α -> Perm β) : sign (prodCongrLeft σ) = ∏ k, sign (σ k) := by
  refine (sign_eq_sign_of_equiv _ _ (prodComm β α) ?_).trans (sign_prodCongrRight σ)
  rintro ⟨b, α⟩
  rfl

@[simp]
/--
theorem `sign_permCongr` / 定理 `sign_permCongr`

English:
theorem sign_permCongr
  given: (e : α ≃ β) (p : Perm α)
  statement: sign (e.permCongr p) = sign p
  proof: sign_eq_sign_of_equiv _ _ e.symm (by simp)

中文:
定理 sign_permCongr
  条件: (e : α ≃ β) (p : Perm α)
  结论: sign (e.permCongr p) = sign p
  证明: sign_eq_sign_of_equiv _ _ e.symm (by simp)

Depends on / 依赖: e.symm, sign_eq_sign_of_equiv
-/
theorem sign_permCongr (e : α ≃ β) (p : Perm α) : sign (e.permCongr p) = sign p :=
  sign_eq_sign_of_equiv _ _ e.symm (by simp)

/--
theorem `sign_trans_trans` / 定理 `sign_trans_trans`

English:
theorem sign_trans_trans
  given: (f : β ≃ α) (p : Perm α) (g : α ≃ β)
  proof: by
  rw [← sign_permCongr g]; rw [← sign_mul]; congr; ext; simp

中文:
定理 sign_trans_trans
  条件: (f : β ≃ α) (p : Perm α) (g : α ≃ β)
  证明: by
  rw [← sign_permCongr g]; rw [← sign_mul]; congr; ext; simp
-/
@[simp] theorem sign_trans_trans (f : β ≃ α) (p : Perm α) (g : α ≃ β) :
    sign (f.trans (p.trans g)) = sign p * sign (f.trans g) := by
  rw [← sign_permCongr g]; rw [← sign_mul]; congr; ext; simp

/--
theorem `sign_equivCongr` / 定理 `sign_equivCongr`

English:
theorem sign_equivCongr
  given: (f g : α ≃ β) (p : Perm α)
  proof: sign_trans_trans ..

@[simp]

中文:
定理 sign_equivCongr
  条件: (f g : α ≃ β) (p : Perm α)
  证明: sign_trans_trans ..

@[simp]
-/
@[simp] theorem sign_equivCongr (f g : α ≃ β) (p : Perm α) :
    sign (f.equivCongr g p) = sign p * sign (f.symm.trans g) :=
  sign_trans_trans ..

@[simp]
/--
theorem `sign_sumCongr` / 定理 `sign_sumCongr`

English:
theorem sign_sumCongr
  given: (σa : Perm α) (σb : Perm β)
  statement: sign (sumCongr σa σb) = sign σa * sign σb
  proof: by
  suffices sign (sumCongr σa (1 : Perm β)) = sign σa ∧ sign (sumCongr (1 : Perm α) σb) = sign σb
    by rw [← this.1, ← this.2, ← sign_mul, sumCongr_mul, one_mul, mul_one]
  constructor
  · induction σa using swap_induction_on with
    | one => simp
    | swap_mul σa' a₁ a₂ ha ih =>
      rw [← o

中文:
定理 sign_sumCongr
  条件: (σa : Perm α) (σb : Perm β)
  结论: sign (sumCongr σa σb) = sign σa * sign σb
  证明: by
  suffices sign (sumCongr σa (1 : Perm β)) = sign σa ∧ sign (sumCongr (1 : Perm α) σb) = sign σb
    by rw [← this.1, ← this.2, ← sign_mul, sumCongr_mul, one_mul, mul_one]
  constructor
  · induction σa using swap_induction_on with
    | one => simp
    | swap_mul σa' a₁ a₂ ha ih =>
      rw [← o

Depends on / 依赖: Sum.inl_injective.ne_iff.mpr, inl_injective, mul_one, ne_iff, one_mul, sign_mul, sign_swap, sumCongr, sumCongr_mul, sumCongr_swap_one, swap_induction_on, swap_mul
-/
theorem sign_sumCongr (σa : Perm α) (σb : Perm β) : sign (sumCongr σa σb) = sign σa * sign σb := by
  suffices sign (sumCongr σa (1 : Perm β)) = sign σa ∧ sign (sumCongr (1 : Perm α) σb) = sign σb
    by rw [← this.1, ← this.2, ← sign_mul, sumCongr_mul, one_mul, mul_one]
  constructor
  · induction σa using swap_induction_on with
    | one => simp
    | swap_mul σa' a₁ a₂ ha ih =>
      rw [← one_mul (1 : Perm β)]; rw [← sumCongr_mul]; rw [sign_mul]; rw [sign_mul]; rw [ih]; rw [sumCongr_swap_one]; rw [sign_swap ha]; rw [sign_swap (Sum.inl_injective.ne_iff.mpr ha)]
  · induction σb using swap_induction_on with
    | one => simp
    | swap_mul σb' b₁ b₂ hb ih =>
      rw [← one_mul (1 : Perm α)]; rw [← sumCongr_mul]; rw [sign_mul]; rw [sign_mul]; rw [ih]; rw [sumCongr_one_swap]; rw [sign_swap hb]; rw [sign_swap (Sum.inr_injective.ne_iff.mpr hb)]

@[simp]
/--
theorem `sign_subtypeCongr` / 定理 `sign_subtypeCongr`

English:
theorem sign_subtypeCongr
  statement: {p : α -> Prop} [DecidablePred p] (ep : Perm { a // p a })
  proof: by
  simp [subtypeCongr]

@[simp]

中文:
定理 sign_subtypeCongr
  结论: {p : α -> 命题} [DecidablePred p] (ep : Perm { a // p a })
  证明: by
  simp [subtypeCongr]

@[simp]

Depends on / 依赖: subtypeCongr
-/
theorem sign_subtypeCongr {p : α -> Prop} [DecidablePred p] (ep : Perm { a // p a })
    (en : Perm { a // ¬p a }) : sign (ep.subtypeCongr en) = sign ep * sign en := by
  simp [subtypeCongr]

@[simp]
/--
theorem `sign_extendDomain` / 定理 `sign_extendDomain`

English:
theorem sign_extendDomain
  given: (e : Perm α) {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p)
  proof: by
  simp only [Equiv.Perm.extendDomain, sign_subtypeCongr, sign_permCongr, sign_refl, mul_one]

@[simp]

中文:
定理 sign_extendDomain
  条件: (e : Perm α) {p : β -> 命题} [DecidablePred p] (f : α ≃ Subtype p)
  证明: by
  simp only [Equiv.Perm.extendDomain, sign_subtypeCongr, sign_permCongr, sign_refl, mul_one]

@[simp]

Depends on / 依赖: Equiv.Perm.extendDomain, extendDomain, mul_one, sign_permCongr, sign_refl, sign_subtypeCongr
-/
theorem sign_extendDomain (e : Perm α) {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p) :
    Equiv.Perm.sign (e.extendDomain f) = Equiv.Perm.sign e := by
  simp only [Equiv.Perm.extendDomain, sign_subtypeCongr, sign_permCongr, sign_refl, mul_one]

@[simp]
/--
theorem `sign_ofSubtype` / 定理 `sign_ofSubtype`

English:
theorem sign_ofSubtype
  statement: {p : α -> Prop} [DecidablePred p] [Fintype (Subtype p)]
  proof: sign_extendDomain f (Equiv.refl (Subtype p))

中文:
定理 sign_ofSubtype
  结论: {p : α -> 命题} [DecidablePred p] [Fintype (Subtype p)]
  证明: sign_extendDomain f (Equiv.refl (Subtype p))

Depends on / 依赖: Equiv.refl, Subtype, sign_extendDomain
-/
theorem sign_ofSubtype {p : α -> Prop} [DecidablePred p] [Fintype (Subtype p)]
    (f : Equiv.Perm (Subtype p)) : sign (ofSubtype f) = sign f :=
  sign_extendDomain f (Equiv.refl (Subtype p))

end congr

end SignType.sign

@[simp]
/--
theorem `viaFintypeEmbedding_sign` / 定理 `viaFintypeEmbedding_sign`

English:
theorem viaFintypeEmbedding_sign
  proof: by
  simp [viaFintypeEmbedding]

中文:
定理 viaFintypeEmbedding_sign
  证明: by
  simp [viaFintypeEmbedding]

Depends on / 依赖: viaFintypeEmbedding
-/
theorem viaFintypeEmbedding_sign
    [Fintype α] [Fintype β] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β) :
    sign (e.viaFintypeEmbedding f) = sign e := by
  simp [viaFintypeEmbedding]

section Finset

variable [Fintype α]

/--
Definition of `ofSign` / `ofSign` 的定义

English:
definition ofSign
  signature: (s : Intˣ)
  body: univ.filter (sign · = s)

@[simp]

中文:
定义 ofSign
  签名: (s : 整数ˣ)
  定义体: univ.filter (sign · = s)

@[simp]

Depends on / 依赖: filter, univ.filter
-/
def ofSign (s : Intˣ) : Finset (Perm α) := univ.filter (sign · = s)

@[simp]
/--
lemma `mem_ofSign` / 引理 `mem_ofSign`

English:
lemma mem_ofSign
  given: {s : Intˣ} {σ : Perm α}
  statement: σ in ofSign s ↔ σ.sign = s
  proof: by
  rw [ofSign]; rw [mem_filter]; rw [and_iff_right (mem_univ σ)]

中文:
引理 mem_ofSign
  条件: {s : 整数ˣ} {σ : Perm α}
  结论: σ in ofSign s ↔ σ.sign = s
  证明: by
  rw [ofSign]; rw [mem_filter]; rw [and_iff_right (mem_univ σ)]

Depends on / 依赖: and_iff_right, mem_filter, mem_univ, ofSign
-/
lemma mem_ofSign {s : Intˣ} {σ : Perm α} : σ in ofSign s ↔ σ.sign = s := by
  rw [ofSign]; rw [mem_filter]; rw [and_iff_right (mem_univ σ)]

/--
lemma `ofSign_disjoint` / 引理 `ofSign_disjoint`

English:
lemma ofSign_disjoint
  statement: _root_.Disjoint (ofSign 1 : Finset (Perm α)) (ofSign (-1))
  proof: by
  rw [Finset.disjoint_iff_ne]
  rintro σ hσ τ hτ rfl
  rw [mem_ofSign] at hσ hτ
  have := hσ.symm.trans hτ
  contradiction

中文:
引理 ofSign_disjoint
  结论: _root_.Disjoint (ofSign 1 : Finset (Perm α)) (ofSign (-1))
  证明: by
  rw [Finset.disjoint_iff_ne]
  rintro σ hσ τ hτ rfl
  rw [mem_ofSign] at hσ hτ
  have := hσ.symm.trans hτ
  contradiction

Depends on / 依赖: Finset, Finset.disjoint_iff_ne, disjoint_iff_ne, mem_ofSign, symm.trans
-/
lemma ofSign_disjoint : _root_.Disjoint (ofSign 1 : Finset (Perm α)) (ofSign (-1)) := by
  rw [Finset.disjoint_iff_ne]
  rintro σ hσ τ hτ rfl
  rw [mem_ofSign] at hσ hτ
  have := hσ.symm.trans hτ
  contradiction

/--
lemma `ofSign_disjUnion` / 引理 `ofSign_disjUnion`

English:
lemma ofSign_disjUnion
  proof: by
  ext σ
  simp_rw [mem_disjUnion, mem_ofSign, Int.units_eq_one_or, mem_univ]

中文:
引理 ofSign_disjUnion
  证明: by
  ext σ
  simp_rw [mem_disjUnion, mem_ofSign, Int.units_eq_one_or, mem_univ]

Depends on / 依赖: Int.units_eq_one_or, mem_disjUnion, mem_ofSign, mem_univ, simp_rw, units_eq_one_or
-/
lemma ofSign_disjUnion :
    (ofSign 1).disjUnion (ofSign (-1)) ofSign_disjoint = (univ : Finset (Perm α)) := by
  ext σ
  simp_rw [mem_disjUnion, mem_ofSign, Int.units_eq_one_or, mem_univ]

end Finset

end Equiv.Perm
