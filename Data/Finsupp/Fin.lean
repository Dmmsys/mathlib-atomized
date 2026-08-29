/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
module

public import Mathlib.Data.Finsupp.Single

/-!
# `cons` and `tail` for maps `Fin n →₀ M`

We interpret maps `Fin n →₀ M` as `n`-tuples of elements of `M`,
We define the following operations:
* `Finsupp.tail` : the tail of a map `Fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `Finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;

In this context, we prove some usual properties of `tail` and `cons`, analogous to those of
`Data.Fin.Tuple.Basic`.
-/

@[expose] public section

open Function

noncomputable section

namespace Finsupp

variable {n : Nat} (i : Fin n) {M : Type*} [Zero M] (y : M) (t : Fin (n + 1) ->₀ M) (s : Fin n ->₀ M)

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (s : Fin (n + 1) ->₀ M)
  body: Finsupp.equivFunOnFinite.symm (Fin.tail s)

中文:
定义 tail
  签名: (s : Fin (n + 1) ->₀ M)
  定义体: Finsupp.equivFunOnFinite.symm (Fin.tail s)

Depends on / 依赖: Fin.tail, Finsupp, Finsupp.equivFunOnFinite.symm, equivFunOnFinite
-/
def tail (s : Fin (n + 1) ->₀ M) : Fin n ->₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.tail s)

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (y : M) (s : Fin n ->₀ M)
  body: Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) -> M)

中文:
定义 cons
  签名: (y : M) (s : Fin n ->₀ M)
  定义体: Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) -> M)

Depends on / 依赖: Fin.cons, Finsupp, Finsupp.equivFunOnFinite.symm, equivFunOnFinite
-/
def cons (y : M) (s : Fin n ->₀ M) : Fin (n + 1) ->₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) -> M)

/--
theorem `tail_apply` / 定理 `tail_apply`

English:
theorem tail_apply
  statement: tail t i = t i.succ
  proof: rfl

@[simp]

中文:
定理 tail_apply
  结论: tail t i = t i.succ
  证明: rfl

@[simp]
-/
theorem tail_apply : tail t i = t i.succ :=
  rfl

@[simp]
/--
theorem `cons_zero` / 定理 `cons_zero`

English:
theorem cons_zero
  statement: cons y s 0 = y
  proof: rfl

@[simp]

中文:
定理 cons_zero
  结论: cons y s 0 = y
  证明: rfl

@[simp]
-/
theorem cons_zero : cons y s 0 = y :=
  rfl

@[simp]
/--
theorem `cons_succ` / 定理 `cons_succ`

English:
theorem cons_succ
  statement: cons y s i.succ = s i
  proof: rfl

@[simp]

中文:
定理 cons_succ
  结论: cons y s i.succ = s i
  证明: rfl

@[simp]
-/
theorem cons_succ : cons y s i.succ = s i :=
  rfl

@[simp]
/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  statement: tail (cons y s) = s
  proof: ext fun k => by simp only [tail_apply, cons_succ]

@[simp]

中文:
定理 tail_cons
  结论: tail (cons y s) = s
  证明: ext fun k => by simp only [tail_apply, cons_succ]

@[simp]

Depends on / 依赖: cons_succ, tail_apply
-/
theorem tail_cons : tail (cons y s) = s :=
  ext fun k => by simp only [tail_apply, cons_succ]

@[simp]
/--
theorem `tail_update_zero` / 定理 `tail_update_zero`

English:
theorem tail_update_zero
  statement: tail (update t 0 y) = tail t
  proof: by simp [tail]

@[simp]

中文:
定理 tail_update_zero
  结论: tail (update t 0 y) = tail t
  证明: by simp [tail]

@[simp]
-/
theorem tail_update_zero : tail (update t 0 y) = tail t := by simp [tail]

@[simp]
/--
theorem `tail_update_succ` / 定理 `tail_update_succ`

English:
theorem tail_update_succ
  statement: tail (update t i.succ y) = update (tail t) i y
  proof: by ext; simp [tail]

@[simp]

中文:
定理 tail_update_succ
  结论: tail (update t i.succ y) = update (tail t) i y
  证明: by ext; simp [tail]

@[simp]
-/
theorem tail_update_succ : tail (update t i.succ y) = update (tail t) i y := by ext; simp [tail]

@[simp]
/--
theorem `cons_tail` / 定理 `cons_tail`

English:
theorem cons_tail
  statement: cons (t 0) (tail t) = t
  proof: by
  ext a
  by_cases c_a : a = 0
  · rw [c_a, cons_zero]
  · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]

中文:
定理 cons_tail
  结论: cons (t 0) (tail t) = t
  证明: by
  ext a
  by_cases c_a : a = 0
  · rw [c_a, cons_zero]
  · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]

Depends on / 依赖: Fin.succ_pred, cons_succ, cons_zero, succ_pred, tail_apply
-/
theorem cons_tail : cons (t 0) (tail t) = t := by
  ext a
  by_cases c_a : a = 0
  · rw [c_a, cons_zero]
  · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]

/--
lemma `cons_zero_eq_single_zero` / 引理 `cons_zero_eq_single_zero`

English:
lemma cons_zero_eq_single_zero
  statement: cons y (0 : Fin n ->₀ M) = single 0 y
  proof: by
  ext j
  cases j using Fin.cases <;> simp

中文:
引理 cons_zero_eq_single_zero
  结论: cons y (0 : Fin n ->₀ M) = single 0 y
  证明: by
  ext j
  cases j using Fin.cases <;> simp

Depends on / 依赖: Fin.cases
-/
lemma cons_zero_eq_single_zero : cons y (0 : Fin n ->₀ M) = single 0 y := by
  ext j
  cases j using Fin.cases <;> simp

/--
lemma `cons_zero_single_eq_single_succ` / 引理 `cons_zero_single_eq_single_succ`

English:
lemma cons_zero_single_eq_single_succ
  statement: cons 0 (single i y) = single i.succ y
  proof: by
  ext j
  cases j using Fin.cases <;> simp [single_apply]

@[simp]

中文:
引理 cons_zero_single_eq_single_succ
  结论: cons 0 (single i y) = single i.succ y
  证明: by
  ext j
  cases j using Fin.cases <;> simp [single_apply]

@[simp]

Depends on / 依赖: Fin.cases, single_apply
-/
lemma cons_zero_single_eq_single_succ : cons 0 (single i y) = single i.succ y := by
  ext j
  cases j using Fin.cases <;> simp [single_apply]

@[simp]
/--
theorem `cons_zero_zero` / 定理 `cons_zero_zero`

English:
theorem cons_zero_zero
  statement: cons 0 (0 : Fin n ->₀ M) = 0
  proof: by simp [cons_zero_eq_single_zero]

中文:
定理 cons_zero_zero
  结论: cons 0 (0 : Fin n ->₀ M) = 0
  证明: by simp [cons_zero_eq_single_zero]

Depends on / 依赖: cons_zero_eq_single_zero
-/
theorem cons_zero_zero : cons 0 (0 : Fin n ->₀ M) = 0 := by simp [cons_zero_eq_single_zero]

variable {s} {y}

/--
theorem `cons_ne_zero_of_left` / 定理 `cons_ne_zero_of_left`

English:
theorem cons_ne_zero_of_left
  given: (h : y != 0)
  statement: cons y s != 0
  proof: by
  contrapose h with c
  rw [← cons_zero y s]; rw [c]; rw [Finsupp.coe_zero]; rw [Pi.zero_apply]

中文:
定理 cons_ne_zero_of_left
  条件: (h : y != 0)
  结论: cons y s != 0
  证明: by
  contrapose h with c
  rw [← cons_zero y s]; rw [c]; rw [Finsupp.coe_zero]; rw [Pi.zero_apply]

Depends on / 依赖: Finsupp, Finsupp.coe_zero, Pi.zero_apply, coe_zero, cons_zero, contrapose, zero_apply
-/
theorem cons_ne_zero_of_left (h : y != 0) : cons y s != 0 := by
  contrapose h with c
  rw [← cons_zero y s]; rw [c]; rw [Finsupp.coe_zero]; rw [Pi.zero_apply]

/--
theorem `cons_ne_zero_of_right` / 定理 `cons_ne_zero_of_right`

English:
theorem cons_ne_zero_of_right
  given: (h : s != 0)
  statement: cons y s != 0
  proof: by
  contrapose h with c
  ext a
  simp [← cons_succ a y s, c]

中文:
定理 cons_ne_zero_of_right
  条件: (h : s != 0)
  结论: cons y s != 0
  证明: by
  contrapose h with c
  ext a
  simp [← cons_succ a y s, c]

Depends on / 依赖: cons_succ, contrapose
-/
theorem cons_ne_zero_of_right (h : s != 0) : cons y s != 0 := by
  contrapose h with c
  ext a
  simp [← cons_succ a y s, c]

/--
theorem `cons_ne_zero_iff` / 定理 `cons_ne_zero_iff`

English:
theorem cons_ne_zero_iff
  statement: cons y s != 0 ↔ y != 0 ∨ s != 0
  proof: by
  refine ⟨fun h => ?_, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h']; rw [c]; rw [Finsupp.cons_zero_zero]

中文:
定理 cons_ne_zero_iff
  结论: cons y s != 0 ↔ y != 0 ∨ s != 0
  证明: by
  refine ⟨fun h => ?_, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h']; rw [c]; rw [Finsupp.cons_zero_zero]

Depends on / 依赖: Finsupp, Finsupp.cons_zero_zero, casesOn, cons_ne_zero_of_left, cons_ne_zero_of_right, cons_zero_zero, h.casesOn, imp_iff_not_or
-/
theorem cons_ne_zero_iff : cons y s != 0 ↔ y != 0 ∨ s != 0 := by
  refine ⟨fun h => ?_, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h']; rw [c]; rw [Finsupp.cons_zero_zero]

/--
lemma `cons_support` / 引理 `cons_support`

English:
lemma cons_support
  statement: (s.cons y).support subseteq insert 0 (s.support.map (Fin.succEmb n))
  proof: by
  intro i hi
  suffices i = 0 ∨ exists a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

中文:
引理 cons_support
  结论: (s.cons y).support subseteq insert 0 (s.support.map (Fin.succEmb n))
  证明: by
  intro i hi
  suffices i = 0 ∨ exists a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

Depends on / 依赖: Exists, Exists.imp, Fin.eq_zero_or_eq_succ, Finsupp, Finsupp.mem_support_iff, a.succ, eq_zero_or_eq_succ, mem_support_iff
-/
lemma cons_support : (s.cons y).support subseteq insert 0 (s.support.map (Fin.succEmb n)) := by
  intro i hi
  suffices i = 0 ∨ exists a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

variable (y) in
/--
lemma `cons_right_injective` / 引理 `cons_right_injective`

English:
lemma cons_right_injective
  statement: Injective (Finsupp.cons y : (Fin n ->₀ M) -> Fin (n + 1) ->₀ M)
  proof: (equivFunOnFinite.symm.injective.comp ((Fin.cons_right_injective _).comp DFunLike.coe_injective))

中文:
引理 cons_right_injective
  结论: Injective (Finsupp.cons y : (Fin n ->₀ M) -> Fin (n + 1) ->₀ M)
  证明: (equivFunOnFinite.symm.injective.comp ((Fin.cons_right_injective _).comp DFunLike.coe_injective))

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Fin.cons_right_injective, coe_injective, cons_right_injective, equivFunOnFinite, equivFunOnFinite.symm.injective.comp, injective
-/
lemma cons_right_injective : Injective (Finsupp.cons y : (Fin n ->₀ M) -> Fin (n + 1) ->₀ M) :=
  (equivFunOnFinite.symm.injective.comp ((Fin.cons_right_injective _).comp DFunLike.coe_injective))

/--
theorem `cons_injective2` / 定理 `cons_injective2`

English:
theorem cons_injective2
  statement: Function.Injective2 (cons (n := n) (M := M))
  proof: by
  refine fun x₀ y₀ x y h => ?_
  have := DFunLike.congr_fun h 0
  simp only [cons_zero] at this
  exact ⟨this, cons_right_injective y₀ (this ▸ h)⟩

中文:
定理 cons_injective2
  结论: Function.Injective2 (cons (n := n) (M := M))
  证明: by
  refine fun x₀ y₀ x y h => ?_
  have := DFunLike.congr_fun h 0
  simp only [cons_zero] at this
  exact ⟨this, cons_right_injective y₀ (this ▸ h)⟩

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, cons_right_injective, cons_zero
-/
theorem cons_injective2 : Function.Injective2 (cons (n := n) (M := M)) := by
  refine fun x₀ y₀ x y h => ?_
  have := DFunLike.congr_fun h 0
  simp only [cons_zero] at this
  exact ⟨this, cons_right_injective y₀ (this ▸ h)⟩

/--
lemma `cons_eq_single_zero_iff` / 引理 `cons_eq_single_zero_iff`

English:
lemma cons_eq_single_zero_iff
  given: {x : M}
  statement: s.cons x = single 0 y ↔ s = 0 ∧ x = y
  proof: by
  rw [← cons_zero_eq_single_zero]; rw [cons_injective2.eq_iff]; rw [and_comm]

中文:
引理 cons_eq_single_zero_iff
  条件: {x : M}
  结论: s.cons x = single 0 y ↔ s = 0 ∧ x = y
  证明: by
  rw [← cons_zero_eq_single_zero]; rw [cons_injective2.eq_iff]; rw [and_comm]

Depends on / 依赖: and_comm, cons_injective2, cons_injective2.eq_iff, cons_zero_eq_single_zero, eq_iff
-/
lemma cons_eq_single_zero_iff {x : M} : s.cons x = single 0 y ↔ s = 0 ∧ x = y := by
  rw [← cons_zero_eq_single_zero]; rw [cons_injective2.eq_iff]; rw [and_comm]

/--
lemma `cons_eq_single_succ_iff` / 引理 `cons_eq_single_succ_iff`

English:
lemma cons_eq_single_succ_iff
  given: {x : M}
  statement: s.cons x = single i.succ y ↔ s = single i y ∧ x = 0
  proof: by
  rw [← cons_zero_single_eq_single_succ]; rw [cons_injective2.eq_iff]; rw [and_comm]

中文:
引理 cons_eq_single_succ_iff
  条件: {x : M}
  结论: s.cons x = single i.succ y ↔ s = single i y ∧ x = 0
  证明: by
  rw [← cons_zero_single_eq_single_succ]; rw [cons_injective2.eq_iff]; rw [and_comm]

Depends on / 依赖: and_comm, cons_injective2, cons_injective2.eq_iff, cons_zero_single_eq_single_succ, eq_iff
-/
lemma cons_eq_single_succ_iff {x : M} : s.cons x = single i.succ y ↔ s = single i y ∧ x = 0 := by
  rw [← cons_zero_single_eq_single_succ]; rw [cons_injective2.eq_iff]; rw [and_comm]

end Finsupp
