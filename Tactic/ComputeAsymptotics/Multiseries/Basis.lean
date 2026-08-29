/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs

/-!
# Well-formed bases

## Main definitions

* `WellFormedBasis basis`: a predicate meaning that all functions from `basis` tend to `atTop`,
  and `basis` is sorted such that if
  `g` goes after `f` in `basis`, then `log f =o[atTop] log g`.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Asymptotics Filter

/--
Definition of `WellFormedBasis` / `WellFormedBasis` 的定义

English:
definition WellFormedBasis
  signature: (basis : Basis)
  body: basis.Pairwise (fun x y => (Real.log ∘ y) =o[atTop] (Real.log ∘ x)) ∧
  forall f in basis, Tendsto f atTop atTop

中文:
定义 WellFormedBasis
  签名: (basis : Basis)
  定义体: basis.Pairwise (fun x y => (Real.log ∘ y) =o[atTop] (Real.log ∘ x)) ∧
  forall f in basis, Tendsto f atTop atTop

Depends on / 依赖: Pairwise, Real.log, Tendsto, basis.Pairwise
-/
def WellFormedBasis (basis : Basis) : Prop :=
  basis.Pairwise (fun x y => (Real.log ∘ y) =o[atTop] (Real.log ∘ x)) ∧
  forall f in basis, Tendsto f atTop atTop

namespace WellFormedBasis

/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  statement: WellFormedBasis []
  proof: by simp [WellFormedBasis]

中文:
定理 nil
  结论: WellFormedBasis []
  证明: by simp [WellFormedBasis]

Depends on / 依赖: WellFormedBasis
-/
theorem nil : WellFormedBasis [] := by simp [WellFormedBasis]

/--
theorem `single` / 定理 `single`

English:
theorem single
  given: (f : Real -> Real) (hf : Tendsto f atTop atTop)
  statement: WellFormedBasis [f]
  proof: by
  simpa [WellFormedBasis]

中文:
定理 single
  条件: (f : 实数 -> 实数) (hf : Tendsto f atTop atTop)
  结论: WellFormedBasis [f]
  证明: by
  simpa [WellFormedBasis]

Depends on / 依赖: WellFormedBasis
-/
theorem single (f : Real -> Real) (hf : Tendsto f atTop atTop) : WellFormedBasis [f] := by
  simpa [WellFormedBasis]

/--
theorem `of_sublist` / 定理 `of_sublist`

English:
theorem of_sublist
  statement: {basis basis' : Basis} (h : List.Sublist basis basis')
  proof: ⟨h_basis.left.sublist h, fun _ hf => h_basis.right _ (h.subset hf)⟩

中文:
定理 of_sublist
  结论: {basis basis' : Basis} (h : List.Sublist basis basis')
  证明: ⟨h_basis.left.sublist h, fun _ hf => h_basis.right _ (h.subset hf)⟩

Depends on / 依赖: h.subset, h_basis, h_basis.left.sublist, h_basis.right, sublist, subset
-/
theorem of_sublist {basis basis' : Basis} (h : List.Sublist basis basis')
    (h_basis : WellFormedBasis basis') : WellFormedBasis basis :=
  ⟨h_basis.left.sublist h, fun _ hf => h_basis.right _ (h.subset hf)⟩

/--
theorem `tail` / 定理 `tail`

English:
theorem tail
  statement: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: h.of_sublist (by simp)

中文:
定理 tail
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: h.of_sublist (by simp)

Depends on / 依赖: h.of_sublist, of_sublist
-/
theorem tail {basis_hd : Real -> Real} {basis_tl : Basis}
    (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFormedBasis basis_tl :=
  h.of_sublist (by simp)

/--
theorem `of_append_right` / 定理 `of_append_right`

English:
theorem of_append_right
  given: {left right : Basis} (h : WellFormedBasis (left ++ right))
  proof: h.of_sublist (by simp)

中文:
定理 of_append_right
  条件: {left right : Basis} (h : WellFormedBasis (left ++ right))
  证明: h.of_sublist (by simp)

Depends on / 依赖: h.of_sublist, of_sublist
-/
theorem of_append_right {left right : Basis} (h : WellFormedBasis (left ++ right)) :
    WellFormedBasis right :=
  h.of_sublist (by simp)

/--
theorem `compare_left_aux` / 定理 `compare_left_aux`

English:
theorem compare_left_aux
  statement: {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis)
  proof: by
  intro g hg
  rcases basis.eq_nil_or_concat with rfl | ⟨basis_begin, basis_end, rfl⟩
  · simp at hg
  simp only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
    forall_eq'

中文:
定理 compare_left_aux
  结论: {basis : Basis} {f : 实数 -> 实数} (h : WellFormedBasis basis)
  证明: by
  intro g hg
  rcases basis.eq_nil_or_concat with rfl | ⟨basis_begin, basis_end, rfl⟩
  · simp at hg
  simp only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
    forall_eq'

Depends on / 依赖: List.concat_eq_append, List.getLast, List.mem_append, List.mem_cons, List.not_mem_nil, Option.some.injEq, Option.some_or, WellFormedBasis, _append, _singleton, basis.eq_nil_or_concat, basis_begin, basis_end, concat_eq_append, eq_nil_or_concat, forall_eq, getLast, h_comp, h_comp.trans, mem_append
-/
theorem compare_left_aux {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis)
    (h_comp : forall g, basis.getLast? = .some g -> (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) :
    forall g in basis, (Real.log ∘ f) =o[atTop] (Real.log ∘ g) := by
  intro g hg
  rcases basis.eq_nil_or_concat with rfl | ⟨basis_begin, basis_end, rfl⟩
  · simp at hg
  simp only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
    forall_eq'] at hg h_comp
  rcases hg with hg | hg
  · simp only [WellFormedBasis, List.concat_eq_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at h
    exact h_comp.trans (by grind)
  · grind

/--
theorem `compare_right_aux` / 定理 `compare_right_aux`

English:
theorem compare_right_aux
  statement: {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis)
  proof: by
  intro g hg
  cases basis with
  | nil => simp at hg
  | cons basis_hd basis_tl =>
    specialize h_comp basis_hd (by simp)
    simp only [List.mem_cons] at hg
    rcases hg with hg | hg
    · simpa [hg]
    · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h


中文:
定理 compare_right_aux
  结论: {basis : Basis} {f : 实数 -> 实数} (h : WellFormedBasis basis)
  证明: by
  intro g hg
  cases basis with
  | nil => simp at hg
  | cons basis_hd basis_tl =>
    specialize h_comp basis_hd (by simp)
    simp only [List.mem_cons] at hg
    rcases hg with hg | hg
    · simpa [hg]
    · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h


Depends on / 依赖: List.mem_cons, List.pairwise_cons, WellFormedBasis, basis_hd, basis_tl, forall_eq_or_imp, h_comp, mem_cons, pairwise_cons, specialize
-/
theorem compare_right_aux {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis)
    (h_comp : forall g, basis.head? = .some g -> (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    forall g in basis, (Real.log ∘ g) =o[atTop] (Real.log ∘ f) := by
  intro g hg
  cases basis with
  | nil => simp at hg
  | cons basis_hd basis_tl =>
    specialize h_comp basis_hd (by simp)
    simp only [List.mem_cons] at hg
    rcases hg with hg | hg
    · simpa [hg]
    · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
      exact .trans (by grind) h_comp

/--
theorem `append` / 定理 `append`

English:
theorem append
  statement: {left right : Basis}
  proof: by
  simp only [WellFormedBasis] at *
  constructor
  · simpa [List.pairwise_append, h_left, h_right] using h
  · grind

中文:
定理 append
  结论: {left right : Basis}
  证明: by
  simp only [WellFormedBasis] at *
  constructor
  · simpa [List.pairwise_append, h_left, h_right] using h
  · grind

Depends on / 依赖: List.pairwise_append, WellFormedBasis, h_left, h_right, pairwise_append
-/
theorem append {left right : Basis}
    (h_left : WellFormedBasis left) (h_right : WellFormedBasis right)
    (h : forall f in left, forall g in right, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (left ++ right) := by
  simp only [WellFormedBasis] at *
  constructor
  · simpa [List.pairwise_append, h_left, h_right] using h
  · grind

/--
theorem `cons` / 定理 `cons`

English:
theorem cons
  statement: {basis : Basis} {f : Real -> Real} (h_basis : WellFormedBasis basis)
  proof: by
  change WellFormedBasis ([f] ++ basis)
  exact append (by simpa [WellFormedBasis]) h_basis (by simpa)

中文:
定理 cons
  结论: {basis : Basis} {f : 实数 -> 实数} (h_basis : WellFormedBasis basis)
  证明: by
  change WellFormedBasis ([f] ++ basis)
  exact append (by simpa [WellFormedBasis]) h_basis (by simpa)

Depends on / 依赖: WellFormedBasis, append, h_basis
-/
theorem cons {basis : Basis} {f : Real -> Real} (h_basis : WellFormedBasis basis)
    (hf_tendsto : Tendsto f atTop atTop)
    (hf : forall g in basis, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (f :: basis) := by
  change WellFormedBasis ([f] ++ basis)
  exact append (by simpa [WellFormedBasis]) h_basis (by simpa)

/--
theorem `insert` / 定理 `insert`

English:
theorem insert
  statement: {left right : Basis} {f : Real -> Real}
  proof: by
  have : WellFormedBasis (f :: right) := cons (h.of_sublist (by simp)) hf_tendsto
    (compare_right_aux (h.of_sublist (by simp)) hf_comp_right)
  apply compare_left_aux (h.of_sublist (by simp)) at hf_comp_left
  apply append (h.of_sublist (by simp)) this
  exact fun g hg => compare_right_aux thi

中文:
定理 insert
  结论: {left right : Basis} {f : 实数 -> 实数}
  证明: by
  have : WellFormedBasis (f :: right) := cons (h.of_sublist (by simp)) hf_tendsto
    (compare_right_aux (h.of_sublist (by simp)) hf_comp_right)
  apply compare_left_aux (h.of_sublist (by simp)) at hf_comp_left
  apply append (h.of_sublist (by simp)) this
  exact fun g hg => compare_right_aux thi

Depends on / 依赖: WellFormedBasis, append, compare_left_aux, compare_right_aux, h.of_sublist, hf_comp_left, hf_comp_right, hf_tendsto, of_sublist
-/
theorem insert {left right : Basis} {f : Real -> Real}
    (h : WellFormedBasis (left ++ right)) (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp_left : forall g, left.getLast? = .some g -> (Real.log ∘ f) =o[atTop] (Real.log ∘ g))
    (hf_comp_right : forall g, right.head? = .some g -> (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (left ++ f :: right) := by
  have : WellFormedBasis (f :: right) := cons (h.of_sublist (by simp)) hf_tendsto
    (compare_right_aux (h.of_sublist (by simp)) hf_comp_right)
  apply compare_left_aux (h.of_sublist (by simp)) at hf_comp_left
  apply append (h.of_sublist (by simp)) this
  exact fun g hg => compare_right_aux this (by grind)

/--
theorem `push` / 定理 `push`

English:
theorem push
  statement: {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis)
  proof: insert (by simp [h]) hf_tendsto hf_comp (by simp)

中文:
定理 push
  结论: {basis : Basis} {f : 实数 -> 实数} (h : WellFormedBasis basis)
  证明: insert (by simp [h]) hf_tendsto hf_comp (by simp)

Depends on / 依赖: hf_comp, hf_tendsto, insert
-/
theorem push {basis : Basis} {f : Real -> Real} (h : WellFormedBasis basis)
    (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp : forall g, basis.getLast? = .some g -> (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) :
    WellFormedBasis (basis ++ [f]) :=
  insert (by simp [h]) hf_tendsto hf_comp (by simp)

/--
theorem `tendsto_atTop` / 定理 `tendsto_atTop`

English:
theorem tendsto_atTop
  statement: {basis : Basis} (h : WellFormedBasis basis) {f : Real -> Real}
  proof: h.right f hf

中文:
定理 tendsto_atTop
  结论: {basis : Basis} (h : WellFormedBasis basis) {f : 实数 -> 实数}
  证明: h.right f hf

Depends on / 依赖: h.right
-/
theorem tendsto_atTop {basis : Basis} (h : WellFormedBasis basis) {f : Real -> Real}
    (hf : f in basis) :
    Tendsto f atTop atTop := h.right f hf

/--
theorem `eventually_pos` / 定理 `eventually_pos`

English:
theorem eventually_pos
  given: {basis : Basis} (h : WellFormedBasis basis)
  proof: by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    exact (h.right.left.eventually <| eventually_gt_atTop 0).and (ih (by tauto))

中文:
定理 eventually_pos
  条件: {basis : Basis} (h : WellFormedBasis basis)
  证明: by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    exact (h.right.left.eventually <| eventually_gt_atTop 0).and (ih (by tauto))

Depends on / 依赖: List.mem_cons, List.pairwise_cons, WellFormedBasis, eventually, eventually_gt_atTop, forall_eq_or_imp, h.right.left.eventually, mem_cons, pairwise_cons
-/
theorem eventually_pos {basis : Basis} (h : WellFormedBasis basis) :
    forallᶠ x in atTop, forall f in basis, 0 < f x := by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    exact (h.right.left.eventually <| eventually_gt_atTop 0).and (ih (by tauto))

/--
theorem `head_eventually_pos` / 定理 `head_eventually_pos`

English:
theorem head_eventually_pos
  statement: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: (forall_eventually_of_eventually_forall h.eventually_pos basis_hd).mono (by grind)

中文:
定理 head_eventually_pos
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: (forall_eventually_of_eventually_forall h.eventually_pos basis_hd).mono (by grind)

Depends on / 依赖: basis_hd, eventually_pos, forall_eventually_of_eventually_forall, h.eventually_pos
-/
theorem head_eventually_pos {basis_hd : Real -> Real} {basis_tl : Basis}
    (h : WellFormedBasis (basis_hd :: basis_tl)) : forallᶠ x in atTop, 0 < basis_hd x :=
  (forall_eventually_of_eventually_forall h.eventually_pos basis_hd).mono (by grind)

/--
theorem `tail_isLittleO_head` / 定理 `tail_isLittleO_head`

English:
theorem tail_isLittleO_head
  statement: {hd : Real -> Real} {tl : Basis}
  proof: by
  rw [WellFormedBasis]; rw [List.pairwise_cons] at h
  exact h.left.left _ hf

中文:
定理 tail_isLittleO_head
  结论: {hd : 实数 -> 实数} {tl : Basis}
  证明: by
  rw [WellFormedBasis]; rw [List.pairwise_cons] at h
  exact h.left.left _ hf

Depends on / 依赖: List.pairwise_cons, WellFormedBasis, h.left.left, pairwise_cons
-/
theorem tail_isLittleO_head {hd : Real -> Real} {tl : Basis}
    (h : WellFormedBasis (hd :: tl)) {f : Real -> Real} (hf : f in tl) :
    (Real.log ∘ f) =o[atTop] (Real.log ∘ hd) := by
  rw [WellFormedBasis]; rw [List.pairwise_cons] at h
  exact h.left.left _ hf

/--
theorem `push_log_last` / 定理 `push_log_last`

English:
theorem push_log_last
  statement: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  apply h_basis.push
  · simp [Real.tendsto_log_atTop.comp, h_basis.right]
  · intro g hg
simpa [List.getLast_of_getLast?_eq_some hg] using Real.isLittleO_log_id_atTop.comp_tendsto
Real.tendsto_log_atTop.comp h_basis.tendsto_atTop List.mem_of_getLast? hg

中文:
定理 push_log_last
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: by
  apply h_basis.push
  · simp [Real.tendsto_log_atTop.comp, h_basis.right]
  · intro g hg
simpa [List.getLast_of_getLast?_eq_some hg] using Real.isLittleO_log_id_atTop.comp_tendsto
Real.tendsto_log_atTop.comp h_basis.tendsto_atTop List.mem_of_getLast? hg

Depends on / 依赖: List.getLast_of_getLast, List.mem_of_getLast, Real.isLittleO_log_id_atTop.comp_tendsto, Real.tendsto_log_atTop.comp, _eq_some, comp_tendsto, getLast_of_getLast, h_basis, h_basis.push, h_basis.right, h_basis.tendsto_atTop, isLittleO_log_id_atTop, mem_of_getLast, tendsto_atTop, tendsto_log_atTop
-/
theorem push_log_last {basis_hd : Real -> Real} {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    WellFormedBasis ((basis_hd :: basis_tl) ++
      [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) := by
  apply h_basis.push
  · simp [Real.tendsto_log_atTop.comp, h_basis.right]
  · intro g hg
simpa [List.getLast_of_getLast?_eq_some hg] using Real.isLittleO_log_id_atTop.comp_tendsto
Real.tendsto_log_atTop.comp h_basis.tendsto_atTop List.mem_of_getLast? hg

/--
theorem `pow_isLittleO_pow_of_log` / 定理 `pow_isLittleO_pow_of_log`

English:
theorem pow_isLittleO_pow_of_log
  statement: {f g : Real -> Real} (a b : Real) (hf : forallᶠ x in atTop, 0 < f x)
  proof: by
  apply IsLittleO.of_tendsto_div_atTop
  apply Tendsto.congr' (f₁ := Real.exp ∘ (b • Real.log ∘ g - a • Real.log ∘ f))
  · refine (hf.and (hg.eventually_gt_atTop 0)).mono (fun x ⟨hf, hg⟩ => ?_)
    simp [Real.exp_sub, mul_comm a, mul_comm b, Real.exp_mul, Real.exp_log hg, Real.exp_log hf]
  apply

中文:
定理 pow_isLittleO_pow_of_log
  结论: {f g : 实数 -> 实数} (a b : 实数) (hf : 对任意ᶠ x in atTop, 0 < f x)
  证明: by
  apply IsLittleO.of_tendsto_div_atTop
  apply Tendsto.congr' (f₁ := Real.exp ∘ (b • Real.log ∘ g - a • Real.log ∘ f))
  · refine (hf.and (hg.eventually_gt_atTop 0)).mono (fun x ⟨hf, hg⟩ => ?_)
    simp [Real.exp_sub, mul_comm a, mul_comm b, Real.exp_mul, Real.exp_log hg, Real.exp_log hf]
  apply

Depends on / 依赖: IsLittleO, IsLittleO.of_tendsto_div_atTop, Real.exp, Real.exp_log, Real.exp_mul, Real.exp_sub, Real.log, Real.tendsto_exp_atTop.comp, Tendsto, Tendsto.congr, const_mul_left, const_mul_right, eventually_gt_atTop, exp_log, exp_mul, exp_sub, h.const_mul_left, hf.and, hg.eventually_gt_atTop, mul_comm
-/
theorem pow_isLittleO_pow_of_log {f g : Real -> Real} (a b : Real) (hf : forallᶠ x in atTop, 0 < f x)
    (hg : Tendsto g atTop atTop) (h : (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) (hb : 0 < b) :
    (f ^ a) =o[atTop] (g ^ b) := by
  apply IsLittleO.of_tendsto_div_atTop
  apply Tendsto.congr' (f₁ := Real.exp ∘ (b • Real.log ∘ g - a • Real.log ∘ f))
  · refine (hf.and (hg.eventually_gt_atTop 0)).mono (fun x ⟨hf, hg⟩ => ?_)
    simp [Real.exp_sub, mul_comm a, mul_comm b, Real.exp_mul, Real.exp_log hg, Real.exp_log hf]
  apply Real.tendsto_exp_atTop.comp
  have h' : (b • Real.log ∘ g - a • Real.log ∘ f) ~[atTop] b • Real.log ∘ g := by
    replace h : (a • Real.log ∘ f) =o[atTop] (b • Real.log ∘ g) :=
      (h.const_mul_left a).const_mul_right (hb.ne')
    grind only [IsEquivalent.sub_isLittleO, IsEquivalent.refl]
  rw [h'.tendsto_atTop_iff]
  apply Filter.Tendsto.const_mul_atTop hb
  apply Real.tendsto_log_atTop.comp hg

/--
theorem `tail_pow_majorized_head` / 定理 `tail_pow_majorized_head`

English:
theorem tail_pow_majorized_head
  statement: {hd f : Real -> Real} {tl : Basis}
  proof: by
  intro exp h_exp
  apply pow_isLittleO_pow_of_log
  · exact h_basis.tail.eventually_pos.mono fun _ h => h _ hf
  · exact h_basis.tendsto_atTop (by simp)
  · grind [WellFormedBasis, List.pairwise_cons]
  · exact h_exp

中文:
定理 tail_pow_majorized_head
  结论: {hd f : 实数 -> 实数} {tl : Basis}
  证明: by
  intro exp h_exp
  apply pow_isLittleO_pow_of_log
  · exact h_basis.tail.eventually_pos.mono fun _ h => h _ hf
  · exact h_basis.tendsto_atTop (by simp)
  · grind [WellFormedBasis, List.pairwise_cons]
  · exact h_exp

Depends on / 依赖: List.pairwise_cons, WellFormedBasis, eventually_pos, h_basis, h_basis.tail.eventually_pos.mono, h_basis.tendsto_atTop, h_exp, pairwise_cons, pow_isLittleO_pow_of_log, tendsto_atTop
-/
theorem tail_pow_majorized_head {hd f : Real -> Real} {tl : Basis}
    (h_basis : WellFormedBasis (hd :: tl)) (hf : f in tl) (r : Real) :
    Majorized (f ^ r) hd 0 := by
  intro exp h_exp
  apply pow_isLittleO_pow_of_log
  · exact h_basis.tail.eventually_pos.mono fun _ h => h _ hf
  · exact h_basis.tendsto_atTop (by simp)
  · grind [WellFormedBasis, List.pairwise_cons]
  · exact h_exp

end WellFormedBasis

/-! ### Basis extensions -/

/--
Inductive type `BasisExtension` / 归纳类型 `BasisExtension`

English:
inductive BasisExtension
  parameters: : Basis -> Type
  constructors (3):
    - nil: BasisExtension []
    - keep: (basis_hd : Real -> Real) {basis_tl : Basis} (ex : BasisExtension basis_tl) : BasisExtension (basis_hd :: basis_tl)
    - insert: {basis : Basis} (f : Real -> Real) (ex : BasisExtension basis) : BasisExtension basis

中文:
归纳类型 BasisExtension
  参数: : Basis -> Type
  构造子 (3 个):
    - nil: BasisExtension []
    - keep: (basis_hd : 实数 -> 实数) {basis_tl : Basis} (ex : BasisExtension basis_tl) : BasisExtension (basis_hd :: basis_tl)
    - insert: {basis : Basis} (f : 实数 -> 实数) (ex : BasisExtension basis) : BasisExtension basis
-/
inductive BasisExtension : Basis -> Type
| nil : BasisExtension []
| keep (basis_hd : Real -> Real) {basis_tl : Basis} (ex : BasisExtension basis_tl) :
  BasisExtension (basis_hd :: basis_tl)
| insert {basis : Basis} (f : Real -> Real) (ex : BasisExtension basis) : BasisExtension basis

namespace BasisExtension

/--
Definition of `getBasis` / `getBasis` 的定义

English:
definition getBasis
  signature: {basis : Basis} (ex : BasisExtension basis)
  body: match ex with
  | nil => []
  | keep basis_hd ex => basis_hd :: ex.getBasis
  | insert f ex => f :: ex.getBasis

中文:
定义 getBasis
  签名: {basis : Basis} (ex : BasisExtension basis)
  定义体: match ex with
  | nil => []
  | keep basis_hd ex => basis_hd :: ex.getBasis
  | insert f ex => f :: ex.getBasis

Depends on / 依赖: basis_hd, ex.getBasis, getBasis, insert
-/
def getBasis {basis : Basis} (ex : BasisExtension basis) : Basis :=
  match ex with
  | nil => []
  | keep basis_hd ex => basis_hd :: ex.getBasis
  | insert f ex => f :: ex.getBasis

/--
theorem `sublist_getBasis` / 定理 `sublist_getBasis`

English:
theorem sublist_getBasis
  given: {basis : Basis} {ex : BasisExtension basis}
  proof: by
  induction ex with
  | nil => simp
  | keep _ ex ih => simpa [getBasis] using ih
  | insert _ ex ih => exact List.Sublist.cons _ ih

中文:
定理 sublist_getBasis
  条件: {basis : Basis} {ex : BasisExtension basis}
  证明: by
  induction ex with
  | nil => simp
  | keep _ ex ih => simpa [getBasis] using ih
  | insert _ ex ih => exact List.Sublist.cons _ ih

Depends on / 依赖: List.Sublist.cons, Sublist, getBasis, insert
-/
theorem sublist_getBasis {basis : Basis} {ex : BasisExtension basis} :
    List.Sublist basis ex.getBasis := by
  induction ex with
  | nil => simp
  | keep _ ex ih => simpa [getBasis] using ih
  | insert _ ex ih => exact List.Sublist.cons _ ih

/--
theorem `insert_tail_wellFormedBasis` / 定理 `insert_tail_wellFormedBasis`

English:
theorem insert_tail_wellFormedBasis
  statement: {basis : Basis} {f : Real -> Real}
  proof: h_basis.of_sublist (by simp [getBasis])

中文:
定理 insert_tail_wellFormedBasis
  结论: {basis : Basis} {f : 实数 -> 实数}
  证明: h_basis.of_sublist (by simp [getBasis])

Depends on / 依赖: getBasis, h_basis, h_basis.of_sublist, of_sublist
-/
theorem insert_tail_wellFormedBasis {basis : Basis} {f : Real -> Real}
    {ex_tl : BasisExtension basis}
    (h_basis : WellFormedBasis <| BasisExtension.getBasis (.insert f ex_tl)) :
    WellFormedBasis ex_tl.getBasis :=
  h_basis.of_sublist (by simp [getBasis])

end BasisExtension

end Tactic.ComputeAsymptotics
