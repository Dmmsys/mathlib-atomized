/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.ElementarySubstructures

/-!
# Skolem Functions and Downward Löwenheim–Skolem

## Main Definitions

- `FirstOrder.Language.skolem₁` is a language consisting of Skolem functions for another language.

## Main Results

- `FirstOrder.Language.exists_elementarySubstructure_card_eq` is the Downward Löwenheim–Skolem
  theorem: If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (#s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.

## TODO

- Use `skolem₁` recursively to construct an actual Skolemization of a language.
-/

@[expose] public section


universe u v w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable (L : Language.{u, v}) {M : Type w} [Nonempty M] [L.Structure M]

/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language. -/
@[simps]
/--
Definition of `skolem₁` / `skolem₁` 的定义

English:
definition skolem₁
  signature: : Language
  body: ⟨fun n => L.BoundedFormula Empty (n + 1), fun _ => Empty⟩

中文:
定义 skolem₁
  签名: : Language
  定义体: ⟨fun n => L.BoundedFormula Empty (n + 1), fun _ => Empty⟩

Depends on / 依赖: BoundedFormula, L.BoundedFormula
-/
def skolem₁ : Language :=
  ⟨fun n => L.BoundedFormula Empty (n + 1), fun _ => Empty⟩

variable {L}

/--
theorem `card_functions_sum_skolem₁` / 定理 `card_functions_sum_skolem₁`

English:
theorem card_functions_sum_skolem₁
  proof: by
  simp only [card_functions_sum, skolem₁_Functions, mk_sigma, sum_add_distrib']
  conv_lhs => enter [2, 1, i]; rw [lift_id'.{u, v}]
  rw [add_comm]; rw [add_eq_max]; rw [max_eq_left]
  · gcongr with n
    rw [← lift_le.{_]; rw [max u v}]; rw [lift_lift]; rw [lift_mk_le.{v}]
    refine ⟨⟨fun f => (func f default).bdEqual (func f default), fun f g h => ?_⟩⟩
    rcases h with ⟨rfl, ⟨rfl⟩⟩
    rfl
  · rw [← mk_sigma]
    exact infinite_iff.1 (Infinite.of_injective (fun n => ⟨n, ⊥⟩) fun x y xy =>
      (Sigma.mk.inj_iff.1 xy).1)

中文:
定理 card_functions_sum_skolem₁
  证明: by
  simp only [card_functions_sum, skolem₁_Functions, mk_sigma, sum_add_distrib']
  conv_lhs => enter [2, 1, i]; rw [lift_id'.{u, v}]
  rw [add_comm]; rw [add_eq_max]; rw [max_eq_left]
  · gcongr with n
    rw [← lift_le.{_]; rw [max u v}]; rw [lift_lift]; rw [lift_mk_le.{v}]
    refine ⟨⟨fun f => (func f default).bdEqual (func f default), fun f g h => ?_⟩⟩
    rcases h with ⟨rfl, ⟨rfl⟩⟩
    rfl
  · rw [← mk_sigma]
    exact infinite_iff.1 (Infinite.of_injective (fun n => ⟨n, ⊥⟩) fun x y xy =>
      (Sigma.mk.inj_iff.1 xy).1)

Depends on / 依赖: Infinite, Infinite.of_injective, Sigma.mk.inj_iff, add_comm, add_eq_max, bdEqual, card_functions_sum, conv_lhs, infinite_iff, inj_iff, lift_id, lift_le, lift_lift, lift_mk_le, max_eq_left, mk_sigma, of_injective, sum_add_distrib
-/
theorem card_functions_sum_skolem₁ :
    #(Σ n, (L.sum L.skolem₁).Functions n) = #(Σ n, L.BoundedFormula Empty (n + 1)) := by
  simp only [card_functions_sum, skolem₁_Functions, mk_sigma, sum_add_distrib']
  conv_lhs => enter [2, 1, i]; rw [lift_id'.{u, v}]
  rw [add_comm]; rw [add_eq_max]; rw [max_eq_left]
  · gcongr with n
    rw [← lift_le.{_]; rw [max u v}]; rw [lift_lift]; rw [lift_mk_le.{v}]
    refine ⟨⟨fun f => (func f default).bdEqual (func f default), fun f g h => ?_⟩⟩
    rcases h with ⟨rfl, ⟨rfl⟩⟩
    rfl
  · rw [← mk_sigma]
    exact infinite_iff.1 (Infinite.of_injective (fun n => ⟨n, ⊥⟩) fun x y xy =>
      (Sigma.mk.inj_iff.1 xy).1)

/--
theorem `card_functions_sum_skolem₁_le` / 定理 `card_functions_sum_skolem₁_le`

English:
theorem card_functions_sum_skolem₁_le
  statement: #(Σ n, (L.sum L.skolem₁).Functions n) <= max ℵ₀ L.card
  proof: by
  rw [card_functions_sum_skolem₁]
  trans #(Σ n, L.BoundedFormula Empty n)
  · exact
      ⟨⟨Sigma.map Nat.succ fun _ => id,
          Nat.succ_injective.sigma_map fun _ => Function.injective_id⟩⟩
  · refine _root_.trans BoundedFormula.card_le (lift_le.{max u v}.1 ?_)
    simp only [mk_empty, lift_zero, lift_uzero, zero_add]
    rfl

中文:
定理 card_functions_sum_skolem₁_le
  结论: #(Σ n, (L.求和 L.skolem₁).函数 n) <= 最大值 ℵ₀ L.card
  证明: by
  rw [card_functions_sum_skolem₁]
  trans #(Σ n, L.BoundedFormula Empty n)
  · exact
      ⟨⟨Sigma.map Nat.succ fun _ => id,
          Nat.succ_injective.sigma_map fun _ => Function.injective_id⟩⟩
  · refine _root_.trans BoundedFormula.card_le (lift_le.{max u v}.1 ?_)
    simp only [mk_empty, lift_zero, lift_uzero, zero_add]
    rfl

Depends on / 依赖: BoundedFormula, BoundedFormula.card_le, Function, Function.injective_id, L.BoundedFormula, Nat.succ, Nat.succ_injective.sigma_map, Sigma.map, _root_, _root_.trans, card_le, injective_id, lift_le, lift_uzero, lift_zero, mk_empty, sigma_map, succ_injective, zero_add
-/
theorem card_functions_sum_skolem₁_le : #(Σ n, (L.sum L.skolem₁).Functions n) <= max ℵ₀ L.card := by
  rw [card_functions_sum_skolem₁]
  trans #(Σ n, L.BoundedFormula Empty n)
  · exact
      ⟨⟨Sigma.map Nat.succ fun _ => id,
          Nat.succ_injective.sigma_map fun _ => Function.injective_id⟩⟩
  · refine _root_.trans BoundedFormula.card_le (lift_le.{max u v}.1 ?_)
    simp only [mk_empty, lift_zero, lift_uzero, zero_add]
    rfl

/--
Instance `skolem₁Structure` / 实例 `skolem₁Structure`

English:
instance skolem₁Structure
  signature: : L.skolem₁.Structure M
  body: ⟨fun {_} φ x => Classical.epsilon fun a => φ.Realize default (Fin.snoc x a : _ -> M), fun {_} r =>
    Empty.elim r⟩

中文:
实例 skolem₁Structure
  签名: : L.skolem₁.结构 M
  定义体: ⟨fun {_} φ x => Classical.epsilon fun a => φ.Realize default (Fin.snoc x a : _ -> M), fun {_} r =>
    Empty.elim r⟩

Depends on / 依赖: Classical, Classical.epsilon, Empty.elim, Fin.snoc, Realize, epsilon
-/
noncomputable instance skolem₁Structure : L.skolem₁.Structure M :=
  ⟨fun {_} φ x => Classical.epsilon fun a => φ.Realize default (Fin.snoc x a : _ -> M), fun {_} r =>
    Empty.elim r⟩

namespace Substructure

/--
theorem `skolem₁_reduct_isElementary` / 定理 `skolem₁_reduct_isElementary`

English:
theorem skolem₁_reduct_isElementary
  given: (S : (L.sum L.skolem₁).Substructure M)
  proof: by
  apply (LHom.sumInl.substructureReduct S).isElementary_of_exists
  intro n φ x a h
  let φ' : (L.sum L.skolem₁).Functions n := LHom.sumInr.onFunction φ
  use ⟨funMap φ' ((↑) ∘ x), ?_⟩
  · exact Classical.epsilon_spec (p := fun a => BoundedFormula.Realize φ default
          (Fin.snoc (Subtype.val ∘ x) a)) ⟨a, h⟩
  · exact S.fun_mem (LHom.sumInr.onFunction φ) ((↑) ∘ x) (by
      exact fun i => (x i).2)

中文:
定理 skolem₁_reduct_isElementary
  条件: (S : (L.求和 L.skolem₁).子结构 M)
  证明: by
  apply (LHom.sumInl.substructureReduct S).isElementary_of_exists
  intro n φ x a h
  let φ' : (L.sum L.skolem₁).Functions n := LHom.sumInr.onFunction φ
  use ⟨funMap φ' ((↑) ∘ x), ?_⟩
  · exact Classical.epsilon_spec (p := fun a => BoundedFormula.Realize φ default
          (Fin.snoc (Subtype.val ∘ x) a)) ⟨a, h⟩
  · exact S.fun_mem (LHom.sumInr.onFunction φ) ((↑) ∘ x) (by
      exact fun i => (x i).2)

Depends on / 依赖: BoundedFormula, BoundedFormula.Realize, Classical, Classical.epsilon_spec, Fin.snoc, Functions, L.skolem, L.sum, LHom.sumInl.substructureReduct, LHom.sumInr.onFunction, Realize, S.fun_mem, Subtype, Subtype.val, epsilon_spec, funMap, fun_mem, isElementary_of_exists, onFunction, substructureReduct
-/
theorem skolem₁_reduct_isElementary (S : (L.sum L.skolem₁).Substructure M) :
    (LHom.sumInl.substructureReduct S).IsElementary := by
  apply (LHom.sumInl.substructureReduct S).isElementary_of_exists
  intro n φ x a h
  let φ' : (L.sum L.skolem₁).Functions n := LHom.sumInr.onFunction φ
  use ⟨funMap φ' ((↑) ∘ x), ?_⟩
  · exact Classical.epsilon_spec (p := fun a => BoundedFormula.Realize φ default
          (Fin.snoc (Subtype.val ∘ x) a)) ⟨a, h⟩
  · exact S.fun_mem (LHom.sumInr.onFunction φ) ((↑) ∘ x) (by
      exact fun i => (x i).2)

/--
Definition of `elementarySkolem₁Reduct` / `elementarySkolem₁Reduct` 的定义

English:
definition elementarySkolem₁Reduct
  signature: (S : (L.sum L.skolem₁).Substructure M)
  body: ⟨LHom.sumInl.substructureReduct S, S.skolem₁_reduct_isElementary⟩

中文:
定义 elementarySkolem₁Reduct
  签名: (S : (L.求和 L.skolem₁).子结构 M)
  定义体: ⟨LHom.sumInl.substructureReduct S, S.skolem₁_reduct_isElementary⟩

Depends on / 依赖: LHom.sumInl.substructureReduct, S.skolem, substructureReduct, sumInl
-/
noncomputable def elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) :
    L.ElementarySubstructure M :=
  ⟨LHom.sumInl.substructureReduct S, S.skolem₁_reduct_isElementary⟩

/--
theorem `coeSort_elementarySkolem₁Reduct` / 定理 `coeSort_elementarySkolem₁Reduct`

English:
theorem coeSort_elementarySkolem₁Reduct
  given: (S : (L.sum L.skolem₁).Substructure M)
  proof: rfl

中文:
定理 coeSort_elementarySkolem₁Reduct
  条件: (S : (L.求和 L.skolem₁).子结构 M)
  证明: rfl
-/
theorem coeSort_elementarySkolem₁Reduct (S : (L.sum L.skolem₁).Substructure M) :
    (S.elementarySkolem₁Reduct : Type w) = S :=
  rfl

end Substructure

open Substructure

variable (L) (M)

/--
Instance `Substructure.elementarySkolem₁Reduct.instSmall` / 实例 `Substructure.elementarySkolem₁Reduct.instSmall`

English:
instance Substructure.elementarySkolem₁Reduct.instSmall
  signature: :
  body: by
  rw [coeSort_elementarySkolem₁Reduct]
  infer_instance

omit [Nonempty M]

中文:
实例 子结构.elementarySkolem₁Reduct.instSmall
  签名: :
  定义体: by
  rw [coeSort_elementarySkolem₁Reduct]
  infer_instance

omit [Nonempty M]

Depends on / 依赖: infer_instance
-/
instance Substructure.elementarySkolem₁Reduct.instSmall :
    Small.{max u v} (⊥ : (L.sum L.skolem₁).Substructure M).elementarySkolem₁Reduct := by
  rw [coeSort_elementarySkolem₁Reduct]
  infer_instance

omit [Nonempty M]

/--
theorem `exists_small_elementarySubstructure` / 定理 `exists_small_elementarySubstructure`

English:
theorem exists_small_elementarySubstructure
  statement: exists S : L.ElementarySubstructure M, Small.{max u v} S
  proof: (isEmpty_or_nonempty M).elim
    (fun _ => ⟨⊤, Countable.toSmall _⟩)
    (fun _ => ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩)

中文:
定理 存在_small_elementarySubstructure
  结论: 存在 S : L.ElementarySubstructure M, Small.{最大值 u v} S
  证明: (isEmpty_or_nonempty M).elim
    (fun _ => ⟨⊤, Countable.toSmall _⟩)
    (fun _ => ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩)

Depends on / 依赖: Countable, Countable.toSmall, Substructure, Substructure.elementarySkolem, isEmpty_or_nonempty, toSmall
-/
theorem exists_small_elementarySubstructure : exists S : L.ElementarySubstructure M, Small.{max u v} S :=
  (isEmpty_or_nonempty M).elim
    (fun _ => ⟨⊤, Countable.toSmall _⟩)
    (fun _ => ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩)

variable {M}

/--
theorem `exists_elementarySubstructure_card_eq` / 定理 `exists_elementarySubstructure_card_eq`

English:
theorem exists_elementarySubstructure_card_eq
  statement: (s : Set M) (κ : Cardinal.{w'}) (h1 : ℵ₀ <= κ)
  proof: by
  obtain ⟨s', hs'⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  rw [← aleph0_le_lift.{_]; rw [w}] at h1
  rw [← hs'] at h1 h2 ⊢
  have : Nonempty M := nonempty_ulift.1 (Cardinal.mk_ne_zero_iff.1
    (aleph0_pos.trans_le (h1.trans (Cardinal.mk_subtype_le _))).ne')
  refine
    ⟨elementarySkolem₁Reduct (closure (L.sum L.skolem₁) (s union Equiv.ulift '' s')),
      (s.subset_union_left).trans subset_closure, ?_⟩
  have h := mk_image_eq_lift _ s' Equiv.ulift.injective
  rw [lift_umax.{w]; rw [w'}]; rw [lift_id'.{w]; rw [w'}] at h
  rw [coeSort_elementarySkolem₁Reduct]; rw [← h]; rw [lift_inj]
  refine
    le_antisymm (lift_le.1 (lift_card_closure_le.trans ?_))
      (mk_le_mk_of_subset ((s.subset_union_right).trans subset_closure))
  rw [max_le_iff]; rw [aleph0_le_lift]; rw [← aleph0_le_lift.{_]; rw [w'}]; rw [h]; rw [add_eq_max]; rw [max_le_iff]; rw [lift_le]
  · refine ⟨h1, (mk_union_le _ _).trans ?_, (lift_le.2 card_functions_sum_skolem₁_le).trans ?_⟩
    · rw [← lift_le, lift_add, h, add_comm, add_eq_max h1]
      exact max_le le_rfl h2
    · rw [lift_max, lift_aleph0, max_le_iff, aleph0_le_lift, and_comm, ← lift_le.{w'},
        lift_lift, lift_lift, ← aleph0_le_lift, h]
      refine ⟨?_, h1⟩
      rw [← lift_lift.{w']; rw [w}]
      refine _root_.trans (lift_le.{w}.2 h3) ?_
      rw [lift_lift]; rw [← lift_lift.{w]; rw [max u v}]; rw [← hs']; rw [← h]; rw [lift_lift]
  · refine _root_.trans ?_ (lift_le.2 (mk_le_mk_of_subset Set.subset_union_right))
    rw [aleph0_le_lift]; rw [← aleph0_le_lift]; rw [h]
    exact h1

中文:
定理 存在_elementarySubstructure_card_eq
  结论: (s : 集合 M) (κ : 基数.{w'}) (h1 : ℵ₀ <= κ)
  证明: by
  obtain ⟨s', hs'⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  rw [← aleph0_le_lift.{_]; rw [w}] at h1
  rw [← hs'] at h1 h2 ⊢
  have : Nonempty M := nonempty_ulift.1 (Cardinal.mk_ne_zero_iff.1
    (aleph0_pos.trans_le (h1.trans (Cardinal.mk_subtype_le _))).ne')
  refine
    ⟨elementarySkolem₁Reduct (closure (L.sum L.skolem₁) (s union Equiv.ulift '' s')),
      (s.subset_union_left).trans subset_closure, ?_⟩
  have h := mk_image_eq_lift _ s' Equiv.ulift.injective
  rw [lift_umax.{w]; rw [w'}]; rw [lift_id'.{w]; rw [w'}] at h
  rw [coeSort_elementarySkolem₁Reduct]; rw [← h]; rw [lift_inj]
  refine
    le_antisymm (lift_le.1 (lift_card_closure_le.trans ?_))
      (mk_le_mk_of_subset ((s.subset_union_right).trans subset_closure))
  rw [max_le_iff]; rw [aleph0_le_lift]; rw [← aleph0_le_lift.{_]; rw [w'}]; rw [h]; rw [add_eq_max]; rw [max_le_iff]; rw [lift_le]
  · refine ⟨h1, (mk_union_le _ _).trans ?_, (lift_le.2 card_functions_sum_skolem₁_le).trans ?_⟩
    · rw [← lift_le, lift_add, h, add_comm, add_eq_max h1]
      exact max_le le_rfl h2
    · rw [lift_max, lift_aleph0, max_le_iff, aleph0_le_lift, and_comm, ← lift_le.{w'},
        lift_lift, lift_lift, ← aleph0_le_lift, h]
      refine ⟨?_, h1⟩
      rw [← lift_lift.{w']; rw [w}]
      refine _root_.trans (lift_le.{w}.2 h3) ?_
      rw [lift_lift]; rw [← lift_lift.{w]; rw [max u v}]; rw [← hs']; rw [← h]; rw [lift_lift]
  · refine _root_.trans ?_ (lift_le.2 (mk_le_mk_of_subset Set.subset_union_right))
    rw [aleph0_le_lift]; rw [← aleph0_le_lift]; rw [h]
    exact h1

Depends on / 依赖: Cardinal, Cardinal.le_mk_iff_exists_set, Cardinal.mk_ne_zero_iff, Cardinal.mk_subtype_le, Equiv.ulift, Equiv.ulift.injective, L.skolem, L.sum, Nonempty, aleph0_le_lift, aleph0_pos, aleph0_pos.trans_le, closure, h1.trans, injective, le_mk_iff_exists_set, lift_id, lift_umax, mk_image_eq_lift, mk_ne_zero_iff
-/
theorem exists_elementarySubstructure_card_eq (s : Set M) (κ : Cardinal.{w'}) (h1 : ℵ₀ <= κ)
    (h2 : Cardinal.lift.{w'} #s <= Cardinal.lift.{w} κ)
    (h3 : Cardinal.lift.{w'} L.card <= Cardinal.lift.{max u v} κ)
    (h4 : Cardinal.lift.{w} κ <= Cardinal.lift.{w'} #M) :
    exists S : L.ElementarySubstructure M, s subseteq S ∧ Cardinal.lift.{w'} #S = Cardinal.lift.{w} κ := by
  obtain ⟨s', hs'⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  rw [← aleph0_le_lift.{_]; rw [w}] at h1
  rw [← hs'] at h1 h2 ⊢
  have : Nonempty M := nonempty_ulift.1 (Cardinal.mk_ne_zero_iff.1
    (aleph0_pos.trans_le (h1.trans (Cardinal.mk_subtype_le _))).ne')
  refine
    ⟨elementarySkolem₁Reduct (closure (L.sum L.skolem₁) (s union Equiv.ulift '' s')),
      (s.subset_union_left).trans subset_closure, ?_⟩
  have h := mk_image_eq_lift _ s' Equiv.ulift.injective
  rw [lift_umax.{w]; rw [w'}]; rw [lift_id'.{w]; rw [w'}] at h
  rw [coeSort_elementarySkolem₁Reduct]; rw [← h]; rw [lift_inj]
  refine
    le_antisymm (lift_le.1 (lift_card_closure_le.trans ?_))
      (mk_le_mk_of_subset ((s.subset_union_right).trans subset_closure))
  rw [max_le_iff]; rw [aleph0_le_lift]; rw [← aleph0_le_lift.{_]; rw [w'}]; rw [h]; rw [add_eq_max]; rw [max_le_iff]; rw [lift_le]
  · refine ⟨h1, (mk_union_le _ _).trans ?_, (lift_le.2 card_functions_sum_skolem₁_le).trans ?_⟩
    · rw [← lift_le, lift_add, h, add_comm, add_eq_max h1]
      exact max_le le_rfl h2
    · rw [lift_max, lift_aleph0, max_le_iff, aleph0_le_lift, and_comm, ← lift_le.{w'},
        lift_lift, lift_lift, ← aleph0_le_lift, h]
      refine ⟨?_, h1⟩
      rw [← lift_lift.{w']; rw [w}]
      refine _root_.trans (lift_le.{w}.2 h3) ?_
      rw [lift_lift]; rw [← lift_lift.{w]; rw [max u v}]; rw [← hs']; rw [← h]; rw [lift_lift]
  · refine _root_.trans ?_ (lift_le.2 (mk_le_mk_of_subset Set.subset_union_right))
    rw [aleph0_le_lift]; rw [← aleph0_le_lift]; rw [h]
    exact h1

end Language

end FirstOrder
