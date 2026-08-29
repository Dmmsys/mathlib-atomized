/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Computability.Encoding
public import Mathlib.Logic.Small.List
public import Mathlib.ModelTheory.Syntax
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Encodings and Cardinality of First-Order Syntax

## Main Definitions

- `FirstOrder.Language.Term.encoding` encodes terms as lists.
- `FirstOrder.Language.BoundedFormula.encoding` encodes bounded formulas as lists.

## Main Results

- `FirstOrder.Language.Term.card_le` shows that the number of terms in `L.Term α` is at most
  `max ℵ₀ # (α ⊕ Σ i, L.Functions i)`.
- `FirstOrder.Language.BoundedFormula.card_le` shows that the number of bounded formulas in
  `Σ n, L.BoundedFormula α n` is at most
  `max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card)`.

## TODO

- `Primcodable` instances for terms and formulas, based on the `encoding`s
- Computability facts about term and formula operations, to set up a computability approach to
  incompleteness

-/

@[expose] public section


universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {α : Type u'}

open FirstOrder Cardinal

open Computability List Structure Fin

namespace Term

/--
Definition of `listEncode` / `listEncode` 的定义

English:
definition listEncode
  signature: : L.Term α -> List (α oplus (Σ i, L.Functions i))

中文:
定义 listEncode
  签名: : L.项 α -> 列表 (α oplus (Σ i, L.函数 i))
-/
def listEncode : L.Term α -> List (α oplus (Σ i, L.Functions i))
  | var i => [Sum.inl i]
  | func f ts =>
    Sum.inr (⟨_, f⟩ : Σ i, L.Functions i)::(List.finRange _).flatMap fun i => (ts i).listEncode

/--
Definition of `listDecode` / `listDecode` 的定义

English:
definition listDecode
  signature: : List (α oplus (Σ i, L.Functions i)) -> List (L.Term α)

中文:
定义 listDecode
  签名: : 列表 (α oplus (Σ i, L.函数 i)) -> 列表 (L.项 α)
-/
def listDecode : List (α oplus (Σ i, L.Functions i)) -> List (L.Term α)
  | [] => []
  | Sum.inl a::l => (var a)::listDecode l
  | Sum.inr ⟨n, f⟩::l =>
    if h : n <= (listDecode l).length then
      (func f (fun i => (listDecode l)[i])) :: (listDecode l).drop n
    else []

/--
theorem `listDecode_encode_list` / 定理 `listDecode_encode_list`

English:
theorem listDecode_encode_list
  given: (l : List (L.Term α))
  proof: by
  suffices h : forall (t : L.Term α) (l : List (α oplus (Σ i, L.Functions i))),
      listDecode (t.listEncode ++ l) = t::listDecode l by
    induction l with
    | nil => rfl
    | cons t l lih => rw [flatMap_cons, h t (l.flatMap listEncode), lih]
  intro t l
  induction t generalizing l with
  | var => rw [listEncode, singleton_append, listDecode]
  | @func n f ts ih =>
    rw [listEncode]; rw [cons_append]; rw [listDecode]
    have h : listDecode (((finRange n).flatMap fun i : Fin n => (ts i).listEncode) ++ l) =
        (finRange n).map ts ++ listDecode l := by
      induction finRange n with
      | nil => rfl
      | cons i l' l'ih => rw [flatMap_cons, List.append_assoc, ih, map_cons, l'ih, cons_append]
    simp only [h, length_append, length_map, length_finRange, le_add_iff_nonneg_right,
      _root_.zero_le, ↓reduceDIte, getElem_fin, cons.injEq, func.injEq, heq_eq_eq, true_and]
    refine ⟨funext (fun i => ?_), ?_⟩
    · simp only [length_map, length_finRange, is_lt, getElem_append_left, getElem_map,
      getElem_finRange, cast_mk, Fin.eta]
    · simp only [length_map, length_finRange, drop_left']

中文:
定理 listDecode_encode_list
  条件: (l : 列表 (L.项 α))
  证明: by
  suffices h : forall (t : L.Term α) (l : List (α oplus (Σ i, L.Functions i))),
      listDecode (t.listEncode ++ l) = t::listDecode l by
    induction l with
    | nil => rfl
    | cons t l lih => rw [flatMap_cons, h t (l.flatMap listEncode), lih]
  intro t l
  induction t generalizing l with
  | var => rw [listEncode, singleton_append, listDecode]
  | @func n f ts ih =>
    rw [listEncode]; rw [cons_append]; rw [listDecode]
    have h : listDecode (((finRange n).flatMap fun i : Fin n => (ts i).listEncode) ++ l) =
        (finRange n).map ts ++ listDecode l := by
      induction finRange n with
      | nil => rfl
      | cons i l' l'ih => rw [flatMap_cons, List.append_assoc, ih, map_cons, l'ih, cons_append]
    simp only [h, length_append, length_map, length_finRange, le_add_iff_nonneg_right,
      _root_.zero_le, ↓reduceDIte, getElem_fin, cons.injEq, func.injEq, heq_eq_eq, true_and]
    refine ⟨funext (fun i => ?_), ?_⟩
    · simp only [length_map, length_finRange, is_lt, getElem_append_left, getElem_map,
      getElem_finRange, cast_mk, Fin.eta]
    · simp only [length_map, length_finRange, drop_left']

Depends on / 依赖: Functions, L.Functions, L.Term, cons_append, finRange, flatMap, flatMap_cons, generalizing, l.flatMap, listDecode, listEncode, singleton_append, t.listEncode
-/
theorem listDecode_encode_list (l : List (L.Term α)) :
    listDecode (l.flatMap listEncode) = l := by
  suffices h : forall (t : L.Term α) (l : List (α oplus (Σ i, L.Functions i))),
      listDecode (t.listEncode ++ l) = t::listDecode l by
    induction l with
    | nil => rfl
    | cons t l lih => rw [flatMap_cons, h t (l.flatMap listEncode), lih]
  intro t l
  induction t generalizing l with
  | var => rw [listEncode, singleton_append, listDecode]
  | @func n f ts ih =>
    rw [listEncode]; rw [cons_append]; rw [listDecode]
    have h : listDecode (((finRange n).flatMap fun i : Fin n => (ts i).listEncode) ++ l) =
        (finRange n).map ts ++ listDecode l := by
      induction finRange n with
      | nil => rfl
      | cons i l' l'ih => rw [flatMap_cons, List.append_assoc, ih, map_cons, l'ih, cons_append]
    simp only [h, length_append, length_map, length_finRange, le_add_iff_nonneg_right,
      _root_.zero_le, ↓reduceDIte, getElem_fin, cons.injEq, func.injEq, heq_eq_eq, true_and]
    refine ⟨funext (fun i => ?_), ?_⟩
    · simp only [length_map, length_finRange, is_lt, getElem_append_left, getElem_map,
      getElem_finRange, cast_mk, Fin.eta]
    · simp only [length_map, length_finRange, drop_left']

/-- An encoding of terms as lists. -/
@[simps]
/--
Definition of `encoding` / `encoding` 的定义

English:
definition encoding
  signature: : Encoding (L.Term α) (α oplus (Σ i, L.Functions i)) where
  body: listEncode
  decode l := (listDecode l).head?.join
  decode_encode t := by
    have h := listDecode_encode_list [t]
    rw [flatMap_singleton] at h
    simp only [Option.join, h, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      id_eq]

中文:
定义 encoding
  签名: : Encoding (L.项 α) (α oplus (Σ i, L.函数 i)) where
  定义体: listEncode
  decode l := (listDecode l).head?.join
  decode_encode t := by
    have h := listDecode_encode_list [t]
    rw [flatMap_singleton] at h
    simp only [Option.join, h, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      id_eq]

Depends on / 依赖: PFun.preimage_eq, _def, inter_mem, preimage_eq, ptendsto, ptendsto_def
-/
protected def encoding : Encoding (L.Term α) (α oplus (Σ i, L.Functions i)) where
  encode := listEncode
  decode l := (listDecode l).head?.join
  decode_encode t := by
    have h := listDecode_encode_list [t]
    rw [flatMap_singleton] at h
    simp only [Option.join, h, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      id_eq]

/--
theorem `listEncode_injective` / 定理 `listEncode_injective`

English:
theorem listEncode_injective
  proof: Term.encoding.encode_injective

中文:
定理 listEncode_injective
  证明: Term.encoding.encode_injective

Depends on / 依赖: Term.encoding.encode_injective, encode_injective, encoding
-/
theorem listEncode_injective :
    Function.Injective (listEncode : L.Term α -> List (α oplus (Σ i, L.Functions i))) :=
  Term.encoding.encode_injective

/--
theorem `card_le` / 定理 `card_le`

English:
theorem card_le
  statement: #(L.Term α) <= max ℵ₀ #(α oplus (Σ i, L.Functions i))
  proof: lift_le.1 (_root_.trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))

中文:
定理 card_le
  结论: #(L.项 α) <= 最大值 ℵ₀ #(α oplus (Σ i, L.函数 i))
  证明: lift_le.1 (_root_.trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))

Depends on / 依赖: Term.encoding.card_le_card_list, _root_, _root_.trans, card_le_card_list, encoding, lift_le, mk_list_le_max
-/
theorem card_le : #(L.Term α) <= max ℵ₀ #(α oplus (Σ i, L.Functions i)) :=
  lift_le.1 (_root_.trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))

/--
theorem `card_sigma` / 定理 `card_sigma`

English:
theorem card_sigma
  statement: #(Σ n, L.Term (α oplus (Fin n))) = max ℵ₀ #(α oplus (Σ i, L.Functions i))
  proof: by
  refine le_antisymm ?_ ?_
  · rw [mk_sigma]
    refine (sum_le_lift_mk_mul_iSup _).trans ?_
    rw [mk_nat]; rw [lift_aleph0]; rw [mul_eq_max_of_aleph0_le_left le_rfl]; rw [max_le_iff]; rw [ciSup_le_iff' bddAbove_of_small]
    · refine ⟨le_max_left _ _, fun i => card_le.trans ?_⟩
      refine max_le (le_max_left _ _) ?_
      grw [← add_eq_max le_rfl, mk_sum, mk_sum, mk_sum, add_comm (Cardinal.lift #α), lift_add,
        add_assoc, lift_lift, lift_lift, mk_fin, lift_natCast, natCast_lt_aleph0]
    · rw [← Cardinal.one_le_iff_ne_zero]
      refine _root_.trans ?_ (le_ciSup bddAbove_of_small 1)
      rw [Cardinal.one_le_iff_ne_zero]; rw [mk_ne_zero_iff]
      exact ⟨var (Sum.inr 0)⟩
  · rw [max_le_iff, ← infinite_iff]
    refine ⟨Infinite.of_injective
        (fun i => ⟨i + 1, var (Sum.inr (last i))⟩) fun i j ij => ?_, ?_⟩
    · cases ij
      rfl
    · rw [Cardinal.le_def]
      refine ⟨⟨Sum.elim (fun i => ⟨0, var (Sum.inl i)⟩)
        fun F => ⟨1, func F.2 fun _ => var (Sum.inr 0)⟩, ?_⟩⟩
      rintro (a | a) (b | b) h
      · simp only [Sum.elim_inl, Sigma.mk.inj_iff, heq_eq_eq, var.injEq, Sum.inl.injEq, true_and]
          at h
        rw [h]
      · simp only [Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sum.elim_inl, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, func.injEq, true_and] at h
        rw [Sigma.ext_iff.2 ⟨h.1]; rw [h.2.1⟩]

中文:
定理 card_sigma
  结论: #(Σ n, L.项 (α oplus (有限集 n))) = 最大值 ℵ₀ #(α oplus (Σ i, L.函数 i))
  证明: by
  refine le_antisymm ?_ ?_
  · rw [mk_sigma]
    refine (sum_le_lift_mk_mul_iSup _).trans ?_
    rw [mk_nat]; rw [lift_aleph0]; rw [mul_eq_max_of_aleph0_le_left le_rfl]; rw [max_le_iff]; rw [ciSup_le_iff' bddAbove_of_small]
    · refine ⟨le_max_left _ _, fun i => card_le.trans ?_⟩
      refine max_le (le_max_left _ _) ?_
      grw [← add_eq_max le_rfl, mk_sum, mk_sum, mk_sum, add_comm (Cardinal.lift #α), lift_add,
        add_assoc, lift_lift, lift_lift, mk_fin, lift_natCast, natCast_lt_aleph0]
    · rw [← Cardinal.one_le_iff_ne_zero]
      refine _root_.trans ?_ (le_ciSup bddAbove_of_small 1)
      rw [Cardinal.one_le_iff_ne_zero]; rw [mk_ne_zero_iff]
      exact ⟨var (Sum.inr 0)⟩
  · rw [max_le_iff, ← infinite_iff]
    refine ⟨Infinite.of_injective
        (fun i => ⟨i + 1, var (Sum.inr (last i))⟩) fun i j ij => ?_, ?_⟩
    · cases ij
      rfl
    · rw [Cardinal.le_def]
      refine ⟨⟨Sum.elim (fun i => ⟨0, var (Sum.inl i)⟩)
        fun F => ⟨1, func F.2 fun _ => var (Sum.inr 0)⟩, ?_⟩⟩
      rintro (a | a) (b | b) h
      · simp only [Sum.elim_inl, Sigma.mk.inj_iff, heq_eq_eq, var.injEq, Sum.inl.injEq, true_and]
          at h
        rw [h]
      · simp only [Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sum.elim_inl, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, func.injEq, true_and] at h
        rw [Sigma.ext_iff.2 ⟨h.1]; rw [h.2.1⟩]

Depends on / 依赖: Cardinal, Cardinal.lift, Cardinal.one_le_iff_ne_ze, add_assoc, add_comm, add_eq_max, bddAbove_of_small, card_le, card_le.trans, ciSup_le_iff, le_antisymm, le_max_left, le_rfl, lift_add, lift_aleph0, lift_lift, lift_natCast, max_le, max_le_iff, mk_fin
-/
theorem card_sigma : #(Σ n, L.Term (α oplus (Fin n))) = max ℵ₀ #(α oplus (Σ i, L.Functions i)) := by
  refine le_antisymm ?_ ?_
  · rw [mk_sigma]
    refine (sum_le_lift_mk_mul_iSup _).trans ?_
    rw [mk_nat]; rw [lift_aleph0]; rw [mul_eq_max_of_aleph0_le_left le_rfl]; rw [max_le_iff]; rw [ciSup_le_iff' bddAbove_of_small]
    · refine ⟨le_max_left _ _, fun i => card_le.trans ?_⟩
      refine max_le (le_max_left _ _) ?_
      grw [← add_eq_max le_rfl, mk_sum, mk_sum, mk_sum, add_comm (Cardinal.lift #α), lift_add,
        add_assoc, lift_lift, lift_lift, mk_fin, lift_natCast, natCast_lt_aleph0]
    · rw [← Cardinal.one_le_iff_ne_zero]
      refine _root_.trans ?_ (le_ciSup bddAbove_of_small 1)
      rw [Cardinal.one_le_iff_ne_zero]; rw [mk_ne_zero_iff]
      exact ⟨var (Sum.inr 0)⟩
  · rw [max_le_iff, ← infinite_iff]
    refine ⟨Infinite.of_injective
        (fun i => ⟨i + 1, var (Sum.inr (last i))⟩) fun i j ij => ?_, ?_⟩
    · cases ij
      rfl
    · rw [Cardinal.le_def]
      refine ⟨⟨Sum.elim (fun i => ⟨0, var (Sum.inl i)⟩)
        fun F => ⟨1, func F.2 fun _ => var (Sum.inr 0)⟩, ?_⟩⟩
      rintro (a | a) (b | b) h
      · simp only [Sum.elim_inl, Sigma.mk.inj_iff, heq_eq_eq, var.injEq, Sum.inl.injEq, true_and]
          at h
        rw [h]
      · simp only [Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sum.elim_inl, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, func.injEq, true_and] at h
        rw [Sigma.ext_iff.2 ⟨h.1]; rw [h.2.1⟩]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Encodable
  signature: α] [Encodable (Σ i, L.Functions i)] : Encodable (L.Term α)
  body: Encodable.ofLeftInjection listEncode (fun l => (listDecode l).head?.join) fun t => by
    rw [← flatMap_singleton listEncode]; rw [listDecode_encode_list]
    simp only [Option.join, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      id_eq]

中文:
实例 [可编码
  签名: α] [可编码 (Σ i, L.函数 i)] : 可编码 (L.项 α)
  定义体: Encodable.ofLeftInjection listEncode (fun l => (listDecode l).head?.join) fun t => by
    rw [← flatMap_singleton listEncode]; rw [listDecode_encode_list]
    simp only [Option.join, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      id_eq]

Depends on / 依赖: Encodable, Encodable.ofLeftInjection, Option.bind_eq_bind, Option.bind_some, Option.join, Option.pure_def, _cons, bind_eq_bind, bind_some, flatMap_singleton, id_eq, listDecode, listDecode_encode_list, listEncode, ofLeftInjection, pure_def
-/
instance [Encodable α] [Encodable (Σ i, L.Functions i)] : Encodable (L.Term α) :=
  Encodable.ofLeftInjection listEncode (fun l => (listDecode l).head?.join) fun t => by
    rw [← flatMap_singleton listEncode]; rw [listDecode_encode_list]
    simp only [Option.join, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      id_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h1
  signature: : Countable α] [h2 : Countable (Σ l, L.Functions l)] : Countable (L.Term α)
  body: by
  refine mk_le_aleph0_iff.1 (card_le.trans (max_le_iff.2 ?_))
  simp only [le_refl, mk_sum, add_le_aleph0, lift_le_aleph0, true_and]
  exact ⟨Cardinal.mk_le_aleph0, Cardinal.mk_le_aleph0⟩

中文:
实例 [h1
  签名: : 可数 α] [h2 : 可数 (Σ l, L.函数 l)] : 可数 (L.项 α)
  定义体: by
  refine mk_le_aleph0_iff.1 (card_le.trans (max_le_iff.2 ?_))
  simp only [le_refl, mk_sum, add_le_aleph0, lift_le_aleph0, true_and]
  exact ⟨Cardinal.mk_le_aleph0, Cardinal.mk_le_aleph0⟩

Depends on / 依赖: Cardinal, Cardinal.mk_le_aleph0, add_le_aleph0, card_le, card_le.trans, le_refl, lift_le_aleph0, max_le_iff, mk_le_aleph0, mk_le_aleph0_iff, mk_sum, true_and
-/
instance [h1 : Countable α] [h2 : Countable (Σ l, L.Functions l)] : Countable (L.Term α) := by
  refine mk_le_aleph0_iff.1 (card_le.trans (max_le_iff.2 ?_))
  simp only [le_refl, mk_sum, add_le_aleph0, lift_le_aleph0, true_and]
  exact ⟨Cardinal.mk_le_aleph0, Cardinal.mk_le_aleph0⟩

/--
Instance `small` / 实例 `small`

English:
instance small
  signature: [Small.{u} α]
  body: small_of_injective listEncode_injective

中文:
实例 small
  签名: [Small.{u} α]
  定义体: small_of_injective listEncode_injective

Depends on / 依赖: listEncode_injective, small_of_injective
-/
instance small [Small.{u} α] : Small.{u} (L.Term α) :=
  small_of_injective listEncode_injective

end Term

namespace BoundedFormula

/--
Definition of `listEncode` / `listEncode` 的定义

English:
definition listEncode
  signature: : forall {n : Nat},

中文:
定义 listEncode
  签名: : 对任意 {n : 自然数},
-/
def listEncode : forall {n : Nat},
    L.BoundedFormula α n -> List ((Σ k, L.Term (α oplus Fin k)) oplus ((Σ n, L.Relations n) oplus Nat))
  | n, falsum => [Sum.inr (Sum.inr (n + 2))]
  | _, equal t₁ t₂ => [Sum.inl ⟨_, t₁⟩, Sum.inl ⟨_, t₂⟩]
  | n, rel R ts => [Sum.inr (Sum.inl ⟨_, R⟩), Sum.inr (Sum.inr n)] ++
      (List.finRange _).map fun i => Sum.inl ⟨n, ts i⟩
  | _, imp φ₁ φ₂ => (Sum.inr (Sum.inr 0)::φ₁.listEncode) ++ φ₂.listEncode
  | _, all φ => Sum.inr (Sum.inr 1)::φ.listEncode

/--
Definition of `sigmaAll` / `sigmaAll` 的定义

English:
definition sigmaAll
  signature: : (Σ n, L.BoundedFormula α n) -> Σ n, L.BoundedFormula α n

中文:
定义 sigmaAll
  签名: : (Σ n, L.BoundedFormula α n) -> Σ n, L.BoundedFormula α n
-/
def sigmaAll : (Σ n, L.BoundedFormula α n) -> Σ n, L.BoundedFormula α n
  | ⟨n + 1, φ⟩ => ⟨n, φ.all⟩
  | _ => default


@[simp]
/--
lemma `sigmaAll_apply` / 引理 `sigmaAll_apply`

English:
lemma sigmaAll_apply
  given: {n} {φ : L.BoundedFormula α (n + 1)}
  proof: rfl

中文:
引理 sigmaAll_apply
  条件: {n} {φ : L.BoundedFormula α (n + 1)}
  证明: rfl
-/
lemma sigmaAll_apply {n} {φ : L.BoundedFormula α (n + 1)} :
    sigmaAll ⟨n + 1, φ⟩ = ⟨n, φ.all⟩ := rfl

/--
Definition of `sigmaImp` / `sigmaImp` 的定义

English:
definition sigmaImp
  signature: : (Σ n, L.BoundedFormula α n) -> (Σ n, L.BoundedFormula α n) -> Σ n, L.BoundedFormula α n

中文:
定义 sigmaImp
  签名: : (Σ n, L.BoundedFormula α n) -> (Σ n, L.BoundedFormula α n) -> Σ n, L.BoundedFormula α n
-/
def sigmaImp : (Σ n, L.BoundedFormula α n) -> (Σ n, L.BoundedFormula α n) -> Σ n, L.BoundedFormula α n
  | ⟨m, φ⟩, ⟨n, ψ⟩ => if h : m = n then ⟨m, φ.imp (Eq.mp (by rw [h]) ψ)⟩ else default

/-- Decodes a list of symbols as a list of formulas. -/
@[simp]
/--
lemma `sigmaImp_apply` / 引理 `sigmaImp_apply`

English:
lemma sigmaImp_apply
  given: {n} {φ ψ : L.BoundedFormula α n}
  proof: by
  simp only [sigmaImp, ↓reduceDIte, eq_mp_eq_cast, cast_eq]

中文:
引理 sigmaImp_apply
  条件: {n} {φ ψ : L.BoundedFormula α n}
  证明: by
  simp only [sigmaImp, ↓reduceDIte, eq_mp_eq_cast, cast_eq]

Depends on / 依赖: cast_eq, eq_mp_eq_cast, reduceDIte, sigmaImp
-/
lemma sigmaImp_apply {n} {φ ψ : L.BoundedFormula α n} :
    sigmaImp ⟨n, φ⟩ ⟨n, ψ⟩ = ⟨n, φ.imp ψ⟩ := by
  simp only [sigmaImp, ↓reduceDIte, eq_mp_eq_cast, cast_eq]

/--
Definition of `listDecode` / `listDecode` 的定义

English:
definition listDecode
  signature: :

中文:
定义 listDecode
  签名: :
-/
def listDecode :
    List ((Σ k, L.Term (α oplus Fin k)) oplus ((Σ n, L.Relations n) oplus Nat)) -> List (Σ n, L.BoundedFormula α n)
  | Sum.inr (Sum.inr (n + 2))::l => ⟨n, falsum⟩::(listDecode l)
  | Sum.inl ⟨n₁, t₁⟩::Sum.inl ⟨n₂, t₂⟩::l =>
    (if h : n₁ = n₂ then ⟨n₁, equal t₁ (Eq.mp (by rw [h]) t₂)⟩ else default)::(listDecode l)
  | Sum.inr (Sum.inl ⟨n, R⟩)::Sum.inr (Sum.inr k)::l => (
    if h : forall i : Fin n, (l.map Sum.getLeft?)[i]?.join.isSome then
        if h' : forall i, (Option.get _ (h i)).1 = k then
          ⟨k, BoundedFormula.rel R fun i => Eq.mp (by rw [h' i]) (Option.get _ (h i)).2⟩
        else default
      else default)::(listDecode (l.drop n))
  | Sum.inr (Sum.inr 0)::l => if h : 2 <= (listDecode l).length
    then (sigmaImp (listDecode l)[0] (listDecode l)[1])::(drop 2 (listDecode l))
    else []
  | Sum.inr (Sum.inr 1)::l => if h : 1 <= (listDecode l).length
    then (sigmaAll (listDecode l)[0])::(drop 1 (listDecode l))
    else []
  | _ => []
  termination_by l => l.length

@[simp]
/--
theorem `listDecode_encode_list` / 定理 `listDecode_encode_list`

English:
theorem listDecode_encode_list
  given: (l : List (Σ n, L.BoundedFormula α n))
  proof: by
  suffices h : forall (φ : Σ n, L.BoundedFormula α n)
      (l' : List ((Σ k, L.Term (α oplus Fin k)) oplus ((Σ n, L.Relations n) oplus Nat))),
      (listDecode (listEncode φ.2 ++ l')) = φ::(listDecode l') by
    induction l with
    | nil =>
      simp [listDecode]
    | cons φ l ih => rw [flatMap_cons, h φ _, ih]
  rintro ⟨n, φ⟩
  induction φ with
  | falsum => intro l; rw [listEncode, singleton_append, listDecode]
  | equal =>
    intro l
    rw [listEncode]; rw [cons_append]; rw [cons_append]; rw [listDecode]; rw [dif_pos]
    · simp only [eq_mp_eq_cast, cast_eq, nil_append]
    · simp only
  | @rel φ_n φ_l φ_R ts =>
    intro l
    rw [listEncode]; rw [cons_append]; rw [cons_append]; rw [singleton_append]; rw [cons_append]; rw [listDecode]
    have h : forall i : Fin φ_l, ((List.map Sum.getLeft? (List.map (fun i : Fin φ_l =>
      Sum.inl (⟨(⟨φ_n, rel φ_R ts⟩ : Σ n, L.BoundedFormula α n).fst, ts i⟩ :
        Σ n, L.Term (α oplus (Fin n)))) (finRange φ_l) ++ l))[↑i]?).join = some ⟨_, ts i⟩ := by
      intro i
      simp only [Option.join, map_append, map_map, getElem?_fin, id, Option.bind_eq_some_iff,
        getElem?_eq_some_iff, length_append, length_map, length_finRange, exists_eq_right]
      refine ⟨lt_of_lt_of_le i.2 le_self_add, ?_⟩
      rw [getElem_append_left]; rw [getElem_map]
      · simp only [getElem_finRange, cast_mk, Fin.eta, Function.comp_apply, Sum.getLeft?_inl]
      · simp only [length_map, length_finRange, is_lt]
    rw [dif_pos]
    swap
    · exact fun i => Option.isSome_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩
    rw [dif_pos]
    swap
    · intro i
      obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [h2]
    simp only [Option.join, eq_mp_eq_cast, cons.injEq, Sigma.mk.inj_iff, heq_eq_eq, rel.injEq,
      true_and]
    refine ⟨funext fun i => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [cast_eq_iff_heq]
      exact (Sigma.ext_iff.1 ((Sigma.eta (Option.get _ h1)).trans h2)).2
    rw [List.drop_append]; rw [length_map]; rw [length_finRange]; rw [Nat.sub_self]; rw [drop]; rw [drop_eq_nil_of_le]; rw [nil_append]
    rw [length_map]; rw [length_finRange]
  | imp _ _ ih1 ih2 =>
    intro l
    simp only at *
    rw [listEncode]; rw [List.append_assoc]; rw [cons_append]; rw [listDecode]
    simp only [ih1, ih2, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, getElem_cons_succ, sigmaImp_apply, drop_succ_cons, drop_zero]
  | all _ ih =>
    intro l
    simp only at *
    rw [listEncode]; rw [cons_append]; rw [listDecode]
    simp only [ih, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, sigmaAll_apply, drop_succ_cons, drop_zero]

中文:
定理 listDecode_encode_list
  条件: (l : 列表 (Σ n, L.BoundedFormula α n))
  证明: by
  suffices h : forall (φ : Σ n, L.BoundedFormula α n)
      (l' : List ((Σ k, L.Term (α oplus Fin k)) oplus ((Σ n, L.Relations n) oplus Nat))),
      (listDecode (listEncode φ.2 ++ l')) = φ::(listDecode l') by
    induction l with
    | nil =>
      simp [listDecode]
    | cons φ l ih => rw [flatMap_cons, h φ _, ih]
  rintro ⟨n, φ⟩
  induction φ with
  | falsum => intro l; rw [listEncode, singleton_append, listDecode]
  | equal =>
    intro l
    rw [listEncode]; rw [cons_append]; rw [cons_append]; rw [listDecode]; rw [dif_pos]
    · simp only [eq_mp_eq_cast, cast_eq, nil_append]
    · simp only
  | @rel φ_n φ_l φ_R ts =>
    intro l
    rw [listEncode]; rw [cons_append]; rw [cons_append]; rw [singleton_append]; rw [cons_append]; rw [listDecode]
    have h : forall i : Fin φ_l, ((List.map Sum.getLeft? (List.map (fun i : Fin φ_l =>
      Sum.inl (⟨(⟨φ_n, rel φ_R ts⟩ : Σ n, L.BoundedFormula α n).fst, ts i⟩ :
        Σ n, L.Term (α oplus (Fin n)))) (finRange φ_l) ++ l))[↑i]?).join = some ⟨_, ts i⟩ := by
      intro i
      simp only [Option.join, map_append, map_map, getElem?_fin, id, Option.bind_eq_some_iff,
        getElem?_eq_some_iff, length_append, length_map, length_finRange, exists_eq_right]
      refine ⟨lt_of_lt_of_le i.2 le_self_add, ?_⟩
      rw [getElem_append_left]; rw [getElem_map]
      · simp only [getElem_finRange, cast_mk, Fin.eta, Function.comp_apply, Sum.getLeft?_inl]
      · simp only [length_map, length_finRange, is_lt]
    rw [dif_pos]
    swap
    · exact fun i => Option.isSome_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩
    rw [dif_pos]
    swap
    · intro i
      obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [h2]
    simp only [Option.join, eq_mp_eq_cast, cons.injEq, Sigma.mk.inj_iff, heq_eq_eq, rel.injEq,
      true_and]
    refine ⟨funext fun i => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [cast_eq_iff_heq]
      exact (Sigma.ext_iff.1 ((Sigma.eta (Option.get _ h1)).trans h2)).2
    rw [List.drop_append]; rw [length_map]; rw [length_finRange]; rw [Nat.sub_self]; rw [drop]; rw [drop_eq_nil_of_le]; rw [nil_append]
    rw [length_map]; rw [length_finRange]
  | imp _ _ ih1 ih2 =>
    intro l
    simp only at *
    rw [listEncode]; rw [List.append_assoc]; rw [cons_append]; rw [listDecode]
    simp only [ih1, ih2, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, getElem_cons_succ, sigmaImp_apply, drop_succ_cons, drop_zero]
  | all _ ih =>
    intro l
    simp only at *
    rw [listEncode]; rw [cons_append]; rw [listDecode]
    simp only [ih, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, sigmaAll_apply, drop_succ_cons, drop_zero]

Depends on / 依赖: BoundedFormula, L.BoundedFormula, L.Relations, L.Term, Relations, cons_append, dif_pos, falsum, flatMap_cons, listDecode, listEncode, singleton_append
-/
theorem listDecode_encode_list (l : List (Σ n, L.BoundedFormula α n)) :
    listDecode (l.flatMap (fun φ => φ.2.listEncode)) = l := by
  suffices h : forall (φ : Σ n, L.BoundedFormula α n)
      (l' : List ((Σ k, L.Term (α oplus Fin k)) oplus ((Σ n, L.Relations n) oplus Nat))),
      (listDecode (listEncode φ.2 ++ l')) = φ::(listDecode l') by
    induction l with
    | nil =>
      simp [listDecode]
    | cons φ l ih => rw [flatMap_cons, h φ _, ih]
  rintro ⟨n, φ⟩
  induction φ with
  | falsum => intro l; rw [listEncode, singleton_append, listDecode]
  | equal =>
    intro l
    rw [listEncode]; rw [cons_append]; rw [cons_append]; rw [listDecode]; rw [dif_pos]
    · simp only [eq_mp_eq_cast, cast_eq, nil_append]
    · simp only
  | @rel φ_n φ_l φ_R ts =>
    intro l
    rw [listEncode]; rw [cons_append]; rw [cons_append]; rw [singleton_append]; rw [cons_append]; rw [listDecode]
    have h : forall i : Fin φ_l, ((List.map Sum.getLeft? (List.map (fun i : Fin φ_l =>
      Sum.inl (⟨(⟨φ_n, rel φ_R ts⟩ : Σ n, L.BoundedFormula α n).fst, ts i⟩ :
        Σ n, L.Term (α oplus (Fin n)))) (finRange φ_l) ++ l))[↑i]?).join = some ⟨_, ts i⟩ := by
      intro i
      simp only [Option.join, map_append, map_map, getElem?_fin, id, Option.bind_eq_some_iff,
        getElem?_eq_some_iff, length_append, length_map, length_finRange, exists_eq_right]
      refine ⟨lt_of_lt_of_le i.2 le_self_add, ?_⟩
      rw [getElem_append_left]; rw [getElem_map]
      · simp only [getElem_finRange, cast_mk, Fin.eta, Function.comp_apply, Sum.getLeft?_inl]
      · simp only [length_map, length_finRange, is_lt]
    rw [dif_pos]
    swap
    · exact fun i => Option.isSome_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩
    rw [dif_pos]
    swap
    · intro i
      obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [h2]
    simp only [Option.join, eq_mp_eq_cast, cons.injEq, Sigma.mk.inj_iff, heq_eq_eq, rel.injEq,
      true_and]
    refine ⟨funext fun i => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [cast_eq_iff_heq]
      exact (Sigma.ext_iff.1 ((Sigma.eta (Option.get _ h1)).trans h2)).2
    rw [List.drop_append]; rw [length_map]; rw [length_finRange]; rw [Nat.sub_self]; rw [drop]; rw [drop_eq_nil_of_le]; rw [nil_append]
    rw [length_map]; rw [length_finRange]
  | imp _ _ ih1 ih2 =>
    intro l
    simp only at *
    rw [listEncode]; rw [List.append_assoc]; rw [cons_append]; rw [listDecode]
    simp only [ih1, ih2, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, getElem_cons_succ, sigmaImp_apply, drop_succ_cons, drop_zero]
  | all _ ih =>
    intro l
    simp only at *
    rw [listEncode]; rw [cons_append]; rw [listDecode]
    simp only [ih, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, sigmaAll_apply, drop_succ_cons, drop_zero]

/-- An encoding of bounded formulas as lists. -/
@[simps]
/--
Definition of `encoding` / `encoding` 的定义

English:
definition encoding
  signature: : Encoding (Σ n, L.BoundedFormula α n)
  body: φ.2.listEncode
  decode l := (listDecode l)[0]?
  decode_encode φ := by
    have h := listDecode_encode_list [φ]
    rw [flatMap_singleton] at h
    rw [h]
    rfl

中文:
定义 encoding
  签名: : Encoding (Σ n, L.BoundedFormula α n)
  定义体: φ.2.listEncode
  decode l := (listDecode l)[0]?
  decode_encode φ := by
    have h := listDecode_encode_list [φ]
    rw [flatMap_singleton] at h
    rw [h]
    rfl
-/
protected def encoding : Encoding (Σ n, L.BoundedFormula α n)
    ((Σ k, L.Term (α oplus Fin k)) oplus ((Σ n, L.Relations n) oplus Nat)) where
  encode φ := φ.2.listEncode
  decode l := (listDecode l)[0]?
  decode_encode φ := by
    have h := listDecode_encode_list [φ]
    rw [flatMap_singleton] at h
    rw [h]
    rfl

/--
theorem `listEncode_sigma_injective` / 定理 `listEncode_sigma_injective`

English:
theorem listEncode_sigma_injective
  proof: BoundedFormula.encoding.encode_injective

中文:
定理 listEncode_sigma_injective
  证明: BoundedFormula.encoding.encode_injective

Depends on / 依赖: BoundedFormula, BoundedFormula.encoding.encode_injective, encode_injective, encoding
-/
theorem listEncode_sigma_injective :
    Function.Injective fun φ : Σ n, L.BoundedFormula α n => φ.2.listEncode :=
  BoundedFormula.encoding.encode_injective

/--
theorem `card_le` / 定理 `card_le`

English:
theorem card_le
  statement: #(Σ n, L.BoundedFormula α n) <=
  proof: by
  refine lift_le.1 (BoundedFormula.encoding.card_le_card_list.trans ?_)
  rw [mk_list_eq_max_mk_aleph0]; rw [lift_max]; rw [lift_aleph0]; rw [lift_max]; rw [lift_aleph0]; rw [max_le_iff]
  refine ⟨?_, le_max_left _ _⟩
  rw [mk_sum]; rw [Term.card_sigma]; rw [mk_sum]; rw [← add_eq_max le_rfl]; rw [mk_sum]; rw [mk_nat]
  simp only [lift_add, lift_lift, lift_aleph0]
  rw [← add_assoc]; rw [add_comm]; rw [← add_assoc]; rw [← add_assoc]; rw [aleph0_add_aleph0]; rw [add_assoc]; rw [add_eq_max le_rfl]; rw [add_assoc]; rw [card]; rw [Symbols]; rw [mk_sum]; rw [lift_add]; rw [lift_lift]; rw [lift_lift]

中文:
定理 card_le
  结论: #(Σ n, L.BoundedFormula α n) <=
  证明: by
  refine lift_le.1 (BoundedFormula.encoding.card_le_card_list.trans ?_)
  rw [mk_list_eq_max_mk_aleph0]; rw [lift_max]; rw [lift_aleph0]; rw [lift_max]; rw [lift_aleph0]; rw [max_le_iff]
  refine ⟨?_, le_max_left _ _⟩
  rw [mk_sum]; rw [Term.card_sigma]; rw [mk_sum]; rw [← add_eq_max le_rfl]; rw [mk_sum]; rw [mk_nat]
  simp only [lift_add, lift_lift, lift_aleph0]
  rw [← add_assoc]; rw [add_comm]; rw [← add_assoc]; rw [← add_assoc]; rw [aleph0_add_aleph0]; rw [add_assoc]; rw [add_eq_max le_rfl]; rw [add_assoc]; rw [card]; rw [Symbols]; rw [mk_sum]; rw [lift_add]; rw [lift_lift]; rw [lift_lift]

Depends on / 依赖: BoundedFormula, BoundedFormula.encoding.card_le_card_list.trans, Term.card_sigma, add_, add_assoc, add_comm, add_eq_max, aleph0_add_aleph0, card_le_card_list, card_sigma, encoding, le_max_left, le_rfl, lift_add, lift_aleph0, lift_le, lift_lift, lift_max, max_le_iff, mk_list_eq_max_mk_aleph0
-/
theorem card_le : #(Σ n, L.BoundedFormula α n) <=
    max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card) := by
  refine lift_le.1 (BoundedFormula.encoding.card_le_card_list.trans ?_)
  rw [mk_list_eq_max_mk_aleph0]; rw [lift_max]; rw [lift_aleph0]; rw [lift_max]; rw [lift_aleph0]; rw [max_le_iff]
  refine ⟨?_, le_max_left _ _⟩
  rw [mk_sum]; rw [Term.card_sigma]; rw [mk_sum]; rw [← add_eq_max le_rfl]; rw [mk_sum]; rw [mk_nat]
  simp only [lift_add, lift_lift, lift_aleph0]
  rw [← add_assoc]; rw [add_comm]; rw [← add_assoc]; rw [← add_assoc]; rw [aleph0_add_aleph0]; rw [add_assoc]; rw [add_eq_max le_rfl]; rw [add_assoc]; rw [card]; rw [Symbols]; rw [mk_sum]; rw [lift_add]; rw [lift_lift]; rw [lift_lift]

section Countable

variable [Countable α] [Countable L.Symbols]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (constantsOn α).Symbols
  body: by
  refine mk_le_aleph0_iff.mp ?_
  change (constantsOn α).card <= ℵ₀
  simpa only [card_constantsOn, mk_le_aleph0_iff]

中文:
实例 :
  签名: 可数 (constantsOn α).Symbols
  定义体: by
  refine mk_le_aleph0_iff.mp ?_
  change (constantsOn α).card <= ℵ₀
  simpa only [card_constantsOn, mk_le_aleph0_iff]

Depends on / 依赖: card_constantsOn, constantsOn, mk_le_aleph0_iff, mk_le_aleph0_iff.mp
-/
instance : Countable (constantsOn α).Symbols := by
  refine mk_le_aleph0_iff.mp ?_
  change (constantsOn α).card <= ℵ₀
  simpa only [card_constantsOn, mk_le_aleph0_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable L[[α]].Symbols
  body: by
  simp only [← mk_le_aleph0_iff]
  change L[[α]].card <= ℵ₀
  simp only [withConstants, card_sum, add_le_aleph0, lift_le_aleph0]
  simp only [card, mk_le_aleph0_iff]
  constructor <;> infer_instance

中文:
实例 :
  签名: 可数 L[[α]].Symbols
  定义体: by
  simp only [← mk_le_aleph0_iff]
  change L[[α]].card <= ℵ₀
  simp only [withConstants, card_sum, add_le_aleph0, lift_le_aleph0]
  simp only [card, mk_le_aleph0_iff]
  constructor <;> infer_instance

Depends on / 依赖: add_le_aleph0, card_sum, infer_instance, lift_le_aleph0, mk_le_aleph0_iff, withConstants
-/
instance : Countable L[[α]].Symbols := by
  simp only [← mk_le_aleph0_iff]
  change L[[α]].card <= ℵ₀
  simp only [withConstants, card_sum, add_le_aleph0, lift_le_aleph0]
  simp only [card, mk_le_aleph0_iff]
  constructor <;> infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (Σ n, L.BoundedFormula α n)
  body: by
  refine Cardinal.mk_le_aleph0_iff.mp (BoundedFormula.card_le.trans (max_le (le_refl _) ?_))
  simp only [card, add_le_aleph0, lift_le_aleph0, mk_le_aleph0_iff]
  constructor <;> infer_instance

中文:
实例 :
  签名: 可数 (Σ n, L.BoundedFormula α n)
  定义体: by
  refine Cardinal.mk_le_aleph0_iff.mp (BoundedFormula.card_le.trans (max_le (le_refl _) ?_))
  simp only [card, add_le_aleph0, lift_le_aleph0, mk_le_aleph0_iff]
  constructor <;> infer_instance

Depends on / 依赖: BoundedFormula, BoundedFormula.card_le.trans, Cardinal, Cardinal.mk_le_aleph0_iff.mp, add_le_aleph0, card_le, infer_instance, le_refl, lift_le_aleph0, max_le, mk_le_aleph0_iff
-/
instance : Countable (Σ n, L.BoundedFormula α n) := by
  refine Cardinal.mk_le_aleph0_iff.mp (BoundedFormula.card_le.trans (max_le (le_refl _) ?_))
  simp only [card, add_le_aleph0, lift_le_aleph0, mk_le_aleph0_iff]
  constructor <;> infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (L.Formula α)
  body: (Function.Injective.countable
    (f := fun φ => (⟨0, φ⟩ : Σ n, L.BoundedFormula α n))) <| sigma_mk_injective

中文:
实例 :
  签名: 可数 (L.公式 α)
  定义体: (Function.Injective.countable
    (f := fun φ => (⟨0, φ⟩ : Σ n, L.BoundedFormula α n))) <| sigma_mk_injective

Depends on / 依赖: BoundedFormula, Function, Function.Injective.countable, Injective, L.BoundedFormula, countable, sigma_mk_injective
-/
instance : Countable (L.Formula α) :=
  (Function.Injective.countable
    (f := fun φ => (⟨0, φ⟩ : Σ n, L.BoundedFormula α n))) <| sigma_mk_injective

end Countable

end BoundedFormula

end Language

end FirstOrder
