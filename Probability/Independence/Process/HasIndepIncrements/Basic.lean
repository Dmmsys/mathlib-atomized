/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Joris van Winden
-/
module

public import Mathlib.Probability.Independence.Basic

import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Stochastic processes with independent increments

A stochastic process `X : T → Ω → E` has independent increments if for any `n ≥ 1` and
`t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent.
Equivalently, for any monotone sequence `(tₙ)`, the random variables `(X tₙ₊₁ - X tₙ)`
are independent.

## Main definition

* `HasIndepIncrements`: A stochastic process `X : T → Ω → E` has independent increments if for any
  `n ≥ 1` and `t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are
  independent.

## Main statement

* `hasIndepIncrements_iff_nat`: A stochastic process `X : T → Ω → E` has independent increments if
  and only if for any monotone sequence `(tₙ)`, the random variables `(X tₙ₊₁ - X tₙ)` are
  independent.

## Tags

independent increments
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T -> Ω -> E}
  [Preorder T] [MeasurableSpace E]

section Def

variable [Sub E]

/--
Definition of `HasIndepIncrements` / `HasIndepIncrements` 的定义

English:
definition HasIndepIncrements
  signature: (X : T -> Ω -> E) (P : Measure Ω := by volume_tac)
  body: forall n, forall t : Fin (n + 1) -> T, Monotone t ->
    iIndepFun (fun (i : Fin n) ω => X (t i.succ) ω - X (t i.castSucc) ω) P

中文:
定义 HasIndepIncrements
  签名: (X : T -> Ω -> E) (P : Measure Ω := by volume_tac)
  定义体: forall n, forall t : Fin (n + 1) -> T, Monotone t ->
    iIndepFun (fun (i : Fin n) ω => X (t i.succ) ω - X (t i.castSucc) ω) P

Depends on / 依赖: Monotone, castSucc, i.castSucc, i.succ, iIndepFun, volume_tac
-/
def HasIndepIncrements (X : T -> Ω -> E) (P : Measure Ω := by volume_tac) : Prop :=
  forall n, forall t : Fin (n + 1) -> T, Monotone t ->
    iIndepFun (fun (i : Fin n) ω => X (t i.succ) ω - X (t i.castSucc) ω) P

/--
lemma `HasIndepIncrements.nat` / 引理 `HasIndepIncrements.nat`

English:
lemma HasIndepIncrements.nat
  proof: by
  refine iIndepFun_iff_finset.2 fun s => ?_
  obtain rfl | hs := s.eq_empty_or_nonempty
  · have := (hX 0 (fun _ => t 0) (fun _ => by grind)).isProbabilityMeasure
    exact iIndepFun.of_subsingleton
  · let g (x : s) : Fin (s.max' hs + 1) := ⟨x.1, Nat.lt_add_one_of_le (s.le_max' x.1 x.2)⟩
    ref

中文:
引理 HasIndepIncrements.nat
  证明: by
  refine iIndepFun_iff_finset.2 fun s => ?_
  obtain rfl | hs := s.eq_empty_or_nonempty
  · have := (hX 0 (fun _ => t 0) (fun _ => by grind)).isProbabilityMeasure
    exact iIndepFun.of_subsingleton
  · let g (x : s) : Fin (s.max' hs + 1) := ⟨x.1, Nat.lt_add_one_of_le (s.le_max' x.1 x.2)⟩
    ref
-/
protected lemma HasIndepIncrements.nat
    (hX : HasIndepIncrements X P) {t : Nat -> T} (ht : Monotone t) :
    iIndepFun (fun i ω => X (t (i + 1)) ω - X (t i) ω) P := by
  refine iIndepFun_iff_finset.2 fun s => ?_
  obtain rfl | hs := s.eq_empty_or_nonempty
  · have := (hX 0 (fun _ => t 0) (fun _ => by grind)).isProbabilityMeasure
    exact iIndepFun.of_subsingleton
  · let g (x : s) : Fin (s.max' hs + 1) := ⟨x.1, Nat.lt_add_one_of_le (s.le_max' x.1 x.2)⟩
    refine iIndepFun.precomp (g := g) ?_ (hX (s.max' hs + 1) (fun m => t m) ?_)
    · simp [g, Function.Injective]
    · exact ht.comp Fin.val_strictMono.monotone

/--
lemma `HasIndepIncrements.of_nat` / 引理 `HasIndepIncrements.of_nat`

English:
lemma HasIndepIncrements.of_nat
  proof: by
  intro n t ht
  let t' k := t ⟨min n k, by grind⟩
  convert! (h t' ?_ ?_).precomp Fin.val_injective with i ω
  · grind
  · grind
  · exact fun a b hab => ht (by grind)
  · exact eventuallyConst_atTop.2 ⟨n, by grind⟩

中文:
引理 HasIndepIncrements.of_nat
  证明: by
  intro n t ht
  let t' k := t ⟨min n k, by grind⟩
  convert! (h t' ?_ ?_).precomp Fin.val_injective with i ω
  · grind
  · grind
  · exact fun a b hab => ht (by grind)
  · exact eventuallyConst_atTop.2 ⟨n, by grind⟩
-/
protected lemma HasIndepIncrements.of_nat
    (h : forall t : Nat -> T, Monotone t -> EventuallyConst t atTop ->
      iIndepFun (fun i ω => X (t (i + 1)) ω - X (t i) ω) P) :
    HasIndepIncrements X P := by
  intro n t ht
  let t' k := t ⟨min n k, by grind⟩
  convert! (h t' ?_ ?_).precomp Fin.val_injective with i ω
  · grind
  · grind
  · exact fun a b hab => ht (by grind)
  · exact eventuallyConst_atTop.2 ⟨n, by grind⟩

/--
lemma `hasIndepIncrements_iff_nat` / 引理 `hasIndepIncrements_iff_nat`

English:
lemma hasIndepIncrements_iff_nat
  proof: h.nat ht
  mpr h := .of_nat (fun t ht _ => h t ht)

中文:
引理 hasIndepIncrements_iff_nat
  证明: h.nat ht
  mpr h := .of_nat (fun t ht _ => h t ht)

Depends on / 依赖: h.nat
-/
lemma hasIndepIncrements_iff_nat :
    HasIndepIncrements X P ↔
    forall t : Nat -> T, Monotone t -> iIndepFun (fun i ω => X (t (i + 1)) ω - X (t i) ω) P where
  mp h _ ht := h.nat ht
  mpr h := .of_nat (fun t ht _ => h t ht)

end Def

/--
lemma `HasIndepIncrements.indepFun_sub_sub` / 引理 `HasIndepIncrements.indepFun_sub_sub`

English:
lemma HasIndepIncrements.indepFun_sub_sub
  statement: [Sub E] (hX : HasIndepIncrements X P) {r s t : T}
  proof: by
  let τ : Nat -> T
    | 0 => r
    | 1 => s
    | _ => t
.indepFun (by grind : 0 != 1) exact hX.nat (t := τ) (fun _ => by grind)

中文:
引理 HasIndepIncrements.indepFun_sub_sub
  结论: [Sub E] (hX : HasIndepIncrements X P) {r s t : T}
  证明: by
  let τ : Nat -> T
    | 0 => r
    | 1 => s
    | _ => t
.indepFun (by grind : 0 != 1) exact hX.nat (t := τ) (fun _ => by grind)

Depends on / 依赖: hX.nat, indepFun
-/
lemma HasIndepIncrements.indepFun_sub_sub [Sub E] (hX : HasIndepIncrements X P) {r s t : T}
    (hrs : r <= s) (hst : s <= t) :
    (X s - X r) ⟂ᵢ[P] (X t - X s) := by
  let τ : Nat -> T
    | 0 => r
    | 1 => s
    | _ => t
.indepFun (by grind : 0 != 1) exact hX.nat (t := τ) (fun _ => by grind)

/--
lemma `HasIndepIncrements.indepFun_eval_sub` / 引理 `HasIndepIncrements.indepFun_eval_sub`

English:
lemma HasIndepIncrements.indepFun_eval_sub
  statement: [SubNegZeroMonoid E] (hX : HasIndepIncrements X P)
  proof: by
  refine (hX.indepFun_sub_sub hrs hst).congr ?_ .rfl
  filter_upwards [h] with ω hω using by simp [hω]

中文:
引理 HasIndepIncrements.indepFun_eval_sub
  结论: [SubNegZeroMonoid E] (hX : HasIndepIncrements X P)
  证明: by
  refine (hX.indepFun_sub_sub hrs hst).congr ?_ .rfl
  filter_upwards [h] with ω hω using by simp [hω]

Depends on / 依赖: filter_upwards, hX.indepFun_sub_sub, indepFun_sub_sub
-/
lemma HasIndepIncrements.indepFun_eval_sub [SubNegZeroMonoid E] (hX : HasIndepIncrements X P)
    {r s t : T} (hrs : r <= s) (hst : s <= t) (h : forallᵐ ω ∂P, X r ω = 0) :
    (X s) ⟂ᵢ[P] (X t - X s) := by
  refine (hX.indepFun_sub_sub hrs hst).congr ?_ .rfl
  filter_upwards [h] with ω hω using by simp [hω]

/--
lemma `HasIndepIncrements.map'` / 引理 `HasIndepIncrements.map'`

English:
lemma HasIndepIncrements.map'
  statement: {F G : Type*} [MeasurableSpace G] [FunLike F E G]
  proof: by
  intro n t ht
  simp_rw [← map_sub]
  exact (hX n t ht).comp (fun _ => f) (fun _ => hf)

中文:
引理 HasIndepIncrements.map'
  结论: {F G : 类型} [MeasurableSpace G] [FunLike F E G]
  证明: by
  intro n t ht
  simp_rw [← map_sub]
  exact (hX n t ht).comp (fun _ => f) (fun _ => hf)
-/
protected lemma HasIndepIncrements.map' {F G : Type*} [MeasurableSpace G] [FunLike F E G]
    [AddGroup E] [SubtractionMonoid G] [AddMonoidHomClass F E G] {f : F} (hf : Measurable f)
    (hX : HasIndepIncrements X P) :
    HasIndepIncrements (fun t ω => f (X t ω)) P := by
  intro n t ht
  simp_rw [← map_sub]
  exact (hX n t ht).comp (fun _ => f) (fun _ => hf)

/--
lemma `HasIndepIncrements.map` / 引理 `HasIndepIncrements.map`

English:
lemma HasIndepIncrements.map
  statement: {R F : Type*} [Semiring R] [SeminormedAddCommGroup E]
  proof: hX.map' L.measurable

中文:
引理 HasIndepIncrements.map
  结论: {R F : 类型} [Semiring R] [SeminormedAddCommGroup E]
  证明: hX.map' L.measurable
-/
protected lemma HasIndepIncrements.map {R F : Type*} [Semiring R] [SeminormedAddCommGroup E]
    [Module R E] [OpensMeasurableSpace E] [SeminormedAddCommGroup F] [Module R F]
    [MeasurableSpace F] [BorelSpace F] (L : E ->L[R] F) (hX : HasIndepIncrements X P) :
    HasIndepIncrements (fun t ω => L (X t ω)) P :=
  hX.map' L.measurable

/--
lemma `HasIndepIncrements.smul` / 引理 `HasIndepIncrements.smul`

English:
lemma HasIndepIncrements.smul
  statement: {R : Type*} [AddGroup E] [DistribSMul R E]
  proof: hX.map' (f := DistribSMul.toAddMonoidHom E c) (MeasurableConstSMul.measurable_const_smul c)

中文:
引理 HasIndepIncrements.smul
  结论: {R : 类型} [AddGroup E] [DistribSMul R E]
  证明: hX.map' (f := DistribSMul.toAddMonoidHom E c) (MeasurableConstSMul.measurable_const_smul c)
-/
protected lemma HasIndepIncrements.smul {R : Type*} [AddGroup E] [DistribSMul R E]
    [MeasurableConstSMul R E] (hX : HasIndepIncrements X P) (c : R) :
    HasIndepIncrements (fun t ω => c • (X t ω)) P :=
  hX.map' (f := DistribSMul.toAddMonoidHom E c) (MeasurableConstSMul.measurable_const_smul c)

/--
lemma `HasIndepIncrements.neg` / 引理 `HasIndepIncrements.neg`

English:
lemma HasIndepIncrements.neg
  statement: [AddCommGroup E] [MeasurableNeg E]
  proof: hX.map' (f := negAddMonoidHom) measurable_neg

中文:
引理 HasIndepIncrements.neg
  结论: [AddCommGroup E] [MeasurableNeg E]
  证明: hX.map' (f := negAddMonoidHom) measurable_neg
-/
protected lemma HasIndepIncrements.neg [AddCommGroup E] [MeasurableNeg E]
    (hX : HasIndepIncrements X P) :
    HasIndepIncrements (-X) P :=
  hX.map' (f := negAddMonoidHom) measurable_neg

end ProbabilityTheory
