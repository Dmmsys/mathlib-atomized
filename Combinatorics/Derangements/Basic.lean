/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Tactic.ApplyFun

/-!
# Derangements on types

In this file we define `derangements α`, the set of derangements on a type `α`.

We also define some equivalences involving various subtypes of `Perm α` and `derangements α`:
* `derangementsOptionEquivSigmaAtMostOneFixedPoint`: An equivalence between
  `derangements (Option α)` and the sigma-type `Σ a : α, {f : Perm α // fixedPoints f ⊆ a}`.
* `derangementsRecursionEquiv`: An equivalence between `derangements (Option α)` and the
  sigma-type `Σ a : α, (derangements (({a}ᶜ : Set α) : Type*) ⊕ derangements α)` which is later
  used to inductively count the number of derangements.

In order to prove the above, we also prove some results about the effect of `Equiv.removeNone`
on derangements: `RemoveNone.fiber_none` and `RemoveNone.fiber_some`.
-/

@[expose] public section


open Equiv Function

/--
Definition of `derangements` / `derangements` 的定义

English:
definition derangements
  signature: (α : Type*)
  body: { f : Perm α | forall x : α, f x != x }

中文:
定义 derangements
  签名: (α : 类型)
  定义体: { f : Perm α | forall x : α, f x != x }
-/
def derangements (α : Type*) : Set (Perm α) :=
  { f : Perm α | forall x : α, f x != x }

variable {α β : Type*}

/--
theorem `mem_derangements_iff_fixedPoints_eq_empty` / 定理 `mem_derangements_iff_fixedPoints_eq_empty`

English:
theorem mem_derangements_iff_fixedPoints_eq_empty
  given: {f : Perm α}
  proof: Set.eq_empty_iff_forall_notMem.symm

中文:
定理 mem_derangements_iff_fixedPoints_eq_empty
  条件: {f : 置换 α}
  证明: Set.eq_empty_iff_forall_notMem.symm

Depends on / 依赖: Set.eq_empty_iff_forall_notMem.symm, eq_empty_iff_forall_notMem
-/
theorem mem_derangements_iff_fixedPoints_eq_empty {f : Perm α} :
    f in derangements α ↔ fixedPoints f = ∅ :=
  Set.eq_empty_iff_forall_notMem.symm

/--
Definition of `Equiv.derangementsCongr` / `Equiv.derangementsCongr` 的定义

English:
definition Equiv.derangementsCongr
  signature: (e : α ≃ β)
  body: e.permCongr.subtypeEquiv fun {f} => e.forall_congr by
    intro b; simp only [ne_eq, permCongr_apply, symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]

中文:
定义 等价.derangementsCongr
  签名: (e : α ≃ β)
  定义体: e.permCongr.subtypeEquiv fun {f} => e.forall_congr by
    intro b; simp only [ne_eq, permCongr_apply, symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq, e.forall_congr, e.permCongr.subtypeEquiv, forall_congr, ne_eq, permCongr, permCongr_apply, subtypeEquiv, symm_apply_apply
-/
def Equiv.derangementsCongr (e : α ≃ β) : derangements α ≃ derangements β :=
e.permCongr.subtypeEquiv fun {f} => e.forall_congr by
    intro b; simp only [ne_eq, permCongr_apply, symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]

namespace derangements

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `subtypeEquiv` / `subtypeEquiv` 的定义

English:
definition subtypeEquiv
  signature: (p : α -> Prop) [DecidablePred p]
  body: calc
    derangements (Subtype p) ≃ { f : { f : Perm α // forall a, ¬p a -> a in fixedPoints f } //
        forall a, a in fixedPoints f -> ¬p a } := by
      refine (Perm.subtypeEquivSubtypePerm p).subtypeEquiv fun f => ⟨fun hf a hfa ha => ?_, ?_⟩
      · refine hf ⟨a, ha⟩ (Subtype.ext ?_)
        

中文:
定义 subtypeEquiv
  签名: (p : α -> 命题) [DecidablePred p]
  定义体: calc
    derangements (Subtype p) ≃ { f : { f : Perm α // forall a, ¬p a -> a in fixedPoints f } //
        forall a, a in fixedPoints f -> ¬p a } := by
      refine (Perm.subtypeEquivSubtypePerm p).subtypeEquiv fun f => ⟨fun hf a hfa ha => ?_, ?_⟩
      · refine hf ⟨a, ha⟩ (Subtype.ext ?_)
        
-/
protected def subtypeEquiv (p : α -> Prop) [DecidablePred p] :
    derangements (Subtype p) ≃ { f : Perm α // forall a, ¬p a ↔ a in fixedPoints f } :=
  calc
    derangements (Subtype p) ≃ { f : { f : Perm α // forall a, ¬p a -> a in fixedPoints f } //
        forall a, a in fixedPoints f -> ¬p a } := by
      refine (Perm.subtypeEquivSubtypePerm p).subtypeEquiv fun f => ⟨fun hf a hfa ha => ?_, ?_⟩
      · refine hf ⟨a, ha⟩ (Subtype.ext ?_)
        simp_rw [mem_fixedPoints, IsFixedPt, Perm.subtypeEquivSubtypePerm,
        Equiv.coe_fn_mk, Perm.ofSubtype_apply_of_mem _ ha] at hfa
        assumption
      rintro hf ⟨a, ha⟩ hfa
      refine hf _ ?_ ha
      simp only [Perm.subtypeEquivSubtypePerm_apply_coe, mem_fixedPoints]
      dsimp [IsFixedPt]
      simp_rw [Perm.ofSubtype_apply_of_mem _ ha, hfa]
    _ ≃ { f : Perm α // exists _h : forall a, ¬p a -> a in fixedPoints f, forall a, a in fixedPoints f -> ¬p a } :=
      subtypeSubtypeEquivSubtypeExists _ _
    _ ≃ { f : Perm α // forall a, ¬p a ↔ a in fixedPoints f } :=
      subtypeEquivRight fun f => by
        simp_rw [exists_prop, ← forall_and, ← iff_iff_implies_and_implies]

universe u
/--
Definition of `atMostOneFixedPointEquivSum_derangements` / `atMostOneFixedPointEquivSum_derangements` 的定义

English:
definition atMostOneFixedPointEquivSum_derangements
  signature: [DecidableEq α] (a : α)
  body: calc
    { f : Perm α // fixedPoints f subseteq {a} } ≃
        { f : { f : Perm α // fixedPoints f subseteq {a} } // a in fixedPoints f } oplus
          { f : { f : Perm α // fixedPoints f subseteq {a} } // a ∉ fixedPoints f } :=
      (Equiv.sumCompl _).symm
    _ ≃ { f : Perm α // fixedPoints f 

中文:
定义 atMostOneFixedPointEquivSum_derangements
  签名: [DecidableEq α] (a : α)
  定义体: calc
    { f : Perm α // fixedPoints f subseteq {a} } ≃
        { f : { f : Perm α // fixedPoints f subseteq {a} } // a in fixedPoints f } oplus
          { f : { f : Perm α // fixedPoints f subseteq {a} } // a ∉ fixedPoints f } :=
      (Equiv.sumCompl _).symm
    _ ≃ { f : Perm α // fixedPoints f 

Depends on / 依赖: Equiv.sumCompl, Equiv.sumCongr, clear.clear, copy.copy, decidable_of_iff, fixedPoints, generalizing, move.move, push.push, read.read, subseteq, subtypeSubtypeEquivSubtypeInter, sumCompl, sumCongr
-/
def atMostOneFixedPointEquivSum_derangements [DecidableEq α] (a : α) :
    { f : Perm α // fixedPoints f subseteq {a} } ≃ (derangements ({a}ᶜ : Set α)) oplus (derangements α) :=
  calc
    { f : Perm α // fixedPoints f subseteq {a} } ≃
        { f : { f : Perm α // fixedPoints f subseteq {a} } // a in fixedPoints f } oplus
          { f : { f : Perm α // fixedPoints f subseteq {a} } // a ∉ fixedPoints f } :=
      (Equiv.sumCompl _).symm
    _ ≃ { f : Perm α // fixedPoints f subseteq {a} ∧ a in fixedPoints f } oplus
          { f : Perm α // fixedPoints f subseteq {a} ∧ a ∉ fixedPoints f } := by
      refine Equiv.sumCongr ?_ ?_
      · exact subtypeSubtypeEquivSubtypeInter
          (fun x : Perm α => fixedPoints x subseteq {a})
          (a in fixedPoints ·)
      · exact subtypeSubtypeEquivSubtypeInter
          (fun x : Perm α => fixedPoints x subseteq {a})
          (a ∉ fixedPoints ·)
    _ ≃ { f : Perm α // fixedPoints f = {a} } oplus { f : Perm α // fixedPoints f = ∅ } := by
      refine Equiv.sumCongr (subtypeEquivRight fun f => ?_) (subtypeEquivRight fun f => ?_)
      · rw [Set.eq_singleton_iff_unique_mem, and_comm]
        rfl
      · rw [Set.eq_empty_iff_forall_notMem]
        exact ⟨fun h x hx => h.2 (h.1 hx ▸ hx), fun h => ⟨fun x hx => (h _ hx).elim, h _⟩⟩
    _ ≃ derangements ({a}ᶜ : Set α) oplus derangements α := by
      refine
        Equiv.sumCongr ((derangements.subtypeEquiv _).trans <|
            subtypeEquivRight fun x => ?_).symm
          (subtypeEquivRight fun f => mem_derangements_iff_fixedPoints_eq_empty.symm)
      rw [eq_comm]; rw [Set.ext_iff]
      simp_rw [Set.mem_compl_iff, Classical.not_not]

namespace Equiv

variable [DecidableEq α]

/--
Definition of `RemoveNone.fiber` / `RemoveNone.fiber` 的定义

English:
definition RemoveNone.fiber
  signature: (a : Option α)
  body: { f : Perm α | (a, f) in Equiv.Perm.decomposeOption '' derangements (Option α) }

中文:
定义 RemoveNone.fiber
  签名: (a : 选项类型 α)
  定义体: { f : Perm α | (a, f) in Equiv.Perm.decomposeOption '' derangements (Option α) }

Depends on / 依赖: Equiv.Perm.decomposeOption, decomposeOption, derangements
-/
def RemoveNone.fiber (a : Option α) : Set (Perm α) :=
  { f : Perm α | (a, f) in Equiv.Perm.decomposeOption '' derangements (Option α) }

set_option backward.isDefEq.respectTransparency false in
/--
theorem `RemoveNone.mem_fiber` / 定理 `RemoveNone.mem_fiber`

English:
theorem RemoveNone.mem_fiber
  given: (a : Option α) (f : Perm α)
  proof: by
  simp [RemoveNone.fiber, derangements]

中文:
定理 RemoveNone.mem_fiber
  条件: (a : 选项类型 α) (f : 置换 α)
  证明: by
  simp [RemoveNone.fiber, derangements]

Depends on / 依赖: RemoveNone, RemoveNone.fiber, derangements
-/
theorem RemoveNone.mem_fiber (a : Option α) (f : Perm α) :
    f in RemoveNone.fiber a ↔
      exists F : Perm (Option α), F in derangements (Option α) ∧ F none = a ∧ removeNone F = f := by
  simp [RemoveNone.fiber, derangements]

/--
theorem `RemoveNone.fiber_none` / 定理 `RemoveNone.fiber_none`

English:
theorem RemoveNone.fiber_none
  statement: RemoveNone.fiber (@none α) = ∅
  proof: by
  rw [Set.eq_empty_iff_forall_notMem]
  intro f hyp
  rw [RemoveNone.mem_fiber] at hyp
  rcases hyp with ⟨F, F_derangement, F_none, _⟩
  exact F_derangement none F_none

中文:
定理 RemoveNone.fiber_none
  结论: RemoveNone.fiber (@none α) = ∅
  证明: by
  rw [Set.eq_empty_iff_forall_notMem]
  intro f hyp
  rw [RemoveNone.mem_fiber] at hyp
  rcases hyp with ⟨F, F_derangement, F_none, _⟩
  exact F_derangement none F_none

Depends on / 依赖: F_derangement, F_none, RemoveNone, RemoveNone.mem_fiber, Set.eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem, mem_fiber
-/
theorem RemoveNone.fiber_none : RemoveNone.fiber (@none α) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro f hyp
  rw [RemoveNone.mem_fiber] at hyp
  rcases hyp with ⟨F, F_derangement, F_none, _⟩
  exact F_derangement none F_none

/--
theorem `RemoveNone.fiber_some` / 定理 `RemoveNone.fiber_some`

English:
theorem RemoveNone.fiber_some
  given: (a : α)
  proof: by
  ext f
  constructor
  · rw [RemoveNone.mem_fiber]
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed
    rw [mem_fixedPoints_iff] at x_fixed
    apply_fun some at x_fixed
    rcases Fx : F (some x) with - | y
    · rwa [removeNone_none F Fx, F_none, Option.some_inj, eq_comm] at x_fixed
    · 

中文:
定理 RemoveNone.fiber_some
  条件: (a : α)
  证明: by
  ext f
  constructor
  · rw [RemoveNone.mem_fiber]
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed
    rw [mem_fixedPoints_iff] at x_fixed
    apply_fun some at x_fixed
    rcases Fx : F (some x) with - | y
    · rwa [removeNone_none F Fx, F_none, Option.some_inj, eq_comm] at x_fixed
    · 

Depends on / 依赖: Equiv.Perm.decomposeOption.symm, Equiv.swap, F_derangement, F_none, Option.some_inj, RemoveNone, RemoveNone.mem_fiber, apply_fun, decomposeOption, eq_comm, h_opfp, mem_fiber, mem_fixedPoints_iff, removeNone_none, removeNone_some, some_inj, x_fixed
-/
theorem RemoveNone.fiber_some (a : α) :
    RemoveNone.fiber (some a) = { f : Perm α | fixedPoints f subseteq {a} } := by
  ext f
  constructor
  · rw [RemoveNone.mem_fiber]
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed
    rw [mem_fixedPoints_iff] at x_fixed
    apply_fun some at x_fixed
    rcases Fx : F (some x) with - | y
    · rwa [removeNone_none F Fx, F_none, Option.some_inj, eq_comm] at x_fixed
    · exfalso
      rw [removeNone_some F ⟨y]; rw [Fx⟩] at x_fixed
      exact F_derangement _ x_fixed
  · intro h_opfp
    use Equiv.Perm.decomposeOption.symm (some a, f)
    constructor
    · intro x
      apply_fun fun x => Equiv.swap none (some a) x
      simp only [Perm.decomposeOption_symm_apply, Perm.coe_mul]
      rcases x with - | x
      · simp
      simp only [comp, optionCongr_apply, Option.map_some, swap_apply_self]
      by_cases x_vs_a : x = a
      · rw [x_vs_a, swap_apply_right]
        apply Option.some_ne_none
      have ne_1 : some x != none := Option.some_ne_none _
      have ne_2 : some x != some a := (Option.some_injective α).ne_iff.mpr x_vs_a
      rw [swap_apply_of_ne_of_ne ne_1 ne_2]; rw [(Option.some_injective α).ne_iff]
      intro contra
      exact x_vs_a (h_opfp contra)
    · rw [apply_symm_apply]

end Equiv

section Option

variable [DecidableEq α]

/--
Definition of `derangementsOptionEquivSigmaAtMostOneFixedPoint` / `derangementsOptionEquivSigmaAtMostOneFixedPoint` 的定义

English:
definition derangementsOptionEquivSigmaAtMostOneFixedPoint
  signature: :
  body: by
  have fiber_none_is_false : Equiv.RemoveNone.fiber (@none α) -> False := by
    rw [Equiv.RemoveNone.fiber_none]
    exact IsEmpty.false
  calc
    derangements (Option α) ≃ Equiv.Perm.decomposeOption '' derangements (Option α) :=
      Equiv.image _ _
    _ ≃ Σ a : Option α, ↥(Equiv.RemoveNone.

中文:
定义 derangementsOptionEquivSigmaAtMostOneFixedPoint
  签名: :
  定义体: by
  have fiber_none_is_false : Equiv.RemoveNone.fiber (@none α) -> False := by
    rw [Equiv.RemoveNone.fiber_none]
    exact IsEmpty.false
  calc
    derangements (Option α) ≃ Equiv.Perm.decomposeOption '' derangements (Option α) :=
      Equiv.image _ _
    _ ≃ Σ a : Option α, ↥(Equiv.RemoveNone.

Depends on / 依赖: Equiv.Perm.decomposeOption, Equiv.RemoveNone.fiber, Equiv.RemoveNone.fiber_none, Equiv.RemoveNone.fiber_som, Equiv.image, IsEmpty, IsEmpty.false, RemoveNone, decomposeOption, derangements, fiber_none, fiber_none_is_false, fiber_som, fixedPoints, setProdEquivSigma, sigmaOptionEquivOfSome, simp_rw, subseteq
-/
def derangementsOptionEquivSigmaAtMostOneFixedPoint :
    derangements (Option α) ≃ Σ a : α, { f : Perm α | fixedPoints f subseteq {a} } := by
  have fiber_none_is_false : Equiv.RemoveNone.fiber (@none α) -> False := by
    rw [Equiv.RemoveNone.fiber_none]
    exact IsEmpty.false
  calc
    derangements (Option α) ≃ Equiv.Perm.decomposeOption '' derangements (Option α) :=
      Equiv.image _ _
    _ ≃ Σ a : Option α, ↥(Equiv.RemoveNone.fiber a) := setProdEquivSigma _
    _ ≃ Σ a : α, ↥(Equiv.RemoveNone.fiber (some a)) :=
      sigmaOptionEquivOfSome _ fiber_none_is_false
    _ ≃ Σ a : α, { f : Perm α | fixedPoints f subseteq {a} } := by
      simp_rw [Equiv.RemoveNone.fiber_some]
      rfl

/--
Definition of `derangementsRecursionEquiv` / `derangementsRecursionEquiv` 的定义

English:
definition derangementsRecursionEquiv
  signature: :
  body: derangementsOptionEquivSigmaAtMostOneFixedPoint.trans
    (sigmaCongrRight atMostOneFixedPointEquivSum_derangements)

中文:
定义 derangementsRecursionEquiv
  签名: :
  定义体: derangementsOptionEquivSigmaAtMostOneFixedPoint.trans
    (sigmaCongrRight atMostOneFixedPointEquivSum_derangements)

Depends on / 依赖: atMostOneFixedPointEquivSum_derangements, derangementsOptionEquivSigmaAtMostOneFixedPoint, derangementsOptionEquivSigmaAtMostOneFixedPoint.trans, sigmaCongrRight
-/
def derangementsRecursionEquiv :
    derangements (Option α) ≃
      Σ a : α, derangements (({a}ᶜ : Set α) : Type _) oplus derangements α :=
  derangementsOptionEquivSigmaAtMostOneFixedPoint.trans
    (sigmaCongrRight atMostOneFixedPointEquivSum_derangements)

end Option

end derangements
