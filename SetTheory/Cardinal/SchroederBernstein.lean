/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.Zorn

/-!
# Schröder-Bernstein theorem, well-ordering of cardinals

This file proves the Schröder-Bernstein theorem (see `schroeder_bernstein`), the well-ordering of
cardinals (see `min_injective`) and the totality of their order (see `total`).

## Notes

Cardinals are naturally ordered by `α ≤ β ↔ ∃ f : a → β, Injective f`:
* `schroeder_bernstein` states that, given injections `α → β` and `β → α`, one can get a
  bijection `α → β`. This corresponds to the antisymmetry of the order.
* The order is also well-founded: any nonempty set of cardinals has a minimal element.
  `min_injective` states that by saying that there exists an element of the set that injects into
  all others.

Cardinals are defined and further developed in the folder `SetTheory.Cardinal`.
-/

public section


open Set Function

universe u v

namespace Function

namespace Embedding

section antisymm

variable {α : Type u} {β : Type v}

/--
theorem `schroeder_bernstein_of_rel` / 定理 `schroeder_bernstein_of_rel`

English:
theorem schroeder_bernstein_of_rel
  statement: {f : α -> β} {g : β -> α} (hf : Function.Injective f)
  proof: by
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty α := Function.isEmpty f
    exact ⟨_, ((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).bijective, by simp⟩
  set F : Set α ->o Set α :=
    { toFun := fun s => (g '' (f '' s)ᶜ)ᶜ
      monotone' := fun s t hst => by d

中文:
定理 schroeder_bernstein_of_rel
  结论: {f : α -> β} {g : β -> α} (hf : Function.Injective f)
  证明: by
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty α := Function.isEmpty f
    exact ⟨_, ((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).bijective, by simp⟩
  set F : Set α ->o Set α :=
    { toFun := fun s => (g '' (f '' s)ᶜ)ᶜ
      monotone' := fun s t hst => by d

Depends on / 依赖: Equiv.equivEmpty, F.lfp, F.map_lfp, Function, Function.isEmpty, IsEmpty, LeftInverse, bijective, classical, compl_injective, equivEmpty, invFun, isEmpty, isEmpty_or_nonempty, leftInverse_inv, map_lfp, monotone
-/
theorem schroeder_bernstein_of_rel {f : α -> β} {g : β -> α} (hf : Function.Injective f)
    (hg : Function.Injective g) (R : α -> β -> Prop) (hp₁ : forall a : α, R a (f a))
    (hp₂ : forall b : β, R (g b) b) :
    exists h : α -> β, Bijective h ∧ forall a : α, R a (h a) := by
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty α := Function.isEmpty f
    exact ⟨_, ((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).bijective, by simp⟩
  set F : Set α ->o Set α :=
    { toFun := fun s => (g '' (f '' s)ᶜ)ᶜ
      monotone' := fun s t hst => by dsimp at hst ⊢; gcongr }
  set s : Set α := F.lfp
  have hs : (g '' (f '' s)ᶜ)ᶜ = s := F.map_lfp
  have hns : g '' (f '' s)ᶜ = sᶜ := compl_injective (by simp [hs])
  set g' := invFun g
  have g'g : LeftInverse g' g := leftInverse_invFun hg
  have hg'ns : g' '' sᶜ = (f '' s)ᶜ := by rw [← hns, g'g.image_image]
  set h : α -> β := s.piecewise f g'
  have : Surjective h := by rw [← range_eq_univ, range_piecewise, hg'ns, union_compl_self]
  have : Injective h := by
    refine (injective_piecewise_iff _).2 ⟨hf.injOn, ?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨x', _, rfl⟩ : x in g '' (f '' s)ᶜ := by rwa [hns]
      obtain ⟨y', _, rfl⟩ : y in g '' (f '' s)ᶜ := by rwa [hns]
      rw [g'g _]; rw [g'g _] at hxy
      rw [hxy]
    · intro x hx y hy hxy
      obtain ⟨y', hy', rfl⟩ : y in g '' (f '' s)ᶜ := by rwa [hns]
      rw [g'g _] at hxy
      exact hy' ⟨x, hx, hxy⟩
  refine ⟨h, ⟨‹Injective h›, ‹Surjective h›⟩, fun a => ?_⟩
  simp only [h, Set.piecewise, g']
  split
  · exact hp₁ a
  · have : g (invFun g a) = a := by
      have : a in g '' (f '' s)ᶜ := by grind
.mp this obtain ⟨x, _, hx⟩ := mem_image _ _ _
      exact Function.invFun_eq ⟨x, hx⟩
    grind

/--
theorem `schroeder_bernstein` / 定理 `schroeder_bernstein`

English:
theorem schroeder_bernstein
  statement: {f : α -> β} {g : β -> α} (hf : Function.Injective f)
  proof: by
  obtain ⟨f, hf, _⟩ := schroeder_bernstein_of_rel hf hg (fun x y => True) (by simp) (by simp)
  exact ⟨f, hf⟩

中文:
定理 schroeder_bernstein
  结论: {f : α -> β} {g : β -> α} (hf : Function.Injective f)
  证明: by
  obtain ⟨f, hf, _⟩ := schroeder_bernstein_of_rel hf hg (fun x y => True) (by simp) (by simp)
  exact ⟨f, hf⟩

Depends on / 依赖: schroeder_bernstein_of_rel
-/
theorem schroeder_bernstein {f : α -> β} {g : β -> α} (hf : Function.Injective f)
    (hg : Function.Injective g) : exists h : α -> β, Bijective h := by
  obtain ⟨f, hf, _⟩ := schroeder_bernstein_of_rel hf hg (fun x y => True) (by simp) (by simp)
  exact ⟨f, hf⟩

/--
theorem `antisymm` / 定理 `antisymm`

English:
theorem antisymm
  statement: (α ↪ β) -> (β ↪ α) -> Nonempty (α ≃ β)
  proof: schroeder_bernstein h₁ h₂
    ⟨Equiv.ofBijective f hf⟩

中文:
定理 antisymm
  结论: (α ↪ β) -> (β ↪ α) -> Nonempty (α ≃ β)
  证明: schroeder_bernstein h₁ h₂
    ⟨Equiv.ofBijective f hf⟩

Depends on / 依赖: schroeder_bernstein
-/
theorem antisymm : (α ↪ β) -> (β ↪ α) -> Nonempty (α ≃ β)
  | ⟨_, h₁⟩, ⟨_, h₂⟩ =>
    let ⟨f, hf⟩ := schroeder_bernstein h₁ h₂
    ⟨Equiv.ofBijective f hf⟩

end antisymm

section Wo

variable {ι : Type u} (β : ι -> Type v)

/--
Definition of `sets` / `sets` 的定义

English:
abbreviation sets
  body: { s : Set (forall i, β i) | forall i : ι, s.InjOn fun x => x i }

中文:
缩写 sets
  定义体: { s : Set (forall i, β i) | forall i : ι, s.InjOn fun x => x i }
-/
private abbrev sets :=
  { s : Set (forall i, β i) | forall i : ι, s.InjOn fun x => x i }

/--
theorem `min_injective` / 定理 `min_injective`

English:
theorem min_injective
  given: [I : Nonempty ι]
  statement: exists i, Nonempty (forall j, β i ↪ β j)
  proof: let ⟨s, hs⟩ := show exists s, Maximal (· in sets β) s by
    refine zorn_subset _ fun c hc hcc =>
      ⟨⋃₀ c, fun i x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ hi => ?_, fun _ => subset_sUnion_of_mem⟩
    exact (hcc.total hpc hqc).elim (fun h => hc hqc i (h hxp) hyq hi)
      fun h => hc hpc i hxp (h hyq) hi
 

中文:
定理 min_injective
  条件: [I : Nonempty ι]
  结论: 存在 i, Nonempty (对任意 j, β i ↪ β j)
  证明: let ⟨s, hs⟩ := show exists s, Maximal (· in sets β) s by
    refine zorn_subset _ fun c hc hcc =>
      ⟨⋃₀ c, fun i x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ hi => ?_, fun _ => subset_sUnion_of_mem⟩
    exact (hcc.total hpc hqc).elim (fun h => hc hqc i (h hxp) hyq hi)
      fun h => hc hpc i hxp (h hyq) hi
 

Depends on / 依赖: Classical, Classical.by_contradiction, Maximal, Surjective, by_contradiction, hcc.total, subset_sUnion_of_mem, x.val, zorn_subset
-/
theorem min_injective [I : Nonempty ι] : exists i, Nonempty (forall j, β i ↪ β j) :=
  let ⟨s, hs⟩ := show exists s, Maximal (· in sets β) s by
    refine zorn_subset _ fun c hc hcc =>
      ⟨⋃₀ c, fun i x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ hi => ?_, fun _ => subset_sUnion_of_mem⟩
    exact (hcc.total hpc hqc).elim (fun h => hc hqc i (h hxp) hyq hi)
      fun h => hc hpc i hxp (h hyq) hi
  let ⟨i, e⟩ :=
    show exists i, Surjective fun x : s => x.val i from
      Classical.by_contradiction fun h =>
        have h : forall i, exists y, forall x in s, (x : forall i, β i) i != y := by
          simpa [Surjective] using h
        let ⟨f, hf⟩ := Classical.axiom_of_choice h
        have : f in s :=
          have : insert f s in sets β := fun i x hx y hy => by
            rcases hx with hx | hx <;> rcases hy with hy | hy; · simp [hx, hy]
            · subst x
              exact fun e => (hf i y hy e.symm).elim
            · subst y
              exact fun e => (hf i x hx e).elim
            · exact hs.prop i hx hy
          hs.eq_of_subset this (subset_insert _ _) ▸ mem_insert ..
        let ⟨i⟩ := I
        hf i f this rfl
  ⟨i, ⟨fun j => ⟨s.domRestrict (fun x => x j) ∘ surjInv e,
    ((hs.1 j).injective).comp (injective_surjInv _)⟩⟩⟩

end Wo

/--
theorem `total` / 定理 `total`

English:
theorem total
  given: (α : Type u) (β : Type v)
  statement: Nonempty (α ↪ β) ∨ Nonempty (β ↪ α)
  proof: match @min_injective Bool (fun b => cond b (ULift α) (ULift.{max u v, v} β)) ⟨true⟩
    with
  | ⟨true, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h false
    Or.inl ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩
  | ⟨false, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h true
    Or.inr ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f

中文:
定理 total
  条件: (α : 类型u) (β : 类型v)
  结论: Nonempty (α ↪ β) ∨ Nonempty (β ↪ α)
  证明: match @min_injective Bool (fun b => cond b (ULift α) (ULift.{max u v, v} β)) ⟨true⟩
    with
  | ⟨true, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h false
    Or.inl ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩
  | ⟨false, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h true
    Or.inr ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f

Depends on / 依赖: Embedding, Embedding.congr, Equiv.ulift, Or.inl, Or.inr, min_injective
-/
theorem total (α : Type u) (β : Type v) : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α) :=
  match @min_injective Bool (fun b => cond b (ULift α) (ULift.{max u v, v} β)) ⟨true⟩
    with
  | ⟨true, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h false
    Or.inl ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩
  | ⟨false, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h true
    Or.inr ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩

end Embedding

end Function
