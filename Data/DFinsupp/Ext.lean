/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.DFinsupp.Defs

/-!
# Extensionality principles for `DFinsupp`

## Main results

* `DFinsupp.addHom_ext`, `DFinsupp.addHom_ext'`: if two additive homomorphisms from `Π₀ i, β i`
  are equal on each `single a b`, then they are equal.
-/

public section


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}

namespace DFinsupp

section DecidableEq
variable [DecidableEq ι]

section AddMonoid

variable [forall i, AddZeroClass (β i)]

@[simp]
/--
theorem `add_closure_iUnion_range_single` / 定理 `add_closure_iUnion_range_single`

English:
theorem add_closure_iUnion_range_single
  proof: top_unique fun x _ => by
    apply DFinsupp.induction x
    · exact AddSubmonoid.zero_mem _
    exact fun a b f _ _ hf =>
      AddSubmonoid.add_mem _
        (AddSubmonoid.subset_closure <| Set.mem_iUnion.2 ⟨a, Set.mem_range_self _⟩) hf

中文:
定理 add_closure_iUnion_range_single
  证明: top_unique fun x _ => by
    apply DFinsupp.induction x
    · exact AddSubmonoid.zero_mem _
    exact fun a b f _ _ hf =>
      AddSubmonoid.add_mem _
        (AddSubmonoid.subset_closure <| Set.mem_iUnion.2 ⟨a, Set.mem_range_self _⟩) hf

Depends on / 依赖: AddSubmonoid, AddSubmonoid.add_mem, AddSubmonoid.subset_closure, AddSubmonoid.zero_mem, DFinsupp, DFinsupp.induction, Set.mem_iUnion, Set.mem_range_self, add_mem, mem_iUnion, mem_range_self, subset_closure, top_unique, zero_mem
-/
theorem add_closure_iUnion_range_single :
    AddSubmonoid.closure (⋃ i : ι, Set.range (single i : β i -> Π₀ i, β i)) = ⊤ :=
  top_unique fun x _ => by
    apply DFinsupp.induction x
    · exact AddSubmonoid.zero_mem _
    exact fun a b f _ _ hf =>
      AddSubmonoid.add_mem _
        (AddSubmonoid.subset_closure <| Set.mem_iUnion.2 ⟨a, Set.mem_range_self _⟩) hf

/--
theorem `addHom_ext` / 定理 `addHom_ext`

English:
theorem addHom_ext
  given: {γ : Type w} [AddZeroClass γ] ⦃f g
  statement: (Π₀ i, β i) ->+ γ⦄
  proof: by
  refine AddMonoidHom.eq_of_eqOn_denseM add_closure_iUnion_range_single fun f hf => ?_
  simp only [Set.mem_iUnion, Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H

中文:
定理 addHom_ext
  条件: {γ : 类型 w} [加法零类 γ] ⦃f g
  结论: (Π₀ i, β i) ->+ γ⦄
  证明: by
  refine AddMonoidHom.eq_of_eqOn_denseM add_closure_iUnion_range_single fun f hf => ?_
  simp only [Set.mem_iUnion, Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H

Depends on / 依赖: AddMonoidHom, AddMonoidHom.eq_of_eqOn_denseM, Set.mem_iUnion, Set.mem_range, add_closure_iUnion_range_single, eq_of_eqOn_denseM, mem_iUnion, mem_range
-/
theorem addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) ->+ γ⦄
    (H : forall (i : ι) (y : β i), f (single i y) = g (single i y)) : f = g := by
  refine AddMonoidHom.eq_of_eqOn_denseM add_closure_iUnion_range_single fun f hf => ?_
  simp only [Set.mem_iUnion, Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `addHom_ext'` / 定理 `addHom_ext'`

English:
theorem addHom_ext'
  given: {γ : Type w} [AddZeroClass γ] ⦃f g
  statement: (Π₀ i, β i) ->+ γ⦄
  proof: addHom_ext fun x => DFunLike.congr_fun (H x)

中文:
定理 addHom_ext'
  条件: {γ : 类型 w} [加法零类 γ] ⦃f g
  结论: (Π₀ i, β i) ->+ γ⦄
  证明: addHom_ext fun x => DFunLike.congr_fun (H x)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, addHom_ext, congr_fun
-/
theorem addHom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) ->+ γ⦄
    (H : forall x, f.comp (singleAddHom β x) = g.comp (singleAddHom β x)) : f = g :=
  addHom_ext fun x => DFunLike.congr_fun (H x)

end AddMonoid

end DecidableEq

end DFinsupp
