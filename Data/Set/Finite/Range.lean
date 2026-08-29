/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.ULift

/-!
# Finiteness of `Set.range`

## Implementation notes

Each result in this file should come in three forms: a `Fintype` instance, a `Finite` instance
and a `Set.Finite` constructor.

## Tags

finite sets
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

/--
Instance `fintypeRange` / 实例 `fintypeRange`

English:
instance fintypeRange
  signature: [DecidableEq α] (f : ι -> α) [Fintype (PLift ι)]
  body: Fintype.ofFinset (Finset.univ.image <| f ∘ PLift.down) by simp

中文:
实例 fintypeRange
  签名: [DecidableEq α] (f : ι -> α) [Fintype (PLift ι)]
  定义体: Fintype.ofFinset (Finset.univ.image <| f ∘ PLift.down) by simp

Depends on / 依赖: Finset, Finset.univ.image, Fintype, Fintype.ofFinset, PLift.down, ofFinset
-/
instance fintypeRange [DecidableEq α] (f : ι -> α) [Fintype (PLift ι)] : Fintype (range f) :=
Fintype.ofFinset (Finset.univ.image <| f ∘ PLift.down) by simp

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

/--
Instance `finite_range` / 实例 `finite_range`

English:
instance finite_range
  signature: (f : ι -> α) [Finite ι]
  body: by
  classical
  have := Fintype.ofFinite (PLift ι)
  infer_instance

中文:
实例 finite_range
  签名: (f : ι -> α) [Finite ι]
  定义体: by
  classical
  have := Fintype.ofFinite (PLift ι)
  infer_instance

Depends on / 依赖: Fintype, Fintype.ofFinite, classical, infer_instance, ofFinite
-/
instance finite_range (f : ι -> α) [Finite ι] : Finite (range f) := by
  classical
  have := Fintype.ofFinite (PLift ι)
  infer_instance

/--
Instance `finite_replacement` / 实例 `finite_replacement`

English:
instance finite_replacement
  signature: [Finite α] (f : α -> β)
  body: Finite.Set.finite_range f

中文:
实例 finite_replacement
  签名: [Finite α] (f : α -> β)
  定义体: Finite.Set.finite_range f

Depends on / 依赖: Finite, Finite.Set.finite_range, finite_range
-/
instance finite_replacement [Finite α] (f : α -> β) :
    Finite {f x | x : α} :=
  Finite.Set.finite_range f

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

/--
theorem `finite_range` / 定理 `finite_range`

English:
theorem finite_range
  given: (f : ι -> α) [Finite ι]
  statement: (range f).Finite
  proof: toFinite _

中文:
定理 finite_range
  条件: (f : ι -> α) [Finite ι]
  结论: (range f).Finite
  证明: toFinite _

Depends on / 依赖: toFinite
-/
theorem finite_range (f : ι -> α) [Finite ι] : (range f).Finite :=
  toFinite _

/--
theorem `Finite.dependent_image` / 定理 `Finite.dependent_image`

English:
theorem Finite.dependent_image
  given: {s : Set α} (hs : s.Finite) (F : forall i in s, β)
  proof: by
  have := hs.to_subtype
  simpa [range] using finite_range fun x : s => F x x.2

中文:
定理 Finite.dependent_image
  条件: {s : Set α} (hs : s.Finite) (F : 对任意 i in s, β)
  证明: by
  have := hs.to_subtype
  simpa [range] using finite_range fun x : s => F x x.2

Depends on / 依赖: finite_range, hs.to_subtype, to_subtype
-/
theorem Finite.dependent_image {s : Set α} (hs : s.Finite) (F : forall i in s, β) :
    {y : β | exists x hx, F x hx = y}.Finite := by
  have := hs.to_subtype
  simpa [range] using finite_range fun x : s => F x x.2

end SetFiniteConstructors

/--
lemma `Finite.exists_subset_finite_image_eq` / 引理 `Finite.exists_subset_finite_image_eq`

English:
lemma Finite.exists_subset_finite_image_eq
  statement: {f : α -> β} {s : Set α} {u : Set β}
  proof: by
  have : Finite u := Finite.to_subtype hu
  choose g hg hg' using hsu
  let g' (x : u) : α := g x.property
  exact ⟨range g', fun a ha => by aesop, finite_range _, by aesop⟩

中文:
引理 Finite.exists_subset_finite_image_eq
  结论: {f : α -> β} {s : Set α} {u : Set β}
  证明: by
  have : Finite u := Finite.to_subtype hu
  choose g hg hg' using hsu
  let g' (x : u) : α := g x.property
  exact ⟨range g', fun a ha => by aesop, finite_range _, by aesop⟩

Depends on / 依赖: Finite, Finite.to_subtype, finite_range, property, to_subtype, x.property
-/
lemma Finite.exists_subset_finite_image_eq {f : α -> β} {s : Set α} {u : Set β}
    (hu : u.Finite) (hsu : u subseteq f '' s) :
    existsᵉ (t subseteq s) (_ : t.Finite), f '' t = u := by
  have : Finite u := Finite.to_subtype hu
  choose g hg hg' using hsu
  let g' (x : u) : α := g x.property
  exact ⟨range g', fun a ha => by aesop, finite_range _, by aesop⟩

end Set
