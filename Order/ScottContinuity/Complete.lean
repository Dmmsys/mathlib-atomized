/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.ScottContinuity.Prod

/-!

# Scott continuity on complete lattices

## Main results

- `scottContinuous_iff_map_sSup`: A function is Scott continuous if and only if it commutes with
  `sSup` on directed sets.

-/

public section

variable {α β : Type*}

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β]

/--
lemma `scottContinuous_iff_map_sSup` / 引理 `scottContinuous_iff_map_sSup`

English:
lemma scottContinuous_iff_map_sSup
  given: {f : α -> β}
  proof: by rw [IsLUB.sSup_eq (h d₁ d₂ (isLUB_iff_sSup_eq.mpr rfl))]
  mpr h _ d₁ d₂ _ hda := by rw [isLUB_iff_sSup_eq, ← (h d₁ d₂), IsLUB.sSup_eq hda]

alias ⟨ScottContinuous.map_sSup, ScottContinuous.of_map_sSup⟩ :=
  scottContinuous_iff_map_sSup

中文:
引理 scottContinuous_iff_map_sSup
  条件: {f : α -> β}
  证明: by rw [IsLUB.sSup_eq (h d₁ d₂ (isLUB_iff_sSup_eq.mpr rfl))]
  mpr h _ d₁ d₂ _ hda := by rw [isLUB_iff_sSup_eq, ← (h d₁ d₂), IsLUB.sSup_eq hda]

alias ⟨ScottContinuous.map_sSup, ScottContinuous.of_map_sSup⟩ :=
  scottContinuous_iff_map_sSup

Depends on / 依赖: IsLUB.sSup_eq, isLUB_iff_sSup_eq, isLUB_iff_sSup_eq.mpr, sSup_eq
-/
lemma scottContinuous_iff_map_sSup {f : α -> β} :
    ScottContinuous f ↔
      forall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d -> f (sSup d) = sSup (f '' d) where
  mp h _ d₁ d₂ := by rw [IsLUB.sSup_eq (h d₁ d₂ (isLUB_iff_sSup_eq.mpr rfl))]
  mpr h _ d₁ d₂ _ hda := by rw [isLUB_iff_sSup_eq, ← (h d₁ d₂), IsLUB.sSup_eq hda]

alias ⟨ScottContinuous.map_sSup, ScottContinuous.of_map_sSup⟩ :=
  scottContinuous_iff_map_sSup

end CompleteLattice

/-!
In a complete linear order, the Scott Topology coincides with the Upper topology, see
`Topology.IsScott.scott_eq_upper_of_completeLinearOrder`
-/

section CompleteLinearOrder

variable [CompleteLinearOrder β]

/--
lemma `scottContinuous_inf_right` / 引理 `scottContinuous_inf_right`

English:
lemma scottContinuous_inf_right
  given: (a : β)
  statement: ScottContinuous fun b => a ⊓ b
  proof: .of_map_sSup (fun d _ _ => by rw [inf_sSup_eq, sSup_image])

中文:
引理 scottContinuous_inf_right
  条件: (a : β)
  结论: ScottContinuous fun b => a ⊓ b
  证明: .of_map_sSup (fun d _ _ => by rw [inf_sSup_eq, sSup_image])

Depends on / 依赖: inf_sSup_eq, of_map_sSup, sSup_image
-/
lemma scottContinuous_inf_right (a : β) : ScottContinuous fun b => a ⊓ b :=
  .of_map_sSup (fun d _ _ => by rw [inf_sSup_eq, sSup_image])

/--
lemma `scottContinuous_inf_left` / 引理 `scottContinuous_inf_left`

English:
lemma scottContinuous_inf_left
  given: (b : β)
  statement: ScottContinuous fun a => a ⊓ b
  proof: .of_map_sSup (fun d _ _ => by rw [sSup_inf_eq, sSup_image])

中文:
引理 scottContinuous_inf_left
  条件: (b : β)
  结论: ScottContinuous fun a => a ⊓ b
  证明: .of_map_sSup (fun d _ _ => by rw [sSup_inf_eq, sSup_image])

Depends on / 依赖: of_map_sSup, sSup_image, sSup_inf_eq
-/
lemma scottContinuous_inf_left (b : β) : ScottContinuous fun a => a ⊓ b :=
  .of_map_sSup (fun d _ _ => by rw [sSup_inf_eq, sSup_image])

/--
lemma `ScottContinuous.inf₂` / 引理 `ScottContinuous.inf₂`

English:
lemma ScottContinuous.inf₂
  statement: ScottContinuous fun (a, b) => (a ⊓ b : β)
  proof: ScottContinuous.fromProd (fun a => scottContinuous_inf_right a) scottContinuous_inf_left

中文:
引理 ScottContinuous.inf₂
  结论: ScottContinuous fun (a, b) => (a ⊓ b : β)
  证明: ScottContinuous.fromProd (fun a => scottContinuous_inf_right a) scottContinuous_inf_left

Depends on / 依赖: ScottContinuous, ScottContinuous.fromProd, fromProd, scottContinuous_inf_left, scottContinuous_inf_right
-/
lemma ScottContinuous.inf₂ : ScottContinuous fun (a, b) => (a ⊓ b : β) :=
  ScottContinuous.fromProd (fun a => scottContinuous_inf_right a) scottContinuous_inf_left

end CompleteLinearOrder
