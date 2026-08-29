/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Map
public import Mathlib.Order.Filter.AtTopBot.Monoid

/-!
# Convergence to ±infinity in ordered commutative groups
-/

public section

variable {α G : Type*}
open Set

namespace Filter

section OrderedCommGroup

variable [CommGroup G] [PartialOrder G] [IsOrderedMonoid G] (l : Filter α) {f g : α -> G}

@[to_additive]
/--
theorem `tendsto_atTop_mul_left_of_le'` / 定理 `tendsto_atTop_mul_left_of_le'`

English:
theorem tendsto_atTop_mul_left_of_le'
  given: (C : G) (hf : forallᶠ x in l, C <= f x) (hg : Tendsto g l atTop)
  proof: .atTop_of_isBoundedUnder_le_mul (f := f⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]

中文:
定理 tendsto_atTop_mul_left_of_le'
  条件: (C : G) (hf : 对任意ᶠ x in l, C <= f x) (hg : 收敛 g l atTop)
  证明: .atTop_of_isBoundedUnder_le_mul (f := f⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]

Depends on / 依赖: atTop_of_isBoundedUnder_le_mul
-/
theorem tendsto_atTop_mul_left_of_le' (C : G) (hf : forallᶠ x in l, C <= f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  .atTop_of_isBoundedUnder_le_mul (f := f⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]
/--
theorem `tendsto_atBot_mul_left_of_ge'` / 定理 `tendsto_atBot_mul_left_of_ge'`

English:
theorem tendsto_atBot_mul_left_of_ge'
  given: (C : G) (hf : forallᶠ x in l, f x <= C) (hg : Tendsto g l atBot)
  proof: tendsto_atTop_mul_left_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]

中文:
定理 tendsto_atBot_mul_left_of_ge'
  条件: (C : G) (hf : 对任意ᶠ x in l, f x <= C) (hg : 收敛 g l atBot)
  证明: tendsto_atTop_mul_left_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]

Depends on / 依赖: tendsto_atTop_mul_left_of_le
-/
theorem tendsto_atBot_mul_left_of_ge' (C : G) (hf : forallᶠ x in l, f x <= C) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_left_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]
/--
theorem `tendsto_atTop_mul_left_of_le` / 定理 `tendsto_atTop_mul_left_of_le`

English:
theorem tendsto_atTop_mul_left_of_le
  given: (C : G) (hf : forall x, C <= f x) (hg : Tendsto g l atTop)
  proof: tendsto_atTop_mul_left_of_le' l C (univ_mem' hf) hg

@[to_additive]

中文:
定理 tendsto_atTop_mul_left_of_le
  条件: (C : G) (hf : 对任意 x, C <= f x) (hg : 收敛 g l atTop)
  证明: tendsto_atTop_mul_left_of_le' l C (univ_mem' hf) hg

@[to_additive]

Depends on / 依赖: tendsto_atTop_mul_left_of_le, univ_mem
-/
theorem tendsto_atTop_mul_left_of_le (C : G) (hf : forall x, C <= f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mul_left_of_le' l C (univ_mem' hf) hg

@[to_additive]
/--
theorem `tendsto_atBot_mul_left_of_ge` / 定理 `tendsto_atBot_mul_left_of_ge`

English:
theorem tendsto_atBot_mul_left_of_ge
  given: (C : G) (hf : forall x, f x <= C) (hg : Tendsto g l atBot)
  proof: tendsto_atTop_mul_left_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]

中文:
定理 tendsto_atBot_mul_left_of_ge
  条件: (C : G) (hf : 对任意 x, f x <= C) (hg : 收敛 g l atBot)
  证明: tendsto_atTop_mul_left_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]

Depends on / 依赖: tendsto_atTop_mul_left_of_le
-/
theorem tendsto_atBot_mul_left_of_ge (C : G) (hf : forall x, f x <= C) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_left_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]
/--
theorem `tendsto_atTop_mul_right_of_le'` / 定理 `tendsto_atTop_mul_right_of_le'`

English:
theorem tendsto_atTop_mul_right_of_le'
  given: (C : G) (hf : Tendsto f l atTop) (hg : forallᶠ x in l, C <= g x)
  proof: .atTop_of_mul_isBoundedUnder_le (g := g⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]

中文:
定理 tendsto_atTop_mul_right_of_le'
  条件: (C : G) (hf : 收敛 f l atTop) (hg : 对任意ᶠ x in l, C <= g x)
  证明: .atTop_of_mul_isBoundedUnder_le (g := g⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]

Depends on / 依赖: atTop_of_mul_isBoundedUnder_le
-/
theorem tendsto_atTop_mul_right_of_le' (C : G) (hf : Tendsto f l atTop) (hg : forallᶠ x in l, C <= g x) :
    Tendsto (fun x => f x * g x) l atTop :=
  .atTop_of_mul_isBoundedUnder_le (g := g⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]
/--
theorem `tendsto_atBot_mul_right_of_ge'` / 定理 `tendsto_atBot_mul_right_of_ge'`

English:
theorem tendsto_atBot_mul_right_of_ge'
  given: (C : G) (hf : Tendsto f l atBot) (hg : forallᶠ x in l, g x <= C)
  proof: tendsto_atTop_mul_right_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]

中文:
定理 tendsto_atBot_mul_right_of_ge'
  条件: (C : G) (hf : 收敛 f l atBot) (hg : 对任意ᶠ x in l, g x <= C)
  证明: tendsto_atTop_mul_right_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]

Depends on / 依赖: tendsto_atTop_mul_right_of_le
-/
theorem tendsto_atBot_mul_right_of_ge' (C : G) (hf : Tendsto f l atBot) (hg : forallᶠ x in l, g x <= C) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_right_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]
/--
theorem `tendsto_atTop_mul_right_of_le` / 定理 `tendsto_atTop_mul_right_of_le`

English:
theorem tendsto_atTop_mul_right_of_le
  given: (C : G) (hf : Tendsto f l atTop) (hg : forall x, C <= g x)
  proof: tendsto_atTop_mul_right_of_le' l C hf (univ_mem' hg)

@[to_additive]

中文:
定理 tendsto_atTop_mul_right_of_le
  条件: (C : G) (hf : 收敛 f l atTop) (hg : 对任意 x, C <= g x)
  证明: tendsto_atTop_mul_right_of_le' l C hf (univ_mem' hg)

@[to_additive]

Depends on / 依赖: tendsto_atTop_mul_right_of_le, univ_mem
-/
theorem tendsto_atTop_mul_right_of_le (C : G) (hf : Tendsto f l atTop) (hg : forall x, C <= g x) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mul_right_of_le' l C hf (univ_mem' hg)

@[to_additive]
/--
theorem `tendsto_atBot_mul_right_of_ge` / 定理 `tendsto_atBot_mul_right_of_ge`

English:
theorem tendsto_atBot_mul_right_of_ge
  given: (C : G) (hf : Tendsto f l atBot) (hg : forall x, g x <= C)
  proof: tendsto_atTop_mul_right_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]

中文:
定理 tendsto_atBot_mul_right_of_ge
  条件: (C : G) (hf : 收敛 f l atBot) (hg : 对任意 x, g x <= C)
  证明: tendsto_atTop_mul_right_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]

Depends on / 依赖: tendsto_atTop_mul_right_of_le
-/
theorem tendsto_atBot_mul_right_of_ge (C : G) (hf : Tendsto f l atBot) (hg : forall x, g x <= C) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_right_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]
/--
theorem `tendsto_atTop_mul_const_left` / 定理 `tendsto_atTop_mul_const_left`

English:
theorem tendsto_atTop_mul_const_left
  given: (C : G) (hf : Tendsto f l atTop)
  proof: tendsto_atTop_mul_left_of_le' l C (univ_mem' fun _ => le_refl C) hf

@[to_additive]

中文:
定理 tendsto_atTop_mul_const_left
  条件: (C : G) (hf : 收敛 f l atTop)
  证明: tendsto_atTop_mul_left_of_le' l C (univ_mem' fun _ => le_refl C) hf

@[to_additive]

Depends on / 依赖: le_refl, tendsto_atTop_mul_left_of_le, univ_mem
-/
theorem tendsto_atTop_mul_const_left (C : G) (hf : Tendsto f l atTop) :
    Tendsto (fun x => C * f x) l atTop :=
  tendsto_atTop_mul_left_of_le' l C (univ_mem' fun _ => le_refl C) hf

@[to_additive]
/--
theorem `tendsto_atBot_mul_const_left` / 定理 `tendsto_atBot_mul_const_left`

English:
theorem tendsto_atBot_mul_const_left
  given: (C : G) (hf : Tendsto f l atBot)
  proof: tendsto_atTop_mul_const_left (G := Gᵒᵈ) _ C hf

@[to_additive]

中文:
定理 tendsto_atBot_mul_const_left
  条件: (C : G) (hf : 收敛 f l atBot)
  证明: tendsto_atTop_mul_const_left (G := Gᵒᵈ) _ C hf

@[to_additive]

Depends on / 依赖: tendsto_atTop_mul_const_left
-/
theorem tendsto_atBot_mul_const_left (C : G) (hf : Tendsto f l atBot) :
    Tendsto (fun x => C * f x) l atBot :=
  tendsto_atTop_mul_const_left (G := Gᵒᵈ) _ C hf

@[to_additive]
/--
theorem `tendsto_atTop_mul_const_right` / 定理 `tendsto_atTop_mul_const_right`

English:
theorem tendsto_atTop_mul_const_right
  given: (C : G) (hf : Tendsto f l atTop)
  proof: tendsto_atTop_mul_right_of_le' l C hf (univ_mem' fun _ => le_refl C)

@[to_additive]

中文:
定理 tendsto_atTop_mul_const_right
  条件: (C : G) (hf : 收敛 f l atTop)
  证明: tendsto_atTop_mul_right_of_le' l C hf (univ_mem' fun _ => le_refl C)

@[to_additive]

Depends on / 依赖: le_refl, tendsto_atTop_mul_right_of_le, univ_mem
-/
theorem tendsto_atTop_mul_const_right (C : G) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * C) l atTop :=
  tendsto_atTop_mul_right_of_le' l C hf (univ_mem' fun _ => le_refl C)

@[to_additive]
/--
theorem `tendsto_atBot_mul_const_right` / 定理 `tendsto_atBot_mul_const_right`

English:
theorem tendsto_atBot_mul_const_right
  given: (C : G) (hf : Tendsto f l atBot)
  proof: tendsto_atTop_mul_const_right (G := Gᵒᵈ) _ C hf

@[to_additive]

中文:
定理 tendsto_atBot_mul_const_right
  条件: (C : G) (hf : 收敛 f l atBot)
  证明: tendsto_atTop_mul_const_right (G := Gᵒᵈ) _ C hf

@[to_additive]

Depends on / 依赖: tendsto_atTop_mul_const_right
-/
theorem tendsto_atBot_mul_const_right (C : G) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * C) l atBot :=
  tendsto_atTop_mul_const_right (G := Gᵒᵈ) _ C hf

@[to_additive]
/--
theorem `map_inv_atBot` / 定理 `map_inv_atBot`

English:
theorem map_inv_atBot
  statement: map (Inv.inv : G -> G) atBot = atTop
  proof: (OrderIso.inv G).map_atBot

@[to_additive]

中文:
定理 map_inv_atBot
  结论: map (取逆.inv : G -> G) atBot = atTop
  证明: (OrderIso.inv G).map_atBot

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, map_atBot
-/
theorem map_inv_atBot : map (Inv.inv : G -> G) atBot = atTop :=
  (OrderIso.inv G).map_atBot

@[to_additive]
/--
theorem `map_inv_atTop` / 定理 `map_inv_atTop`

English:
theorem map_inv_atTop
  statement: map (Inv.inv : G -> G) atTop = atBot
  proof: (OrderIso.inv G).map_atTop

@[to_additive]

中文:
定理 map_inv_atTop
  结论: map (取逆.inv : G -> G) atTop = atBot
  证明: (OrderIso.inv G).map_atTop

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, map_atTop
-/
theorem map_inv_atTop : map (Inv.inv : G -> G) atTop = atBot :=
  (OrderIso.inv G).map_atTop

@[to_additive]
/--
theorem `comap_inv_atBot` / 定理 `comap_inv_atBot`

English:
theorem comap_inv_atBot
  statement: comap (Inv.inv : G -> G) atBot = atTop
  proof: (OrderIso.inv G).comap_atTop

@[to_additive]

中文:
定理 comap_inv_atBot
  结论: comap (取逆.inv : G -> G) atBot = atTop
  证明: (OrderIso.inv G).comap_atTop

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, comap_atTop
-/
theorem comap_inv_atBot : comap (Inv.inv : G -> G) atBot = atTop :=
  (OrderIso.inv G).comap_atTop

@[to_additive]
/--
theorem `comap_inv_atTop` / 定理 `comap_inv_atTop`

English:
theorem comap_inv_atTop
  statement: comap (Inv.inv : G -> G) atTop = atBot
  proof: (OrderIso.inv G).comap_atBot

@[to_additive]

中文:
定理 comap_inv_atTop
  结论: comap (取逆.inv : G -> G) atTop = atBot
  证明: (OrderIso.inv G).comap_atBot

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, comap_atBot
-/
theorem comap_inv_atTop : comap (Inv.inv : G -> G) atTop = atBot :=
  (OrderIso.inv G).comap_atBot

@[to_additive]
/--
theorem `tendsto_inv_atTop_atBot` / 定理 `tendsto_inv_atTop_atBot`

English:
theorem tendsto_inv_atTop_atBot
  statement: Tendsto (Inv.inv : G -> G) atTop atBot
  proof: (OrderIso.inv G).tendsto_atTop

@[to_additive]

中文:
定理 tendsto_inv_atTop_atBot
  结论: 收敛 (取逆.inv : G -> G) atTop atBot
  证明: (OrderIso.inv G).tendsto_atTop

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, tendsto_atTop
-/
theorem tendsto_inv_atTop_atBot : Tendsto (Inv.inv : G -> G) atTop atBot :=
  (OrderIso.inv G).tendsto_atTop

@[to_additive]
/--
theorem `tendsto_inv_atBot_atTop` / 定理 `tendsto_inv_atBot_atTop`

English:
theorem tendsto_inv_atBot_atTop
  statement: Tendsto (Inv.inv : G -> G) atBot atTop
  proof: tendsto_inv_atTop_atBot (G := Gᵒᵈ)

中文:
定理 tendsto_inv_atBot_atTop
  结论: 收敛 (取逆.inv : G -> G) atBot atTop
  证明: tendsto_inv_atTop_atBot (G := Gᵒᵈ)

Depends on / 依赖: tendsto_inv_atTop_atBot
-/
theorem tendsto_inv_atBot_atTop : Tendsto (Inv.inv : G -> G) atBot atTop :=
  tendsto_inv_atTop_atBot (G := Gᵒᵈ)

variable {l}

@[to_additive (attr := simp)]
/--
theorem `tendsto_inv_atTop_iff` / 定理 `tendsto_inv_atTop_iff`

English:
theorem tendsto_inv_atTop_iff
  statement: Tendsto (fun x => (f x)⁻¹) l atTop ↔ Tendsto f l atBot
  proof: (OrderIso.inv G).tendsto_atBot_iff

@[to_additive (attr := simp)]

中文:
定理 tendsto_inv_atTop_iff
  结论: 收敛 (fun x => (f x)⁻¹) l atTop ↔ 收敛 f l atBot
  证明: (OrderIso.inv G).tendsto_atBot_iff

@[to_additive (attr := simp)]

Depends on / 依赖: OrderIso, OrderIso.inv, tendsto_atBot_iff
-/
theorem tendsto_inv_atTop_iff : Tendsto (fun x => (f x)⁻¹) l atTop ↔ Tendsto f l atBot :=
  (OrderIso.inv G).tendsto_atBot_iff

@[to_additive (attr := simp)]
/--
theorem `tendsto_inv_atBot_iff` / 定理 `tendsto_inv_atBot_iff`

English:
theorem tendsto_inv_atBot_iff
  statement: Tendsto (fun x => (f x)⁻¹) l atBot ↔ Tendsto f l atTop
  proof: (OrderIso.inv G).tendsto_atTop_iff

@[to_additive (attr := simp)]

中文:
定理 tendsto_inv_atBot_iff
  结论: 收敛 (fun x => (f x)⁻¹) l atBot ↔ 收敛 f l atTop
  证明: (OrderIso.inv G).tendsto_atTop_iff

@[to_additive (attr := simp)]

Depends on / 依赖: OrderIso, OrderIso.inv, tendsto_atTop_iff
-/
theorem tendsto_inv_atBot_iff : Tendsto (fun x => (f x)⁻¹) l atBot ↔ Tendsto f l atTop :=
  (OrderIso.inv G).tendsto_atTop_iff

@[to_additive (attr := simp)]
/--
theorem `tendsto_comp_inv_atTop_iff` / 定理 `tendsto_comp_inv_atTop_iff`

English:
theorem tendsto_comp_inv_atTop_iff
  given: {f : G -> α}
  proof: by
  simp [← Function.comp_def, Tendsto, ← map_map, map_inv_atTop]

@[to_additive (attr := simp)]

中文:
定理 tendsto_comp_inv_atTop_iff
  条件: {f : G -> α}
  证明: by
  simp [← Function.comp_def, Tendsto, ← map_map, map_inv_atTop]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, Tendsto, comp_def, map_inv_atTop, map_map
-/
theorem tendsto_comp_inv_atTop_iff {f : G -> α} :
    Tendsto (fun x => f (x⁻¹)) atTop l ↔ Tendsto f atBot l := by
  simp [← Function.comp_def, Tendsto, ← map_map, map_inv_atTop]

@[to_additive (attr := simp)]
/--
theorem `tendsto_comp_inv_atBot_iff` / 定理 `tendsto_comp_inv_atBot_iff`

English:
theorem tendsto_comp_inv_atBot_iff
  given: {f : G -> α}
  proof: by
  simp [← Function.comp_def, Tendsto, ← map_map, map_inv_atBot]

中文:
定理 tendsto_comp_inv_atBot_iff
  条件: {f : G -> α}
  证明: by
  simp [← Function.comp_def, Tendsto, ← map_map, map_inv_atBot]

Depends on / 依赖: Function, Function.comp_def, Tendsto, comp_def, map_inv_atBot, map_map
-/
theorem tendsto_comp_inv_atBot_iff {f : G -> α} :
    Tendsto (fun x => f (x⁻¹)) atBot l ↔ Tendsto f atTop l := by
  simp [← Function.comp_def, Tendsto, ← map_map, map_inv_atBot]

end OrderedCommGroup

section LinearOrderedCommGroup

variable [CommGroup G] [LinearOrder G]

/-- $\lim_{x\to+\infty}|x|_m=+\infty$ -/
@[to_additive /-- $\lim_{x\to+\infty}|x|=+\infty$ -/]
/--
theorem `tendsto_mabs_atTop_atTop` / 定理 `tendsto_mabs_atTop_atTop`

English:
theorem tendsto_mabs_atTop_atTop
  statement: Tendsto (mabs : G -> G) atTop atTop
  proof: tendsto_atTop_mono le_mabs_self tendsto_id

中文:
定理 tendsto_mabs_atTop_atTop
  结论: 收敛 (mabs : G -> G) atTop atTop
  证明: tendsto_atTop_mono le_mabs_self tendsto_id

Depends on / 依赖: le_mabs_self, tendsto_atTop_mono, tendsto_id
-/
theorem tendsto_mabs_atTop_atTop : Tendsto (mabs : G -> G) atTop atTop :=
  tendsto_atTop_mono le_mabs_self tendsto_id

/-- $\lim_{x\to\infty^{-1}|x|_m=+\infty$ -/
@[to_additive /-- $\lim_{x\to-\infty}|x|=+\infty$ -/]
/--
theorem `tendsto_mabs_atBot_atTop` / 定理 `tendsto_mabs_atBot_atTop`

English:
theorem tendsto_mabs_atBot_atTop
  given: [IsOrderedMonoid G]
  statement: Tendsto (mabs : G -> G) atBot atTop
  proof: tendsto_atTop_mono inv_le_mabs tendsto_inv_atBot_atTop

@[to_additive (attr := simp)]

中文:
定理 tendsto_mabs_atBot_atTop
  条件: [是Ordered幺半群 G]
  结论: 收敛 (mabs : G -> G) atBot atTop
  证明: tendsto_atTop_mono inv_le_mabs tendsto_inv_atBot_atTop

@[to_additive (attr := simp)]

Depends on / 依赖: inv_le_mabs, tendsto_atTop_mono, tendsto_inv_atBot_atTop
-/
theorem tendsto_mabs_atBot_atTop [IsOrderedMonoid G] : Tendsto (mabs : G -> G) atBot atTop :=
  tendsto_atTop_mono inv_le_mabs tendsto_inv_atBot_atTop

@[to_additive (attr := simp)]
/--
theorem `comap_mabs_atTop` / 定理 `comap_mabs_atTop`

English:
theorem comap_mabs_atTop
  given: [IsOrderedMonoid G]
  statement: comap (mabs : G -> G) atTop = atBot ⊔ atTop
  proof: by
  refine
    le_antisymm (((atTop_basis.comap _).le_basis_iff (atBot_basis.sup atTop_basis)).2 ?_)
      (sup_le tendsto_mabs_atBot_atTop.le_comap tendsto_mabs_atTop_atTop.le_comap)
  rintro ⟨a, b⟩ -
  refine ⟨max (a⁻¹) b, trivial, fun x hx => ?_⟩
  rw [mem_preimage]; rw [mem_Ici]; rw [le_mabs'];

中文:
定理 comap_mabs_atTop
  条件: [是Ordered幺半群 G]
  结论: comap (mabs : G -> G) atTop = atBot ⊔ atTop
  证明: by
  refine
    le_antisymm (((atTop_basis.comap _).le_basis_iff (atBot_basis.sup atTop_basis)).2 ?_)
      (sup_le tendsto_mabs_atBot_atTop.le_comap tendsto_mabs_atTop_atTop.le_comap)
  rintro ⟨a, b⟩ -
  refine ⟨max (a⁻¹) b, trivial, fun x hx => ?_⟩
  rw [mem_preimage]; rw [mem_Ici]; rw [le_mabs'];

Depends on / 依赖: And.left, And.right, atBot_basis, atBot_basis.sup, atTop_basis, atTop_basis.comap, hx.imp, inv_inv, le_antisymm, le_basis_iff, le_comap, le_mabs, le_min_iff, max_le_iff, mem_Ici, mem_preimage, min_inv_inv, sup_le, tendsto_mabs_atBot_atTop, tendsto_mabs_atBot_atTop.le_comap
-/
theorem comap_mabs_atTop [IsOrderedMonoid G] : comap (mabs : G -> G) atTop = atBot ⊔ atTop := by
  refine
    le_antisymm (((atTop_basis.comap _).le_basis_iff (atBot_basis.sup atTop_basis)).2 ?_)
      (sup_le tendsto_mabs_atBot_atTop.le_comap tendsto_mabs_atTop_atTop.le_comap)
  rintro ⟨a, b⟩ -
  refine ⟨max (a⁻¹) b, trivial, fun x hx => ?_⟩
  rw [mem_preimage]; rw [mem_Ici]; rw [le_mabs']; rw [max_le_iff]; rw [← min_inv_inv']; rw [le_min_iff]; rw [inv_inv] at hx
  exact hx.imp And.left And.right

end LinearOrderedCommGroup

end Filter
