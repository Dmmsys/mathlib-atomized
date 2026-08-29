/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

/-!
# Lemmas which are consequences of monoidal coherence

These lemmas are all proved `by coherence`.

## Future work
Investigate whether these lemmas are really needed,
or if they can be replaced by use of the `coherence` tactic.
-/

public section


open CategoryTheory Category Iso

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
@[reassoc]
/--
theorem `leftUnitor_tensor_hom''` / 定理 `leftUnitor_tensor_hom''`

English:
theorem leftUnitor_tensor_hom''
  given: (X Y : C)
  proof: by
  simp

@[reassoc]

中文:
定理 leftUnitor_tensor_hom''
  条件: (X Y : C)
  证明: by
  simp

@[reassoc]
-/
theorem leftUnitor_tensor_hom'' (X Y : C) :
    (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes Y)).hom = (fun_ X).hom otimesₘ 𝟙 Y := by
  simp

@[reassoc]
/--
theorem `leftUnitor_tensor_hom'` / 定理 `leftUnitor_tensor_hom'`

English:
theorem leftUnitor_tensor_hom'
  given: (X Y : C)
  proof: by
  simp

@[reassoc]

中文:
定理 leftUnitor_tensor_hom'
  条件: (X Y : C)
  证明: by
  simp

@[reassoc]
-/
theorem leftUnitor_tensor_hom' (X Y : C) :
    (fun_ (X otimes Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ ((fun_ X).hom otimesₘ 𝟙 Y) := by
  simp

@[reassoc]
/--
theorem `leftUnitor_tensor_inv'` / 定理 `leftUnitor_tensor_inv'`

English:
theorem leftUnitor_tensor_inv'
  given: (X Y : C)
  proof: by simp

@[reassoc]

中文:
定理 leftUnitor_tensor_inv'
  条件: (X Y : C)
  证明: by simp

@[reassoc]
-/
theorem leftUnitor_tensor_inv' (X Y : C) :
    (fun_ (X otimes Y)).inv = ((fun_ X).inv otimesₘ 𝟙 Y) ≫ (α_ (𝟙_ C) X Y).hom := by simp

@[reassoc]
/--
theorem `id_tensor_rightUnitor_inv` / 定理 `id_tensor_rightUnitor_inv`

English:
theorem id_tensor_rightUnitor_inv
  given: (X Y : C)
  statement: 𝟙 X otimesₘ (ρ_ Y).inv = (ρ_ _).inv ≫ (α_ _ _ _).hom
  proof: by
  simp

@[reassoc]

中文:
定理 id_tensor_rightUnitor_inv
  条件: (X Y : C)
  结论: 𝟙 X otimesₘ (ρ_ Y).inv = (ρ_ _).inv ≫ (α_ _ _ _).hom
  证明: by
  simp

@[reassoc]
-/
theorem id_tensor_rightUnitor_inv (X Y : C) : 𝟙 X otimesₘ (ρ_ Y).inv = (ρ_ _).inv ≫ (α_ _ _ _).hom := by
  simp

@[reassoc]
/--
theorem `leftUnitor_inv_tensor_id` / 定理 `leftUnitor_inv_tensor_id`

English:
theorem leftUnitor_inv_tensor_id
  given: (X Y : C)
  statement: (fun_ X).inv otimesₘ 𝟙 Y = (fun_ _).inv ≫ (α_ _ _ _).inv
  proof: by
  simp

@[reassoc]

中文:
定理 leftUnitor_inv_tensor_id
  条件: (X Y : C)
  结论: (fun_ X).inv otimesₘ 𝟙 Y = (fun_ _).inv ≫ (α_ _ _ _).inv
  证明: by
  simp

@[reassoc]
-/
theorem leftUnitor_inv_tensor_id (X Y : C) : (fun_ X).inv otimesₘ 𝟙 Y = (fun_ _).inv ≫ (α_ _ _ _).inv := by
  simp

@[reassoc]
/--
theorem `pentagon_inv_inv_hom` / 定理 `pentagon_inv_inv_hom`

English:
theorem pentagon_inv_inv_hom
  given: (W X Y Z : C)
  proof: by
  simp

中文:
定理 pentagon_inv_inv_hom
  条件: (W X Y Z : C)
  证明: by
  simp
-/
theorem pentagon_inv_inv_hom (W X Y Z : C) :
    (α_ W (X otimes Y) Z).inv ≫ ((α_ W X Y).inv otimesₘ 𝟙 Z) ≫ (α_ (W otimes X) Y Z).hom =
      (𝟙 W otimesₘ (α_ X Y Z).hom) ≫ (α_ W X (Y otimes Z)).inv := by
  simp

/--
theorem `unitors_equal` / 定理 `unitors_equal`

English:
theorem unitors_equal
  statement: (fun_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom
  proof: by
  monoidal_coherence

中文:
定理 unitors_equal
  结论: (fun_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom
  证明: by
  monoidal_coherence

Depends on / 依赖: monoidal_coherence
-/
theorem unitors_equal : (fun_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  monoidal_coherence

/--
theorem `unitors_inv_equal` / 定理 `unitors_inv_equal`

English:
theorem unitors_inv_equal
  statement: (fun_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv
  proof: by
  monoidal_coherence

@[reassoc]

中文:
定理 unitors_inv_equal
  结论: (fun_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv
  证明: by
  monoidal_coherence

@[reassoc]

Depends on / 依赖: monoidal_coherence
-/
theorem unitors_inv_equal : (fun_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by
  monoidal_coherence

@[reassoc]
/--
theorem `pentagon_hom_inv` / 定理 `pentagon_hom_inv`

English:
theorem pentagon_hom_inv
  given: {W X Y Z : C}
  proof: by
  simp

@[reassoc]

中文:
定理 pentagon_hom_inv
  条件: {W X Y Z : C}
  证明: by
  simp

@[reassoc]

Depends on / 依赖: Coverage, Coverage.Saturate.of, Coverage.Saturate.transitive, Nonempty, Presieve, Presieve.ofArrows, Saturate, Sieve.effectiveEpimorphic_family, Sieve.forallYonedaIsSheaf_iff_colimit, Sieve.generate, Sieve.pullback_comp, effectiveEpi_iff_effectiveEpiFamily, effectiveEpimorphic_family, forallYonedaIsSheaf_iff_colimit, generate, isSheaf_yoneda_obj, ofArrows, pullback_comp, regularTopology, regularTopology.isSheaf_yoneda_obj
-/
theorem pentagon_hom_inv {W X Y Z : C} :
    (α_ W X (Y otimes Z)).hom ≫ (𝟙 W otimesₘ (α_ X Y Z).inv) =
      (α_ (W otimes X) Y Z).inv ≫ ((α_ W X Y).hom otimesₘ 𝟙 Z) ≫ (α_ W (X otimes Y) Z).hom := by
  simp

@[reassoc]
/--
theorem `pentagon_inv_hom` / 定理 `pentagon_inv_hom`

English:
theorem pentagon_inv_hom
  given: (W X Y Z : C)
  proof: by
  simp

中文:
定理 pentagon_inv_hom
  条件: (W X Y Z : C)
  证明: by
  simp
-/
theorem pentagon_inv_hom (W X Y Z : C) :
    (α_ (W otimes X) Y Z).inv ≫ ((α_ W X Y).hom otimesₘ 𝟙 Z) =
      (α_ W X (Y otimes Z)).hom ≫ (𝟙 W otimesₘ (α_ X Y Z).inv) ≫ (α_ W (X otimes Y) Z).inv := by
  simp

end CategoryTheory.MonoidalCategory
