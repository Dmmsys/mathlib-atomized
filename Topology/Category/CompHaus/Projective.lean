/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# CompHaus has enough projectives

In this file we show that `CompHaus` has enough projectives.

## Main results

Let `X` be a compact Hausdorff space.

* `CompHaus.projective_ultrafilter`: the space `Ultrafilter X` is a projective object
* `CompHaus.projectivePresentation`: the natural map `Ultrafilter X → X`
  is a projective presentation

## Reference

See [miraglia2006introduction] Chapter 21 for a proof that `CompHaus` has enough projectives.

-/

@[expose] public section


noncomputable section

open CategoryTheory Function

namespace CompHaus

/--
Instance `projective_ultrafilter` / 实例 `projective_ultrafilter`

English:
instance projective_ultrafilter
  signature: (X : Type*)
  body: by
    rw [epi_iff_surjective] at hg
    obtain ⟨g', hg'⟩ := hg.hasRightInverse
    let t : X -> Y := g' ∘ f ∘ (pure : X -> Ultrafilter X)
    let h : Ultrafilter X -> Y := Ultrafilter.extend t
    have hh : Continuous h := continuous_ultrafilter_extend _
    use CompHausLike.ofHom _ ⟨h, hh⟩
    app

中文:
实例 projective_ultrafilter
  签名: (X : 类型)
  定义体: by
    rw [epi_iff_surjective] at hg
    obtain ⟨g', hg'⟩ := hg.hasRightInverse
    let t : X -> Y := g' ∘ f ∘ (pure : X -> Ultrafilter X)
    let h : Ultrafilter X -> Y := Ultrafilter.extend t
    have hh : Continuous h := continuous_ultrafilter_extend _
    use CompHausLike.ofHom _ ⟨h, hh⟩
    app

Depends on / 依赖: CompHausLike, CompHausLike.ofHom, ConcreteCategory, ConcreteCategory.coe_ext, Continuous, Ultrafilter, Ultrafilter.extend, coe_ext, comp_eq_id, continuous, continuous_ultrafilter_extend, convert, denseRange_pure, denseRange_pure.equalizer, epi_iff_surjective, equalizer, extend, f.hom.hom.continuous, g.hom, g.hom.hom.continuous.comp
-/
instance projective_ultrafilter (X : Type*) : Projective (of <| Ultrafilter X) where
  factors {Y Z} f g hg := by
    rw [epi_iff_surjective] at hg
    obtain ⟨g', hg'⟩ := hg.hasRightInverse
    let t : X -> Y := g' ∘ f ∘ (pure : X -> Ultrafilter X)
    let h : Ultrafilter X -> Y := Ultrafilter.extend t
    have hh : Continuous h := continuous_ultrafilter_extend _
    use CompHausLike.ofHom _ ⟨h, hh⟩
    apply ConcreteCategory.coe_ext
    have : g.hom ∘ g' = id := hg'.comp_eq_id
    convert!
      denseRange_pure.equalizer (g.hom.hom.continuous.comp hh) f.hom.hom.continuous
        _
          -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644

    -- This used to be `rw`, but we need `rw; rfl` after https://github.com/leanprover/lean4/pull/2644
    rw [comp_assoc]; rw [ultrafilter_extend_extends]; rw [← comp_assoc]; rw [this]; rw [id_comp]
    rfl

/--
Definition of `projectivePresentation` / `projectivePresentation` 的定义

English:
definition projectivePresentation
  signature: (X : CompHaus)
  body: of Ultrafilter X
  f := CompHausLike.ofHom _ ⟨_, continuous_ultrafilter_extend id⟩
  projective := CompHaus.projective_ultrafilter X
  epi :=
    ConcreteCategory.epi_of_surjective _ fun x =>
      ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩

中文:
定义 projectivePresentation
  签名: (X : CompHaus)
  定义体: of Ultrafilter X
  f := CompHausLike.ofHom _ ⟨_, continuous_ultrafilter_extend id⟩
  projective := CompHaus.projective_ultrafilter X
  epi :=
    ConcreteCategory.epi_of_surjective _ fun x =>
      ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩

Depends on / 依赖: Ultrafilter
-/
def projectivePresentation (X : CompHaus) : ProjectivePresentation X where
p := of Ultrafilter X
  f := CompHausLike.ofHom _ ⟨_, continuous_ultrafilter_extend id⟩
  projective := CompHaus.projective_ultrafilter X
  epi :=
    ConcreteCategory.epi_of_surjective _ fun x =>
      ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnoughProjectives CompHaus
  body: ⟨projectivePresentation X⟩

中文:
实例 :
  签名: 有足够投射 CompHaus
  定义体: ⟨projectivePresentation X⟩

Depends on / 依赖: projectivePresentation
-/
instance : EnoughProjectives CompHaus where presentation X := ⟨projectivePresentation X⟩

end CompHaus
