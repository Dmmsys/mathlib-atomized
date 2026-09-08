/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Flat monomorphisms of finite presentation are open immersions

We show the titular result `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono` by fpqc descent.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

@[stacks 06NC]
/-
**AlgebraicGeometry.Flat.isIso_of_surjective_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Flat`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Flat f] 
[AlgebraicGeometry.QuasiCompact f]   [AlgebraicGeometry.Surjective f] [CategoryT
heory.Mono f], CategoryTheory.IsIso f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_pullback_fst_of_descendsAlong`：of_pul
lback_fst_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hf : Q f) (hfs
t : P (pullback.fst f g)) : P g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
-/
lemma Flat.isIso_of_surjective_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [QuasiCompact f] [Surjective f] [Mono f] : IsIso f := by
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := f)
  · tauto
  · exact inferInstanceAs <| IsIso (pullback.fst f f)

set_option backward.isDefEq.respectTransparency.types false in
/--
Flat monomorphisms that are locally of finite presentation are open immersions. In particular,
every smooth monomorphism is an open immersion.
The converse holds by `inferInstance`.
-/
/-
**AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.IsOpenImmersion`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Flat f] 
  [AlgebraicGeometry.LocallyOfFinitePresentation f] [CategoryTheory.Mono f], Alg
ebraicGeometry.IsOpenImmersion f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenMap`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyOpen f], IsOpenMap ⇑f
· 使用定理 `AlgebraicGeometry.UniversallyOpen.of_flat`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]   [AlgebraicGeometry.LocallyOfFinit
ePresentation f], AlgebraicGeom…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.injective`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyInjective f], Function.Injective ⇑f
· 使用定理 `AlgebraicGeometry.instUniversallyInjectiveOfMonoScheme`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.Mono f], AlgebraicGeometry.Univer
sallyInjective f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.surjective`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isCompact_preimage`：isCompact_preimage {s : Set Y} (h : X ≃ₜ 
Y) : IsCompact (h ⁻¹' s) ↔ IsCompact s
· 使用定理 `AlgebraicGeometry.Flat.isIso_of_surjective_of_mono`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Flat f] [AlgebraicGeometry.QuasiCo
mpact f]   [AlgebraicGeometry.Surjective…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `IsOpenMap.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → IsOpen (S
et.range f)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.instHasOfPostcompPropertySchemeIsOpenImmersionOfIsStab
leUnderBaseChange`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sche
me) [P.IsStableUnderBaseChange],   P.HasOfPostcompProperty AlgebraicGeometry.Is…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …

--- 原说明 ---
Flat monomorphisms that are locally of finite presentation are open immersions. 
In particular,
every smooth monomorphism is an open immersion.
The converse holds by `inferInstance`.
-/
theorem IsOpenImmersion.of_flat_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] [Mono f] : IsOpenImmersion f := by
  wlog hf : Surjective f
  · let U : Y.Opens := ⟨Set.range f.base, f.isOpenMap.isOpen_range⟩
    -- needed to prevent `wlog` to go in a typeclass loop
    have hU : IsOpenImmersion U.ι := U.instIsOpenImmersionι
    let f' := hU.lift U.ι f (by simp [U])
    have heq : f = f' ≫ U.ι := by simp [f']
    have hflat : Flat f' :=
      of_postcomp (W := @Flat) f' U.ι hU (by rwa [← heq])
    have hfinpres : LocallyOfFinitePresentation f' :=
      of_postcomp (W := @LocallyOfFinitePresentation) f' U.ι hU (by rwa [← heq])
    have hmono : Mono f' := mono_of_mono_fac heq.symm
    rw [heq]
    have := this f' ⟨fun ⟨x, ⟨y, hy⟩⟩ ↦
      ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, f', hy]⟩⟩
    infer_instance
  have hhomeo : IsHomeomorph f.base := ⟨f.continuous, f.isOpenMap, f.injective, f.surjective⟩
  have : QuasiCompact f := ⟨fun U hU hc ↦ hhomeo.homeomorph.isCompact_preimage.mpr hc⟩
  have := Flat.isIso_of_surjective_of_mono f
  exact .of_isIso f

end AlgebraicGeometry

