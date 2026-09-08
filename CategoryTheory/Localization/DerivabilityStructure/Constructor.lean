/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic

/-!
# Constructor for derivability structures

In this file, we provide a constructor for right and left derivability structures.
Assume that `W₁` and `W₂` are classes of morphisms in categories `C₁` and `C₂`,
and that we have a localizer morphism `Φ : LocalizerMorphism W₁ W₂` that is
a localized equivalence, i.e. `Φ.functor` induces an equivalence of categories
between the localized categories. Assume moreover that `W₂` contains identities.
Then, `Φ` is a right derivability structure
(`LocalizerMorphism.IsRightDerivabilityStructure.mk'`) if it satisfies the
two following conditions:
* for any `X₂ : C₂`, the category `Φ.RightResolution X₂` of resolutions of `X₂` is connected
* any arrow in `C₂` admits a resolution (i.e. `Φ.arrow.HasRightResolutions` holds, where
  `Φ.arrow` is the induced localizer morphism on categories of arrows in `C₁` and `C₂`)

(The dual statement for left derivability structures is also obtained.)

This statement is essentially Lemme 6.5 in
[the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008].

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

@[expose] public section

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism
namespace IsRightDerivabilityStructure

section

variable (Φ : LocalizerMorphism W₁ W₂)
  [∀ X₂, IsConnected (Φ.RightResolution X₂)]
  [Φ.arrow.HasRightResolutions] [W₂.ContainsIdentities]

namespace Constructor

variable {D : Type*} [Category* D] (L : C₂ ⥤ D) [L.IsLocalization W₂]
  {X₂ : C₂} {X₃ : D} (y : L.obj X₂ ⟶ X₃)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `Φ : LocalizerMorphism W₁ W₂`, `L : C₂ ⥤ D` a localization functor for `W₂` and
a morphism `y : L.obj X₂ ⟶ X₃`, this is the functor which sends `R : Φ.RightResolution d` to
`(isoOfHom L W₂ R.w R.hw).inv ≫ y` in the category `w.CostructuredArrowDownwards y`
where `w` is `TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.Constructor.from
RightResolution** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.LocalizerMorphism.IsRi
ghtDerivabilityStructure.Constructor`。
形式化陈述：fromRightResolution : Φ.RightResolution X₂ ⥤ (TwoSquare.mk Φ.functor (Φ.fu
nctor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv).CostructuredArrowDownwards y whe
re obj R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…

--- 原说明 ---
Given `Φ : LocalizerMorphism W₁ W₂`, `L : C₂ ⥤ D` a localization functor for `W₂
` and
a morphism `y : L.obj X₂ ⟶ X₃`, this is the functor which sends `R : Φ.RightReso
lution d` to
`(isoOfHom L W₂ R.w R.hw).inv ≫ y` in the category `w.CostructuredArrowDownwards
 y`
where `w` is `TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnito
r _).inv`.
-/
noncomputable def fromRightResolution :
    Φ.RightResolution X₂ ⥤ (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
      (Functor.rightUnitor _).inv).CostructuredArrowDownwards y where
  obj R := CostructuredArrow.mk (Y := StructuredArrow.mk R.w)
    (StructuredArrow.homMk ((isoOfHom L W₂ R.w R.hw).inv ≫ y))
  map {R R'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.f) (by
    ext
    dsimp
    rw [← assoc, ← cancel_epi (isoOfHom L W₂ R.w R.hw).hom,
      isoOfHom_hom, isoOfHom_hom_inv_id_assoc, assoc, ← L.map_comp_assoc,
      φ.comm, isoOfHom_hom_inv_id_assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.Constructor.isCo
nnected** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsRightDeriv
abilityStructure.Constructor`。
形式化陈述：isConnected : IsConnected ((TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
 (Functor.rightUnitor _).inv).CostructuredArrowDownwards y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
· 使用定理 `CategoryTheory.TwoSquare.CostructuredArrowDownwards.mk_surjective`：∀ {C₁
 : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.
Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Catego…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.zigzag_obj_of_zigzag`：zigzag_obj_of_zigzag (F : J ⥤ K) {j
₁ j₂ : J} (h : Zigzag j₁ j₂) : Zigzag (F.obj j₁) (F.obj j₂)
· 使用定理 `CategoryTheory.isPreconnected_zigzag`：isPreconnected_zigzag [IsPreconnec
ted J] (j₁ j₂ : J) : Zigzag j₁ j₂
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Localization.isoOfHom_id_inv`：isoOfHom_id_inv (X : C) (hX
 : W (𝟙 X)) : (isoOfHom L W (𝟙 X) hX).inv = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.StructuredArrow.homMk.congr_simp`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {S : D} {T : Categ…
· 使用定理 `CategoryTheory.TwoSquare.CostructuredArrowDownwards.mk.congr_simp`：∀ {C₁
 : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.
Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Zigzag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right
· 使用引理 `CategoryTheory.StructuredArrow.hom_ext`：hom_ext {X Y : StructuredArrow S
 T} (f g : X ⟶ Y) (h : f.right = g.right) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 36 条，此处仅展示前 30 条）
-/
lemma isConnected :
    IsConnected ((TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
      (Functor.rightUnitor _).inv).CostructuredArrowDownwards y) := by
  let w := (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv)
  have : Nonempty (w.CostructuredArrowDownwards y) :=
    ⟨(fromRightResolution Φ L y).obj (Classical.arbitrary _)⟩
  suffices ∀ (X : w.CostructuredArrowDownwards y),
      ∃ Y, Zigzag X ((fromRightResolution Φ L y).obj Y) by
    refine zigzag_isConnected (fun X X' => ?_)
    obtain ⟨Y, hX⟩ := this X
    obtain ⟨Y', hX'⟩ := this X'
    exact hX.trans ((zigzag_obj_of_zigzag _ (isPreconnected_zigzag Y Y')).trans hX'.symm)
  intro X
  obtain ⟨c, g, x, fac, rfl⟩ := TwoSquare.CostructuredArrowDownwards.mk_surjective X
  dsimp [w] at x fac
  rw [id_comp] at fac
  let ρ : Φ.arrow.RightResolution (Arrow.mk g) := Classical.arbitrary _
  refine ⟨RightResolution.mk ρ.w.left ρ.hw.1, ?_⟩
  have := zigzag_obj_of_zigzag
    (fromRightResolution Φ L x ⋙ w.costructuredArrowDownwardsPrecomp x y g fac)
      (isPreconnected_zigzag (RightResolution.mk (𝟙 _) (W₂.id_mem _))
        (RightResolution.mk ρ.w.right ρ.hw.2))
  refine Zigzag.trans ?_ (Zigzag.trans this ?_)
  · exact Zigzag.of_hom (eqToHom (by simp))
  · apply Zigzag.of_inv
    refine CostructuredArrow.homMk (StructuredArrow.homMk ρ.X₁.hom (by simp)) ?_
    ext
    simp [← cancel_epi (isoOfHom L W₂ ρ.w.left ρ.hw.1).hom, ← L.map_comp_assoc, fac]

end Constructor

set_option backward.isDefEq.respectTransparency.types false in
/-- If a localizer morphism `Φ` is a localized equivalence, then it is a right
derivability structure if the categories of right resolutions are connected and the
categories of right resolutions of arrows are nonempty. -/
/-
**CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.mk'** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure`。
形式化陈述：mk' [Φ.IsLocalizedEquivalence] : Φ.IsRightDerivabilityStructure
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff`：isRig
htDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F
) : Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartE…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.isLocalization`：
∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : CategoryTheory.Category.{
v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂]…
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_iff_isConnected_downwards`：guitart
Exact_iff_isConnected_downwards : w.GuitartExact ↔ forall {X₂ : C₂} {X₃ : C₃} (g
 : R.obj X₂ ⟶ B.obj X₃), IsConnected (w.CostructuredA…
· 使用引理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.Constructo
r.isConnected`：isConnected : IsConnected ((TwoSquare.mk Φ.functor (Φ.functor ⋙ L
) L (𝟭 _) (Functor.rightUnitor _).inv).CostructuredArrowDownwards y)

--- 原说明 ---
If a localizer morphism `Φ` is a localized equivalence, then it is a right
derivability structure if the categories of right resolutions are connected and 
the
categories of right resolutions of arrows are nonempty.
-/
lemma mk' [Φ.IsLocalizedEquivalence] : Φ.IsRightDerivabilityStructure := by
  rw [Φ.isRightDerivabilityStructure_iff (Φ.functor ⋙ W₂.Q) W₂.Q (𝟭 _)
    (Functor.rightUnitor _).symm, TwoSquare.guitartExact_iff_isConnected_downwards]
  apply Constructor.isConnected

end

end IsRightDerivabilityStructure

/-- If a localizer morphism `Φ` is a localized equivalence, then it is a left
derivability structure if the categories of left resolutions are connected and the
categories of left resolutions of arrows are nonempty. -/
/-
**CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure.mk'** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_
1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] {W₁ : CategoryTheory.M
orphismProperty C₁}   {W₂ : CategoryTheory.MorphismProperty C₂} (Φ : CategoryThe
ory.LocalizerMorphism W₁ W₂)   [∀ (X₂ : C₂), CategoryTheory.IsConnected (Φ.LeftR
esolution X₂)] [Φ.arrow.HasLeftResolutions] [W₂.ContainsIdentities]   [Φ.IsLocal
izedEquivalence], Φ.IsLeftDerivabilityStructure
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；X₂ : C₂；Φ.LeftResolution X₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff_op`：isL
eftDerivabilityStructure_iff_op : Φ.IsLeftDerivabilityStructure ↔ Φ.op.IsRightDe
rivabilityStructure
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.hw`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用引理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.mk'`：mk' [
Φ.IsLocalizedEquivalence] : Φ.IsRightDerivabilityStructure
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsLocalizedEquivalenceOppositeOpOp`
：∀ {C₁ : Type u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   
[inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…

--- 原说明 ---
If a localizer morphism `Φ` is a localized equivalence, then it is a left
derivability structure if the categories of left resolutions are connected and t
he
categories of left resolutions of arrows are nonempty.
-/
lemma IsLeftDerivabilityStructure.mk' (Φ : LocalizerMorphism W₁ W₂)
    [∀ X₂, IsConnected (Φ.LeftResolution X₂)]
    [Φ.arrow.HasLeftResolutions] [W₂.ContainsIdentities]
    [Φ.IsLocalizedEquivalence] :
    Φ.IsLeftDerivabilityStructure := by
  rw [isLeftDerivabilityStructure_iff_op]
  have : Φ.op.arrow.HasRightResolutions := fun f ↦ by
    let R : Φ.arrow.LeftResolution (Arrow.mk f.hom.unop) := Classical.arbitrary _
    exact ⟨{
      X₁ := Arrow.mk R.X₁.hom.op
      w := Arrow.homMk R.w.right.op R.w.left.op (Quiver.Hom.unop_inj R.w.w.symm)
      hw := ⟨R.hw.right, R.hw.left⟩ }⟩
  have (X₂ : C₂ᵒᵖ) : IsConnected (Φ.op.RightResolution X₂) :=
    isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂.unop)
  exact IsRightDerivabilityStructure.mk' _

end LocalizerMorphism

end CategoryTheory

