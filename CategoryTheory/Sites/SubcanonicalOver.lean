/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Topology on `Over X` is subcanonical if the base is

We show that if `J` is subcanonical, then also `J.over X` is subcanonical.
-/

public section

namespace CategoryTheory.GrothendieckTopology

variable {C : Type*} [Category* C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.subcanonical_over** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：subcanonical_over (J : GrothendieckTopology C) [J.Subcanonical] (X : C) : 
(J.over X).Subcanonical
参数：J : GrothendieckTopology C；X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`：
of_isSheaf_yoneda_obj (J : GrothendieckTopology C) (h : forall X, Presieve.IsShe
af J (yoneda.obj X)) : Subcanonical J where le_canonical
· 使用引理 `CategoryTheory.Sieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Sieve X
) : exists (I : Type max u₁ v₁) (Y : I -> C) (f : forall i, Y i ⟶ X), R = Sieve.
ofArrows _ f
· 使用引理 `CategoryTheory.Sieve.ofArrows_mk`：ofArrows_mk (i : I) : ofArrows Y f (f 
i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresenta
ble`：isSheaf_of_isRepresentable {J : GrothendieckTopology C} [Subcanonical J] (P
 : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] : Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Functor.instIsRepresentableObjOppositeTypeYoneda`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C}, (CategoryTheory.yo
neda.obj X).IsRepresentable
· 使用引理 `CategoryTheory.Presieve.map_ofArrows`：map_ofArrows {X : C} {ι : Type*} {
Y : ι -> C} (f : forall i, Y i ⟶ X) : (ofArrows Y f).map F = ofArrows _ (fun i =
> F.map (f i))
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用定理 `CategoryTheory.Sieve.arrows_generate_map_eq_functorPushforward`：arrows_g
enerate_map_eq_functorPushforward {s : Presieve X} : (generate (s.map F)).arrows
 = s.functorPushforward F
· 使用引理 `CategoryTheory.Sieve.overEquiv_generate`：overEquiv_generate {X : C} {Y :
 Over X} (R : Presieve Y) : overEquiv Y (.generate R) = .generate (Presieve.func
torPushforward (Over.forget X…
· 使用定理 `CategoryTheory.Sieve.ofArrows.eq_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {I : Type u_1} {X : C} (Y : I → C) (f : (i : I) → Y i ⟶ 
X),   CategoryTheory.Sie…
· 使用引理 `CategoryTheory.GrothendieckTopology.mem_over_iff`：mem_over_iff {X : C} {
Y : Over X} (S : Sieve Y) : S in (J.over X) Y ↔ Sieve.overEquiv _ S in J Y.left
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.sieveExtend`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor
 Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.Arrows.Compatible.familyOfElements_compatible`：f
amilyOfElements_compatible : hx.familyOfElements.Compatible
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `CategoryTheory.Presieve.extend_agrees`：extend_agrees {x : FamilyOfElemen
ts P R} (t : x.Compatible) {f : Y ⟶ X} (hf : R f) : x.sieveExtend f (le_generate
 R Y _ hf) = x f hf
（共 35 条，此处仅展示前 30 条）
-/
instance subcanonical_over (J : GrothendieckTopology C) [J.Subcanonical] (X : C) :
    (J.over X).Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun E Z R hR t ht ↦ ?_
  obtain ⟨ι, T, g, rfl⟩ := R.exists_eq_ofArrows
  let hg : Presieve.Arrows.Compatible (CategoryTheory.yoneda.obj E.left)
      (fun i ↦ (g i).left) (fun i ↦ (t (g i) (Sieve.ofArrows_mk T g i)).left) :=
    fun i j Z gi gj hgij ↦ congr($(ht (Over.homMk (U := Over.mk (gi ≫ (T i).hom)) gi rfl)
      (Over.homMk (U := Over.mk (gi ≫ (T i).hom)) gj
      (by dsimp; rw [← Over.w (g i), reassoc_of% hgij, ← Over.w (g j)]))
      (Sieve.ofArrows_mk _ _ i) (Sieve.ofArrows_mk _ _ j) (by ext; exact hgij)).left)
  rw [J.mem_over_iff, Sieve.ofArrows, Sieve.overEquiv_generate,
    ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
    Presieve.map_ofArrows] at hR
  obtain ⟨a, ha, huniq⟩ := Subcanonical.isSheaf_of_isRepresentable
    (CategoryTheory.yoneda.obj E.left) _ hR _ hg.familyOfElements_compatible.sieveExtend
  refine ⟨?_, ?_, fun y hty ↦ ?_⟩
  · refine Over.homMk a ?_
    refine (Subcanonical.isSheaf_of_isRepresentable <| CategoryTheory.yoneda.obj X)
      (.ofArrows _ <| fun i ↦ (g i).left) hR |>.isSeparatedFor.ext ?_
    rintro W u ⟨V, v, _, ⟨i⟩, rfl⟩
    have := ha _ (Sieve.ofArrows_mk _ _ i)
    dsimp at this
    simp [reassoc_of% this, Presieve.extend_agrees hg.familyOfElements_compatible (.mk i)]
  · rintro W p ⟨V, v, _, ⟨i⟩, rfl⟩
    refine Over.OverMorphism.ext ?_
    have := ha (g i).left (Sieve.ofArrows_mk _ _ i)
    dsimp at this
    simp [Category.assoc, this, Presieve.extend_agrees hg.familyOfElements_compatible (.mk i),
      Presieve.FamilyOfElements.comp_of_compatible _ ht (Sieve.ofArrows_mk _ _ i)]
  · refine Over.OverMorphism.ext (huniq _ ?_)
    rintro W p ⟨V, v, _, ⟨i⟩, rfl⟩
    have := congr($(hty _ (Sieve.ofArrows_mk _ _ i)).left)
    dsimp at this
    simp [Presieve.FamilyOfElements.comp_of_compatible _
      hg.familyOfElements_compatible.sieveExtend (Sieve.ofArrows_mk _ _ i),
      Presieve.extend_agrees hg.familyOfElements_compatible (.mk i), this]

end CategoryTheory.GrothendieckTopology

