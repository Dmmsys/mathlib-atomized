/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Sites.MorphismProperty

/-!
# Local closure of morphism properties

We define the source local closure of a morphism property `P` w.r.t. a precoverage `K` as the
weakest property containing `P` that is `K`-local on the source.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MorphismProperty

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.MorphismProperty

variable {K : Precoverage C}

/-- The source-local closure of `P` along a precoverage `K` is the weakest property
containing `P` that is local on the source. -/
/-
**CategoryTheory.MorphismProperty.sourceLocalClosure** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Precoverage C → CategoryTheory.MorphismProperty C → CategoryTheory.Morphis
mProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The source-local closure of `P` along a precoverage `K` is the weakest property
containing `P` that is local on the source.
-/
inductive sourceLocalClosure (K : Precoverage C) (P : MorphismProperty C) : MorphismProperty C
  /-- Force `P ≤ sourceLocalClosure K P`. -/
  | of {X Y : C} (f : X ⟶ Y) : P f → sourceLocalClosure K P f
  /-- Force `RespectsIso`. -/
  | of_iso {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (e : Arrow.mk f ≅ Arrow.mk g) :
      sourceLocalClosure K P f → sourceLocalClosure K P g
  | comp {X Y : C} (f : X ⟶ Y) (hf : sourceLocalClosure K P f) (R : Presieve X) (hR : R ∈ K X)
      {U : C} (g : U ⟶ X) : R g → sourceLocalClosure K P (g ≫ f)
  | of_presieve {X Y : C} (f : X ⟶ Y) (R : Presieve X) (hR : R ∈ K X)
      (h : ∀ (U : C) (g : U ⟶ X), R g → sourceLocalClosure K P (g ≫ f)) :
      sourceLocalClosure K P f

namespace sourceLocalClosure

attribute [grind .] of

variable {P Q : MorphismProperty C} {X Y : C}

/-
**CategoryTheory.MorphismProperty.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (sourceLocalClosure K P).IsLocalAtSource K where
  precomp i hi f hf := .of_iso _ _ (Arrow.isoMk' _ _ (asIso i).symm (.refl _)) hf
  postcomp i hi f hf := .of_iso _ _ (Arrow.isoMk' _ _ (.refl _) (asIso i)) hf
  comp hR _ g hg hf := .comp _ hf _ hR _ hg
  of_forall_comp hR h := .of_presieve _ _ hR h
/-
**CategoryTheory.MorphismProperty.sourceLocalClosure.le** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty.sourceLocalClosure`。
形式化陈述：le : P <= sourceLocalClosure K P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le : P ≤ sourceLocalClosure K P :=
  fun _ _ _ ↦ .of _
/-
**CategoryTheory.MorphismProperty.sourceLocalClosure.le_of_isLocalAtSource** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.sourceLocalClosure`。
形式化陈述：le_of_isLocalAtSource (h : P <= Q) [Q.IsLocalAtSource K] : sourceLocalClos
ure K P <= Q
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.comp`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}  
 {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.of_forall_comp`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPro
perty C}   {K : CategoryTheory.Precoverage C} [self …
-/
lemma le_of_isLocalAtSource (h : P ≤ Q) [Q.IsLocalAtSource K] : sourceLocalClosure K P ≤ Q := by
  intro X Y f hf
  induction hf with
  | of f hf => exact h _ hf
  | of_iso f g e _ hf => rwa [Q.arrow_mk_iso_iff e.symm]
  | comp f hf R hR g hg ih => apply IsLocalAtSource.comp hR _ hg ih
  | of_presieve f R hR h ih => apply IsLocalAtSource.of_forall_comp hR fun U g hg ↦ ih _ _ hg
/-
**CategoryTheory.MorphismProperty.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] : ContainsIdentities (sourceLocalClosure K P) where
  id_mem _ := le _ (P.id_mem _)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderBaseChange] [K.IsStableUnderBaseChange] [HasPullbacks C] :
    IsStableUnderBaseChange (sourceLocalClosure K P) where
  of_isPullback {Y} X W Z g f fst snd h hf := by
    induction hf generalizing W snd with
    | of f' hf' => exact .of _ (P.of_isPullback h hf')
    | of_iso f' g' e hf' ih =>
      exact ih _ (g ≫ e.inv.right) (fst ≫ e.inv.left) _ (h.paste_horiz (.of_horiz_isIso ⟨e.inv.w⟩))
    | comp f' hf' R hR g' hg' ih =>
      let u : W ⟶ pullback g f' := pullback.lift snd (fst ≫ g') (by simp [h.w.symm])
      have : snd = u ≫ pullback.fst g f' := by simp [u]
      rw [this] at h ⊢
      let e : W ≅ pullback g' (pullback.snd g f') :=
        IsPullback.isoPullback (.of_bot h (by simp [u]) (.flip <| .of_hasPullback _ _))
      rw [← (sourceLocalClosure K P).cancel_left_of_respectsIso e.inv, ← Category.assoc]
      refine .comp _ (ih _ _ _ _ (.flip (.of_hasPullback _ _))) _
        (K.pullbackArrows_mem (pullback.snd _ _) hR) _ ?_
      simpa [e, u] using .mk _ _ hg'
    | of_presieve f R hR h ih =>
      refine .of_presieve _ _ (K.pullbackArrows_mem fst hR) ?_
      intro U v ⟨Z, u, hu⟩
      exact ih _ _ hu _ g (pullback.fst _ _) _ (.paste_vert (.of_hasPullback _ _) h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.sourceLocalClosure.sourceLocalClosure_iff_of_r
espectsLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.sourceLoc
alClosure`。
形式化陈述：sourceLocalClosure_iff_of_respectsLeft [P.RespectsIso] [P.RespectsLeft K.m
orphismProperty] [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposi
tion] [K.HasPullbacks] {X Y : C} {f : X ⟶ Y} : sourceLocalClosure K P f ↔ exists
 R in K X, forall (U : C) (g : U ⟶ X), R g -> P (g ≫ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.mem_coverings_of_isIso`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {J : CategoryTheory.Precoverage C} [self : J
.HasIsos] {S T : C}   (f : S ⟶ T) [Cate…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover`：mem_iff_exists
_zeroHypercover {X : C} {R : Presieve X} : R in J X ↔ exists (𝒰 : ZeroHypercover
.{max u v} J X), R = Presieve.ofArrows 𝒰.X 𝒰.f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.precomp`：∀ {C : Type u} {in
st : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPrope
rty C}   [self : P.RespectsLeft Q] {X Y Z …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.morphismProperty`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {K : CategoryTheory.Precovera
ge C} {X : C}   {E : K.ZeroHypercover X} (i : E.…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (E
 : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma sourceLocalClosure_iff_of_respectsLeft [P.RespectsIso] [P.RespectsLeft K.morphismProperty]
    [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition] [K.HasPullbacks] {X Y : C}
    {f : X ⟶ Y} :
    sourceLocalClosure K P f ↔ ∃ R ∈ K X, ∀ (U : C) (g : U ⟶ X), R g → P (g ≫ f) := by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | of f hf => exact ⟨.singleton (𝟙 _), K.mem_coverings_of_isIso _, fun U g ⟨⟩ ↦ by simpa⟩
    | of_iso f g e hf h =>
      obtain ⟨R, hR, h⟩ := h
      rw [K.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      refine ⟨_, (E.pushforward e.hom.left (K.mem_coverings_of_isIso _)).mem₀, ?_⟩
      intro U v ⟨i⟩
      dsimp
      simp only [Category.assoc, Arrow.w_mk_right, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
      rw [← Category.assoc, P.cancel_right_of_respectsIso]
      exact h _ _ ⟨i⟩
    | comp f hf R hR g hg ih =>
      obtain ⟨S, hS, h⟩ := ih
      rw [K.mem_iff_exists_zeroHypercover] at hS hR
      obtain ⟨E, rfl⟩ := hS
      obtain ⟨F, rfl⟩ := hR
      refine ⟨(E.pullback₁ g).presieve₀, (E.pullback₁ g).mem₀, ?_⟩
      intro U v ⟨i⟩
      dsimp
      rw [pullback.condition_assoc]
      refine RespectsLeft.precomp (Q := K.morphismProperty) _ ?_ _ ?_
      · obtain ⟨j⟩ := hg
        exact (F.pullback₂ (E.f i)).morphismProperty j
      · exact h _ _ ⟨i⟩
    | of_presieve f R hR h ih =>
      rw [K.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      choose S hS h' using fun i : E.I₀ ↦ ih _ _ ⟨i⟩
      simp_rw [K.mem_iff_exists_zeroHypercover] at hS
      choose F hF using hS
      refine ⟨_, (E.bind F).mem₀, fun U g ⟨j⟩ ↦ ?_⟩
      dsimp
      rw [Category.assoc]
      exact h' _ _ _ (by simp [hF])
  · intro ⟨R, hR, h⟩
    exact .of_presieve _ _ hR (by grind)

end sourceLocalClosure

end CategoryTheory.MorphismProperty

