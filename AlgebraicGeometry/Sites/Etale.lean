/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!

# The étale site

In this file we define the big étale site, i.e. the étale topology as a Grothendieck topology
on the category of schemes.

-/

@[expose] public section

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

/-- Big étale site: the étale precoverage on the category of schemes. -/
/-
**AlgebraicGeometry.Scheme.etalePrecoverage** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：etalePrecoverage : Precoverage Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Big étale site: the étale precoverage on the category of schemes.
-/
def etalePrecoverage : Precoverage Scheme.{u} :=
  precoverage @Etale

/-- Big étale site: the étale pretopology on the category of schemes. -/
/-
**AlgebraicGeometry.Scheme.etalePretopology** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：etalePretopology : Pretopology Scheme.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Etale.instIsMultiplicativeScheme`：CategoryTheory.Morph
ismProperty.IsMultiplicative @AlgebraicGeometry.Etale

--- 原说明 ---
Big étale site: the étale pretopology on the category of schemes.
-/
def etalePretopology : Pretopology Scheme.{u} :=
  pretopology @Etale

/-- Big étale site: the étale topology on the category of schemes. -/
/-
**AlgebraicGeometry.Scheme.etaleTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：etaleTopology : GrothendieckTopology Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Big étale site: the étale topology on the category of schemes.
-/
abbrev etaleTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology @Etale
/-
**AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：zariskiTopology_le_etaleTopology : zariskiTopology <= etaleTopology
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.grothendieckTopology_monotone`：grothendieckTopo
logy_monotone (hPQ : P <= Q) : grothendieckTopology P <= grothendieckTopology Q
· 使用定理 `AlgebraicGeometry.Etale.instOfIsOpenImmersion`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeometry.E
tale f
-/
lemma zariskiTopology_le_etaleTopology : zariskiTopology ≤ etaleTopology := by
  apply grothendieckTopology_monotone
  intro X Y f hf
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The small étale site of a scheme is the Grothendieck topology on the
category of schemes étale over `X` induced from the étale topology on `Scheme.{u}`. -/
/-
**AlgebraicGeometry.Scheme.smallEtaleTopology** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale
参数：X : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The small étale site of a scheme is the Grothendieck topology on the
category of schemes étale over `X` induced from the étale topology on `Scheme.{u
}`.
-/
def smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  X.smallGrothendieckTopology (P := @Etale)

set_option backward.isDefEq.respectTransparency.types false in
/-- The pretopology generating the small étale site. -/
/-
**AlgebraicGeometry.Scheme.smallEtalePretopology** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：smallEtalePretopology (X : Scheme.{u}) : Pretopology X.Etale
参数：X : Scheme.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Etale.instIsMultiplicativeScheme`：CategoryTheory.Morph
ismProperty.IsMultiplicative @AlgebraicGeometry.Etale
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme`：CategoryTheory.
MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.Etale @AlgebraicGeomet
ry.Etale

--- 原说明 ---
The pretopology generating the small étale site.
-/
def smallEtalePretopology (X : Scheme.{u}) : Pretopology X.Etale :=
  X.smallPretopology (Q := @Etale) (P := @Etale)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：ofArrows_mem_smallEtaleTopology_iff {X : Scheme.{u}} {W : X.Etale} {ι : Ty
pe*} {Z : ι -> X.Etale} (f : forall i, Z i ⟶ W) : Sieve.ofArrows _ f in smallEta
leTopology _ _ ↔ ⋃ i, Set.range (f i).left = .univ
参数：f : forall i, Z i ⟶ W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.Scheme.mem_smallGrothendieckTopology`：mem_smallGrothen
dieckTopology [P.HasOfPostcompProperty P] (X : P.Over ⊤ S) (R : Sieve X) : R in 
S.smallGrothendieckTopology P X ↔ exists (𝒰 …
· 使用定理 `AlgebraicGeometry.Etale.instIsMultiplicativeScheme`：CategoryTheory.Morph
ismProperty.IsMultiplicative @AlgebraicGeometry.Etale
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.Etale.instHasRingHomPropertyEtale`：AlgebraicGeometry.H
asRingHomProperty @AlgebraicGeometry.Etale fun {R S} [CommRing R] [CommRing S] =
> RingHom.Etale
· 使用定理 `AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme`：CategoryTheory.
MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.Etale @AlgebraicGeomet
ry.Etale
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff`：ofArrows_mem_prec
overage_iff {S : Scheme.{u}} {ι : Type*} {X : ι -> Scheme.{u}} {f : forall i, X 
i ⟶ S} : .ofArrows X f in precoverage P S ↔…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `AlgebraicGeometry.Scheme.instEtaleLeftDiscretePUnit`：∀ {X : AlgebraicGeo
metry.Scheme} {Z Y : X.Etale} (f : Z ⟶ Y), AlgebraicGeometry.Etale f.left
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma ofArrows_mem_smallEtaleTopology_iff
    {X : Scheme.{u}} {W : X.Etale} {ι : Type*}
    {Z : ι → X.Etale} (f : ∀ i, Z i ⟶ W) :
    Sieve.ofArrows _ f ∈ smallEtaleTopology _ _ ↔
      ⋃ i, Set.range (f i).left = .univ := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ (mem_smallGrothendieckTopology _ _).2 ?_⟩
  · obtain ⟨U, _, _, hU⟩ := (mem_smallGrothendieckTopology _ _).1 hf
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, ⟨u, rfl⟩⟩ := ((ofArrows_mem_precoverage_iff _).1 U.mem₀).1 y
    obtain ⟨_, b, _, ⟨j⟩, fac⟩ := hU _ _ ⟨i⟩
    replace fac : b.left ≫ (f j).left = U.f i :=
      (Etale.forget _ ⋙ CategoryTheory.Over.forget _).congr_map fac
    exact ⟨j, b.left u, by simp [← fac]⟩
  · have (w : W.left) : ∃ (i : ι), w ∈ Set.range (f i).left := by
      have := Set.mem_univ w
      simpa [← hf]
    choose i z hz using this
    let V : Cover (precoverage @Etale) W.left :=
      Cover.mkOfCovers W.left (fun w ↦ (Z (i w)).left)
        (fun w ↦ (f (i w)).left) (fun w ↦ ⟨_, _, hz w⟩) inferInstance
    let : Cover.Over X V :=
      { over w := ⟨(Z (i w)).hom⟩
        isOver_map w := by cat_disch }
    have (w : W.left) : Etale (V.X w ↘ X) := (Z (i w)).prop
    refine ⟨V, inferInstance, inferInstance, ?_⟩
    rintro _ _ ⟨w⟩
    refine ⟨_, 𝟙 _, _, ⟨i w⟩, by cat_disch⟩
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Scheme.{u}} (𝒰 : S.Cover (precoverage @Etale)) (i : 𝒰.I₀) : Etale (𝒰.f i) :=
  𝒰.map_prop i

set_option backward.isDefEq.respectTransparency false in
/-- A separably closed field `Ω` defines a point on the étale topology by the fiber
functor `X ↦ Hom(Spec Ω, X)`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.geometricFiber** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：geometricFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] : etaleTopology.Poin
t where fiber
参数：Ω : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def geometricFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] : etaleTopology.Point where
  fiber := coyoneda.obj ⟨Spec (.of Ω)⟩
  jointly_surjective {S} R hR (f : Spec (.of Ω) ⟶ S) := by
    obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective f
    rw [mem_grothendieckTopology_iff] at hR
    obtain ⟨𝒰, hle⟩ := hR
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    refine ⟨𝒰.X i, 𝒰.f i, hle _ _ ⟨i⟩, ?_⟩
    let k := (𝒰.X i).residueField y
    let m : S.residueField (𝒰.f i y) ⟶ (𝒰.X i).residueField y :=
      (𝒰.f i).residueFieldMap y
    algebraize [((𝒰.f i).residueFieldMap y).hom, a.hom]
    let b : (𝒰.X i).residueField y →ₐ[S.residueField (𝒰.f i y)] Ω :=
      IsSepClosed.lift
    have hfac : (𝒰.f i).residueFieldMap y ≫ CommRingCat.ofHom b.toRingHom = a := by
      ext1; exact b.comp_algebraMap
    use Spec.map (CommRingCat.ofHom b.toRingHom) ≫ (𝒰.X i).fromSpecResidueField y
    simp [SpecToEquivOfField, ← hfac]

end AlgebraicGeometry.Scheme

