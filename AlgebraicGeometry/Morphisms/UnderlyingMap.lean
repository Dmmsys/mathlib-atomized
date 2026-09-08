/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.LocalAtTarget
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors

/-!
# Properties on the underlying functions of morphisms of schemes

This file includes various results on properties of morphisms of schemes that come from properties
of the underlying map of topological spaces, including

- `Injective`
- `Surjective`
- `IsOpenMap`
- `IsClosedMap`
- `GeneralizingMap`
- `IsEmbedding`
- `IsOpenEmbedding`
- `IsClosedEmbedding`
- `DenseRange` (`IsDominant`)

-/

@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u v

section Injective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.RespectsIso (topologically Function.Injective) :=
  topologically_respectsIso _ (fun e ↦ e.injective) (fun _ _ hf hg ↦ hg.comp hf)
/-
**AlgebraicGeometry.injective_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：injective_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically F
unction.Injective)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget`：topologically_is
ZariskiLocalAtTarget [(topologically P).RespectsIso] (hP₂ : forall {α β : Type u
} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyInjective`：(Algebrai
cGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace β] => F
unction.Injective).RespectsIso
· 使用定理 `Function.Injective.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} (t 
: Set β) {f : α → β},   Function.Injective f → Function.Injective (t.restrictPre
image f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
instance injective_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically Function.Injective) := by
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h ↦ h.restrictPreimage s)
    fun f ι U H _ hf x₁ x₂ e ↦ ?_
  obtain ⟨i, hxi⟩ : ∃ i, f x₁ ∈ U i := by simpa using congr(f x₁ ∈ $H)
  exact congr(($(@hf i ⟨x₁, hxi⟩ ⟨x₂, show f x₂ ∈ U i from e ▸ hxi⟩ (Subtype.ext e))).1)

end Injective

section Surjective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is surjective if the underlying map is. -/
@[mk_iff]
/-
**AlgebraicGeometry.Surjective** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes is surjective if the underlying map is.
-/
class Surjective : Prop where
  surj : Function.Surjective f
/-
**AlgebraicGeometry.surjective_eq_topologically** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：surjective_eq_topologically : @Surjective = topologically Function.Surject
ive
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.surjective_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.Surjective f ↔ Function.Surjective ⇑f
-/
lemma surjective_eq_topologically :
    @Surjective = topologically Function.Surjective := by ext; exact surjective_iff _

@[grind .]
/-
**AlgebraicGeometry.Scheme.Hom.surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Surjecti
ve f], Function.Surjective ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Surjective.surj`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 : X ⟶ Y} [self : AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
-/
lemma Scheme.Hom.surjective (f : X ⟶ Y) [Surjective f] : Function.Surjective f :=
  Surjective.surj
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsIso f] : Surjective f := ⟨f.homeomorph.surjective⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Surjective f] [Surjective g] : Surjective (f ≫ g) := ⟨g.surjective.comp f.surjective⟩
/-
**AlgebraicGeometry.Surjective.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Surjective`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.Surjective (CategoryTheory.CategoryStruct.comp f g)], AlgebraicGeometry.
Surjective g
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.surjective`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
-/
lemma Surjective.of_comp [Surjective (f ≫ g)] : Surjective g where
  surj := Function.Surjective.of_comp (g := f) (f ≫ g).surjective
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Nonempty X] [Subsingleton Y] (f : X ⟶ Y) :
    Surjective f := ⟨Function.surjective_to_subsingleton _⟩
/-
**AlgebraicGeometry.Surjective.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Surjective`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeo
metry.Surjective f],   AlgebraicGeometry.Surjective (CategoryTheory.CategoryStru
ct.comp f g) ↔ AlgebraicGeometry.Surjective g
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Surjective.of_comp`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.Surjective (CategoryTheory.Categ
oryStruct.comp f g)], Alge…
· 使用定理 `AlgebraicGeometry.instSurjectiveCompScheme`：∀ {X Y Z : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.Surjective f]   [AlgebraicGe
ometry.Surjective g], AlgebraicG…
-/
lemma Surjective.comp_iff [Surjective f] : Surjective (f ≫ g) ↔ Surjective g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @Surjective.{u} where
  id_mem _ := inferInstance
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.RespectsIso @Surjective :=
  surjective_eq_topologically ▸ topologically_respectsIso _ (fun e ↦ e.surjective)
    (fun _ _ hf hg ↦ hg.comp hf)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty Scheme.{u}) :
    MorphismProperty.HasOfPrecompProperty @Surjective P where
  of_precomp f g _ _ := .of_comp f g
/-
**AlgebraicGeometry.surjective_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：surjective_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @Surjective
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeSurjective`：CategoryTheory.Morphi
smProperty.RespectsIso @AlgebraicGeometry.Surjective
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.surjective_eq_topologically`：surjective_eq_topological
ly : @Surjective = topologically Function.Surjective
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget`：topologically_is
ZariskiLocalAtTarget [(topologically P).RespectsIso] (hP₂ : forall {α β : Type u
} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `Function.Surjective.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} (t
 : Set β) {f : α → β},   Function.Surjective f → Function.Surjective (t.restrict
Preimage f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
instance surjective_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @Surjective := by
  have : MorphismProperty.RespectsIso @Surjective := inferInstance
  rw [surjective_eq_topologically] at this ⊢
  refine topologically_isZariskiLocalAtTarget _ (fun _ s _ _ h ↦ h.restrictPreimage s) ?_
  intro α β _ _ f ι U H _ hf x
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by simpa using congr(x ∈ $H)
  obtain ⟨⟨y, _⟩, hy⟩ := hf i ⟨x, hxi⟩
  exact ⟨y, congr(($hy).1)⟩

@[simp]
/-
**AlgebraicGeometry.range_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：range_eq_univ [Surjective f] : Set.range f = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.surjective`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
-/
lemma range_eq_univ [Surjective f] : Set.range f = Set.univ := by
  simpa [Set.range_eq_univ] using f.surjective
/-
**AlgebraicGeometry.range_eq_range_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：range_eq_range_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e :
 X ⟶ Y) [Surjective e] (hge : e ≫ g = f) : Set.range f = Set.range g
参数：f : X ⟶ S；g : Y ⟶ S；e : X ⟶ Y；hge : e ≫ g = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `AlgebraicGeometry.range_eq_univ`：range_eq_univ [Surjective f] : Set.rang
e f = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_eq_range_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
    [Surjective e] (hge : e ≫ g = f) : Set.range f = Set.range g := by
  rw [← hge]
  simp [Set.range_comp]
/-
**AlgebraicGeometry.mem_range_iff_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：mem_range_iff_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : 
X ⟶ Y) [Surjective e] (hge : e ≫ g = f) (s : S) : s in Set.range f ↔ s in Set.ra
nge g
参数：f : X ⟶ S；g : Y ⟶ S；e : X ⟶ Y；hge : e ≫ g = f；s : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.range_eq_range_of_surjective`：range_eq_range_of_surjec
tive {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y) [Surjective e] (hge : 
e ≫ g = f) : Set.range f = Set.range…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_range_iff_of_surjective {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (e : X ⟶ Y)
    [Surjective e] (hge : e ≫ g = f) (s : S) : s ∈ Set.range f ↔ s ∈ Set.range g := by
  rw [range_eq_range_of_surjective f g e hge]
/-
**AlgebraicGeometry.Surjective.sigmaDesc_of_union_range_eq_univ** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.Surjective`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {ι : Type v} [inst : Small.{u, v} ι] {Y :
 ι → AlgebraicGeometry.Scheme}   {f : (i : ι) → Y i ⟶ X},   ⋃ i, Set.range ⇑(f i
) = Set.univ → AlgebraicGeometry.Surjective (CategoryTheory.Limits.Sigma.desc f)
参数：i : ι；f i；CategoryTheory.Limits.Sigma.desc f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.Limits.Sigma.ι_desc`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {β : Type w} {f : β → C}   [inst_1 : CategoryTheory.Limits.
HasCoproduct f] {P : C} …
-/
lemma Surjective.sigmaDesc_of_union_range_eq_univ {X : Scheme.{u}}
    {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    (H : ⋃ i, Set.range (f i) = Set.univ) : Surjective (Limits.Sigma.desc f) := by
  refine ⟨fun x ↦ ?_⟩
  simp_rw [Set.eq_univ_iff_forall, Set.mem_iUnion] at H
  obtain ⟨i, x, rfl⟩ := H x
  use Limits.Sigma.ι Y i x
  rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} {P : MorphismProperty Scheme.{u}} (𝒰 : X.Cover (Scheme.precoverage P)) :
    Surjective (Limits.Sigma.desc fun i ↦ 𝒰.f i) :=
  Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range

/-- The single object covering by one surjective morphism satisfying `P`. -/
@[simps! I₀ X f]
/-
**AlgebraicGeometry.Scheme.Hom.cover** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {X S : 
AlgebraicGeometry.Scheme} →     (f : X ⟶ S) →       P f → [AlgebraicGeometry.Sur
jective f] → AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverag
e P) S
参数：f : X ⟶ S；AlgebraicGeometry.Scheme.precoverage P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The single object covering by one surjective morphism satisfying `P`.
-/
def Scheme.Hom.cover {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
    [Surjective f] : Cover.{v} (precoverage P) S :=
  .singleton f <| by
    rw [singleton_mem_precoverage_iff]
    exact ⟨f.surjective, hf⟩

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.presieve** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.presieve₀_cover {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : P f) [Surjective f] : (f.cover hf).presieve₀ = Presieve.singleton f := by
  simp [cover]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f)
    [Surjective f] : Unique (Scheme.Hom.cover f hf).I₀ :=
  inferInstanceAs <| Unique PUnit

end Surjective

section Injective

/-
**AlgebraicGeometry.injective_isStableUnderComposition** 是 Mathlib 中的一个实例，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：injective_isStableUnderComposition : MorphismProperty.IsStableUnderComposi
tion (topologically (Function.Injective ·)) where comp_mem _ _ hf hg
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
-/
instance injective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (topologically (Function.Injective ·)) where
  comp_mem _ _ hf hg := hg.comp hf

end Injective

section IsOpenMap

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (topologically IsOpenMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenMap) (fun _ _ hf hg ↦ hg.comp hf)
/-
**AlgebraicGeometry.isOpenMap_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：isOpenMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically I
sOpenMap)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget'`：topologically_i
sZariskiLocalAtTarget' [(topologically P).RespectsIso] (hP : forall {α β : Type 
u} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyIsOpenMap`：(Algebrai
cGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace β] => I
sOpenMap).RespectsIso
· 使用定理 `TopologicalSpace.IsOpenCover.isOpenMap_iff_restrictPreimage`：isOpenMap_i
ff_restrictPreimage : IsOpenMap f ↔ forall i, IsOpenMap ((U i).1.restrictPreimag
e f)
-/
instance isOpenMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ ↦ hU.isOpenMap_iff_restrictPreimage
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtSource (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.isOpenMap_iff_comp

end IsOpenMap

section IsClosedMap

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (topologically IsClosedMap).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedMap) (fun _ _ hf hg ↦ hg.comp hf)
/-
**AlgebraicGeometry.isClosedMap_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：isClosedMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically
 IsClosedMap)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget'`：topologically_i
sZariskiLocalAtTarget' [(topologically P).RespectsIso] (hP : forall {α β : Type 
u} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyIsClosedMap`：(Algebr
aicGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace β] =>
 IsClosedMap).RespectsIso
· 使用定理 `TopologicalSpace.IsOpenCover.isClosedMap_iff_restrictPreimage`：isClosedM
ap_iff_restrictPreimage : IsClosedMap f ↔ forall i, IsClosedMap ((U i).1.restric
tPreimage f)
-/
instance isClosedMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsClosedMap) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU _ ↦ hU.isClosedMap_iff_restrictPreimage

end IsClosedMap

section IsEmbedding

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (topologically IsEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isEmbedding) (fun _ _ hf hg ↦ hg.comp hf)
/-
**AlgebraicGeometry.isEmbedding_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：isEmbedding_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically
 IsEmbedding)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget'`：topologically_i
sZariskiLocalAtTarget' [(topologically P).RespectsIso] (hP : forall {α β : Type 
u} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyIsEmbedding`：(Algebr
aicGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace β] =>
     Topology.IsEmbedding).RespectsIso
· 使用定理 `TopologicalSpace.IsOpenCover.isEmbedding_iff_restrictPreimage`：isEmbeddi
ng_iff_restrictPreimage (h : Continuous f) : IsEmbedding f ↔ forall i, IsEmbeddi
ng ((U i).1.restrictPreimage f)
-/
instance isEmbedding_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologically IsEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isEmbedding_iff_restrictPreimage

end IsEmbedding

section IsOpenEmbedding

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (topologically IsOpenEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isOpenEmbedding) (fun _ _ hf hg ↦ hg.comp hf)
/-
**AlgebraicGeometry.isOpenEmbedding_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：isOpenEmbedding_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologic
ally IsOpenEmbedding)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget'`：topologically_i
sZariskiLocalAtTarget' [(topologically P).RespectsIso] (hP : forall {α β : Type 
u} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyIsOpenEmbedding`：(Al
gebraicGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace β
] =>     Topology.IsOpenEmbedding).RespectsIso
· 使用定理 `TopologicalSpace.IsOpenCover.isOpenEmbedding_iff_restrictPreimage`：isOpe
nEmbedding_iff_restrictPreimage (h : Continuous f) : IsOpenEmbedding f ↔ forall 
i, IsOpenEmbedding ((U i).1.restrictPreimage f)
-/
instance isOpenEmbedding_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically IsOpenEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isOpenEmbedding_iff_restrictPreimage

end IsOpenEmbedding

section IsClosedEmbedding

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (topologically IsClosedEmbedding).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isClosedEmbedding) (fun _ _ hf hg ↦ hg.comp hf)
/-
**AlgebraicGeometry.isClosedEmbedding_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，
位于命名空间 `AlgebraicGeometry`。
形式化陈述：isClosedEmbedding_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topolog
ically IsClosedEmbedding)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget'`：topologically_i
sZariskiLocalAtTarget' [(topologically P).RespectsIso] (hP : forall {α β : Type 
u} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyIsClosedEmbedding`：(
AlgebraicGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace
 β] =>     Topology.IsClosedEmbedding).RespectsIso
· 使用定理 `TopologicalSpace.IsOpenCover.isClosedEmbedding_iff_restrictPreimage`：isC
losedEmbedding_iff_restrictPreimage (h : Continuous f) : IsClosedEmbedding f ↔ f
orall i, IsClosedEmbedding ((U i).1.restrictPreimage f)
-/
instance isClosedEmbedding_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically IsClosedEmbedding) :=
  topologically_isZariskiLocalAtTarget' _ fun _ _ _ hU ↦ hU.isClosedEmbedding_iff_restrictPreimage

end IsClosedEmbedding

section IsDominant

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is dominant if the underlying map has dense range. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsDominant** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes is dominant if the underlying map has dense range.
-/
class IsDominant : Prop where
  denseRange : DenseRange f
/-
**AlgebraicGeometry.dominant_eq_topologically** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：dominant_eq_topologically : @IsDominant = topologically DenseRange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.isDominant_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.IsDominant f ↔ DenseRange ⇑f
-/
lemma dominant_eq_topologically :
    @IsDominant = topologically DenseRange := by ext; exact isDominant_iff _
/-
**AlgebraicGeometry.Scheme.Hom.denseRange** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsDomina
nt f], DenseRange ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsDominant.denseRange`：∀ {X Y : AlgebraicGeometry.Sche
me} {f : X ⟶ Y} [self : AlgebraicGeometry.IsDominant f], DenseRange ⇑f
-/
lemma Scheme.Hom.denseRange (f : X ⟶ Y) [IsDominant f] : DenseRange f :=
  IsDominant.denseRange
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Surjective f] : IsDominant f := ⟨f.surjective.denseRange⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDominant f] [IsDominant g] : IsDominant (f ≫ g) :=
  ⟨g.denseRange.comp f.denseRange g.continuous⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @IsDominant where
  id_mem := fun _ ↦ inferInstance
  comp_mem := fun _ _ _ _ ↦ inferInstance
/-
**AlgebraicGeometry.IsDominant.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.IsDominant`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [H : Algebr
aicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp f g)], AlgebraicGeome
try.IsDominant g
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isDominant_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.IsDominant f ↔ DenseRange ⇑f
· 使用定理 `denseRange_iff_closure_range`：denseRange_iff_closure_range : DenseRange 
f ↔ closure (range f) = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
lemma IsDominant.of_comp [H : IsDominant (f ≫ g)] : IsDominant g := by
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff] at H ⊢
  exact H.trans (closure_mono (Set.range_comp_subset_range f g))
/-
**AlgebraicGeometry.IsDominant.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.IsDominant`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeo
metry.IsDominant f],   AlgebraicGeometry.IsDominant (CategoryTheory.CategoryStru
ct.comp f g) ↔ AlgebraicGeometry.IsDominant g
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsDominant.of_comp`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) (g : Y ⟶ Z)   [H : AlgebraicGeometry.IsDominant (CategoryTheory.C
ategoryStruct.comp f g)], …
· 使用定理 `AlgebraicGeometry.instIsDominantCompScheme`：∀ {X Y Z : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsDominant f]   [AlgebraicGe
ometry.IsDominant g], AlgebraicG…
-/
lemma IsDominant.comp_iff [IsDominant f] : IsDominant (f ≫ g) ↔ IsDominant g :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsDominant.respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.IsDominant`。
形式化陈述：CategoryTheory.MorphismProperty.RespectsIso @AlgebraicGeometry.IsDominant
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition`
：respectsIso_of_isStableUnderComposition {P : MorphismProperty C} [P.IsStableUnd
erComposition] (hP : isomorphisms C <= P) : RespectsIso P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.instIsMultiplicativeSchemeIsDominant`：CategoryTheory.M
orphismProperty.IsMultiplicative @AlgebraicGeometry.IsDominant
· 使用定理 `AlgebraicGeometry.instIsDominantOfSurjective`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], AlgebraicGeometry.IsDomin
ant f
· 使用定理 `AlgebraicGeometry.instSurjectiveOfIsIsoScheme`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.Surjective f
-/
instance IsDominant.respectsIso : MorphismProperty.RespectsIso @IsDominant :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦ inferInstance
/-
**AlgebraicGeometry.IsDominant.isZariskiLocalAtTarget** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.IsDominant`。
形式化陈述：AlgebraicGeometry.IsZariskiLocalAtTarget @AlgebraicGeometry.IsDominant
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsDominant.respectsIso`：CategoryTheory.MorphismPropert
y.RespectsIso @AlgebraicGeometry.IsDominant
· 使用引理 `AlgebraicGeometry.dominant_eq_topologically`：dominant_eq_topologically :
 @IsDominant = topologically DenseRange
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget'`：topologically_i
sZariskiLocalAtTarget' [(topologically P).RespectsIso] (hP : forall {α β : Type 
u} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `TopologicalSpace.IsOpenCover.denseRange_iff_restrictPreimage`：denseRange
_iff_restrictPreimage : DenseRange f ↔ forall i, DenseRange ((U i).1.restrictPre
image f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance IsDominant.isZariskiLocalAtTarget : IsZariskiLocalAtTarget @IsDominant :=
  have : MorphismProperty.RespectsIso (topologically DenseRange) :=
    dominant_eq_topologically ▸ IsDominant.respectsIso
  dominant_eq_topologically ▸ topologically_isZariskiLocalAtTarget' DenseRange
    fun _ _ _ hU _ ↦ hU.denseRange_iff_restrictPreimage
/-
**AlgebraicGeometry.surjective_of_isDominant_of_isClosed_range** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：surjective_of_isDominant_of_isClosed_range (f : X ⟶ Y) [IsDominant f] (hf 
: IsClosed (Set.range f)) : Surjective f
参数：f : X ⟶ Y；hf : IsClosed (Set.range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `DenseRange.closure_range`：DenseRange.closure_range (h : DenseRange f) : 
closure (range f) = univ
· 使用定理 `AlgebraicGeometry.Scheme.Hom.denseRange`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.IsDominant f], DenseRange ⇑f
-/
lemma surjective_of_isDominant_of_isClosed_range (f : X ⟶ Y) [IsDominant f]
    (hf : IsClosed (Set.range f)) :
    Surjective f :=
  ⟨by rw [← Set.range_eq_univ, ← hf.closure_eq, f.denseRange.closure_range]⟩
/-
**AlgebraicGeometry.IsDominant.of_comp_of_isOpenImmersion** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.IsDominant`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [H : Algebr
aicGeometry.IsDominant (CategoryTheory.CategoryStruct.comp f g)] [AlgebraicGeome
try.IsOpenImmersion g],   AlgebraicGeometry.IsDominant f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isDominant_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.IsDominant f ↔ DenseRange ⇑f
· 使用定理 `DenseRange.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] {α : Type u_
1} (f : α → X), DenseRange f = Dense (Set.range f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `Dense.preimage`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] {s : Set Y},   Dense s → IsOpenMap
 f →…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
-/
lemma IsDominant.of_comp_of_isOpenImmersion
    (f : X ⟶ Y) (g : Y ⟶ Z) [H : IsDominant (f ≫ g)] [IsOpenImmersion g] :
    IsDominant f := by
  rw [isDominant_iff, DenseRange] at H ⊢
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at H
  convert H.preimage g.isOpenEmbedding.isOpenMap
  rw [Set.preimage_image_eq _ g.isOpenEmbedding.injective]
/-
**AlgebraicGeometry.Opens.isDominant_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Opens.isDominant_ι {U : X.Opens} (hU : Dense (X := X) U) : IsDominant U.ι :=
  ⟨by simpa [DenseRange] using hU⟩
/-
**AlgebraicGeometry.Opens.isDominant_homOfLE** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Opens`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens},   Dense ↑U → ∀ (hU' : U 
≤ V), AlgebraicGeometry.IsDominant (X.homOfLE hU')
参数：hU' : U ≤ V；X.homOfLE hU'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.Opens.isDominant_ι`：∀ {X : AlgebraicGeometry.Scheme} {
U : X.Opens}, Dense ↑U → AlgebraicGeometry.IsDominant U.ι
· 使用定理 `AlgebraicGeometry.IsDominant.of_comp_of_isOpenImmersion`：∀ {X Y Z : Alge
braicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [H : AlgebraicGeometry.IsDominan
t (CategoryTheory.CategoryStruct.comp f g)] […
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
-/
lemma Opens.isDominant_homOfLE {U V : X.Opens} (hU : Dense (X := X) U) (hU' : U ≤ V) :
    IsDominant (X.homOfLE hU') :=
  have : IsDominant (X.homOfLE hU' ≫ V.ι) := by simpa using Opens.isDominant_ι hU
  IsDominant.of_comp_of_isOpenImmersion (g := V.ι) _

end IsDominant

section SpecializingMap

open TopologicalSpace

/-
**AlgebraicGeometry.specializingMap_respectsIso** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：specializingMap_respectsIso : (topologically @SpecializingMap).RespectsIso
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_respectsIso`：topologically_respectsIso (
hP₁ : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ 
β), P f) (hP₂ : forall {α β γ : T…
· 使用引理 `IsClosedMap.specializingMap`：IsClosedMap.specializingMap (hf : IsClosedM
ap f) : SpecializingMap f
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
· 使用引理 `SpecializingMap.comp`：SpecializingMap.comp {f : X -> Y} {g : Y -> Z} (hf
 : SpecializingMap f) (hg : SpecializingMap g) : SpecializingMap (g ∘ f)
-/
instance specializingMap_respectsIso : (topologically @SpecializingMap).RespectsIso := by
  apply topologically_respectsIso
  · introv
    exact f.isClosedMap.specializingMap
  · introv hf hg
    exact hf.comp hg

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.specializingMap_isZariskiLocalAtTarget** 是 Mathlib 中的一个实例，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：specializingMap_isZariskiLocalAtTarget : IsZariskiLocalAtTarget (topologic
ally @SpecializingMap)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget`：topologically_is
ZariskiLocalAtTarget [(topologically P).RespectsIso] (hP₂ : forall {α β : Type u
} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `specializingMap_iff_closure_singleton_subset`：specializingMap_iff_closur
e_singleton_subset : SpecializingMap f ↔ forall x, closure {f x} subseteq f '' c
losure {x}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用引理 `TopologicalSpace.Opens.mem_top`：mem_top (x : α) : x in (⊤ : Opens α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsOpen.stableUnderGeneralization`：IsOpen.stableUnderGeneralization {s : 
Set X} (hs : IsOpen s) : StableUnderGeneralization s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `closure_subtype`：closure_subtype {x : { a // p a }} {s : Set { a // p a 
}} : x in closure s ↔ (x : X) in closure (((↑) : _ -> X) '' s)
· 使用定理 `Set.restrictPreimage_coe`：∀ {α : Type u} {β : Type v} (t : Set β) (f : α
 → β) (a : ↑(f ⁻¹' t)), ↑(t.restrictPreimage f a) = f ↑a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance specializingMap_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (topologically @SpecializingMap) := by
  apply topologically_isZariskiLocalAtTarget
  · introv _ _ hf
    rw [specializingMap_iff_closure_singleton_subset] at hf ⊢
    intro ⟨x, hx⟩ ⟨y, hy⟩ hcl
    simp only [closure_subtype, Set.restrictPreimage_mk, Set.image_singleton] at hcl
    obtain ⟨a, ha, hay⟩ := hf x hcl
    rw [← specializes_iff_mem_closure] at hcl
    exact ⟨⟨a, by simp [hay, hy]⟩, by simpa [closure_subtype], by simpa⟩
  · introv hU _ hsp
    simp_rw [specializingMap_iff_closure_singleton_subset] at hsp ⊢
    intro x y hy
    have : ∃ i, y ∈ U i := Opens.mem_iSup.mp (hU ▸ Opens.mem_top _)
    obtain ⟨i, hi⟩ := this
    rw [← specializes_iff_mem_closure] at hy
    have hfx : f x ∈ U i := (U i).2.stableUnderGeneralization hy hi
    have hy : (⟨y, hi⟩ : U i) ∈ closure {⟨f x, hfx⟩} := by
      simp only [closure_subtype, Set.image_singleton]
      rwa [← specializes_iff_mem_closure]
    obtain ⟨a, ha, hay⟩ := hsp i ⟨x, hfx⟩ hy
    rw [closure_subtype] at ha
    simp only [Opens.carrier_eq_coe, Set.image_singleton] at ha
    apply_fun Subtype.val at hay
    simp only [Opens.carrier_eq_coe, Set.restrictPreimage_coe] at hay
    use a.val, ha, hay

end SpecializingMap

section GeneralizingMap

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (topologically GeneralizingMap).RespectsIso :=
  topologically_respectsIso _ (fun f ↦ f.isOpenEmbedding.generalizingMap)
    (fun _ _ hf hg ↦ hf.comp hg)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtSource (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.generalizingMap_iff_comp
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtTarget' (fun _ ↦ _) fun _ _ _ hU _ ↦
    hU.generalizingMap_iff_restrictPreimage

end GeneralizingMap

end AlgebraicGeometry

