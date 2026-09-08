/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
public import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPrecoherent
public import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Whiskering
/-!

# Categories of coherent sheaves

Given a fully faithful functor `F : C ⥤ D` into a precoherent category, which preserves and reflects
finite effective epi families, and satisfies the property `F.EffectivelyEnough` (meaning that to
every object in `C` there is an effective epi from an object in the image of `F`), the categories
of coherent sheaves on `C` and `D` are equivalent (see
`CategoryTheory.coherentTopology.equivalence`).

The main application of this equivalence is the characterisation of condensed sets as coherent
sheaves on either `CompHaus`, `Profinite` or `Stonean`. See the file
`Mathlib/Condensed/Equivalence.lean`.

We give the corresponding result for the regular topology as well (see
`CategoryTheory.regularTopology.equivalence`).
-/

@[expose] public section


universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Limits CategoryTheory.Functor regularTopology

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

namespace coherentTopology

variable [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [F.Full] [F.Faithful] [F.EffectivelyEnough] [Precoherent D]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.coherentTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.coh
erentTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.IsCoverDense (coherentTopology _) := by
  refine F.isCoverDense_of_generate_singleton_functor_π_mem _ fun B ↦ ⟨_, F.effectiveEpiOver B, ?_⟩
  apply Coverage.Saturate.of
  refine ⟨Unit, inferInstance, fun _ => F.effectiveEpiOverObj B,
    fun _ => F.effectiveEpiOver B, ?_, ?_⟩
  · funext; ext -- Do we want `Presieve.ext`?
    refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
    rintro ⟨⟩
    simp
  · rw [← effectiveEpi_iff_effectiveEpiFamily]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.coherentTopology.exists_effectiveEpiFamily_iff_mem_induced** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.coherentTopology`。
形式化陈述：exists_effectiveEpiFamily_iff_mem_induced (X : C) (S : Sieve X) : (exists 
(α : Type) (_ : Finite α) (Y : α -> C) (π : (a : α) -> (Y a ⟶ X)), EffectiveEpiF
amily Y π ∧ (forall a : α, (S.arrows) (π a))) ↔ (S in F.inducedTopology (coheren
tTopology _) X)
参数：X : C；S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense`：mem_indu
cedTopology_iff_of_isCoverDense [G.IsCoverDense K] {X : C} (S : Sieve X) : S in 
G.inducedTopology K X ↔ S.functorPushforward G in K …
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.coherentTopology.instIsCoverDense`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryT
heory.Precoherent C] {X : C}   (S : CategoryTheory.Sieve X…
· 使用定理 `CategoryTheory.Sieve.image_mem_functorPushforward`：image_mem_functorPush
forward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) : R.functorPushforward F (F.map 
f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.EffectivelyEnough.presentation`：∀ {C : Type u_1} 
{D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Categor
yTheory.Category.{v_2, u_2} D} {F : Categor…
· 使用定理 `CategoryTheory.Functor.instEffectiveEpiEffectiveEpiOver`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用引理 `CategoryTheory.Functor.finite_effectiveEpiFamily_of_map`：finite_effectiv
eEpiFamily_of_map (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F] {α : Type} 
[Finite α] {B : C} (X : α -> C) (π : (a : α) …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
-/
theorem exists_effectiveEpiFamily_iff_mem_induced (X : C) (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a))) ↔
    (S ∈ F.inducedTopology (coherentTopology _) X) := by
  refine ⟨fun ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · rw [mem_inducedTopology_iff_of_isCoverDense]
    apply (mem_sieves_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mpr
    refine ⟨α, inferInstance, fun i => F.obj (Y i),
      fun i => F.map (π i), ⟨?_,
      fun a => Sieve.image_mem_functorPushforward F S (H₂ a)⟩⟩
    exact F.map_finite_effectiveEpiFamily _ _
  · rw [mem_inducedTopology_iff_of_isCoverDense] at hS
    obtain ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩ := (mem_sieves_iff_hasEffectiveEpiFamily _).mp hS
    refine ⟨α, inferInstance, ?_⟩
    let Z : α → C := fun a ↦ (Functor.EffectivelyEnough.presentation (F := F) (Y a)).some.p
    let g₀ : (a : α) → F.obj (Z a) ⟶ Y a := fun a ↦ F.effectiveEpiOver (Y a)
    have : EffectiveEpiFamily _ (fun a ↦ g₀ a ≫ π a) := inferInstance
    refine ⟨Z, fun a ↦ F.preimage (g₀ a ≫ π a), ?_, fun a ↦ (?_ : S.arrows (F.preimage _))⟩
    · refine F.finite_effectiveEpiFamily_of_map _ _ ?_
      simpa using this
    · obtain ⟨W, g₁, g₂, h₁, h₂⟩ := H₂ a
      rw [h₂]
      convert! S.downward_closed h₁ (F.preimage (g₀ a ≫ g₂))
      exact F.map_injective (by simp)
/-
**CategoryTheory.coherentTopology.eq_induced** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.coherentTopology`。
形式化陈述：eq_induced : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.ext`：ext {J₁ J₂ : GrothendieckTopolo
gy C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂
· 使用定理 `CategoryTheory.Functor.reflects_precoherent`：∀ {C : Type u_1} {D : Type 
u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Ca
tegory.{v_2, u_2} D] (F : Categor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.coherentTopology.exists_effectiveEpiFamily_iff_mem_induce
d`：exists_effectiveEpiFamily_iff_mem_induced (X : C) (S : Sieve X) : (exists (α 
: Type) (_ : Finite α) (Y : α -> C) (π : (a : α) -> (Y a ⟶ X)),…
· 使用定理 `CategoryTheory.coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryT
heory.Precoherent C] {X : C}   (S : CategoryTheory.Sieve X…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_induced : haveI := F.reflects_precoherent
    coherentTopology C =
      F.inducedTopology (coherentTopology _) := by
  ext X S
  have := F.reflects_precoherent
  rw [← exists_effectiveEpiFamily_iff_mem_induced F X]
  rw [← coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily S]
/-
**CategoryTheory.coherentTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.coh
erentTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : haveI := F.reflects_precoherent;
    F.IsDenseSubsite (coherentTopology C) (coherentTopology D) where
  functorPushforward_mem_iff := by simp [eq_induced F]
/-
**CategoryTheory.coherentTopology.coverPreserving** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.coherentTopology`。
形式化陈述：coverPreserving : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.coverPreserving`：coverPreserving :
 CoverPreserving J K G
· 使用定理 `CategoryTheory.Functor.reflects_precoherent`：∀ {C : Type u_1} {D : Type 
u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Ca
tegory.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.coherentTopology.instIsDenseSubsite`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] (F : Categor…
-/
lemma coverPreserving : haveI := F.reflects_precoherent
    CoverPreserving (coherentTopology _) (coherentTopology _) F :=
  IsDenseSubsite.coverPreserving _ _ _

section SheafEquiv

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [F.Full] [F.Faithful]
  [Precoherent D]
  [F.EffectivelyEnough]

/--
The equivalence from coherent sheaves on `C` to coherent sheaves on `D`, given a fully faithful
functor `F : C ⥤ D` to a precoherent category, which preserves and reflects effective epimorphic
families, and satisfies `F.EffectivelyEnough`.
-/
noncomputable
/-
**CategoryTheory.coherentTopology.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.coherentTopology`。
形式化陈述：equivalence (A : Type u₃) [Category.{v₃} A] [forall X, HasLimitsOfShape (S
tructuredArrow X F.op) A] : haveI
参数：A : Type u₃；StructuredArrow X F.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.reflects_precoherent`：∀ {C : Type u_1} {D : Type 
u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Ca
tegory.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.coherentTopology.instIsDenseSubsite`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] (F : Categor…
-/
def equivalence (A : Type u₃) [Category.{v₃} A] [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsDenseSubsite.sheafEquiv _ _ F _

end SheafEquiv

section RegularExtensive

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.Full] [F.Faithful]
  [FinitaryExtensive D] [Preregular D]
  [FinitaryPreExtensive C]
  [PreservesFiniteCoproducts F]
  [F.EffectivelyEnough]

/--
The equivalence from coherent sheaves on `C` to coherent sheaves on `D`, given a fully faithful
functor `F : C ⥤ D` to an extensive preregular category, which preserves and reflects effective
epimorphisms and satisfies `F.EffectivelyEnough`.
-/
noncomputable
/-
**CategoryTheory.coherentTopology.equivalence'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.coherentTopology`。
形式化陈述：equivalence' (A : Type u₃) [Category.{v₃} A] [forall X, HasLimitsOfShape (
StructuredArrow X F.op) A] : haveI
参数：A : Type u₃；StructuredArrow X F.op。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivalence' (A : Type u₃) [Category.{v₃} A]
    [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A :=
  Functor.IsDenseSubsite.sheafEquiv _ _ F _

end RegularExtensive

end coherentTopology

namespace regularTopology

variable [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis] [F.Full] [F.Faithful]
  [F.EffectivelyEnough] [Preregular D]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.regularTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.regu
larTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.IsCoverDense (regularTopology _) := by
  refine F.isCoverDense_of_generate_singleton_functor_π_mem _ fun B ↦ ⟨_, F.effectiveEpiOver B, ?_⟩
  apply Coverage.Saturate.of
  refine ⟨F.effectiveEpiOverObj B, F.effectiveEpiOver B, ?_, inferInstance⟩
  funext; ext -- Do we want `Presieve.ext`?
  refine ⟨fun ⟨⟩ ↦ ⟨()⟩, ?_⟩
  rintro ⟨⟩
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.regularTopology.exists_effectiveEpi_iff_mem_induced** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：exists_effectiveEpi_iff_mem_induced (X : C) (S : Sieve X) : (exists (Y : C
) (π : Y ⟶ X), EffectiveEpi π ∧ S.arrows π) ↔ (S in F.inducedTopology (regularTo
pology _) X)
参数：X : C；S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense`：mem_indu
cedTopology_iff_of_isCoverDense [G.IsCoverDense K] {X : C} (S : Sieve X) : S in 
G.inducedTopology K X ↔ S.functorPushforward G in K …
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.regularTopology.instIsCoverDense`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.regularTopology.mem_sieves_iff_hasEffectiveEpi`：mem_sieve
s_iff_hasEffectiveEpi (S : Sieve X) : (S in (regularTopology C) X) ↔ exists (Y :
 C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π)
· 使用定理 `CategoryTheory.Sieve.image_mem_functorPushforward`：image_mem_functorPush
forward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) : R.functorPushforward F (F.map 
f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.EffectivelyEnough.presentation`：∀ {C : Type u_1} 
{D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Categor
yTheory.Category.{v_2, u_2} D} {F : Categor…
· 使用引理 `CategoryTheory.Functor.effectiveEpi_of_map`：effectiveEpi_of_map (F : C ⥤
 D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X ⟶ Y) (h : EffectiveEpi (F.map f))
 : EffectiveEpi f
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.regularTopology.instEffectiveEpiComp`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Preregular C] {X Y Y
' : C} (π : Y ⟶ X)   [CategoryTheory.Effe…
· 使用定理 `CategoryTheory.Functor.instEffectiveEpiEffectiveEpiOver`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
-/
theorem exists_effectiveEpi_iff_mem_induced (X : C) (S : Sieve X) :
    (∃ (Y : C) (π : Y ⟶ X),
      EffectiveEpi π ∧ S.arrows π) ↔
    (S ∈ F.inducedTopology (regularTopology _) X) := by
  refine ⟨fun ⟨Y, π, ⟨H₁, H₂⟩⟩ ↦ ?_, fun hS ↦ ?_⟩
  · rw [mem_inducedTopology_iff_of_isCoverDense]
    apply (mem_sieves_iff_hasEffectiveEpi (Sieve.functorPushforward _ S)).mpr
    refine ⟨F.obj Y, F.map π, ⟨?_, Sieve.image_mem_functorPushforward F S H₂⟩⟩
    exact F.map_effectiveEpi _
  · rw [mem_inducedTopology_iff_of_isCoverDense] at hS
    obtain ⟨Y, π, ⟨H₁, H₂⟩⟩ := (mem_sieves_iff_hasEffectiveEpi _).mp hS
    let g₀ := F.effectiveEpiOver Y
    refine ⟨_, F.preimage (g₀ ≫ π), ?_, (?_ : S.arrows (F.preimage _))⟩
    · refine F.effectiveEpi_of_map _ ?_
      simp only [map_preimage]
      infer_instance
    · obtain ⟨W, g₁, g₂, h₁, h₂⟩ := H₂
      rw [h₂]
      convert! S.downward_closed h₁ (F.preimage (g₀ ≫ g₂))
      exact F.map_injective (by simp)
/-
**CategoryTheory.regularTopology.eq_induced** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.regularTopology`。
形式化陈述：eq_induced : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.ext`：ext {J₁ J₂ : GrothendieckTopolo
gy C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂
· 使用定理 `CategoryTheory.Functor.reflects_preregular`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (F : Categor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.regularTopology.exists_effectiveEpi_iff_mem_induced`：exis
ts_effectiveEpi_iff_mem_induced (X : C) (S : Sieve X) : (exists (Y : C) (π : Y ⟶
 X), EffectiveEpi π ∧ S.arrows π) ↔ (S in F.inducedTopol…
· 使用定理 `CategoryTheory.regularTopology.mem_sieves_iff_hasEffectiveEpi`：mem_sieve
s_iff_hasEffectiveEpi (S : Sieve X) : (S in (regularTopology C) X) ↔ exists (Y :
 C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_induced : haveI := F.reflects_preregular
    regularTopology C =
      F.inducedTopology (regularTopology _) := by
  ext X S
  have := F.reflects_preregular
  rw [← exists_effectiveEpi_iff_mem_induced F X]
  rw [← mem_sieves_iff_hasEffectiveEpi S]
/-
**CategoryTheory.regularTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.regu
larTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : haveI := F.reflects_preregular;
    F.IsDenseSubsite (regularTopology C) (regularTopology D) where
  functorPushforward_mem_iff := by simp [eq_induced F]
/-
**CategoryTheory.regularTopology.coverPreserving** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.regularTopology`。
形式化陈述：coverPreserving : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.coverPreserving`：coverPreserving :
 CoverPreserving J K G
· 使用定理 `CategoryTheory.Functor.reflects_preregular`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.regularTopology.instIsDenseSubsite`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
-/
lemma coverPreserving : haveI := F.reflects_preregular
    CoverPreserving (regularTopology _) (regularTopology _) F :=
  IsDenseSubsite.coverPreserving _ _ _

section SheafEquiv

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  [F.Full] [F.Faithful]
  [Preregular D]
  [F.EffectivelyEnough]

/--
The equivalence from regular sheaves on `C` to regular sheaves on `D`, given a fully faithful
functor `F : C ⥤ D` to a preregular category, which preserves and reflects effective
epimorphisms and satisfies `F.EffectivelyEnough`.
-/
noncomputable
/-
**CategoryTheory.regularTopology.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.regularTopology`。
形式化陈述：equivalence (A : Type u₃) [Category.{v₃} A] [forall X, HasLimitsOfShape (S
tructuredArrow X F.op) A] : haveI
参数：A : Type u₃；StructuredArrow X F.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.reflects_preregular`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.regularTopology.instIsDenseSubsite`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
-/
def equivalence (A : Type u₃) [Category.{v₃} A] [∀ X, HasLimitsOfShape (StructuredArrow X F.op) A] :
    haveI := F.reflects_preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A :=
  Functor.IsDenseSubsite.sheafEquiv _ _ F _

end SheafEquiv

end regularTopology

namespace Presheaf

variable {A : Type u₃} [Category.{v₃} A] (F : Cᵒᵖ ⥤ A)

/-
**CategoryTheory.Presheaf.isSheaf_coherent_iff_regular_and_extensive** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_coherent_iff_regular_and_extensive [Preregular C] [FinitaryPreExte
nsive C] : IsSheaf (coherentTopology C) F ↔ IsSheaf (extensiveTopology C) F ∧ Is
Sheaf (regularTopology C) F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.extensive_regular_generate_coherent`：extensive_regular_ge
nerate_coherent [Preregular C] [FinitaryPreExtensive C] : ((extensiveCoverage C)
 ⊔ (regularCoverage C)).toGrothendieck =…
· 使用定理 `CategoryTheory.Presheaf.isSheaf_sup`：isSheaf_sup (K L : Coverage C) (P :
 Cᵒᵖ ⥤ D) : (IsSheaf (K ⊔ L).toGrothendieck) P ↔ (IsSheaf K.toGrothendieck) P ∧ 
(IsSheaf L.toGrothendieck…
-/
theorem isSheaf_coherent_iff_regular_and_extensive [Preregular C] [FinitaryPreExtensive C] :
    IsSheaf (coherentTopology C) F ↔
    IsSheaf (extensiveTopology C) F ∧ IsSheaf (regularTopology C) F := by
  rw [← extensive_regular_generate_coherent]
  exact isSheaf_sup (extensiveCoverage C) (regularCoverage C) F
/-
**CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondi
tion** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_iff_preservesFiniteProducts_and_equalizerCondition [Preregular C] 
[FinitaryExtensive C] [h : forall {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPul
lback f f] : IsSheaf (coherentTopology C) F ↔ PreservesFiniteProducts F ∧ Equali
zerCondition F
参数：f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_coherent_iff_regular_and_extensive`：isSh
eaf_coherent_iff_regular_and_extensive [Preregular C] [FinitaryPreExtensive C] :
 IsSheaf (coherentTopology C) F ↔ IsSheaf (extensiveTopo…
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_iff_isSheaf`：equalizer
Condition_iff_isSheaf (F : Cᵒᵖ ⥤ D) [Preregular C] [forall {Y X : C} (f : Y ⟶ X)
 [EffectiveEpi f], HasPullback f f] : EqualizerCond…
-/
theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] :
    IsSheaf (coherentTopology C) F ↔ PreservesFiniteProducts F ∧
      EqualizerCondition F := by
  rw [isSheaf_coherent_iff_regular_and_extensive]
  exact and_congr (isSheaf_iff_preservesFiniteProducts _)
    (@equalizerCondition_iff_isSheaf _ _ _ _ F _ h).symm
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Preregular C] [FinitaryExtensive C]
    (F : Sheaf (coherentTopology C) A) : PreservesFiniteProducts F.obj :=
  (Presheaf.isSheaf_iff_preservesFiniteProducts F.obj).1
    ((Presheaf.isSheaf_coherent_iff_regular_and_extensive F.obj).mp F.property).1
/-
**CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_of_projective** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_iff_preservesFiniteProducts_of_projective [Preregular C] [Finitary
Extensive C] [forall (X : C), Projective X] : IsSheaf (coherentTopology C) F ↔ P
reservesFiniteProducts F
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_coherent_iff_regular_and_extensive`：isSh
eaf_coherent_iff_regular_and_extensive [Preregular C] [FinitaryPreExtensive C] :
 IsSheaf (coherentTopology C) F ↔ IsSheaf (extensiveTopo…
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `CategoryTheory.regularTopology.isSheaf_of_projective`：isSheaf_of_project
ive (F : Cᵒᵖ ⥤ D) [Preregular C] [forall (X : C), Projective X] : Presheaf.IsShe
af (regularTopology C) F
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSheaf_iff_preservesFiniteProducts_of_projective [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X] :
    IsSheaf (coherentTopology C) F ↔ PreservesFiniteProducts F := by
  rw [isSheaf_coherent_iff_regular_and_extensive, and_iff_left (isSheaf_of_projective F),
    isSheaf_iff_preservesFiniteProducts]
/-
**CategoryTheory.Presheaf.isSheaf_iff_extensiveSheaf_of_projective** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_iff_extensiveSheaf_of_projective [Preregular C] [FinitaryExtensive
 C] [forall (X : C), Projective X] : IsSheaf (coherentTopology C) F ↔ IsSheaf (e
xtensiveTopology C) F
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_of_projectiv
e`：isSheaf_iff_preservesFiniteProducts_of_projective [Preregular C] [FinitaryExt
ensive C] [forall (X : C), Projective X] : IsSheaf (coherentTop…
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSheaf_iff_extensiveSheaf_of_projective [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X] :
    IsSheaf (coherentTopology C) F ↔ IsSheaf (extensiveTopology C) F := by
  rw [isSheaf_iff_preservesFiniteProducts_of_projective, isSheaf_iff_preservesFiniteProducts]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The categories of coherent sheaves and extensive sheaves on `C` are equivalent if `C` is
preregular, finitary extensive, and every object is projective.
-/
@[simps!]
/-
**CategoryTheory.Presheaf.coherentExtensiveEquivalence** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：coherentExtensiveEquivalence [Preregular C] [FinitaryExtensive C] [forall 
(X : C), Projective X] : Sheaf (coherentTopology C) A ≌ Sheaf (extensiveTopology
 C) A where functor
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C

--- 原说明 ---
The categories of coherent sheaves and extensive sheaves on `C` are equivalent i
f `C` is
preregular, finitary extensive, and every object is projective.
-/
def coherentExtensiveEquivalence [Preregular C] [FinitaryExtensive C] [∀ (X : C), Projective X] :
    Sheaf (coherentTopology C) A ≌ Sheaf (extensiveTopology C) A where
  functor :=
    ObjectProperty.lift _ (sheafToPresheaf _ _) (fun F ↦
      (isSheaf_iff_extensiveSheaf_of_projective F.obj).mp F.property)
  inverse :=
    ObjectProperty.lift _ (sheafToPresheaf _ _) (fun F ↦
      (isSheaf_iff_extensiveSheaf_of_projective F.obj).mpr F.property)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {B : Type u₄} [Category.{v₄} B]
variable (s : A ⥤ B)
/-
**CategoryTheory.Presheaf.isSheaf_coherent_of_hasPullbacks_comp** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_coherent_of_hasPullbacks_comp [Preregular C] [FinitaryExtensive C]
 [h : forall {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] [Preserves
FiniteLimits s] (hF : IsSheaf (coherentTopology C) F) : IsSheaf (coherentTopolog
y C) (F ⋙ s)
参数：f : Y ⟶ X；hF : IsSheaf (coherentTopology C) F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalize
rCondition`：isSheaf_iff_preservesFiniteProducts_and_equalizerCondition [Preregul
ar C] [FinitaryExtensive C] [h : forall {Y X : C} (f : Y ⟶ X) [Effective…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isSheaf_coherent_of_hasPullbacks_comp [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] [PreservesFiniteLimits s]
    (hF : IsSheaf (coherentTopology C) F) : IsSheaf (coherentTopology C) (F ⋙ s) := by
  rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition (h := h)] at hF ⊢
  have := hF.1
  refine ⟨inferInstance, fun _ _ π _ c hc ↦ ⟨?_⟩⟩
  exact isLimitForkMapOfIsLimit s _ (hF.2 π c hc).some
/-
**CategoryTheory.Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_coherent_of_hasPullbacks_of_comp [Preregular C] [FinitaryExtensive
 C] [h : forall {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] [Reflec
tsFiniteLimits s] (hF : IsSheaf (coherentTopology C) (F ⋙ s)) : IsSheaf (coheren
tTopology C) F
参数：f : Y ⟶ X；hF : IsSheaf (coherentTopology C) (F ⋙ s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalize
rCondition`：isSheaf_iff_preservesFiniteProducts_and_equalizerCondition [Preregul
ar C] [FinitaryExtensive C] [h : forall {Y X : C} (f : Y ⟶ X) [Effective…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op
-/
lemma isSheaf_coherent_of_hasPullbacks_of_comp [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f]
    [ReflectsFiniteLimits s]
    (hF : IsSheaf (coherentTopology C) (F ⋙ s)) : IsSheaf (coherentTopology C) F := by
  rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition (h := h)] at hF ⊢
  obtain ⟨_, hF₂⟩ := hF
  refine ⟨⟨fun n ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩, fun _ _ π _ c hc ↦ ⟨?_⟩⟩
  · exact ⟨isLimitOfReflects s (isLimitOfPreserves (F ⋙ s) hc)⟩
  · exact isLimitOfIsLimitForkMap s _ (hF₂ π c hc).some
/-
**CategoryTheory.Presheaf.isSheaf_coherent_of_projective_comp** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_coherent_of_projective_comp [Preregular C] [FinitaryExtensive C] [
forall (X : C), Projective X] [PreservesFiniteProducts s] (hF : IsSheaf (coheren
tTopology C) F) : IsSheaf (coherentTopology C) (F ⋙ s)
参数：X : C；hF : IsSheaf (coherentTopology C) F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_of_projectiv
e`：isSheaf_iff_preservesFiniteProducts_of_projective [Preregular C] [FinitaryExt
ensive C] [forall (X : C), Projective X] : IsSheaf (coherentTop…
-/
lemma isSheaf_coherent_of_projective_comp [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X] [PreservesFiniteProducts s]
    (hF : IsSheaf (coherentTopology C) F) : IsSheaf (coherentTopology C) (F ⋙ s) := by
  rw [isSheaf_iff_preservesFiniteProducts_of_projective] at hF ⊢
  infer_instance
/-
**CategoryTheory.Presheaf.isSheaf_coherent_of_projective_of_comp** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_coherent_of_projective_of_comp [Preregular C] [FinitaryExtensive C
] [forall (X : C), Projective X] [ReflectsFiniteProducts s] (hF : IsSheaf (coher
entTopology C) (F ⋙ s)) : IsSheaf (coherentTopology C) F
参数：X : C；hF : IsSheaf (coherentTopology C) (F ⋙ s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_of_projectiv
e`：isSheaf_iff_preservesFiniteProducts_of_projective [Preregular C] [FinitaryExt
ensive C] [forall (X : C), Projective X] : IsSheaf (coherentTop…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instReflectsLimitsOfShapeDiscreteOfReflectsFiniteP
roductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma isSheaf_coherent_of_projective_of_comp [Preregular C] [FinitaryExtensive C]
    [∀ (X : C), Projective X]
    [ReflectsFiniteProducts s]
    (hF : IsSheaf (coherentTopology C) (F ⋙ s)) : IsSheaf (coherentTopology C) F := by
  rw [isSheaf_iff_preservesFiniteProducts_of_projective] at hF ⊢
  exact ⟨fun n ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨isLimitOfReflects s (isLimitOfPreserves (F ⋙ s) hc)⟩⟩⟩⟩
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preregular C] [FinitaryExtensive C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f]
    [PreservesFiniteLimits s] : (coherentTopology C).HasSheafCompose s where
      isSheaf F hF := isSheaf_coherent_of_hasPullbacks_comp (h := h) F s hF
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preregular C] [FinitaryExtensive C] [∀ (X : C), Projective X]
    [PreservesFiniteProducts s] : (coherentTopology C).HasSheafCompose s where
  isSheaf F hF := isSheaf_coherent_of_projective_comp F s hF

end CategoryTheory.Presheaf

