/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Localization.Bousfield

/-!
# Local epimorphisms with respect to an object property

Let `P` be an object property on a category `C`. We say that `f : X ⟶ Y`
is a local epimorphism wrt. `P` if `f` cancels on the left for morphisms with
codomain in `P`.

If `C` is the category of presheafs on some category with Grothendieck topology `J` and `P` the
property of being a sheaf for `J`, then being a local epimorphism wrt. `P` is being
an epimorphism after sheafification.

## Main declarations

- `CategoryTheory.ObjectProperty.localEpi`: The morphism property of local epimorphisms.
- `CategoryTheory.ObjectProperty.localEpi_mem_range_iff_epi`: If `F ⊣ G` and `G`
  is fully faithful, then `f : X ⟶ Y` is a local epimorphism if and only if `F.map f` is an
  epimorphism.

## References

The terminology is from [M. Kashiwara, P. Schapira, *Categories and Sheaves*, 16.1][Kashiwara2006].
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {P : ObjectProperty C}

namespace ObjectProperty

/-- A morphism `f` is a local epimorphism wrt. the object property `P`
if it satisfies left cancellation for morphisms with codomain in `P`. -/
/-
**CategoryTheory.ObjectProperty.localEpi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：localEpi (P : ObjectProperty C) : MorphismProperty C
参数：P : ObjectProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f` is a local epimorphism wrt. the object property `P`
if it satisfies left cancellation for morphisms with codomain in `P`.
-/
def localEpi (P : ObjectProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃Z⦄, P Z → Function.Injective fun (g : _ ⟶ Z) ↦ f ≫ g
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.localEpi.IsMultiplicative where
  id_mem X Z _ := by simpa using! Function.injective_id
  comp_mem f g hf hg T hT _ _ huv := hg hT (hf hT <| by simpa using huv)
/-
**CategoryTheory.ObjectProperty.localEpi.of_epi** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ObjectProperty.localEpi`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.ObjectProperty C} {X Y : C}   (f : X ⟶ Y) [CategoryTheory.Epi f], P.loc
alEpi f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
-/
lemma localEpi.of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : P.localEpi f := by
  intro Z hZ u v huv
  rwa [← cancel_epi f]

@[simp]
/-
**CategoryTheory.ObjectProperty.localEpi_top_apply_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：localEpi_top_apply_iff {X Y : C} {f : X ⟶ Y} : (⊤ : ObjectProperty C).loca
lEpi f ↔ Epi f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.ObjectProperty.localEpi.of_epi`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectProperty C} {X Y
 : C}   (f : X ⟶ Y) [CategoryTheory…
-/
lemma localEpi_top_apply_iff {X Y : C} {f : X ⟶ Y} :
    (⊤ : ObjectProperty C).localEpi f ↔ Epi f :=
  ⟨fun h ↦ ⟨fun _ _ huv ↦ h trivial huv⟩, fun _ ↦ .of_epi _⟩
/-
**CategoryTheory.ObjectProperty.localEpi_top_eq_epimorphisms** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：localEpi_top_eq_epimorphisms : (⊤ : ObjectProperty C).localEpi = .epimorph
isms C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma localEpi_top_eq_epimorphisms : (⊤ : ObjectProperty C).localEpi = .epimorphisms C := by
  ext
  simp
/-
**CategoryTheory.ObjectProperty.localEpi_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：localEpi_antitone : Antitone (localEpi (C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma localEpi_antitone : Antitone (localEpi (C := C)) :=
  fun _ _ hPQ _ _ _ hf _ hZ _ _ huv ↦ hf (hPQ _ hZ) huv
/-
**CategoryTheory.ObjectProperty.localEpi_isoClosure** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：localEpi_isoClosure : P.isoClosure.localEpi = P.localEpi
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ObjectProperty.localEpi_antitone`：localEpi_antitone : Ant
itone (localEpi (C
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma localEpi_isoClosure : P.isoClosure.localEpi = P.localEpi := by
  refine le_antisymm (localEpi_antitone <| le_isoClosure P) ?_
  intro X Y f hf Z ⟨T, hT, ⟨e⟩⟩ u v huv
  rw [← cancel_mono e.hom]
  apply hf hT
  simpa
/-
**CategoryTheory.ObjectProperty.isLocal_le_localEpi** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：isLocal_le_localEpi : P.isLocal <= P.localEpi
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
lemma isLocal_le_localEpi : P.isLocal ≤ P.localEpi :=
  fun _ _ _ hf Z hZ ↦ (hf Z hZ).injective
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.localEpi.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ _ ↦ .of_epi _
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : MorphismProperty C) : P.localEpi.HasOfPrecompProperty W where
  of_precomp {X Y Z} f g _ hfg T hT u v huv := hfg hT (by simp [huv])
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.localEpi.HasOfPostcompProperty P.isLocal where
  of_postcomp {X Y Z} f g hg hfg T hT u v huv := by
    obtain ⟨u, rfl⟩ := (hg _ hT).surjective u
    obtain ⟨v, rfl⟩ := (hg _ hT).surjective v
    simp [hfg hT (by simpa using huv)]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.localEpi.IsStableUnderCobaseChange := by
  refine .mk' fun X Y S f g _ hg T hT u v huv ↦ ?_
  refine pushout.hom_ext (hg hT ?_) huv
  simp [pushout.condition_assoc, huv]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.localEpi.Respects P.isLocal where
  precomp _ hf _ hg := MorphismProperty.comp_mem _ _ _ (isLocal_le_localEpi _ hf) hg
  postcomp _ hf _ hg := MorphismProperty.comp_mem _ _ _ hg (isLocal_le_localEpi _ hf)

variable {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [G.Faithful] [G.Full]
include adj

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.localEpi_mem_range_iff_epi** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：localEpi_mem_range_iff_epi {X Y : C} (f : X ⟶ Y) : localEpi (· in Set.rang
e G.obj) f ↔ Epi (F.map f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.postcomp_iff`：postcomp_iff [W.RespectsRi
ght W'] [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W
' g) : W (f ≫ g) ↔ W f
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.ObjectProperty.instRespectsLocalEpiIsLocal`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectProp
erty C},   P.localEpi.Respects P.isLocal
· 使用定理 `CategoryTheory.ObjectProperty.instHasOfPostcompPropertyLocalEpiIsLocal`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheo
ry.ObjectProperty C},   P.localEpi.HasOfPostcompProperty P.i…
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_adj_unit_app`：isLocal_adj_unit_app
 (X : D) : isLocal (· in Set.range F.obj) (adj.unit.app X)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.MorphismProperty.precomp_iff`：precomp_iff [W.RespectsLeft
 W'] [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
 : W (f ≫ g) ↔ W g
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.ObjectProperty.instHasOfPrecompPropertyLocalEpi`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.Objec
tProperty C}   (W : CategoryTheory.MorphismProperty …
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.map_injective_iff`：map_injective_iff (F : C ⥤ D) 
[Faithful F] {X Y : C} (f g : X ⟶ Y) : F.map f = F.map g ↔ f = g
-/
lemma localEpi_mem_range_iff_epi {X Y : C} (f : X ⟶ Y) :
    localEpi (· ∈ Set.range G.obj) f ↔ Epi (F.map f) := by
  rw [← dsimp% (localEpi (· ∈ Set.range G.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y),
    dsimp% adj.unit.naturality f,
    dsimp% (localEpi (· ∈ Set.range G.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X)]
  refine ⟨fun h ↦ ⟨fun {Z} u v huv ↦ ?_⟩, ?_⟩
  · refine G.map_injective ?_
    apply h ⟨Z, rfl⟩
    simp [← Functor.map_comp, huv]
  · rintro h _ ⟨Z, rfl⟩ u v huv
    obtain ⟨u, rfl⟩ := G.map_surjective u
    obtain ⟨v, rfl⟩ := G.map_surjective v
    simp only [← G.map_comp, G.map_injective_iff, cancel_epi] at huv
    rw [huv]
/-
**CategoryTheory.ObjectProperty.localEpi_mem_range_eq_inverseImage_epimorphisms*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：localEpi_mem_range_eq_inverseImage_epimorphisms : localEpi (· in Set.range
 G.obj) = (MorphismProperty.epimorphisms _).inverseImage F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.localEpi_mem_range_iff_epi`：localEpi_mem_r
ange_iff_epi {X Y : C} (f : X ⟶ Y) : localEpi (· in Set.range G.obj) f ↔ Epi (F.
map f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma localEpi_mem_range_eq_inverseImage_epimorphisms :
    localEpi (· ∈ Set.range G.obj) = (MorphismProperty.epimorphisms _).inverseImage F := by
  ext X Y f
  rw [localEpi_mem_range_iff_epi adj]
  simp
/-
**CategoryTheory.ObjectProperty.localEpi_essImage** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：localEpi_essImage : G.essImage.localEpi = (MorphismProperty.epimorphisms _
).inverseImage F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.isoClosure_eq_essImage`：isoClosure_eq_essImage : 
ObjectProperty.isoClosure (· in Set.range F.obj) = F.essImage
· 使用引理 `CategoryTheory.ObjectProperty.localEpi_isoClosure`：localEpi_isoClosure :
 P.isoClosure.localEpi = P.localEpi
· 使用引理 `CategoryTheory.ObjectProperty.localEpi_mem_range_eq_inverseImage_epimorp
hisms`：localEpi_mem_range_eq_inverseImage_epimorphisms : localEpi (· in Set.rang
e G.obj) = (MorphismProperty.epimorphisms _).inverseImage F
-/
lemma localEpi_essImage :
    G.essImage.localEpi = (MorphismProperty.epimorphisms _).inverseImage F := by
  rw [← Functor.isoClosure_eq_essImage, localEpi_isoClosure,
    localEpi_mem_range_eq_inverseImage_epimorphisms adj]

end ObjectProperty

end CategoryTheory

