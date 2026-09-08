/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import Mathlib.CategoryTheory.GuitartExact.HorizontalComposition

/-!
# Derivability structures deduced from localized equivalences

Assume that we have a diagram of localizer morphisms, in the
sense that we have an isomorphism `T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor`.
```
      T
 W₁  ---> W₂
 |        |
L|        |R
 v        v
 W₁' ---> W₂'
      B
```
In this file, we obtain the lemma
`LocalizerMorphism.isRightDerivabilityStructure_of_isLocalizedEquivalence` which shows
that if both `L` and `R` are localized equivalences (with `R.functor` essentially surjective),
then `B` is a right derivability structure when `T` is a right derivability structure,
the `2`-square above is Guitart exact (and `W₂'` respects isomorphisms).
In addition, if we require that `L.functor` is also essentially surjective,
that `R.functor` is full and that `W₂` is induced by `W₂'`, then
`B` is a right derivability structure iff `T` is.

The dual results for left derivability structures are also obtained.

This will be particularly useful when `L.functor` and `R.functor` are functors
from a category to a quotient category (e.g. functors from categories of homological
complexes to homotopy categories).

-/

@[expose] public section

namespace CategoryTheory

namespace LocalizerMorphism

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {W₁ : MorphismProperty C₁} {W₁' : MorphismProperty D₁}
  {W₂ : MorphismProperty C₂} {W₂' : MorphismProperty D₂}
  {T : LocalizerMorphism W₁ W₂} {L : LocalizerMorphism W₁ W₁'}
  {R : LocalizerMorphism W₂ W₂'} {B : LocalizerMorphism W₁' W₂'}

section

variable [W₂'.RespectsIso]
  [L.IsLocalizedEquivalence] [R.IsLocalizedEquivalence] [R.functor.EssSurj]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_isLocalizedEqu
ivalence** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLeftDerivabilityStructure_of_isLocalizedEquivalence [T.IsLeftDerivabilit
yStructure] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [TwoSquare.Gui
tartExact iso.inv] : B.IsLeftDerivabilityStructure
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftReso
lutions`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁
} C₁}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.LocalizerMorphism.map`：∀ {C₁ : Type u₁} {C₂ : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{
v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.hw`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.TwoSquare.hComp_app`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ 
: Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1
 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.CatCommSq.vComp_iso_inv_app`：∀ {C₁ : Type u_1} {C₂ : Type
 u_2} {C₃ : Type u_3} {C₄ : Type u_4} {C₅ : Type u_5} {C₆ : Type u_6}   [inst : 
CategoryTheory.Category.{v_1, u_…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.isLocalization`：
∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : CategoryTheory.Category.{
v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂]…
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff`：isLeft
DerivabilityStructure_iff [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
 Φ.IsLeftDerivabilityStructure ↔ TwoSquare.GuitartExac…
· 使用引理 `CategoryTheory.TwoSquare.GuitartExact.of_hComp`：of_hComp [B₁.EssSurj] [w
.GuitartExact] [(w ≫ₕ w').GuitartExact] : w'.GuitartExact
-/
lemma isLeftDerivabilityStructure_of_isLocalizedEquivalence
    [T.IsLeftDerivabilityStructure]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
    [TwoSquare.GuitartExact iso.inv] :
    B.IsLeftDerivabilityStructure := by
  have : B.HasLeftResolutions := fun Y₂ ↦ by
    obtain ⟨X₂, ⟨e₂⟩⟩ := Functor.EssSurj.mem_essImage R.functor Y₂
    have ρ : T.LeftResolution X₂ := Classical.arbitrary _
    exact ⟨{
      X₁ := L.functor.obj ρ.X₁
      w := iso.inv.app _ ≫ R.functor.map ρ.w ≫ e₂.hom
      hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk (iso.app _) e₂)).1 (R.map _ ρ.hw) }⟩
  let F := B.localizedFunctor W₁'.Q W₂'.Q
  let e' := CatCommSq.iso B.functor W₁'.Q W₂'.Q F
  let iso' : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  let : CatCommSq T.functor (L.functor ⋙ W₁'.Q) (R.functor ⋙ W₂'.Q) F :=
    CatCommSq.vComp (H₂ := B.functor) _ _ _ _ _ _
  have : (TwoSquare.hComp iso.inv e'.inv).GuitartExact := by
    convert!
      T.guitartExact_of_isLeftDerivabilityStructure' (L.functor ⋙ W₁'.Q) (R.functor ⋙ W₂'.Q) F
        (CatCommSq.iso _ _ _ _)
    ext
    simp [e', CatCommSq.iso, iso']
  rw [B.isLeftDerivabilityStructure_iff W₁'.Q W₂'.Q F e']
  apply TwoSquare.GuitartExact.of_hComp iso.inv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff_of_isLocalize
dEquivalence** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLeftDerivabilityStructure_iff_of_isLocalizedEquivalence [L.functor.EssSu
rj] [R.functor.Full] [R.IsInduced] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.
functor) [TwoSquare.GuitartExact iso.inv] : T.IsLeftDerivabilityStructure ↔ B.Is
LeftDerivabilityStructure
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_isLocali
zedEquivalence`：isLeftDerivabilityStructure_of_isLocalizedEquivalence [T.IsLeftD
erivabilityStructure] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) …
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftReso
lutions`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁
} C₁}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.LocalizerMorphism.IsInduced.inverseImage_eq`：∀ {C₁ : Type
 u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁}   {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.hw`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure.guitartExac
t'`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁}
   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `CategoryTheory.TwoSquare.hComp_app`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ 
: Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1
 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff`：isLeft
DerivabilityStructure_iff [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
 Φ.IsLeftDerivabilityStructure ↔ TwoSquare.GuitartExac…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.isLocalization`：
∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : CategoryTheory.Category.{
v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂]…
-/
lemma isLeftDerivabilityStructure_iff_of_isLocalizedEquivalence
    [L.functor.EssSurj] [R.functor.Full] [R.IsInduced]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
    [TwoSquare.GuitartExact iso.inv] :
    T.IsLeftDerivabilityStructure ↔ B.IsLeftDerivabilityStructure := by
  refine ⟨fun _ ↦ isLeftDerivabilityStructure_of_isLocalizedEquivalence iso, fun _ ↦ ?_⟩
  have : T.HasLeftResolutions := fun X₂ ↦ by
    let ρ : B.LeftResolution (R.functor.obj X₂) := Classical.arbitrary _
    exact ⟨{
      X₁ := L.functor.objPreimage ρ.X₁
      w :=
        R.functor.preimage (iso.hom.app _ ≫
          B.functor.map (L.functor.objObjPreimageIso ρ.X₁).hom ≫ ρ.w)
      hw := by
        simp only [← R.inverseImage_eq, Functor.comp_obj,
          MorphismProperty.inverseImage_iff, Functor.map_preimage]
        refine (W₂'.arrow_mk_iso_iff ?_).2 ρ.hw
        exact Arrow.isoMk (iso.app _ ≪≫ B.functor.mapIso (L.functor.objObjPreimageIso ρ.X₁))
          (Iso.refl _) }⟩
  let F := B.localizedFunctor W₁'.Q W₂'.Q
  let e' := CatCommSq.iso B.functor W₁'.Q W₂'.Q F
  let e : T.functor ⋙ R.functor ⋙ W₂'.Q ≅ (L.functor ⋙ W₁'.Q) ⋙ F :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iso _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e' ≪≫ (Functor.associator _ _ _).symm
  have he' : TwoSquare.GuitartExact e'.inv := inferInstance
  have : TwoSquare.hComp iso.inv e'.inv = e.inv := by ext; simp [e]
  rw [T.isLeftDerivabilityStructure_iff (L.functor ⋙ W₁'.Q)
    (R.functor ⋙ W₂'.Q) F e, ← this]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_of_isLocalizedEq
uivalence** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isRightDerivabilityStructure_of_isLocalizedEquivalence [T.IsRightDerivabil
ityStructure] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [TwoSquare.G
uitartExact iso.hom] : B.IsRightDerivabilityStructure
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff_op`：is
RightDerivabilityStructure_iff_op : Φ.IsRightDerivabilityStructure ↔ Φ.op.IsLeft
DerivabilityStructure
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_isLocali
zedEquivalence`：isLeftDerivabilityStructure_of_isLocalizedEquivalence [T.IsLeftD
erivabilityStructure] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) …
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.op`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [P.Resp
ectsIso],   P.op.RespectsIso
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsLocalizedEquivalenceOppositeOpOp`
：∀ {C₁ : Type u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   
[inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.Functor.instEssSurjOppositeOp`：∀ (C : Type u₁) [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsLeftDerivabilityStructureOpposite
OpOpOfIsRightDerivabilityStructure`：∀ {C₁ : Type u₁} {C₂ : Type u₂} [inst : Cate
goryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂
] {W₁ : Category…
-/
lemma isRightDerivabilityStructure_of_isLocalizedEquivalence
    [T.IsRightDerivabilityStructure]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
    [TwoSquare.GuitartExact iso.hom] :
    B.IsRightDerivabilityStructure := by
  rw [isRightDerivabilityStructure_iff_op]
  let iso' : T.op.functor ⋙ R.op.functor ≅ L.op.functor ⋙ B.op.functor := NatIso.op iso.symm
  have : TwoSquare.GuitartExact iso'.inv :=
    inferInstanceAs (TwoSquare.op iso.hom).GuitartExact
  exact isLeftDerivabilityStructure_of_isLocalizedEquivalence iso'

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff_of_isLocaliz
edEquivalence** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isRightDerivabilityStructure_iff_of_isLocalizedEquivalence [L.functor.EssS
urj] [R.functor.Full] [R.IsInduced] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B
.functor) [TwoSquare.GuitartExact iso.hom] : T.IsRightDerivabilityStructure ↔ B.
IsRightDerivabilityStructure
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff_of_isLo
calizedEquivalence`：isLeftDerivabilityStructure_iff_of_isLocalizedEquivalence [L
.functor.EssSurj] [R.functor.Full] [R.IsInduced] (iso : T.functor ⋙ R.functor ≅ 
…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.op`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [P.Resp
ectsIso],   P.op.RespectsIso
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsLocalizedEquivalenceOppositeOpOp`
：∀ {C₁ : Type u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   
[inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.Functor.instEssSurjOppositeOp`：∀ (C : Type u₁) [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsInducedOppositeOpOp`：∀ {C₁ : Type
 u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
-/
lemma isRightDerivabilityStructure_iff_of_isLocalizedEquivalence
    [L.functor.EssSurj] [R.functor.Full] [R.IsInduced]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)
    [TwoSquare.GuitartExact iso.hom] :
    T.IsRightDerivabilityStructure ↔ B.IsRightDerivabilityStructure := by
  simp only [isRightDerivabilityStructure_iff_op]
  let iso' : T.op.functor ⋙ R.op.functor ≅ L.op.functor ⋙ B.op.functor := NatIso.op iso.symm
  have : TwoSquare.GuitartExact iso'.inv :=
    inferInstanceAs (TwoSquare.op iso.hom).GuitartExact
  exact isLeftDerivabilityStructure_iff_of_isLocalizedEquivalence iso'

end

variable [W₁'.RespectsIso] [W₂'.RespectsIso] [L.IsInduced] [L.functor.IsEquivalence]
  [R.IsInduced] [R.functor.IsEquivalence]
  (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_equivalences**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLeftDerivabilityStructure_of_equivalences [T.IsLeftDerivabilityStructure
] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) : B.IsLeftDerivabilitySt
ructure
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_isInduced`：is
LocalizedEquivalence_of_isInduced : Φ.IsLocalizedEquivalence
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_isLocali
zedEquivalence`：isLeftDerivabilityStructure_of_isLocalizedEquivalence [T.IsLeftD
erivabilityStructure] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) …
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma isLeftDerivabilityStructure_of_equivalences
    [T.IsLeftDerivabilityStructure]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    B.IsLeftDerivabilityStructure := by
  have := L.isLocalizedEquivalence_of_isInduced
  have := R.isLocalizedEquivalence_of_isInduced
  exact isLeftDerivabilityStructure_of_isLocalizedEquivalence iso

open CategoryTheory.Functor in
/-
**CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff_of_equivalenc
es** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLeftDerivabilityStructure_iff_of_equivalences (iso : T.functor ⋙ R.funct
or ≅ L.functor ⋙ B.functor) : T.IsLeftDerivabilityStructure ↔ B.IsLeftDerivabili
tyStructure
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_equivale
nces`：isLeftDerivabilityStructure_of_equivalences [T.IsLeftDerivabilityStructure
] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) : B.IsLeft…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.LocalizerMorphism.IsInduced.inverseImage_eq`：∀ {C₁ : Type
 u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁}   {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.inverseImage`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheo
ry.Category.{v_1, u_1} D]   (P : CategoryTheor…
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsInducedInv`：∀ {C₁ : Type u₁} {C₂ 
: Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsEquivalenceFunctorInv`：∀ {C₁ : Ty
pe u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : C
ategoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
-/
lemma isLeftDerivabilityStructure_iff_of_equivalences
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.IsLeftDerivabilityStructure ↔ B.IsLeftDerivabilityStructure :=
  ⟨fun _ ↦ isLeftDerivabilityStructure_of_equivalences iso, fun _ ↦ by
    let e : B.functor ⋙ R.inv.functor ≅ L.inv.functor ⋙ T.functor :=
      (leftUnitor _).symm ≪≫
        isoWhiskerRight L.functor.asEquivalence.counitIso.symm _ ≪≫
        associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _).symm ≪≫
        isoWhiskerLeft _ (isoWhiskerRight iso.symm R.inv.functor) ≪≫
        isoWhiskerLeft _ (associator _ _ _) ≪≫
        isoWhiskerLeft _ (isoWhiskerLeft _ R.functor.asEquivalence.unitIso.symm) ≪≫
        (associator _ _ _).symm ≪≫ rightUnitor _
    have : W₁.RespectsIso := by rw [← L.inverseImage_eq]; infer_instance
    have : W₂.RespectsIso := by rw [← R.inverseImage_eq]; infer_instance
    exact isLeftDerivabilityStructure_of_equivalences e⟩
/-
**CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff_of_equivalen
ces** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isRightDerivabilityStructure_iff_of_equivalences (iso : T.functor ⋙ R.func
tor ≅ L.functor ⋙ B.functor) : T.IsRightDerivabilityStructure ↔ B.IsRightDerivab
ilityStructure
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff_of_equi
valences`：isLeftDerivabilityStructure_iff_of_equivalences (iso : T.functor ⋙ R.f
unctor ≅ L.functor ⋙ B.functor) : T.IsLeftDerivabilityStructure ↔ B.Is…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.op`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [P.Resp
ectsIso],   P.op.RespectsIso
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsInducedOppositeOpOp`：∀ {C₁ : Type
 u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceOppositeOp`：∀ (C : Type u₁) [ins
t : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isRightDerivabilityStructure_iff_of_equivalences
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.IsRightDerivabilityStructure ↔ B.IsRightDerivabilityStructure := by
  let e : T.op.functor ⋙ R.op.functor ≅ L.op.functor ⋙ B.op.functor := NatIso.op iso.symm
  simp only [isRightDerivabilityStructure_iff_op,
    isLeftDerivabilityStructure_iff_of_equivalences e]
/-
**CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_of_equivalences*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isRightDerivabilityStructure_of_equivalences [T.IsRightDerivabilityStructu
re] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) : B.IsRightDerivabilit
yStructure
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff_of_equ
ivalences`：isRightDerivabilityStructure_iff_of_equivalences (iso : T.functor ⋙ R
.functor ≅ L.functor ⋙ B.functor) : T.IsRightDerivabilityStructure ↔ B.…
-/
lemma isRightDerivabilityStructure_of_equivalences
    [T.IsRightDerivabilityStructure]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    B.IsRightDerivabilityStructure := by
  rwa [← isRightDerivabilityStructure_iff_of_equivalences iso]

end LocalizerMorphism

end CategoryTheory

