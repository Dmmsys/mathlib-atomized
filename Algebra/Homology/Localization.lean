/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Localization.Composition
public import Mathlib.CategoryTheory.Localization.HasLocalization

/-! # The category of homological complexes up to quasi-isomorphisms

Given a category `C` with homology and any complex shape `c`, we define
the category `HomologicalComplexUpToQuasiIso C c` which is the localized
category of `HomologicalComplex C c` with respect to quasi-isomorphisms.
When `C` is abelian, this will be the derived category of `C` in the
particular case of the complex shape `ComplexShape.up ℤ`.

Under suitable assumptions on `c` (e.g. chain complexes, or cochain
complexes indexed by `ℤ`), we shall show that `HomologicalComplexUpToQuasiIso C c`
is also the localized category of `HomotopyCategory C c` with respect to
the class of quasi-isomorphisms.

-/

@[expose] public section

open CategoryTheory Limits

section

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C]

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.homologyFunctor_inverts_quasiIso** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：HomologicalComplex.homologyFunctor_inverts_quasiIso (i : ι) : (quasiIso C 
c).IsInvertedBy (homologyFunctor C c i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsIsoHomologyMapOfQuasiIsoAt`：∀ {ι : Type u_1} {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C] {c : ComplexSh…
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.mem_quasiIso_iff`：mem_quasiIso_iff (f : K ⟶ L) : quas
iIso C c f ↔ QuasiIso f
-/
lemma HomologicalComplex.homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => by
  rw [mem_quasiIso_iff] at hf
  dsimp
  infer_instance

variable [(HomologicalComplex.quasiIso C c).HasLocalization]

/-- The category of homological complexes up to quasi-isomorphisms. -/
/-
**HomologicalComplexUpToQuasiIso** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HomologicalComplexUpToQuasiIso
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of homological complexes up to quasi-isomorphisms.
-/
abbrev HomologicalComplexUpToQuasiIso := (HomologicalComplex.quasiIso C c).Localization'

variable {C c} in
/-- The localization functor `HomologicalComplex C c ⥤ HomologicalComplexUpToQuasiIso C c`. -/
/-
**HomologicalComplexUpToQuasiIso.Q** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HomologicalComplexUpToQuasiIso.Q : HomologicalComplex C c ⥤ HomologicalCom
plexUpToQuasiIso C c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization functor `HomologicalComplex C c ⥤ HomologicalComplexUpToQuasiIs
o C c`.
-/
abbrev HomologicalComplexUpToQuasiIso.Q :
    HomologicalComplex C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  (HomologicalComplex.quasiIso C c).Q'

namespace HomologicalComplexUpToQuasiIso

/-- The homology functor `HomologicalComplexUpToQuasiIso C c ⥤ C` for each `i : ι`. -/
/-
**HomologicalComplexUpToQuasiIso.homologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Homo
logicalComplexUpToQuasiIso`。
形式化陈述：homologyFunctor (i : ι) : HomologicalComplexUpToQuasiIso C c ⥤ C
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.homologyFunctor_inverts_quasiIso`：HomologicalComplex.
homologyFunctor_inverts_quasiIso (i : ι) : (quasiIso C c).IsInvertedBy (homology
Functor C c i)

--- 原说明 ---
The homology functor `HomologicalComplexUpToQuasiIso C c ⥤ C` for each `i : ι`.
-/
noncomputable def homologyFunctor (i : ι) : HomologicalComplexUpToQuasiIso C c ⥤ C :=
  Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

/-- The homology functor on `HomologicalComplexUpToQuasiIso C c` is induced by
the homology functor on `HomologicalComplex C c`. -/
/-
**HomologicalComplexUpToQuasiIso.homologyFunctorFactors** 是 Mathlib 中的一个定义，位于命名空
间 `HomologicalComplexUpToQuasiIso`。
形式化陈述：homologyFunctorFactors (i : ι) : Q ⋙ homologyFunctor C c i ≅ HomologicalCo
mplex.homologyFunctor C c i
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.homologyFunctor_inverts_quasiIso`：HomologicalComplex.
homologyFunctor_inverts_quasiIso (i : ι) : (quasiIso C c).IsInvertedBy (homology
Functor C c i)

--- 原说明 ---
The homology functor on `HomologicalComplexUpToQuasiIso C c` is induced by
the homology functor on `HomologicalComplex C c`.
-/
noncomputable def homologyFunctorFactors (i : ι) :
    Q ⋙ homologyFunctor C c i ≅ HomologicalComplex.homologyFunctor C c i :=
  Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

variable {C c}

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso** 是 Mathlib 中的一个引理
，位于命名空间 `HomologicalComplexUpToQuasiIso`。
形式化陈述：isIso_Q_map_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) : 
IsIso (Q.map f) ↔ HomologicalComplex.quasiIso C c f
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.mem_quasiIso_iff`：mem_quasiIso_iff (f : K ⟶ L) : quas
iIso C c f ↔ QuasiIso f
· 使用引理 `quasiIso_iff`：quasiIso_iff (f : K ⟶ L) [forall i, K.HasHomology i] [fora
ll i, L.HasHomology i] : QuasiIso f ↔ forall i, QuasiIsoAt f i
· 使用引理 `quasiIsoAt_iff_isIso_homologyMap`：quasiIsoAt_iff_isIso_homologyMap (f : 
K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : QuasiIsoAt f i ↔ IsIso (hom
ologyMap f i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.NatIso.isIso_map_iff`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F₁ F₂ : CategoryT…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.MorphismProperty.instIsLocalizationLocalization'Q'`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Morphism
Property C)   [inst_1 : W.HasLocalization], W.Q'.IsLoca…
-/
lemma isIso_Q_map_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsIso (Q.map f) ↔ HomologicalComplex.quasiIso C c f := by
  constructor
  · intro h
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 ?_
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.quasiIso C c) _ h

end HomologicalComplexUpToQuasiIso

end

section

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

/-
**HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences [(Homologica
lComplex.quasiIso C c).HasLocalization] : (HomologicalComplex.homotopyEquivalenc
es C c).IsInvertedBy HomologicalComplexUpToQuasiIso.Q
参数：HomologicalComplex.quasiIso C c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsInvertedBy.of_le`：of_le (P Q : Morphis
mProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P <= Q) : P.IsInvertedBy F
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.MorphismProperty.instIsLocalizationLocalization'Q'`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Morphism
Property C)   [inst_1 : W.HasLocalization], W.Q'.IsLoca…
· 使用引理 `homotopyEquivalences_le_quasiIso`：homotopyEquivalences_le_quasiIso {ι : 
Type*} (C : Type u) [Category.{v} C] [Preadditive C] (c : ComplexShape ι) [Categ
oryWithHomology C] : h…
-/
lemma HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences
    [(HomologicalComplex.quasiIso C c).HasLocalization] :
    (HomologicalComplex.homotopyEquivalences C c).IsInvertedBy
      HomologicalComplexUpToQuasiIso.Q :=
  MorphismProperty.IsInvertedBy.of_le _ _ _
    (Localization.inverts Q (HomologicalComplex.quasiIso C c))
    (homotopyEquivalences_le_quasiIso C c)

namespace HomotopyCategory

/-- The class of quasi-isomorphisms in the homotopy category. -/
/-
**HomotopyCategory.quasiIso** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory`。
形式化陈述：quasiIso : MorphismProperty (HomotopyCategory C c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of quasi-isomorphisms in the homotopy category.
-/
def quasiIso : MorphismProperty (HomotopyCategory C c) :=
  fun _ _ f => ∀ (i : ι), IsIso ((homologyFunctor C c i).map f)

variable {C c}
/-
**HomotopyCategory.mem_quasiIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyCategory`
。
形式化陈述：mem_quasiIso_iff {X Y : HomotopyCategory C c} (f : X ⟶ Y) : quasiIso C c f
 ↔ forall (n : ι), IsIso ((homologyFunctor _ _ n).map f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_quasiIso_iff {X Y : HomotopyCategory C c} (f : X ⟶ Y) :
    quasiIso C c f ↔ ∀ (n : ι), IsIso ((homologyFunctor _ _ n).map f) := by
  rfl

set_option backward.defeqAttrib.useBackward true in
/-
**HomotopyCategory.quotient_map_mem_quasiIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topyCategory`。
形式化陈述：quotient_map_mem_quasiIso_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
 quasiIso C c ((quotient C c).map f) ↔ HomologicalComplex.quasiIso C c f
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_map_iff`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F₁ F₂ : CategoryT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma quotient_map_mem_quasiIso_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    quasiIso C c ((quotient C c).map f) ↔ HomologicalComplex.quasiIso C c f := by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.mem_quasiIso_iff, mem_quasiIso_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]

variable (C c)
/-
**HomotopyCategory.respectsIso_quasiIso** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCateg
ory`。
形式化陈述：respectsIso_quasiIso : (quasiIso C c).RespectsIso
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.of_respects_arrow_iso`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphism
Property C),   (∀ (f g : CategoryTheory.Arrow C) (x : f…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
-/
instance respectsIso_quasiIso : (quasiIso C c).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf i
  exact ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    ((homologyFunctor C c i).mapArrow.mapIso e)).1 (hf i)
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quasiIso C c).IsMultiplicative where
  id_mem K := by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem f g hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    simp only [Functor.map_comp]
    infer_instance
/-
**HomotopyCategory.homologyFunctor_inverts_quasiIso** 是 Mathlib 中的一个引理，位于命名空间 `H
omotopyCategory`。
形式化陈述：homologyFunctor_inverts_quasiIso (i : ι) : (quasiIso C c).IsInvertedBy (ho
mologyFunctor C c i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => hf i

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopyCategory.quasiIso_eq_quasiIso_map_quotient** 是 Mathlib 中的一个引理，位于命名空间 `
HomotopyCategory`。
形式化陈述：quasiIso_eq_quasiIso_map_quotient : quasiIso C c = (HomologicalComplex.qua
siIso C c).map (quotient C c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用引理 `CategoryTheory.MorphismProperty.map_mem_map`：map_mem_map (P : MorphismPr
operty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) : (P.map F) (F.map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopyCategory.quotient_map_mem_quasiIso_iff`：quotient_map_mem_quasiIs
o_iff {K L : HomologicalComplex C c} (f : K ⟶ L) : quasiIso C c ((quotient C c).
map f) ↔ HomologicalComplex.quasiIso…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma quasiIso_eq_quasiIso_map_quotient :
    quasiIso C c = (HomologicalComplex.quasiIso C c).map (quotient C c) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_quasiIso_iff] at h
    exact ((quasiIso C c).arrow_mk_iso_iff e).1 h

end HomotopyCategory

/-- The condition on a complex shape `c` saying that homotopic maps become equal in
the localized category with respect to quasi-isomorphisms. -/
/-
**ComplexShape.QFactorsThroughHomotopy** 是 Mathlib 中的一个归纳类型，位于命名空间 `ComplexShape
`。
形式化陈述：{ι : Type u_3} →   ComplexShape ι →     (C : Type u_4) →       [inst : Cat
egoryTheory.Category.{v_2, u_4} C] →         [inst_1 : CategoryTheory.Preadditiv
e C] → [CategoryTheory.CategoryWithHomology C] → Prop
参数：C : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition on a complex shape `c` saying that homotopic maps become equal in
the localized category with respect to quasi-isomorphisms.
-/
class ComplexShape.QFactorsThroughHomotopy {ι : Type*} (c : ComplexShape ι)
    (C : Type*) [Category* C] [Preadditive C]
    [CategoryWithHomology C] : Prop where
  areEqualizedByLocalization {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    AreEqualizedByLocalization (HomologicalComplex.quasiIso C c) f g

namespace HomologicalComplexUpToQuasiIso

variable {C c}
variable [(HomologicalComplex.quasiIso C c).HasLocalization] [c.QFactorsThroughHomotopy C]

/-
**HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy** 是 Mathlib 中的一个引理，位于命名空间 
`HomologicalComplexUpToQuasiIso`。
形式化陈述：Q_map_eq_of_homotopy {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Hom
otopy f g) : Q.map f = Q.map g
参数：h : Homotopy f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.AreEqualizedByLocalization.map_eq`：map_eq (h : AreEqualiz
edByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W] : L.map f = L.map g
· 使用定理 `ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization`：∀ {ι : 
Type u_3} {c : ComplexShape ι} {C : Type u_4} {inst : CategoryTheory.Category.{v
_2, u_4} C}   {inst_1 : CategoryTheory.Preadditive C}…
· 使用定理 `CategoryTheory.MorphismProperty.instIsLocalizationLocalization'Q'`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Morphism
Property C)   [inst_1 : W.HasLocalization], W.Q'.IsLoca…
-/
lemma Q_map_eq_of_homotopy {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    Q.map f = Q.map g :=
  (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization h).map_eq Q

/-- The functor `HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c` from the homotopy
category to the localized category with respect to quasi-isomorphisms. -/
/-
**HomologicalComplexUpToQuasiIso.Qh** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
xUpToQuasiIso`。
形式化陈述：Qh : HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c` from the
 homotopy
category to the localized category with respect to quasi-isomorphisms.
-/
def Qh : HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  CategoryTheory.Quotient.lift _ HomologicalComplexUpToQuasiIso.Q (by
    intro K L f g ⟨h⟩
    exact Q_map_eq_of_homotopy h)

variable (C c)

/-- The canonical isomorphism `HomotopyCategory.quotient C c ⋙ Qh ≅ Q`. -/
/-
**HomologicalComplexUpToQuasiIso.quotientCompQhIso** 是 Mathlib 中的一个定义，位于命名空间 `Ho
mologicalComplexUpToQuasiIso`。
形式化陈述：quotientCompQhIso : HomotopyCategory.quotient C c ⋙ Qh ≅ Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `HomotopyCategory.quotient C c ⋙ Qh ≅ Q`.
-/
def quotientCompQhIso : HomotopyCategory.quotient C c ⋙ Qh ≅ Q := by
  apply Quotient.lift.isLift

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplexUpToQuasiIso.Qh_inverts_quasiIso** 是 Mathlib 中的一个引理，位于命名空间 `
HomologicalComplexUpToQuasiIso`。
形式化陈述：Qh_inverts_quasiIso : (HomotopyCategory.quasiIso C c).IsInvertedBy Qh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopyCategory.quotient_map_mem_quasiIso_iff`：quotient_map_mem_quasiIs
o_iff {K L : HomologicalComplex C c} (f : K ⟶ L) : quasiIso C c ((quotient C c).
map f) ↔ HomologicalComplex.quasiIso…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso`：isIso_Q_map
_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) : IsIso (Q.map f) ↔
 HomologicalComplex.quasiIso C c f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.NatIso.isIso_map_iff`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F₁ F₂ : CategoryT…
-/
lemma Qh_inverts_quasiIso : (HomotopyCategory.quasiIso C c).IsInvertedBy Qh := by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff φ,
    ← HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso]
  exact (NatIso.isIso_map_iff (quotientCompQhIso C c) φ).2
/-
**HomologicalComplexUpToQuasiIso.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplexU
pToQuasiIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (HomotopyCategory.quotient C c ⋙ Qh).IsLocalization
    (HomologicalComplex.quasiIso C c) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C c).symm

/-- The homology functor on `HomologicalComplexUpToQuasiIso C c` is induced by
the homology functor on `HomotopyCategory C c`. -/
/-
**HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh** 是 Mathlib 中的一个定义，位于命名
空间 `HomologicalComplexUpToQuasiIso`。
形式化陈述：homologyFunctorFactorsh (i : ι) : Qh ⋙ homologyFunctor C c i ≅ HomotopyCat
egory.homologyFunctor C c i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology functor on `HomologicalComplexUpToQuasiIso C c` is induced by
the homology functor on `HomotopyCategory C c`.
-/
noncomputable def homologyFunctorFactorsh (i : ι) :
    Qh ⋙ homologyFunctor C c i ≅ HomotopyCategory.homologyFunctor C c i :=
  Quotient.natIsoLift _ ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quotientCompQhIso C c) _ ≪≫
    homologyFunctorFactors C c i ≪≫ (HomotopyCategory.homologyFunctorFactors C c i).symm)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_obj** 
是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplexUpToQuasiIso`。
形式化陈述：homologyFunctorFactorsh_hom_app_quotient_obj (K : HomologicalComplex C c) 
(i : ι) : (homologyFunctorFactorsh C c i).hom.app ((HomotopyCategory.quotient _ 
_).obj K) = (homologyFunctor C c i).map ((quotientCompQhIso C c).hom.app K) ≫ (h
omologyFunctorFactors C c i).hom.app K ≫ (HomotopyCategory.homologyFunctorFactor
s C c i).inv.app K
参数：K : HomologicalComplex C c；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Quotient.natTransLift_app`：natTransLift_app (F G : Quotie
nt r ⥤ D) (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G) (X : C) : (natTr
ansLift r τ).app ((Quotient.fu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyFunctorFactorsh_hom_app_quotient_obj
    (K : HomologicalComplex C c) (i : ι) :
    (homologyFunctorFactorsh C c i).hom.app ((HomotopyCategory.quotient _ _).obj K) =
    (homologyFunctor C c i).map ((quotientCompQhIso C c).hom.app K) ≫
      (homologyFunctorFactors C c i).hom.app K ≫
        (HomotopyCategory.homologyFunctorFactors C c i).inv.app K :=
  (Quotient.natTransLift_app ..).trans (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_obj** 
是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplexUpToQuasiIso`。
形式化陈述：homologyFunctorFactorsh_inv_app_quotient_obj (K : HomologicalComplex C c) 
(i : ι) : (homologyFunctorFactorsh C c i).inv.app ((HomotopyCategory.quotient _ 
_).obj K) = (HomotopyCategory.homologyFunctorFactors C c i).hom.app K ≫ (homolog
yFunctorFactors C c i).inv.app K ≫ (homologyFunctor C c i).map ((quotientCompQhI
so C c).inv.app K)
参数：K : HomologicalComplex C c；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Quotient.natTransLift_app`：natTransLift_app (F G : Quotie
nt r ⥤ D) (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G) (X : C) : (natTr
ansLift r τ).app ((Quotient.fu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homologyFunctorFactorsh_inv_app_quotient_obj
    (K : HomologicalComplex C c) (i : ι) :
    (homologyFunctorFactorsh C c i).inv.app ((HomotopyCategory.quotient _ _).obj K) =
    (HomotopyCategory.homologyFunctorFactors C c i).hom.app K ≫
      (homologyFunctorFactors C c i).inv.app K ≫
        (homologyFunctor C c i).map ((quotientCompQhIso C c).inv.app K) :=
  (Quotient.natTransLift_app ..).trans (by simp)

section

variable [(HomotopyCategory.quotient C c).IsLocalization
  (HomologicalComplex.homotopyEquivalences C c)]

/-- The category `HomologicalComplexUpToQuasiIso C c` which was defined as a localization of
`HomologicalComplex C c` with respect to quasi-isomorphisms also identifies to a localization
of the homotopy category with respect to quasi-isomorphisms. -/
/-
**HomologicalComplexUpToQuasiIso.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplexU
pToQuasiIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `HomologicalComplexUpToQuasiIso C c` which was defined as a localiz
ation of
`HomologicalComplex C c` with respect to quasi-isomorphisms also identifies to a
 localization
of the homotopy category with respect to quasi-isomorphisms.
-/
instance : HomologicalComplexUpToQuasiIso.Qh.IsLocalization (HomotopyCategory.quasiIso C c) :=
  Functor.IsLocalization.of_comp (HomotopyCategory.quotient C c)
    Qh (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quasiIso C c) (HomologicalComplex.quasiIso C c)
    (homotopyEquivalences_le_quasiIso C c)
    (HomotopyCategory.quasiIso_eq_quasiIso_map_quotient C c)

end

end HomologicalComplexUpToQuasiIso

end

section Cylinder

variable {ι : Type*} (c : ComplexShape ι) (hc : ∀ j, ∃ i, c.Rel i j)
  (C : Type*) [Category* C] [Preadditive C] [HasBinaryBiproducts C]
include hc

/-- The homotopy category satisfies the universal property of the localized category
with respect to homotopy equivalences. -/
/-
**ComplexShape.strictUniversalPropertyFixedTargetQuotient** 是 Mathlib 中的一个定义，位于命
名空间 ``。
形式化陈述：ComplexShape.strictUniversalPropertyFixedTargetQuotient (E : Type*) [Categ
ory* E] : Localization.StrictUniversalPropertyFixedTarget (HomotopyCategory.quot
ient C c) (HomologicalComplex.homotopyEquivalences C c) E where inverts
参数：E : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopyCategory.quotient_inverts_homotopyEquivalences`：quotient_inverts
_homotopyEquivalences : (HomologicalComplex.homotopyEquivalences V c).IsInverted
By (quotient V c)

--- 原说明 ---
The homotopy category satisfies the universal property of the localized category
with respect to homotopy equivalences.
-/
def ComplexShape.strictUniversalPropertyFixedTargetQuotient (E : Type*) [Category* E] :
    Localization.StrictUniversalPropertyFixedTarget (HomotopyCategory.quotient C c)
      (HomologicalComplex.homotopyEquivalences C c) E where
  inverts := HomotopyCategory.quotient_inverts_homotopyEquivalences C c
  lift F hF := CategoryTheory.Quotient.lift _ F (by
    intro K L f g ⟨h⟩
    have : DecidableRel c.Rel := by classical infer_instance
    exact h.map_eq_of_inverts_homotopyEquivalences hc F hF)
  fac _ _ := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h
/-
**ComplexShape.quotient_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ComplexShape.quotient_isLocalization : (HomotopyCategory.quotient C c).IsL
ocalization (HomologicalComplex.homotopyEquivalences _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.mk'`：∀ {C : Type u_1} {D : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_2} D] (L : Categor…
-/
lemma ComplexShape.quotient_isLocalization :
    (HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences _ _) := by
  apply Functor.IsLocalization.mk'
  all_goals apply c.strictUniversalPropertyFixedTargetQuotient hc
/-
**ComplexShape.QFactorsThroughHomotopy_of_exists_prev** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：ComplexShape.QFactorsThroughHomotopy_of_exists_prev [CategoryWithHomology 
C] : c.QFactorsThroughHomotopy C where areEqualizedByLocalization {K L f g} h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homotopy.map_eq_of_inverts_homotopyEquivalences`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
{ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `HomologicalComplex.instHasHomotopyCofiberOfHasBinaryBiproducts`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.
Preadditive C] {ι : Type u_2}   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用引理 `CategoryTheory.MorphismProperty.IsInvertedBy.of_le`：of_le (P Q : Morphis
mProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P <= Q) : P.IsInvertedBy F
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `homotopyEquivalences_le_quasiIso`：homotopyEquivalences_le_quasiIso {ι : 
Type*} (C : Type u) [Category.{v} C] [Preadditive C] (c : ComplexShape ι) [Categ
oryWithHomology C] : h…
-/
lemma ComplexShape.QFactorsThroughHomotopy_of_exists_prev [CategoryWithHomology C] :
    c.QFactorsThroughHomotopy C where
  areEqualizedByLocalization {K L f g} h := by
    exact h.map_eq_of_inverts_homotopyEquivalences hc _
      (MorphismProperty.IsInvertedBy.of_le _ _ _
        (Localization.inverts _ (HomologicalComplex.quasiIso C _))
        (homotopyEquivalences_le_quasiIso C _))

end Cylinder

section ChainComplex

variable (C : Type*) [Category* C] {ι : Type*} [Preadditive C]
  [AddRightCancelSemigroup ι] [One ι] [HasBinaryBiproducts C]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (HomotopyCategory.quotient C (ComplexShape.down ι)).IsLocalization
    (HomologicalComplex.homotopyEquivalences _ _) :=
  (ComplexShape.down ι).quotient_isLocalization (fun _ => ⟨_, rfl⟩) C

variable [CategoryWithHomology C]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ComplexShape.down ι).QFactorsThroughHomotopy C :=
  (ComplexShape.down ι).QFactorsThroughHomotopy_of_exists_prev (fun _ => ⟨_, rfl⟩) C
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [(HomologicalComplex.quasiIso C (ComplexShape.down ι)).HasLocalization] :
    HomologicalComplexUpToQuasiIso.Qh.IsLocalization
    (HomotopyCategory.quasiIso C (ComplexShape.down ι)) :=
  inferInstance

/- By duality, the results obtained here for chain complexes could be dualized in
order to obtain similar results for general cochain complexes. However, the case of
interest for the construction of the derived category (cochain complexes indexed by `ℤ`)
can also be obtained directly, which is done below. -/

end ChainComplex

section CochainComplex

variable (C : Type*) [Category* C] {ι : Type*} [Preadditive C] [HasBinaryBiproducts C]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences _ _) :=
  (ComplexShape.up ℤ).quotient_isLocalization (fun n => ⟨n - 1, by simp⟩) C

variable [CategoryWithHomology C]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ComplexShape.up ℤ).QFactorsThroughHomotopy C :=
  (ComplexShape.up ℤ).QFactorsThroughHomotopy_of_exists_prev (fun n => ⟨n - 1, by simp⟩) C

/-- When we define the derived category as `HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`,
i.e. as the localization of cochain complexes with respect to quasi-isomorphisms, this
example shall say that the derived category is also the localization of the homotopy
category with respect to quasi-isomorphisms. -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When we define the derived category as `HomologicalComplexUpToQuasiIso C (Comple
xShape.up ℤ)`,
i.e. as the localization of cochain complexes with respect to quasi-isomorphisms
, this
example shall say that the derived category is also the localization of the homo
topy
category with respect to quasi-isomorphisms.
-/
example [(HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).HasLocalization] :
    HomologicalComplexUpToQuasiIso.Qh.IsLocalization
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  inferInstance

end CochainComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  {ι : Type*} (c : ComplexShape ι)

section

variable [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  [(HomologicalComplex.quasiIso D c).HasLocalization]
  [F.Additive] [F.PreservesHomology]

/-- The localizer morphism which expresses that `F.mapHomologicalComplex c` preserves
quasi-isomorphisms. -/
@[simps]
/-
**CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplexUpToQuasiIsoLocalizerMorphism : LocalizerMorphism (Ho
mologicalComplex.quasiIso C c) (HomologicalComplex.quasiIso D c) where functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The localizer morphism which expresses that `F.mapHomologicalComplex c` preserve
s
quasi-isomorphisms.
-/
def mapHomologicalComplexUpToQuasiIsoLocalizerMorphism :
    LocalizerMorphism (HomologicalComplex.quasiIso C c) (HomologicalComplex.quasiIso D c) where
  functor := F.mapHomologicalComplex c
  map _ _ f (_ : QuasiIso f) := HomologicalComplex.quasiIso_map_of_preservesHomology _ _
/-
**CategoryTheory.Functor.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso : (HomologicalComple
x.quasiIso C c).IsInvertedBy (F.mapHomologicalComplex c ⋙ HomologicalComplexUpTo
QuasiIso.Q)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.LocalizerMorphism.inverts`：inverts : W₁.IsInvertedBy (Φ.f
unctor ⋙ L₂)
· 使用定理 `CategoryTheory.MorphismProperty.instIsLocalizationLocalization'Q'`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Morphism
Property C)   [inst_1 : W.HasLocalization], W.Q'.IsLoca…
-/
lemma mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso :
    (HomologicalComplex.quasiIso C c).IsInvertedBy
      (F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q) := by
  apply (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).inverts

variable [(HomologicalComplex.quasiIso C c).HasLocalization]

/-- The functor `HomologicalComplexUpToQuasiIso C c ⥤ HomologicalComplexUpToQuasiIso D c`
induced by a functor `F : C ⥤ D` which preserves homology. -/
/-
**CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIso** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplexUpToQuasiIso : HomologicalComplexUpToQuasiIso C c ⥤ H
omologicalComplexUpToQuasiIso D c
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The functor `HomologicalComplexUpToQuasiIso C c ⥤ HomologicalComplexUpToQuasiIso
 D c`
induced by a functor `F : C ⥤ D` which preserves homology.
-/
noncomputable def mapHomologicalComplexUpToQuasiIso :
    HomologicalComplexUpToQuasiIso C c ⥤ HomologicalComplexUpToQuasiIso D c :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).localizedFunctor
    HomologicalComplexUpToQuasiIso.Q HomologicalComplexUpToQuasiIso.Q
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
    Localization.Lifting HomologicalComplexUpToQuasiIso.Q
      (HomologicalComplex.quasiIso C c)
      (F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q)
      (F.mapHomologicalComplexUpToQuasiIso c) :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).liftingLocalizedFunctor _ _

/-- The functor `F.mapHomologicalComplexUpToQuasiIso c` is induced by
`F.mapHomologicalComplex c`. -/
/-
**CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIsoFactors** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplexUpToQuasiIsoFactors : HomologicalComplexUpToQuasiIso.
Q ⋙ F.mapHomologicalComplexUpToQuasiIso c ≅ F.mapHomologicalComplex c ⋙ Homologi
calComplexUpToQuasiIso.Q
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The functor `F.mapHomologicalComplexUpToQuasiIso c` is induced by
`F.mapHomologicalComplex c`.
-/
noncomputable def mapHomologicalComplexUpToQuasiIsoFactors :
    HomologicalComplexUpToQuasiIso.Q ⋙ F.mapHomologicalComplexUpToQuasiIso c ≅
      F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q :=
  Localization.Lifting.iso HomologicalComplexUpToQuasiIso.Q
      (HomologicalComplex.quasiIso C c) _ _

variable [c.QFactorsThroughHomotopy C] [c.QFactorsThroughHomotopy D]
  [(HomotopyCategory.quotient C c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C c)]

/-- The functor `F.mapHomologicalComplexUpToQuasiIso c` is induced by
`F.mapHomotopyCategory c`. -/
/-
**CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIsoFactorsh** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplexUpToQuasiIsoFactorsh : HomologicalComplexUpToQuasiIso
.Qh ⋙ F.mapHomologicalComplexUpToQuasiIso c ≅ F.mapHomotopyCategory c ⋙ Homologi
calComplexUpToQuasiIso.Qh
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The functor `F.mapHomologicalComplexUpToQuasiIso c` is induced by
`F.mapHomotopyCategory c`.
-/
noncomputable def mapHomologicalComplexUpToQuasiIsoFactorsh :
    HomologicalComplexUpToQuasiIso.Qh ⋙ F.mapHomologicalComplexUpToQuasiIso c ≅
      F.mapHomotopyCategory c ⋙ HomologicalComplexUpToQuasiIso.Qh :=
  Localization.liftNatIso (HomotopyCategory.quotient C c)
    (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quotient C c ⋙ HomologicalComplexUpToQuasiIso.Qh ⋙
      F.mapHomologicalComplexUpToQuasiIso c)
    (HomotopyCategory.quotient C c ⋙ F.mapHomotopyCategory c ⋙
      HomologicalComplexUpToQuasiIso.Qh) _ _
      (F.mapHomologicalComplexUpToQuasiIsoFactors c)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
    Localization.Lifting HomologicalComplexUpToQuasiIso.Qh (HomotopyCategory.quasiIso C c)
      (F.mapHomotopyCategory c ⋙ HomologicalComplexUpToQuasiIso.Qh)
      (F.mapHomologicalComplexUpToQuasiIso c) :=
  ⟨F.mapHomologicalComplexUpToQuasiIsoFactorsh c⟩

variable {c}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app (K : HomologicalComplex 
C c) : (F.mapHomologicalComplexUpToQuasiIsoFactorsh c).hom.app ((HomotopyCategor
y.quotient _ _).obj K) = (F.mapHomologicalComplexUpToQuasiIso c).map ((Homologic
alComplexUpToQuasiIso.quotientCompQhIso C c).hom.app K) ≫ (F.mapHomologicalCompl
exUpToQuasiIsoFactors c).hom.app K ≫ (HomologicalComplexUpToQuasiIso.quotientCom
pQhIso D c).inv.app _ ≫ HomologicalComplexUpToQuasiIso.Qh.map ((F.mapHomotopyCat
egoryFactors c).inv.app K)
参数：K : HomologicalComplex C c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexUpToQuasiIsoFactorsh c).hom.app
        ((HomotopyCategory.quotient _ _).obj K) =
      (F.mapHomologicalComplexUpToQuasiIso c).map
          ((HomologicalComplexUpToQuasiIso.quotientCompQhIso C c).hom.app K) ≫
        (F.mapHomologicalComplexUpToQuasiIsoFactors c).hom.app K ≫
          (HomologicalComplexUpToQuasiIso.quotientCompQhIso D c).inv.app _ ≫
            HomologicalComplexUpToQuasiIso.Qh.map
              ((F.mapHomotopyCategoryFactors c).inv.app K) := by
  dsimp [mapHomologicalComplexUpToQuasiIsoFactorsh]
  rw [Localization.liftNatTrans_app]
  dsimp
  simp only [Category.comp_id, Category.id_comp]
  change _ = (F.mapHomologicalComplexUpToQuasiIso c).map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
    HomologicalComplexUpToQuasiIso.Qh.map (𝟙 _)
  simp only [map_id, Category.comp_id, Category.id_comp]

end

end CategoryTheory.Functor

