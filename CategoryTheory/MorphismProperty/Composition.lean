/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou, Aras Ergus
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Compatibilities of properties of morphisms with respect to composition

Given `P : MorphismProperty C`, we define the predicate `P.IsStableUnderComposition`
which means that `P f → P g → P (f ≫ g)`. We also introduce the type classes
`W.ContainsIdentities`, `W.IsMultiplicative`, and `W.HasTwoOutOfThreeProperty`.

-/

@[expose] public section


universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (C) in
/-- The property of morphisms that is satisfied by `𝟙 X` for any `X`. -/
/-
**CategoryTheory.MorphismProperty.identities** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：identities : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of morphisms that is satisfied by `𝟙 X` for any `X`.
-/
abbrev identities : MorphismProperty C :=
  .ofHoms fun X ↦ 𝟙 X
/-
**CategoryTheory.MorphismProperty.identities_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：identities_op_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : identities Cᵒᵖ f ↔ identities 
C f.unop
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma identities_op_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    identities Cᵒᵖ f ↔ identities C f.unop := by
  obtain ⟨X⟩ := X
  obtain ⟨f⟩ := f
  dsimp
  exact ⟨fun ⟨_⟩ ↦ ⟨_⟩, fun ⟨_⟩ ↦ ⟨_⟩⟩

/-- Typeclass expressing that a morphism property contains identities. -/
/-
**CategoryTheory.MorphismProperty.ContainsIdentities** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass expressing that a morphism property contains identities.
-/
class ContainsIdentities (W : MorphismProperty C) : Prop where
  /-- for all `X : C`, the identity of `X` satisfies the morphism property -/
  id_mem : ∀ (X : C), W (𝟙 X)
/-
**CategoryTheory.MorphismProperty.id_mem** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.MorphismProperty`。
形式化陈述：id_mem (W : MorphismProperty C) [W.ContainsIdentities] (X : C) : W (𝟙 X)
参数：W : MorphismProperty C；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.ContainsIdentities.id_mem`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty
 C}   [self : W.ContainsIdentities] (X : C), W …
-/
lemma id_mem (W : MorphismProperty C) [W.ContainsIdentities] (X : C) :
    W (𝟙 X) := ContainsIdentities.id_mem X

namespace ContainsIdentities

/-
**CategoryTheory.MorphismProperty.ContainsIdentities.op** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：op (W : MorphismProperty C) [W.ContainsIdentities] : W.op.ContainsIdentiti
es
参数：W : MorphismProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
instance op (W : MorphismProperty C) [W.ContainsIdentities] :
    W.op.ContainsIdentities := ⟨fun X => W.id_mem X.unop⟩
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.unop** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：unop (W : MorphismProperty Cᵒᵖ) [W.ContainsIdentities] : W.unop.ContainsId
entities
参数：W : MorphismProperty Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
instance unop (W : MorphismProperty Cᵒᵖ) [W.ContainsIdentities] :
    W.unop.ContainsIdentities := ⟨fun X => W.id_mem (Opposite.op X)⟩
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.of_op** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：of_op (W : MorphismProperty C) [W.op.ContainsIdentities] : W.ContainsIdent
ities
参数：W : MorphismProperty C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_op (W : MorphismProperty C) [W.op.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.op.unop.ContainsIdentities)
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.of_unop** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：of_unop (W : MorphismProperty Cᵒᵖ) [W.unop.ContainsIdentities] : W.Contain
sIdentities
参数：W : MorphismProperty Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_unop (W : MorphismProperty Cᵒᵖ) [W.unop.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.unop.op.ContainsIdentities)
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.eqToHom** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：eqToHom (W : MorphismProperty C) [W.ContainsIdentities] {x y : C} (h : x =
 y) : W (eqToHom h)
参数：W : MorphismProperty C；h : x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.MorphismProperty.ContainsIdentities.id_mem`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty
 C}   [self : W.ContainsIdentities] (X : C), W …
-/
lemma eqToHom (W : MorphismProperty C) [W.ContainsIdentities] {x y : C} (h : x = y) :
    W (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact id_mem x
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.inverseImage** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：inverseImage {P : MorphismProperty D} [P.ContainsIdentities] (F : C ⥤ D) :
 (P.inverseImage F).ContainsIdentities where id_mem X
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
instance inverseImage {P : MorphismProperty D} [P.ContainsIdentities] (F : C ⥤ D) :
    (P.inverseImage F).ContainsIdentities where
  id_mem X := by simpa only [← F.map_id] using! P.id_mem (F.obj X)
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.inf** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：inf {P Q : MorphismProperty C} [P.ContainsIdentities] [Q.ContainsIdentitie
s] : (P ⊓ Q).ContainsIdentities where id_mem X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
instance inf {P Q : MorphismProperty C} [P.ContainsIdentities] [Q.ContainsIdentities] :
    (P ⊓ Q).ContainsIdentities where
  id_mem X := ⟨P.id_mem X, Q.id_mem X⟩
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.sInf** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：sInf {W : Set (MorphismProperty C)} (h : forall W' in W, W'.ContainsIdenti
ties) : (sInf W).ContainsIdentities where id_mem _
参数：MorphismProperty C；h : forall W' in W, W'.ContainsIdentities。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.MorphismProperty.sInf_iff`：sInf_iff (S : Set (MorphismPro
perty C)) {X Y : C} (f : X ⟶ Y) : sInf S f ↔ forall W in S, W f
· 使用定理 `CategoryTheory.MorphismProperty.ContainsIdentities.id_mem`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty
 C}   [self : W.ContainsIdentities] (X : C), W …
-/
lemma sInf {W : Set (MorphismProperty C)} (h : ∀ W' ∈ W, W'.ContainsIdentities) :
    (sInf W).ContainsIdentities where
  id_mem _ := (sInf_iff _ _).2 fun _ hW' ↦ (h _ hW').id_mem _
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.iInf** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：iInf {ι : Type*} {W : ι -> MorphismProperty C} [forall i, (W i).ContainsId
entities] : (⨅ i, W i).ContainsIdentities
参数：W i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用引理 `CategoryTheory.MorphismProperty.ContainsIdentities.sInf`：sInf {W : Set (
MorphismProperty C)} (h : forall W' in W, W'.ContainsIdentities) : (sInf W).Cont
ainsIdentities where id_mem _
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance iInf {ι : Type*} {W : ι → MorphismProperty C}
    [∀ i, (W i).ContainsIdentities] : (⨅ i, W i).ContainsIdentities := by
  rw [← sInf_range]
  exact sInf (by simpa)
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.iff_identities_le** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.ContainsIdentities`。
形式化陈述：iff_identities_le {W : MorphismProperty C} : W.ContainsIdentities ↔ identi
ties C <= W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.ContainsIdentities.id_mem`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty
 C}   [self : W.ContainsIdentities] (X : C), W …
-/
lemma iff_identities_le {W : MorphismProperty C} :
    W.ContainsIdentities ↔ identities C ≤ W :=
  ⟨fun _ ↦ by intro _ _ _ ⟨_⟩; exact id_mem _, fun h ↦ ⟨fun _ ↦ h _ ⟨_⟩⟩⟩
/-
**CategoryTheory.MorphismProperty.ContainsIdentities.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.ContainsIdentities`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (identities C).ContainsIdentities :=
  iff_identities_le.2 (by rfl)

end ContainsIdentities

/-
**CategoryTheory.MorphismProperty.Prod.containsIdentities** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MorphismProperty.Prod`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_
1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] (W₁ : CategoryTheory.M
orphismProperty C₁)   (W₂ : CategoryTheory.MorphismProperty C₂) [W₁.ContainsIden
tities] [W₂.ContainsIdentities],   (W₁.prod W₂).ContainsIdentities
参数：W₁ : CategoryTheory.MorphismProperty C₁；W₂ : CategoryTheory.MorphismProperty 
C₂；W₁.prod W₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
instance Prod.containsIdentities {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [W₁.ContainsIdentities] [W₂.ContainsIdentities] : (prod W₁ W₂).ContainsIdentities :=
  ⟨fun _ => ⟨W₁.id_mem _, W₂.id_mem _⟩⟩
/-
**CategoryTheory.MorphismProperty.Pi.containsIdentities** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MorphismProperty.Pi`。
形式化陈述：∀ {J : Type w} {C : J → Type u} [inst : (j : J) → CategoryTheory.Category.
{v, u} (C j)]   (W : (j : J) → CategoryTheory.MorphismProperty (C j)) [∀ (j : J)
, (W j).ContainsIdentities],   (CategoryTheory.MorphismProperty.pi W).ContainsId
entities
参数：j : J；C j；W : (j : J) → CategoryTheory.MorphismProperty (C j)；j : J；W j；Categ
oryTheory.MorphismProperty.pi W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
instance Pi.containsIdentities {J : Type w} {C : J → Type u}
    [∀ j, Category.{v} (C j)] (W : ∀ j, MorphismProperty (C j)) [∀ j, (W j).ContainsIdentities] :
    (pi W).ContainsIdentities :=
  ⟨fun _ _ => MorphismProperty.id_mem _ _⟩
/-
**CategoryTheory.MorphismProperty.of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：of_isIso (P : MorphismProperty C) [P.ContainsIdentities] [P.RespectsIso] {
X Y : C} (f : X ⟶ Y) [IsIso f] : P f
参数：P : MorphismProperty C；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.postcomp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [
P.RespectsIso]   {X Y Z : C} (e : Y ⟶ Z) […
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma of_isIso (P : MorphismProperty C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y)
    [IsIso f] : P f :=
  Category.id_comp f ▸ RespectsIso.postcomp P f (𝟙 X) (P.id_mem X)
/-
**CategoryTheory.MorphismProperty.isomorphisms_le_of_containsIdentities** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isomorphisms_le_of_containsIdentities (P : MorphismProperty C) [P.Contains
Identities] [P.RespectsIso] : isomorphisms C <= P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isIso`：of_isIso (P : MorphismProperty
 C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y) [IsIso f] : P f
-/
lemma isomorphisms_le_of_containsIdentities (P : MorphismProperty C) [P.ContainsIdentities]
    [P.RespectsIso] :
    isomorphisms C ≤ P := fun _ _ f (_ : IsIso f) ↦ P.of_isIso f

/-- A morphism property satisfies `IsStableUnderComposition` if the composition of
two such morphisms still falls in the class. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition** 是 Mathlib 中的一个归纳类型，
位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property satisfies `IsStableUnderComposition` if the composition of
two such morphisms still falls in the class.
-/
class IsStableUnderComposition (P : MorphismProperty C) : Prop where
  comp_mem {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) : P f → P g → P (f ≫ g)
/-
**CategoryTheory.MorphismProperty.comp_mem** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：comp_mem (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y Z : C}
 (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) : W (f ≫ g)
参数：W : MorphismProperty C；f : X ⟶ Y；g : Y ⟶ Z；hf : W f；hg : W g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morphism
Property C}   [self : P.IsStableUnderComposition] {X Y …
-/
lemma comp_mem (W : MorphismProperty C) [W.IsStableUnderComposition]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) : W (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g hf hg
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) (W : MorphismProperty C) [W.IsStableUnderComposition] :
    W.Respects W where
  precomp _ hi _ hf := W.comp_mem _ _ hi hf
  postcomp _ hi _ hf := W.comp_mem _ _ hf hi
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition.op** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderComposition`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [P.IsStableUnderComposition], P.op.IsStableUnderComposi
tion
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
-/
instance IsStableUnderComposition.op {P : MorphismProperty C} [P.IsStableUnderComposition] :
    P.op.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.unop f.unop hg hf
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition.unop** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderComposition`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty Cᵒᵖ}   [P.IsStableUnderComposition], P.unop.IsStableUnderCom
position
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
-/
instance IsStableUnderComposition.unop {P : MorphismProperty Cᵒᵖ} [P.IsStableUnderComposition] :
    P.unop.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.op f.op hg hf
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition.inf** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderComposition`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTh
eory.MorphismProperty C}   [P.IsStableUnderComposition] [Q.IsStableUnderComposit
ion], (P ⊓ Q).IsStableUnderComposition
参数：P ⊓ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance IsStableUnderComposition.inf {P Q : MorphismProperty C} [P.IsStableUnderComposition]
    [Q.IsStableUnderComposition] :
    (P ⊓ Q).IsStableUnderComposition where
  comp_mem f g hf hg := ⟨P.comp_mem f g hf.left hg.left, Q.comp_mem f g hf.right hg.right⟩
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition.sInf** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderComposition`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : Set (Categor
yTheory.MorphismProperty C)},   (∀ W' ∈ W, W'.IsStableUnderComposition) → (sInf 
W).IsStableUnderComposition
参数：CategoryTheory.MorphismProperty C；∀ W' ∈ W, W'.IsStableUnderComposition；sInf 
W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.sInf_iff`：sInf_iff (S : Set (MorphismPro
perty C)) {X Y : C} (f : X ⟶ Y) : sInf S f ↔ forall W in S, W f
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morphism
Property C}   [self : P.IsStableUnderComposition] {X Y …
-/
lemma IsStableUnderComposition.sInf {W : Set (MorphismProperty C)}
    (h : ∀ W' ∈ W, W'.IsStableUnderComposition) : (sInf W).IsStableUnderComposition where
  comp_mem f g hf hg := by
    rw [sInf_iff] at hf hg ⊢
    exact fun W' hW' ↦ (h W' hW').comp_mem _ _ (hf _ hW') (hg _ hW')
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition.iInf** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderComposition`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {W
 : ι → CategoryTheory.MorphismProperty C}   [∀ (i : ι), (W i).IsStableUnderCompo
sition], (⨅ i, W i).IsStableUnderComposition
参数：i : ι；W i；⨅ i, W i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.sInf`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {W : Set (CategoryTheory.Morphis
mProperty C)},   (∀ W' ∈ W, W'.IsStableUnderComposi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance IsStableUnderComposition.iInf {ι : Type*} {W : ι → MorphismProperty C}
    [∀ i, (W i).IsStableUnderComposition] : (⨅ i, W i).IsStableUnderComposition := by
  rw [← sInf_range]
  exact sInf (by simpa)

/-- A morphism property is `StableUnderInverse` if the inverse of a morphism satisfying
the property still falls in the class. -/
/-
**CategoryTheory.MorphismProperty.StableUnderInverse** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：StableUnderInverse (P : MorphismProperty C) : Prop
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property is `StableUnderInverse` if the inverse of a morphism satisfy
ing
the property still falls in the class.
-/
def StableUnderInverse (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y⦄ (e : X ≅ Y), P e.hom → P e.inv
/-
**CategoryTheory.MorphismProperty.StableUnderInverse.op** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MorphismProperty.StableUnderInverse`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C},   P.StableUnderInverse → P.op.StableUnderInverse
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StableUnderInverse.op {P : MorphismProperty C} (h : StableUnderInverse P) :
    StableUnderInverse P.op := fun _ _ e he => h e.unop he
/-
**CategoryTheory.MorphismProperty.StableUnderInverse.unop** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MorphismProperty.StableUnderInverse`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty Cᵒᵖ},   P.StableUnderInverse → P.unop.StableUnderInverse
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StableUnderInverse.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P) :
    StableUnderInverse P.unop := fun _ _ e he => h e.op he
/-
**CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：respectsIso_of_isStableUnderComposition {P : MorphismProperty C} [P.IsStab
leUnderComposition] (hP : isomorphisms C <= P) : RespectsIso P
参数：hP : isomorphisms C <= P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.isomorphisms.infer_property`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Catego
ryTheory.IsIso f],   CategoryTheory.MorphismPrope…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem respectsIso_of_isStableUnderComposition {P : MorphismProperty C}
    [P.IsStableUnderComposition] (hP : isomorphisms C ≤ P) :
    RespectsIso P := RespectsIso.mk _
  (fun _ _ hf => P.comp_mem _ _ (hP _ (isomorphisms.infer_property _)) hf)
    (fun _ _ hf => P.comp_mem _ _ hf (hP _ (isomorphisms.infer_property _)))
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition.inverseImage** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderComposition`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {P : CategoryTheory.MorphismPropert
y D} [P.IsStableUnderComposition] (F : CategoryTheory.Functor C D),   (P.inverse
Image F).IsStableUnderComposition
参数：F : CategoryTheory.Functor C D；P.inverseImage F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
-/
instance IsStableUnderComposition.inverseImage {P : MorphismProperty D} [P.IsStableUnderComposition]
    (F : C ⥤ D) : (P.inverseImage F).IsStableUnderComposition where
  comp_mem f g hf hg := by simpa only [← F.map_comp] using! P.comp_mem _ _ hf hg

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `MorphismProperty C` satisfied by the morphisms in `C` with respect
to which `app` is natural. -/
@[simp]
/-
**CategoryTheory.MorphismProperty.naturalityProperty** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：naturalityProperty {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X) :
 MorphismProperty C
参数：app : forall X, F₁.obj X ⟶ F₂.obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `MorphismProperty C` satisfied by the morphisms in `C` with respect
to which `app` is natural.
-/
def naturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C :=
  fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace naturalityProperty

/-
**CategoryTheory.MorphismProperty.naturalityProperty.isStableUnderComposition** 
是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty.naturalityProperty`。
形式化陈述：isStableUnderComposition {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.ob
j X) : (naturalityProperty app).IsStableUnderComposition where comp_mem f g hf h
g
参数：app : forall X, F₁.obj X ⟶ F₂.obj X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance isStableUnderComposition {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).IsStableUnderComposition where
  comp_mem f g hf hg := by
    simp only [naturalityProperty] at hf hg ⊢
    simp only [Functor.map_comp, Category.assoc, hg]
    slice_lhs 1 2 => rw [hf]
    rw [Category.assoc]
/-
**CategoryTheory.MorphismProperty.naturalityProperty.stableUnderInverse** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.naturalityProperty`。
形式化陈述：stableUnderInverse {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X) :
 (naturalityProperty app).StableUnderInverse
参数：app : forall X, F₁.obj X ⟶ F₂.obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stableUnderInverse {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).StableUnderInverse := fun X Y e he => by
  simp only [naturalityProperty] at he ⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [Category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp, e.hom_inv_id, Functor.map_id,
    Category.id_comp, Category.comp_id]

end naturalityProperty

/-- A morphism property is multiplicative if it contains identities and is stable by
composition. -/
/-
**CategoryTheory.MorphismProperty.IsMultiplicative** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property is multiplicative if it contains identities and is stable by
composition.
-/
class IsMultiplicative (W : MorphismProperty C) : Prop
    extends W.ContainsIdentities, W.IsStableUnderComposition

namespace IsMultiplicative

/-
**CategoryTheory.MorphismProperty.IsMultiplicative.op** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：op (W : MorphismProperty C) [IsMultiplicative W] : IsMultiplicative W.op w
here comp_mem f g hf hg
参数：W : MorphismProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
-/
instance op (W : MorphismProperty C) [IsMultiplicative W] : IsMultiplicative W.op where
  comp_mem f g hf hg := W.comp_mem g.unop f.unop hg hf
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.unop** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W] : IsMultiplicative W.
unop where id_mem _
参数：W : MorphismProperty Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
-/
instance unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W] : IsMultiplicative W.unop where
  id_mem _ := W.id_mem _
  comp_mem f g hf hg := W.comp_mem g.op f.op hg hf
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.of_op** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：of_op (W : MorphismProperty C) [IsMultiplicative W.op] : IsMultiplicative 
W
参数：W : MorphismProperty C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_op (W : MorphismProperty C) [IsMultiplicative W.op] : IsMultiplicative W :=
  inferInstanceAs <| IsMultiplicative W.op.unop
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.of_unop** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：of_unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W.unop] : IsMultiplic
ative W
参数：W : MorphismProperty Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W.unop] : IsMultiplicative W :=
  inferInstanceAs <| IsMultiplicative W.unop.op
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.MorphismProperty.IsMultiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative (⊤ : MorphismProperty C) where
  comp_mem _ _ _ _ := trivial
  id_mem _ := trivial
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.MorphismProperty.IsMultiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isomorphisms C).IsMultiplicative where
  id_mem _ := isomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [isomorphisms.iff] at hf hg ⊢
    infer_instance
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.MorphismProperty.IsMultiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (monomorphisms C).IsMultiplicative where
  id_mem _ := monomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [monomorphisms.iff] at hf hg ⊢
    apply mono_comp
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.MorphismProperty.IsMultiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (epimorphisms C).IsMultiplicative where
  id_mem _ := epimorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [epimorphisms.iff] at hf hg ⊢
    apply epi_comp
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.MorphismProperty.IsMultiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (identities C).IsMultiplicative where
  comp_mem := by
    rintro _ _ _ _ _ ⟨_⟩ ⟨_⟩
    simp only [Category.comp_id]
    constructor
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.MorphismProperty.IsMultiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : MorphismProperty D} [P.IsMultiplicative] (F : C ⥤ D) :
    (P.inverseImage F).IsMultiplicative where
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.inf** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTh
eory.MorphismProperty C} [P.IsMultiplicative]   [Q.IsMultiplicative], (P ⊓ Q).Is
Multiplicative
参数：P ⊓ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.inf`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismPro
perty C}   [P.IsStableUnderComposition] [Q.IsStabl…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
-/
instance inf {P Q : MorphismProperty C} [P.IsMultiplicative] [Q.IsMultiplicative] :
    (P ⊓ Q).IsMultiplicative where
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.sInf** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：sInf {W : Set (MorphismProperty C)} (h : forall W' in W, W'.IsMultiplicati
ve) : (sInf W).IsMultiplicative
参数：MorphismProperty C；h : forall W' in W, W'.IsMultiplicative。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ContainsIdentities.sInf`：sInf {W : Set (
MorphismProperty C)} (h : forall W' in W, W'.ContainsIdentities) : (sInf W).Cont
ainsIdentities where id_mem _
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.sInf`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {W : Set (CategoryTheory.Morphis
mProperty C)},   (∀ W' ∈ W, W'.IsStableUnderComposi…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
-/
lemma sInf {W : Set (MorphismProperty C)} (h : ∀ W' ∈ W, W'.IsMultiplicative) :
    (sInf W).IsMultiplicative := by
  have := ContainsIdentities.sInf (fun W' hW' ↦ (h W' hW').toContainsIdentities)
  have := IsStableUnderComposition.sInf (fun W' hW' ↦ (h W' hW').toIsStableUnderComposition)
  constructor
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.iInf** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：iInf {ι : Type*} {W : ι -> MorphismProperty C} [forall i, (W i).IsMultipli
cative] : (⨅ i, W i).IsMultiplicative
参数：W i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用引理 `CategoryTheory.MorphismProperty.IsMultiplicative.sInf`：sInf {W : Set (Mo
rphismProperty C)} (h : forall W' in W, W'.IsMultiplicative) : (sInf W).IsMultip
licative
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance iInf {ι : Type*} {W : ι → MorphismProperty C}
    [∀ i, (W i).IsMultiplicative] : (⨅ i, W i).IsMultiplicative := by
  rw [← sInf_range]
  exact sInf (by simpa)
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.naturalityProperty** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：naturalityProperty {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X) :
 (naturalityProperty app).IsMultiplicative where id_mem _
参数：app : forall X, F₁.obj X ⟶ F₂.obj X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance naturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).IsMultiplicative where
  id_mem _ := by simp

end IsMultiplicative

/-- Given a morphism property `W`, the `multiplicativeClosure W` is the smallest
multiplicative property greater than or equal to `W`. -/
/-
**CategoryTheory.MorphismProperty.multiplicativeClosure** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.MorphismProperty C → CategoryTheory.MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism property `W`, the `multiplicativeClosure W` is the smallest
multiplicative property greater than or equal to `W`.
-/
inductive multiplicativeClosure (W : MorphismProperty C) : MorphismProperty C
  | of {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure W f
  | id (x : C) : multiplicativeClosure W (𝟙 x)
  | comp_of {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : multiplicativeClosure W f) (hg : W g) :
    multiplicativeClosure W (f ≫ g)

/-- A variant of `multiplicativeClosure` in which compositions are taken on the left rather than
on the right. It is not intended to be used directly, and one should rather access this via
`multiplicativeClosure_eq_multiplicativeClosure'` in cases where the inductive principle of this
variant is needed. -/
/-
**CategoryTheory.MorphismProperty.multiplicativeClosure'** 是 Mathlib 中的一个归纳类型，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.MorphismProperty C → CategoryTheory.MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `multiplicativeClosure` in which compositions are taken on the left
 rather than
on the right. It is not intended to be used directly, and one should rather acce
ss this via
`multiplicativeClosure_eq_multiplicativeClosure'` in cases where the inductive p
rinciple of this
variant is needed.
-/
inductive multiplicativeClosure' (W : MorphismProperty C) : MorphismProperty C
  | of {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure' W f
  | id (x : C) : multiplicativeClosure' W (𝟙 x)
  | of_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : W f) (hg : multiplicativeClosure' W g) :
    multiplicativeClosure' W (f ≫ g)

variable (W : MorphismProperty C)

/-- `multiplicativeClosure W` is multiplicative. -/
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`multiplicativeClosure W` is multiplicative.
-/
instance : IsMultiplicative W.multiplicativeClosure where
  id_mem x := .id x
  comp_mem f g hf hg := by
    induction hg with
    | of _ hf₀ => exact .comp_of f _ hf hf₀
    | id _ => rwa [Category.comp_id]
    | comp_of f' g hf' hg h_rec =>
      rw [← Category.assoc]
      exact .comp_of (f ≫ f') g (h_rec f hf) hg

/-- `multiplicativeClosure' W` is multiplicative. -/
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`multiplicativeClosure' W` is multiplicative.
-/
instance : IsMultiplicative W.multiplicativeClosure' where
  id_mem x := .id x
  comp_mem f g hf hg := by
    induction hf with
    | of _ h => exact .of_comp _ g h hg
    | id _ => rwa [Category.id_comp]
    | of_comp g' f hg' hf h_rec =>
      rw [Category.assoc]
      exact .of_comp g' (f ≫ g) hg' (h_rec g hg)

/-- The multiplicative closure is greater than or equal to the original property. -/
/-
**CategoryTheory.MorphismProperty.le_multiplicativeClosure** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：le_multiplicativeClosure : W <= W.multiplicativeClosure
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative closure is greater than or equal to the original property.
-/
lemma le_multiplicativeClosure : W ≤ W.multiplicativeClosure := fun {_ _} _ hf ↦ .of _ hf

/-- The multiplicative closure of a multiplicative property is equal to itself. -/
@[simp]
/-
**CategoryTheory.MorphismProperty.multiplicativeClosure_eq_self** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：multiplicativeClosure_eq_self [W.IsMultiplicative] : W.multiplicativeClosu
re = W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用引理 `CategoryTheory.MorphismProperty.le_multiplicativeClosure`：le_multiplicat
iveClosure : W <= W.multiplicativeClosure

--- 原说明 ---
The multiplicative closure of a multiplicative property is equal to itself.
-/
lemma multiplicativeClosure_eq_self [W.IsMultiplicative] : W.multiplicativeClosure = W := by
  apply le_antisymm _ <| le_multiplicativeClosure W
  intro _ _ _ hf
  induction hf with
  | of _ hf₀ => exact hf₀
  | id x => exact W.id_mem x
  | comp_of _ _ _ hg hf => exact W.comp_mem _ _ hf hg
/-
**CategoryTheory.MorphismProperty.multiplicativeClosure_eq_self_iff** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：multiplicativeClosure_eq_self_iff : W.multiplicativeClosure = W ↔ W.IsMult
iplicative where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeMultiplicativeClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.
MorphismProperty C),   W.multiplicativeClosure.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.multiplicativeClosure_eq_self`：multiplic
ativeClosure_eq_self [W.IsMultiplicative] : W.multiplicativeClosure = W
-/
lemma multiplicativeClosure_eq_self_iff : W.multiplicativeClosure = W ↔ W.IsMultiplicative where
  mp h := by
    rw [← h]
    infer_instance
  mpr h := multiplicativeClosure_eq_self W

/-- The multiplicative closure of `W` is the smallest multiplicative property greater than or equal
to `W`. -/
@[simp]
/-
**CategoryTheory.MorphismProperty.multiplicativeClosure_le_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：multiplicativeClosure_le_iff (W' : MorphismProperty C) [W'.IsMultiplicativ
e] : multiplicativeClosure W <= W' ↔ W <= W' where .trans h mp h
参数：W' : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.MorphismProperty.le_multiplicativeClosure`：le_multiplicat
iveClosure : W <= W.multiplicativeClosure
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…

--- 原说明 ---
The multiplicative closure of `W` is the smallest multiplicative property greate
r than or equal
to `W`.
-/
lemma multiplicativeClosure_le_iff (W' : MorphismProperty C) [W'.IsMultiplicative] :
    multiplicativeClosure W ≤ W' ↔ W ≤ W' where
  mp h := le_multiplicativeClosure W |>.trans h
  mpr h := by
    intro _ _ _ hf
    induction hf with
    | of _ hf => exact h _ hf
    | id x => exact W'.id_mem _
    | comp_of _ _ _ hg hf => exact W'.comp_mem _ _ hf (h _ hg)
/-
**CategoryTheory.MorphismProperty.multiplicativeClosure_monotone** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：multiplicativeClosure_monotone : Monotone (multiplicativeClosure (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeMultiplicativeClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.
MorphismProperty C),   W.multiplicativeClosure.IsMultiplicative
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.MorphismProperty.le_multiplicativeClosure`：le_multiplicat
iveClosure : W <= W.multiplicativeClosure
-/
lemma multiplicativeClosure_monotone :
    Monotone (multiplicativeClosure (C := C)) :=
  fun _ W' h ↦ by simpa using h.trans W'.le_multiplicativeClosure
/-
**CategoryTheory.MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure
'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：multiplicativeClosure_eq_multiplicativeClosure' : W.multiplicativeClosure 
= W.multiplicativeClosure'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.MorphismProperty.multiplicativeClosure_le_iff`：multiplica
tiveClosure_le_iff (W' : MorphismProperty C) [W'.IsMultiplicative] : multiplicat
iveClosure W <= W' ↔ W <= W' where .trans h mp h
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeMultiplicativeClosur
e'`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory
.MorphismProperty C),   W.multiplicativeClosure'.IsMultiplicativ…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeMultiplicativeClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.
MorphismProperty C),   W.multiplicativeClosure.IsMultiplicative
-/
lemma multiplicativeClosure_eq_multiplicativeClosure' :
    W.multiplicativeClosure = W.multiplicativeClosure' :=
  le_antisymm
    ((multiplicativeClosure_le_iff _ _).mpr (fun _ _ f hf ↦ .of f hf)) <|
    fun x y f hf ↦ by induction hf with
      | of _ h => exact .of _ h
      | id x => exact .id x
      | of_comp f g hf hg hr => exact W.multiplicativeClosure.comp_mem f g (.of f hf) hr
/-
**CategoryTheory.MorphismProperty.strictMap_multiplicativeClosure_le** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：strictMap_multiplicativeClosure_le (F : C ⥤ D) : W.multiplicativeClosure.s
trictMap F <= (W.strictMap F).multiplicativeClosure
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.le_multiplicativeClosure`：le_multiplicat
iveClosure : W <= W.multiplicativeClosure
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma strictMap_multiplicativeClosure_le (F : C ⥤ D) :
    W.multiplicativeClosure.strictMap F ≤ (W.strictMap F).multiplicativeClosure := by
  intro _ _ f hf
  induction hf with | map hf
  induction hf with
  | of f hf => exact le_multiplicativeClosure _ _ ⟨hf⟩
  | id x => simpa using .id (F.obj x)
  | comp_of _ _ hf hg h =>
    simpa using multiplicativeClosure.comp_of _ _ h (strictMap.map hg)

/-- A class of morphisms `W` has the of-postcomp property w.r.t. `W'` if whenever
`g` is in `W'` and `f ≫ g` is in `W`, also `f` is in `W`. -/
/-
**CategoryTheory.MorphismProperty.HasOfPostcompProperty** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of morphisms `W` has the of-postcomp property w.r.t. `W'` if whenever
`g` is in `W'` and `f ≫ g` is in `W`, also `f` is in `W`.
-/
class HasOfPostcompProperty (W W' : MorphismProperty C) : Prop where
  of_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W' g → W (f ≫ g) → W f

/-- A class of morphisms `W` has the of-precomp property w.r.t. `W'` if whenever
`f` is in `W'` and `f ≫ g` is in `W`, also `g` is in `W`. -/
/-
**CategoryTheory.MorphismProperty.HasOfPrecompProperty** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of morphisms `W` has the of-precomp property w.r.t. `W'` if whenever
`f` is in `W'` and `f ≫ g` is in `W`, also `g` is in `W`.
-/
class HasOfPrecompProperty (W W' : MorphismProperty C) : Prop where
  of_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W' f → W (f ≫ g) → W g

/-- A class of morphisms `W` has the two-out-of-three property if whenever two out
of three maps in `f`, `g`, `f ≫ g` are in `W`, then the third map is also in `W`. -/
/-
**CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty** 是 Mathlib 中的一个归纳类型，
位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of morphisms `W` has the two-out-of-three property if whenever two out
of three maps in `f`, `g`, `f ≫ g` are in `W`, then the third map is also in `W`
.
-/
class HasTwoOutOfThreeProperty (W : MorphismProperty C) : Prop
    extends W.IsStableUnderComposition, W.HasOfPostcompProperty W, W.HasOfPrecompProperty W where

section

variable (W W' : MorphismProperty C) {W'}

/-
**CategoryTheory.MorphismProperty.of_postcomp** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：of_postcomp [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ 
Z) (hg : W' g) (hfg : W (f ≫ g)) : W f
参数：f : X ⟶ Y；g : Y ⟶ Z；hg : W' g；hfg : W (f ≫ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasOfPostcompProperty.of_postcomp`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {W W' : CategoryTheory.Morph
ismProperty C}   [self : W.HasOfPostcompProperty W'] {X…
-/
lemma of_postcomp [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g)
    (hfg : W (f ≫ g)) : W f :=
  HasOfPostcompProperty.of_postcomp f g hg hfg
/-
**CategoryTheory.MorphismProperty.of_precomp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：of_precomp [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
 (hf : W' f) (hfg : W (f ≫ g)) : W g
参数：f : X ⟶ Y；g : Y ⟶ Z；hf : W' f；hfg : W (f ≫ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasOfPrecompProperty.of_precomp`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} {W W' : CategoryTheory.Morphis
mProperty C}   [self : W.HasOfPrecompProperty W'] {X …
-/
lemma of_precomp [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
    (hfg : W (f ≫ g)) : W g :=
  HasOfPrecompProperty.of_precomp f g hf hfg
/-
**CategoryTheory.MorphismProperty.postcomp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：postcomp_iff [W.RespectsRight W'] [W.HasOfPostcompProperty W'] {X Y Z : C}
 (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) : W (f ≫ g) ↔ W f
参数：f : X ⟶ Y；g : Y ⟶ Z；hg : W' g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.postcomp`：∀ {C : Type u} {
inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPro
perty C}   [self : P.RespectsRight Q] {X Y Z…
-/
lemma postcomp_iff [W.RespectsRight W'] [W.HasOfPostcompProperty W']
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) : W (f ≫ g) ↔ W f :=
  ⟨W.of_postcomp f g hg, fun hf ↦ RespectsRight.postcomp _ hg _ hf⟩
/-
**CategoryTheory.MorphismProperty.precomp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：precomp_iff [W.RespectsLeft W'] [W.HasOfPrecompProperty W'] {X Y Z : C} (f
 : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) : W (f ≫ g) ↔ W g
参数：f : X ⟶ Y；g : Y ⟶ Z；hf : W' f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_precomp`：of_precomp [W.HasOfPrecompPr
operty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) (hfg : W (f ≫ g)) : W
 g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.precomp`：∀ {C : Type u} {in
st : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPrope
rty C}   [self : P.RespectsLeft Q] {X Y Z …
-/
lemma precomp_iff [W.RespectsLeft W'] [W.HasOfPrecompProperty W']
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) :
    W (f ≫ g) ↔ W g :=
  ⟨W.of_precomp f g hf, fun hg ↦ RespectsLeft.precomp _ hf _ hg⟩
/-
**CategoryTheory.MorphismProperty.HasOfPostcompProperty.of_le** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MorphismProperty.HasOfPostcompProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheo
ry.MorphismProperty C)   {W' : CategoryTheory.MorphismProperty C} (Q : CategoryT
heory.MorphismProperty C) [W.HasOfPostcompProperty Q],   W' ≤ Q → W.HasOfPostcom
pProperty W'
参数：W : CategoryTheory.MorphismProperty C；Q : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
-/
lemma HasOfPostcompProperty.of_le (Q : MorphismProperty C) [W.HasOfPostcompProperty Q]
    (hle : W' ≤ Q) : W.HasOfPostcompProperty W' where
  of_postcomp f g hg hfg := W.of_postcomp (W' := Q) f g (hle _ hg) hfg
/-
**CategoryTheory.MorphismProperty.HasOfPrecompProperty.of_le** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MorphismProperty.HasOfPrecompProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheo
ry.MorphismProperty C)   {W' : CategoryTheory.MorphismProperty C} (Q : CategoryT
heory.MorphismProperty C) [W.HasOfPrecompProperty Q],   W' ≤ Q → W.HasOfPrecompP
roperty W'
参数：W : CategoryTheory.MorphismProperty C；Q : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_precomp`：of_precomp [W.HasOfPrecompPr
operty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) (hfg : W (f ≫ g)) : W
 g
-/
lemma HasOfPrecompProperty.of_le (Q : MorphismProperty C) [W.HasOfPrecompProperty Q]
    (hle : W' ≤ Q) : W.HasOfPrecompProperty W' where
  of_precomp f g hg hfg := W.of_precomp (W' := Q) f g (hle _ hg) hfg
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.HasOfPostcompProperty W'] : W.op.HasOfPrecompProperty W'.op where
  of_precomp _ _ hf hfg := W.of_postcomp _ _ hf hfg
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.HasOfPrecompProperty W'] : W.op.HasOfPostcompProperty W'.op where
  of_postcomp _ _ hg hfg := W.of_precomp _ _ hg hfg
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.HasTwoOutOfThreeProperty] : W.op.HasTwoOutOfThreeProperty where
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : MorphismProperty C).HasOfPostcompProperty W where
  of_postcomp _ _ _ _ := trivial
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : MorphismProperty C).HasOfPrecompProperty W where
  of_precomp _ _ _ _ := trivial
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊤ : MorphismProperty C).HasTwoOutOfThreeProperty where

variable (P Q : MorphismProperty C)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.HasOfPostcompProperty W] [Q.HasOfPostcompProperty W] :
    (P ⊓ Q).HasOfPostcompProperty W where
  of_postcomp f g hg hfg := ⟨P.of_postcomp f g hg hfg.1, Q.of_postcomp f g hg hfg.2⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.HasOfPrecompProperty W] [Q.HasOfPrecompProperty W] :
    (P ⊓ Q).HasOfPrecompProperty W where
  of_precomp f g hg hfg := ⟨P.of_precomp f g hg hfg.1, Q.of_precomp f g hg hfg.2⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.HasTwoOutOfThreeProperty] [Q.HasTwoOutOfThreeProperty] :
    (P ⊓ Q).HasTwoOutOfThreeProperty := by
  have : P.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : P.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : Q.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  have : Q.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  constructor

end

section

variable (W₁ W₂ : MorphismProperty Cᵒᵖ)

/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W₁.HasOfPostcompProperty W₂] : W₁.unop.HasOfPrecompProperty W₂.unop where
  of_precomp _ _ hf hfg := W₁.of_postcomp _ _ hf hfg
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W₁.HasOfPrecompProperty W₂] : W₁.unop.HasOfPostcompProperty W₂.unop where
  of_postcomp _ _ hg hfg := W₁.of_precomp _ _ hg hfg
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W₁.HasTwoOutOfThreeProperty] : W₁.unop.HasTwoOutOfThreeProperty where

end

/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isomorphisms C).HasTwoOutOfThreeProperty where
  of_postcomp f g := fun (hg : IsIso g) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso ((f ≫ g) ≫ inv g))
  of_precomp f g := fun (hf : IsIso f) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso (inv f ≫ (f ≫ g)))
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty] :
    (W.inverseImage F).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := W.of_postcomp (F.map f) (F.map g) hg (by simpa using hfg)
  of_precomp f g hf hfg := W.of_precomp (F.map f) (F.map g) hf (by simpa using hfg)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.RespectsIso] : W.HasOfPrecompProperty (isomorphisms C) where
  of_precomp _ _ (_ : IsIso _) := (W.cancel_left_of_respectsIso _ _).mp
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.RespectsIso] : W.HasOfPostcompProperty (isomorphisms C) where
  of_postcomp _ _ (_ : IsIso _) := (W.cancel_right_of_respectsIso _ _).mp

end MorphismProperty

end CategoryTheory

