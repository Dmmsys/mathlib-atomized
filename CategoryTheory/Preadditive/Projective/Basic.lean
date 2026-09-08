/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Projective objects and categories with enough projectives

An object `P` is called *projective* if every morphism out of `P` factors through every epimorphism.

A category `C` *has enough projectives* if every object admits an epimorphism from some
projective object.

`CategoryTheory.Projective.over X` picks an arbitrary such projective object, and
`CategoryTheory.Projective.π X : CategoryTheory.Projective.over X ⟶ X` is the corresponding
epimorphism.

Given a morphism `f : X ⟶ Y`, `CategoryTheory.Projective.left f` is a projective object over
`CategoryTheory.Limits.kernel f`, and `Projective.d f : Projective.left f ⟶ X` is the morphism
`π (kernel f) ≫ kernel.ι f`.

-/

@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/--
An object `P` is called *projective* if every morphism out of `P` factors through every epimorphism.
-/
/-
**CategoryTheory.Projective** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [CategoryTheory.Category.{v, u} C] → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `P` is called *projective* if every morphism out of `P` factors throug
h every epimorphism.
-/
class Projective (P : C) : Prop where
  factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [Epi e], ∃ f', f' ≫ e = f

variable (C) in
/-- The `ObjectProperty C` corresponding to the notion of projective objects in `C`. -/
/-
**CategoryTheory.isProjective** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：isProjective : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ObjectProperty C` corresponding to the notion of projective objects in `C`.
-/
abbrev isProjective : ObjectProperty C := Projective
/-
**CategoryTheory.Limits.IsZero.projective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.IsZero`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C},   Catego
ryTheory.Limits.IsZero X → CategoryTheory.Projective X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
lemma Limits.IsZero.projective {X : C} (h : IsZero X) : Projective X where
  factors _ _ _ := ⟨h.to_ _, h.eq_of_src _ _⟩

section

/-- A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
/-
**CategoryTheory.ProjectivePresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory`。
形式化陈述：{C : Type u} → [CategoryTheory.Category.{v, u} C] → C → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X
`
from some projective object `P`.
-/
structure ProjectivePresentation (X : C) where
  /-- The projective object `p` of this presentation -/
  p : C
  [projective : Projective p]
  /-- The epimorphism from `p` of this presentation -/
  f : p ⟶ X
  [epi : Epi f]

attribute [instance] ProjectivePresentation.projective ProjectivePresentation.epi

variable (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
an epimorphism `P ↠ X`. -/
/-
**CategoryTheory.EnoughProjectives** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category "has enough projectives" if for every object `X` there is a projectiv
e object `P` and
an epimorphism `P ↠ X`.
-/
class EnoughProjectives : Prop where
  presentation : ∀ X : C, Nonempty (ProjectivePresentation X)

attribute [instance low] EnoughProjectives.presentation

end

namespace Projective

/--
An arbitrarily chosen factorisation of a morphism out of a projective object through an epimorphism.
-/
/-
**CategoryTheory.Projective.factorThru** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Projective`。
形式化陈述：factorThru {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : P 
⟶ E
参数：f : P ⟶ X；e : E ⟶ X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.factors`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {P : C} [self : CategoryTheory.Projective P] {E X : C}   (f 
: P ⟶ X) (e : E ⟶ X) [C…

--- 原说明 ---
An arbitrarily chosen factorisation of a morphism out of a projective object thr
ough an epimorphism.
-/
def factorThru {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : P ⟶ E :=
  (Projective.factors f e).choose

@[reassoc (attr := simp)]
/-
**CategoryTheory.Projective.factorThru_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Projective`。
形式化陈述：factorThru_comp {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e]
 : factorThru f e ≫ e = f
参数：f : P ⟶ X；e : E ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.Projective.factors`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {P : C} [self : CategoryTheory.Projective P] {E X : C}   (f 
: P ⟶ X) (e : E ⟶ X) [C…
-/
theorem factorThru_comp {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] :
    factorThru f e ≫ e = f :=
  (Projective.factors f e).choose_spec

section

open ZeroObject

/-
**CategoryTheory.Projective.zero_projective** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Projective`。
形式化陈述：zero_projective [HasZeroObject C] : Projective (0 : C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.projective`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → CategoryTh
eory.Projective X
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
instance zero_projective [HasZeroObject C] : Projective (0 : C) :=
  (isZero_zero C).projective

end

/-
**CategoryTheory.Projective.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pro
jective`。
形式化陈述：of_iso {P Q : C} (i : P ≅ Q) (_ : Projective P) : Projective Q where facto
rs f e _
参数：i : P ≅ Q；_ : Projective P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.factors`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {P : C} [self : CategoryTheory.Projective P] {E X : C}   (f 
: P ⟶ X) (e : E ⟶ X) [C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_iso {P Q : C} (i : P ≅ Q) (_ : Projective P) : Projective Q where
  factors f e _ :=
    let ⟨f', hf'⟩ := Projective.factors (i.hom ≫ f) e
    ⟨i.inv ≫ f', by simp [hf']⟩
/-
**CategoryTheory.Projective.iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pr
ojective`。
形式化陈述：iso_iff {P Q : C} (i : P ≅ Q) : Projective P ↔ Projective Q
参数：i : P ≅ Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.of_iso`：of_iso {P Q : C} (i : P ≅ Q) (_ : Proj
ective P) : Projective Q where factors f e _
-/
theorem iso_iff {P Q : C} (i : P ≅ Q) : Projective P ↔ Projective Q :=
  ⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every type is a projective object in `Type`. -/
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The axiom of choice says that every type is a projective object in `Type`.
-/
instance (X : Type u) : Projective X where
  factors f e _ :=
    have he : Function.Surjective e := surjective_of_epi e
    ⟨↾fun x => (he (f x)).choose, by ext x; exact (he (f x)).choose_spec⟩
/-
**CategoryTheory.Projective.Type.enoughProjectives** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Projective.Type`。
形式化陈述：CategoryTheory.EnoughProjectives (Type u)
参数：Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.inst`：∀ (X : Type u), CategoryTheory.Projectiv
e X
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
-/
instance Type.enoughProjectives : EnoughProjectives (Type u) where
  presentation X := ⟨⟨X, 𝟙 X⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : C} [HasBinaryCoproduct P Q] [Projective P] [Projective Q] : Projective (P ⨿ Q) where
  factors f e epi := ⟨coprod.desc (factorThru (coprod.inl ≫ f) e) (factorThru (coprod.inr ≫ f) e),
    by cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type v} (g : β → C) [HasCoproduct g] [∀ b, Projective (g b)] : Projective (∐ g) where
  factors f e epi := ⟨Sigma.desc fun b => factorThru (Sigma.ι g b ≫ f) e, by cat_disch⟩
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Projective P] [Projective Q] :
    Projective (P ⊞ Q) where
  factors f e epi := ⟨biprod.desc (factorThru (biprod.inl ≫ f) e) (factorThru (biprod.inr ≫ f) e),
    by cat_disch⟩
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type v} (g : β → C) [HasZeroMorphisms C] [HasBiproduct g] [∀ b, Projective (g b)] :
    Projective (⨁ g) where
  factors f e epi := ⟨biproduct.desc fun b => factorThru (biproduct.ι g b ≫ f) e, by cat_disch⟩
/-
**CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_obj** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Projective`。
形式化陈述：projective_iff_preservesEpimorphisms_coyoneda_obj (P : C) : Projective P ↔
 (coyoneda.obj (op P)).PreservesEpimorphisms
参数：P : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.Projective.factorThru_comp`：factorThru_comp {P X E : C} [
Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : factorThru f e ≫ e = f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem projective_iff_preservesEpimorphisms_coyoneda_obj (P : C) :
    Projective P ↔ (coyoneda.obj (op P)).PreservesEpimorphisms :=
  ⟨fun hP =>
    ⟨fun f _ =>
      (epi_iff_surjective _).2 fun g =>
        have : Projective (unop (op P)) := hP
        ⟨factorThru g f, factorThru_comp _ _⟩⟩,
    fun _ =>
    ⟨fun f e _ =>
      (epi_iff_surjective _).1 (inferInstance : Epi ((coyoneda.obj (op P)).map e)) f⟩⟩

section EnoughProjectives

variable [EnoughProjectives C]

/-- `Projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `Projective.π : Projective.over X ⟶ X`.
-/
/-
**CategoryTheory.Projective.over** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Proje
ctive`。
形式化陈述：over (X : C) : C
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnoughProjectives.presentation`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.EnoughProjectives C] (X :
 C),   Nonempty (CategoryTheory.Pro…

--- 原说明 ---
`Projective.over X` provides an arbitrarily chosen projective object equipped wi
th
an epimorphism `Projective.π : Projective.over X ⟶ X`.
-/
def over (X : C) : C :=
  (EnoughProjectives.presentation X).some.p
/-
**CategoryTheory.Projective.projective_over** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Projective`。
形式化陈述：projective_over (X : C) : Projective (over X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ProjectivePresentation.projective`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X : C} (self : CategoryTheory.ProjectivePres
entation X),   CategoryTheory.Projecti…
· 使用定理 `CategoryTheory.EnoughProjectives.presentation`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.EnoughProjectives C] (X :
 C),   Nonempty (CategoryTheory.Pro…
-/
instance projective_over (X : C) : Projective (over X) :=
  (EnoughProjectives.presentation X).some.projective

/-- The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
  (EnoughProjectives.presentation X).some.f
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance π_epi (X : C) : Epi (π X) :=
  (EnoughProjectives.presentation X).some.epi

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f]

/-- When `C` has enough projectives, the object `Projective.syzygies f` is
an arbitrarily chosen projective object over `kernel f`.
-/
/-
**CategoryTheory.Projective.syzygies** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
rojective`。
形式化陈述：syzygies : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` has enough projectives, the object `Projective.syzygies f` is
an arbitrarily chosen projective object over `kernel f`.
-/
def syzygies : C := over (kernel f)
/-
**CategoryTheory.Projective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Projectiv
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Projective (syzygies f) := inferInstanceAs (Projective (over _))

/-- When `C` has enough projectives,
`Projective.d f : Projective.syzygies f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.

(When `C` is abelian, we have `exact (projective.d f) f`.)
-/
/-
**CategoryTheory.Projective.d** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Projec
tive`。
形式化陈述：d : syzygies f ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` has enough projectives,
`Projective.d f : Projective.syzygies f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.

(When `C` is abelian, we have `exact (projective.d f) f`.)
-/
abbrev d : syzygies f ⟶ X :=
  π (kernel f) ≫ kernel.ι f

end

end EnoughProjectives

end Projective

namespace Adjunction

variable {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.map_projective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Adjunction`。
形式化陈述：map_projective (adj : F ⊣ G) [G.PreservesEpimorphisms] (P : C) (hP : Proje
ctive P) : Projective (F.obj P) where factors f g _
参数：adj : F ⊣ G；P : C；hP : Projective P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.factors`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {P : C} [self : CategoryTheory.Projective P] {E X : C}   (f 
: P ⟶ X) (e : E ⟶ X) [C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_projective (adj : F ⊣ G) [G.PreservesEpimorphisms] (P : C) (hP : Projective P) :
    Projective (F.obj P) where
  factors f g _ := by
    rcases hP.factors (adj.unit.app P ≫ G.map f) (G.map g) with ⟨f', hf'⟩
    use F.map f' ≫ adj.counit.app _
    rw [Category.assoc, ← Adjunction.counit_naturality, ← Category.assoc, ← F.map_comp, hf']
    simp
/-
**CategoryTheory.Adjunction.projective_of_map_projective** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：projective_of_map_projective (adj : F ⊣ G) [F.Full] [F.Faithful] (P : C) (
hP : Projective (F.obj P)) : Projective P where factors f g _
参数：adj : F ⊣ G；P : C；hP : Projective (F.obj P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `CategoryTheory.Projective.factors`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {P : C} [self : CategoryTheory.Projective P] {E X : C}   (f 
: P ⟶ X) (e : E ⟶ X) [C…
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize0.preservesFiniteColimits`：
∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_
1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Adjunction.inv_map_unit`：inv_map_unit {X : C} [IsIso (h.u
nit.app X)] : inv (L.map (h.unit.app X)) = h.counit.app (L.obj X)
· 使用定理 `CategoryTheory.Adjunction.counit_naturality_assoc`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem projective_of_map_projective (adj : F ⊣ G) [F.Full] [F.Faithful] (P : C)
    (hP : Projective (F.obj P)) : Projective P where
  factors f g _ := by
    have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj
    rcases (@hP).1 (F.map f) (F.map g) with ⟨f', hf'⟩
    use adj.unit.app _ ≫ G.map f' ≫ (inv <| adj.unit.app _)
    exact F.map_injective (by simpa)

/-- Given an adjunction `F ⊣ G` such that `G` preserves epis, `F` maps a projective presentation of
`X` to a projective presentation of `F(X)`. -/
/-
**CategoryTheory.Adjunction.mapProjectivePresentation** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：mapProjectivePresentation (adj : F ⊣ G) [G.PreservesEpimorphisms] (X : C) 
(Y : ProjectivePresentation X) : ProjectivePresentation (F.obj X) where p
参数：adj : F ⊣ G；X : C；Y : ProjectivePresentation X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `F ⊣ G` such that `G` preserves epis, `F` maps a projective 
presentation of
`X` to a projective presentation of `F(X)`.
-/
def mapProjectivePresentation (adj : F ⊣ G) [G.PreservesEpimorphisms] (X : C)
    (Y : ProjectivePresentation X) : ProjectivePresentation (F.obj X) where
  p := F.obj Y.p
  projective := adj.map_projective _ Y.projective
  f := F.map Y.f
  epi := have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj; inferInstance

end Adjunction

namespace Functor

variable {D : Type*} [Category* D] (F : C ⥤ D)

/-
**CategoryTheory.Functor.projective_of_map_projective** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：projective_of_map_projective [F.Full] [F.Faithful] [F.PreservesEpimorphism
s] {P : C} (hP : Projective (F.obj P)) : Projective P where factors g f _
参数：hP : Projective (F.obj P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.factors`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {P : C} [self : CategoryTheory.Projective P] {E X : C}   (f 
: P ⟶ X) (e : E ⟶ X) [C…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projective_of_map_projective [F.Full] [F.Faithful]
    [F.PreservesEpimorphisms] {P : C} (hP : Projective (F.obj P)) : Projective P where
  factors g f _ := by
    obtain ⟨h, fac⟩ := hP.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

end Functor

namespace Equivalence

variable {D : Type u'} [Category.{v'} D] (F : C ≌ D)

/-
**CategoryTheory.Equivalence.map_projective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Equivalence`。
形式化陈述：map_projective_iff (P : C) : Projective (F.functor.obj P) ↔ Projective P
参数：P : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.projective_of_map_projective`：projective_of_ma
p_projective (adj : F ⊣ G) [F.Full] [F.Faithful] (P : C) (hP : Projective (F.obj
 P)) : Projective P where factors f g _
· 使用定理 `CategoryTheory.Adjunction.map_projective`：map_projective (adj : F ⊣ G) [
G.PreservesEpimorphisms] (P : C) (hP : Projective P) : Projective (F.obj P) wher
e factors f g _
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
theorem map_projective_iff (P : C) : Projective (F.functor.obj P) ↔ Projective P :=
  ⟨F.toAdjunction.projective_of_map_projective P, F.toAdjunction.map_projective P⟩

/-- Given an equivalence of categories `F`, a projective presentation of `F(X)` induces a
projective presentation of `X.` -/
/-
**CategoryTheory.Equivalence.projectivePresentationOfMapProjectivePresentation**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：projectivePresentationOfMapProjectivePresentation (X : C) (Y : ProjectiveP
resentation (F.functor.obj X)) : ProjectivePresentation X where p
参数：X : C；Y : ProjectivePresentation (F.functor.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equivalence of categories `F`, a projective presentation of `F(X)` indu
ces a
projective presentation of `X.`
-/
def projectivePresentationOfMapProjectivePresentation (X : C)
    (Y : ProjectivePresentation (F.functor.obj X)) : ProjectivePresentation X where
  p := F.inverse.obj Y.p
  projective := Adjunction.map_projective F.symm.toAdjunction Y.p Y.projective
  f := F.inverse.map Y.f ≫ F.unitInv.app _
  epi := epi_comp _ _
/-
**CategoryTheory.Equivalence.enoughProjectives_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：enoughProjectives_iff (F : C ≌ D) : EnoughProjectives C ↔ EnoughProjective
s D
参数：F : C ≌ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnoughProjectives.presentation`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.EnoughProjectives C] (X :
 C),   Nonempty (CategoryTheory.Pro…
-/
theorem enoughProjectives_iff (F : C ≌ D) : EnoughProjectives C ↔ EnoughProjectives D := by
  constructor
  all_goals intro H; constructor; intro X; constructor
  · exact F.symm.projectivePresentationOfMapProjectivePresentation _
      (Nonempty.some (H.presentation (F.inverse.obj X)))
  · exact F.projectivePresentationOfMapProjectivePresentation X
      (Nonempty.some (H.presentation (F.functor.obj X)))

end Equivalence

/-
**CategoryTheory.Retract.projective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Re
tract`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : Ca
tegoryTheory.Retract X Y)   [p : CategoryTheory.Projective Y], CategoryTheory.Pr
ojective X
参数：h : CategoryTheory.Retract X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.factors`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {P : C} [self : CategoryTheory.Projective P] {E X : C}   (f 
: P ⟶ X) (e : E ⟶ X) [C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Retract.retract_assoc`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} (self : CategoryTheory.Retract X Y) {Z : C}   (
h : X ⟶ Z), CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Retract.projective {X Y : C} (h : Retract X Y) [p : Projective Y] : Projective X := by
  refine Projective.mk (fun {A B} f e _ ↦ ?_)
  rcases p.factors (h.r ≫ f) e with ⟨g, hg⟩
  use h.i ≫ g
  simp [hg]

end CategoryTheory

