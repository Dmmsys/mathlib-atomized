/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kevin Buzzard
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Injective objects and categories with enough injectives

An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/

@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite

universe v v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/--
An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/
/-
**CategoryTheory.Injective** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [CategoryTheory.Category.{v₁, u₁} C] → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `J` is injective iff every morphism into `J` can be obtained by extend
ing a monomorphism.
-/
class Injective (J : C) : Prop where
  factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], ∃ h : Y ⟶ J, f ≫ h = g

attribute [inherit_doc Injective] Injective.factors

variable (C) in
/-- The `ObjectProperty C` corresponding to the notion of injective objects in `C`. -/
/-
**CategoryTheory.isInjective** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：isInjective : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ObjectProperty C` corresponding to the notion of injective objects in `C`.
-/
abbrev isInjective : ObjectProperty C := Injective
/-
**CategoryTheory.Limits.IsZero.injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.IsZero`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C},   Cat
egoryTheory.Limits.IsZero X → CategoryTheory.Injective X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
lemma Limits.IsZero.injective {X : C} (h : IsZero X) : Injective X where
  factors _ _ _ := ⟨h.from_ _, h.eq_of_tgt _ _⟩

section

/-- An injective presentation of an object `X` consists of a monomorphism `f : X ⟶ J`
to some injective object `J`.
-/
/-
**CategoryTheory.InjectivePresentation** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
`。
形式化陈述：InjectivePresentation (X : C) where J : C injective : Injective J
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective presentation of an object `X` consists of a monomorphism `f : X ⟶ J
`
to some injective object `J`.
-/
structure InjectivePresentation (X : C) where
  J : C
  injective : Injective J := by infer_instance
  f : X ⟶ J
  mono : Mono f := by infer_instance

open InjectivePresentation in
attribute [inherit_doc InjectivePresentation] J injective f mono

attribute [instance] InjectivePresentation.injective InjectivePresentation.mono

variable (C)

/-- A category "has enough injectives" if every object has an injective presentation,
i.e. if for every object `X` there is an injective object `J` and a monomorphism `X ↪ J`. -/
/-
**CategoryTheory.EnoughInjectives** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category "has enough injectives" if every object has an injective presentation
,
i.e. if for every object `X` there is an injective object `J` and a monomorphism
 `X ↪ J`.
-/
class EnoughInjectives : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)

attribute [inherit_doc EnoughInjectives] EnoughInjectives.presentation

attribute [instance low] EnoughInjectives.presentation

end

namespace Injective

/--
Let `J` be injective and `g` a morphism into `J`, then `g` can be factored through any monomorphism.
-/
/-
**CategoryTheory.Injective.factorThru** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Injective`。
形式化陈述：factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y 
⟶ J
参数：g : X ⟶ J；f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …

--- 原说明 ---
Let `J` be injective and `g` a morphism into `J`, then `g` can be factored throu
gh any monomorphism.
-/
def factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y ⟶ J :=
  (Injective.factors g f).choose

@[reassoc (attr := simp)]
/-
**CategoryTheory.Injective.comp_factorThru** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Injective`。
形式化陈述：comp_factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f]
 : f ≫ factorThru g f = g
参数：g : X ⟶ J；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …
-/
theorem comp_factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] :
    f ≫ factorThru g f = g :=
  (Injective.factors g f).choose_spec

section

open ZeroObject

/-
**CategoryTheory.Injective.zero_injective** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Injective`。
形式化陈述：zero_injective [HasZeroObject C] : Injective (0 : C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.injective`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {X : C},   CategoryTheory.Limits.IsZero X → Category
Theory.Injective X
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
instance zero_injective [HasZeroObject C] : Injective (0 : C) :=
  (isZero_zero C).injective

end

/-
**CategoryTheory.Injective.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Inje
ctive`。
形式化陈述：of_iso {P Q : C} (i : P ≅ Q) (hP : Injective P) : Injective Q
参数：i : P ≅ Q；hP : Injective P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Injective P) : Injective Q :=
  {
    factors := fun g f mono => by
      obtain ⟨h, h_eq⟩ := @Injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      refine ⟨h ≫ i.hom, ?_⟩
      rw [← Category.assoc, h_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id] }
/-
**CategoryTheory.Injective.iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Inj
ective`。
形式化陈述：iso_iff {P Q : C} (i : P ≅ Q) : Injective P ↔ Injective Q
参数：i : P ≅ Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.of_iso`：of_iso {P Q : C} (i : P ≅ Q) (hP : Inje
ctive P) : Injective Q
-/
theorem iso_iff {P Q : C} (i : P ≅ Q) : Injective P ↔ Injective Q :=
  ⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The axiom of choice says that every nonempty type is an injective object in `Typ
e`.
-/
instance (X : Type u₁) [Nonempty X] : Injective X where
  factors g f mono :=
    ⟨↾fun z => by
      classical
      exact
          if h : z ∈ Set.range f then g (Classical.choose h) else Nonempty.some inferInstance, by
      ext y
      classical
      change dite (f y ∈ Set.range f) (fun h => g (Classical.choose h)) _ = _
      split_ifs <;> rename_i h
      · rw [mono_iff_injective] at mono
        simp [mono (Classical.choose_spec h)]
      · exact False.elim (h ⟨y, rfl⟩)⟩
/-
**CategoryTheory.Injective.Type.enoughInjectives** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Injective.Type`。
形式化陈述：CategoryTheory.EnoughInjectives (Type u₁)
参数：Type u₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.instOfNonempty`：∀ (X : Type u₁) [Nonempty X], C
ategoryTheory.Injective X
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `WithBot.coe_injective`：coe_injective : Injective ((↑) : α -> WithBot α)
-/
instance Type.enoughInjectives : EnoughInjectives (Type u₁) where
  presentation X :=
    Nonempty.intro
      { J := WithBot X
        injective := inferInstance
        f := ↾WithBot.some
        mono := by
          rw [mono_iff_injective]
          exact WithBot.coe_injective }
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : C} [HasBinaryProduct P Q] [Injective P] [Injective Q] : Injective (P ⨯ Q) where
  factors g f mono := by
    use Limits.prod.lift (factorThru (g ≫ Limits.prod.fst) f) (factorThru (g ≫ Limits.prod.snd) f)
    simp only [prod.comp_lift, comp_factorThru]
    ext
    · simp only [prod.lift_fst]
    · simp only [prod.lift_snd]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type v} (c : β → C) [HasProduct c] [∀ b, Injective (c b)] : Injective (∏ᶜ c) where
  factors g f mono := by
    refine ⟨Pi.lift fun b => factorThru (g ≫ Pi.π c _) f, ?_⟩
    ext b
    simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, comp_factorThru]
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Injective P] [Injective Q] :
    Injective (P ⊞ Q) where
  factors g f mono := by
    refine ⟨biprod.lift (factorThru (g ≫ biprod.fst) f) (factorThru (g ≫ biprod.snd) f), ?_⟩
    ext
    · simp only [Category.assoc, biprod.lift_fst, comp_factorThru]
    · simp only [Category.assoc, biprod.lift_snd, comp_factorThru]
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type v} (c : β → C) [HasZeroMorphisms C] [HasBiproduct c] [∀ b, Injective (c b)] :
    Injective (⨁ c) where
  factors g f mono := by
    refine ⟨biproduct.lift fun b => factorThru (g ≫ biproduct.π _ _) f, ?_⟩
    ext
    simp only [Category.assoc, biproduct.lift_π, comp_factorThru]
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : Cᵒᵖ} [Projective P] : Injective no_index (unop P) where
  factors g f mono :=
    ⟨(@Projective.factorThru Cᵒᵖ _ P _ _ _ g.op f.op _).unop, Quiver.Hom.op_inj (by simp)⟩
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Cᵒᵖ} [Injective J] : Projective no_index (unop J) where
  factors f e he :=
    ⟨(@factorThru Cᵒᵖ _ J _ _ _ f.op e.op _).unop, Quiver.Hom.op_inj (by simp)⟩
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : C} [Injective J] : Projective (op J) where
  factors f e epi :=
    ⟨(@factorThru C _ J _ _ _ f.unop e.unop _).op, Quiver.Hom.unop_inj (by simp)⟩
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : C} [Projective P] : Injective (op P) where
  factors g f mono :=
    ⟨(@Projective.factorThru C _ P _ _ _ g.unop f.unop _).op, Quiver.Hom.unop_inj (by simp)⟩
/-
**CategoryTheory.Injective.injective_iff_projective_op** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Injective`。
形式化陈述：injective_iff_projective_op {J : C} : Injective J ↔ Projective (op J)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.instProjectiveOppositeOp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {J : C} [CategoryTheory.Injective J],   C
ategoryTheory.Projective (Opposite.op J…
· 使用定理 `CategoryTheory.Injective.instUnopOfProjectiveOpposite`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {P : Cᵒᵖ} [CategoryTheory.Projective 
P],   CategoryTheory.Injective (Opposite.un…
-/
theorem injective_iff_projective_op {J : C} : Injective J ↔ Projective (op J) :=
  ⟨fun _ => inferInstance, fun _ => show Injective (unop (op J)) from inferInstance⟩
/-
**CategoryTheory.Injective.projective_iff_injective_op** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Injective`。
形式化陈述：projective_iff_injective_op {P : C} : Projective P ↔ Injective (op P)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.instOppositeOpOfProjective`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {P : C} [CategoryTheory.Projective P], 
  CategoryTheory.Injective (Opposite.op P…
· 使用定理 `CategoryTheory.Injective.instProjectiveUnopOfOpposite`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {J : Cᵒᵖ} [CategoryTheory.Injective J
],   CategoryTheory.Projective (Opposite.un…
-/
theorem projective_iff_injective_op {P : C} : Projective P ↔ Injective (op P) :=
  ⟨fun _ => inferInstance, fun _ => show Projective (unop (op P)) from inferInstance⟩
/-
**CategoryTheory.Injective.injective_iff_preservesEpimorphisms_yoneda_obj** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Injective`。
形式化陈述：injective_iff_preservesEpimorphisms_yoneda_obj (J : C) : Injective J ↔ (yo
neda.obj J).PreservesEpimorphisms
参数：J : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Injective.injective_iff_projective_op`：injective_iff_proj
ective_op {J : C} : Injective J ↔ Projective (op J)
· 使用定理 `CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_
obj`：projective_iff_preservesEpimorphisms_coyoneda_obj (P : C) : Projective P ↔ 
(coyoneda.obj (op P)).PreservesEpimorphisms
· 使用定理 `CategoryTheory.Functor.PreservesEpimorphisms.iso_iff`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   {F G : CategoryThe…
-/
theorem injective_iff_preservesEpimorphisms_yoneda_obj (J : C) :
    Injective J ↔ (yoneda.obj J).PreservesEpimorphisms := by
  rw [injective_iff_projective_op, Projective.projective_iff_preservesEpimorphisms_coyoneda_obj]
  exact Functor.PreservesEpimorphisms.iso_iff (Coyoneda.objOpOp _)

section Adjunction

open CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} [PreservesMonomorphisms L]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Injective.injective_of_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Injective`。
形式化陈述：injective_of_adjoint (adj : L ⊣ R) (J : D) [Injective J] : Injective R.obj
 J
参数：adj : L ⊣ R；J : D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Injective.factorThru.congr_simp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {J X Y : C} [inst_1 : CategoryTheory.Injecti
ve J]   (g g_1 : X ⟶ J),   g = g_1 →…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Injective.comp_factorThru`：comp_factorThru {J X Y : C} [I
njective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem injective_of_adjoint (adj : L ⊣ R) (J : D) [Injective J] : Injective <| R.obj J :=
  ⟨fun {A} {_} g f im =>
    ⟨adj.homEquiv _ _ (factorThru ((adj.homEquiv A J).symm g) (L.map f)),
      (adj.homEquiv _ _).symm.injective
        (by simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit])⟩⟩

end Adjunction

section EnoughInjectives

variable [EnoughInjectives C]

/-- If `C` has enough injectives, we may choose an injective presentation of `X : C`
which is given by a zero object when `X` is a zero object. -/
/-
**CategoryTheory.Injective.exists_presentation** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Injective`。
形式化陈述：exists_presentation (X : C) : exists (p : InjectivePresentation X), IsZero
 X -> IsZero p.J
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.injective`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {X : C},   CategoryTheory.Limits.IsZero X → Category
Theory.Injective X
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.EnoughInjectives.presentation`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.EnoughInjectives C] (X 
: C),   Nonempty (CategoryTheory.I…

--- 原说明 ---
If `C` has enough injectives, we may choose an injective presentation of `X : C`
which is given by a zero object when `X` is a zero object.
-/
lemma exists_presentation (X : C) : ∃ (p : InjectivePresentation X), IsZero X → IsZero p.J := by
  by_cases h : IsZero X
  · have := h.injective
    exact ⟨{ J := X, f := 𝟙 X}, by tauto⟩
  · exact ⟨(EnoughInjectives.presentation X).some, by tauto⟩

/-- `Injective.under X` provides an arbitrarily chosen injective object equipped with
a monomorphism `Injective.ι : X ⟶ Injective.under X`.
-/
/-
**CategoryTheory.Injective.under** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Injec
tive`。
形式化陈述：under (X : C) : C
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Injective.exists_presentation`：exists_presentation (X : C
) : exists (p : InjectivePresentation X), IsZero X -> IsZero p.J

--- 原说明 ---
`Injective.under X` provides an arbitrarily chosen injective object equipped wit
h
a monomorphism `Injective.ι : X ⟶ Injective.under X`.
-/
def under (X : C) : C :=
  (exists_presentation X).choose.J
/-
**CategoryTheory.Injective.injective_under** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Injective`。
形式化陈述：injective_under (X : C) : Injective (under X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InjectivePresentation.injective`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.InjectivePres
entation X),   CategoryTheory.Inject…
· 使用引理 `CategoryTheory.Injective.exists_presentation`：exists_presentation (X : C
) : exists (p : InjectivePresentation X), IsZero X -> IsZero p.J
-/
instance injective_under (X : C) : Injective (under X) :=
  (exists_presentation X).choose.injective

/-- The monomorphism `Injective.ι : X ⟶ Injective.under X`
from the arbitrarily chosen injective object under `X`.
-/
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monomorphism `Injective.ι : X ⟶ Injective.under X`
from the arbitrarily chosen injective object under `X`.
-/
def ι (X : C) : X ⟶ under X :=
  (exists_presentation X).choose.f
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ι_mono (X : C) : Mono (ι X) :=
  (exists_presentation X).choose.mono
/-
**CategoryTheory.Injective.isZero_under** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Injective`。
形式化陈述：isZero_under (X : C) (hX : IsZero X) : IsZero (under X)
参数：X : C；hX : IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `CategoryTheory.Injective.exists_presentation`：exists_presentation (X : C
) : exists (p : InjectivePresentation X), IsZero X -> IsZero p.J
-/
lemma isZero_under (X : C) (hX : IsZero X) :
    IsZero (under X) :=
  (exists_presentation X).choose_spec hX

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/-- When `C` has enough injectives, the object `Injective.syzygies f` is
an arbitrarily chosen injective object under `cokernel f`.
-/
/-
**CategoryTheory.Injective.syzygies** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.In
jective`。
形式化陈述：syzygies : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` has enough injectives, the object `Injective.syzygies f` is
an arbitrarily chosen injective object under `cokernel f`.
-/
def syzygies : C :=
  under (cokernel f)
deriving Injective

/-- When `C` has enough injective,
`Injective.d f : Y ⟶ syzygies f` is the composition
`cokernel.π f ≫ ι (cokernel f)`.

(When `C` is abelian, we have `exact f (injective.d f)`.)
-/
/-
**CategoryTheory.Injective.d** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Injecti
ve`。
形式化陈述：d : Y ⟶ syzygies f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` has enough injective,
`Injective.d f : Y ⟶ syzygies f` is the composition
`cokernel.π f ≫ ι (cokernel f)`.

(When `C` is abelian, we have `exact f (injective.d f)`.)
-/
abbrev d : Y ⟶ syzygies f :=
  cokernel.π f ≫ ι (cokernel f)

end

end EnoughInjectives

/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EnoughInjectives C] : EnoughProjectives Cᵒᵖ :=
  ⟨fun X => ⟨{ p := _, f := (Injective.ι (unop X)).op}⟩⟩
/-
**CategoryTheory.Injective.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Injective`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EnoughProjectives C] : EnoughInjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩
/-
**CategoryTheory.Injective.enoughProjectives_of_enoughInjectives_op** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Injective`。
形式化陈述：enoughProjectives_of_enoughInjectives_op [EnoughInjectives Cᵒᵖ] : EnoughPr
ojectives C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.instProjectiveUnopOfOpposite`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {J : Cᵒᵖ} [CategoryTheory.Injective J
],   CategoryTheory.Projective (Opposite.un…
-/
theorem enoughProjectives_of_enoughInjectives_op [EnoughInjectives Cᵒᵖ] : EnoughProjectives C :=
  ⟨fun X => ⟨{ p := _, f := (Injective.ι (op X)).unop} ⟩⟩
/-
**CategoryTheory.Injective.enoughInjectives_of_enoughProjectives_op** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Injective`。
形式化陈述：enoughInjectives_of_enoughProjectives_op [EnoughProjectives Cᵒᵖ] : EnoughI
njectives C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.instUnopOfProjectiveOpposite`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {P : Cᵒᵖ} [CategoryTheory.Projective 
P],   CategoryTheory.Injective (Opposite.un…
· 使用定理 `CategoryTheory.unop_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {A B : Cᵒᵖ} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryT
heory.Mono f.unop
-/
theorem enoughInjectives_of_enoughProjectives_op [EnoughProjectives Cᵒᵖ] : EnoughInjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (op X)).unop, inferInstance⟩⟩⟩

end Injective

namespace Adjunction

variable {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C}

/-
**CategoryTheory.Adjunction.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：map_injective (adj : F ⊣ G) [F.PreservesMonomorphisms] (I : D) (hI : Injec
tive I) : Injective (G.obj I)
参数：adj : F ⊣ G；I : D；hI : Injective I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_injective (adj : F ⊣ G) [F.PreservesMonomorphisms] (I : D) (hI : Injective I) :
    Injective (G.obj I) :=
  ⟨fun {X} {Y} f g => by
    intro
    rcases hI.factors (F.map f ≫ adj.counit.app _) (F.map g) with ⟨w,h⟩
    use adj.unit.app Y ≫ G.map w
    rw [← unit_naturality_assoc, ← G.map_comp, h]
    simp⟩
/-
**CategoryTheory.Adjunction.injective_of_map_injective** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：injective_of_map_injective (adj : F ⊣ G) [G.Full] [G.Faithful] (I : D) (hI
 : Injective (G.obj I)) : Injective I
参数：adj : F ⊣ G；I : D；hI : Injective (G.obj I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`：rightAdjoint_pre
servesLimits : PreservesLimitsOfSize.{v, u} G where preservesLimitsOfShape
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize0.preservesFiniteLimits`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Adjunction.inv_counit_map`：inv_counit_map {X : D} [IsIso 
(h.counit.app X)] : inv (R.map (h.counit.app X)) = h.unit.app (R.obj X)
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem injective_of_map_injective (adj : F ⊣ G) [G.Full] [G.Faithful] (I : D)
    (hI : Injective (G.obj I)) : Injective I :=
  ⟨fun {X} {Y} f g => by
    intro
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    rcases hI.factors (G.map f) (G.map g) with ⟨w,h⟩
    use inv (adj.counit.app _) ≫ F.map w ≫ adj.counit.app _
    exact G.map_injective (by simpa)⟩

/-- Given an adjunction `F ⊣ G` such that `F` preserves monos, `G` maps an injective presentation
of `X` to an injective presentation of `G(X)`. -/
/-
**CategoryTheory.Adjunction.mapInjectivePresentation** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：mapInjectivePresentation (adj : F ⊣ G) [F.PreservesMonomorphisms] (X : D) 
(I : InjectivePresentation X) : InjectivePresentation (G.obj X) where J
参数：adj : F ⊣ G；X : D；I : InjectivePresentation X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `F ⊣ G` such that `F` preserves monos, `G` maps an injective
 presentation
of `X` to an injective presentation of `G(X)`.
-/
def mapInjectivePresentation (adj : F ⊣ G) [F.PreservesMonomorphisms] (X : D)
    (I : InjectivePresentation X) : InjectivePresentation (G.obj X) where
  J := G.obj I.J
  injective := adj.map_injective _ I.injective
  f := G.map I.f
  mono := by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits; infer_instance

/-- Given an adjunction `F ⊣ G` such that `F` preserves monomorphisms and is faithful,
  then any injective presentation of `F(X)` can be pulled back to an injective presentation of `X`.
  This is similar to `mapInjectivePresentation`. -/
/-
**CategoryTheory.Adjunction.injectivePresentationOfMap** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：injectivePresentationOfMap (adj : F ⊣ G) [F.PreservesMonomorphisms] [F.Ref
lectsMonomorphisms] (X : C) (I : InjectivePresentation <| F.obj X) : InjectivePr
esentation X where J
参数：adj : F ⊣ G；X : C；I : InjectivePresentation <| F.obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `F ⊣ G` such that `F` preserves monomorphisms and is faithfu
l,
  then any injective presentation of `F(X)` can be pulled back to an injective p
resentation of `X`.
  This is similar to `mapInjectivePresentation`.
-/
def injectivePresentationOfMap (adj : F ⊣ G)
    [F.PreservesMonomorphisms] [F.ReflectsMonomorphisms] (X : C)
    (I : InjectivePresentation <| F.obj X) :
    InjectivePresentation X where
  J := G.obj I.J
  injective := Injective.injective_of_adjoint adj _
  f := adj.homEquiv _ _ I.f

end Adjunction

namespace Functor

variable {D : Type*} [Category* D] (F : C ⥤ D)

/-
**CategoryTheory.Functor.injective_of_map_injective** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：injective_of_map_injective [F.Full] [F.Faithful] [F.PreservesMonomorphisms
] {I : C} (hI : Injective (F.obj I)) : Injective I where factors g f _
参数：hI : Injective (F.obj I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
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
theorem injective_of_map_injective [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {I : C} (hI : Injective (F.obj I)) : Injective I where
  factors g f _ := by
    obtain ⟨h, fac⟩ := hI.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

end Functor

/--
[Lemma 3.8](https://ncatlab.org/nlab/show/injective+object#preservation_of_injective_objects)
-/
/-
**CategoryTheory.EnoughInjectives.of_adjunction** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.EnoughInjectives`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheory.Functor C D}
 {R : CategoryTheory.Functor D C} (adj : L ⊣ R) [L.PreservesMonomorphisms]   [L.
ReflectsMonomorphisms] [CategoryTheory.EnoughInjectives D], CategoryTheory.Enoug
hInjectives C
参数：adj : L ⊣ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnoughInjectives.presentation`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.EnoughInjectives C] (X 
: C),   Nonempty (CategoryTheory.I…

--- 原说明 ---
[Lemma 3.8](https://ncatlab.org/nlab/show/injective+object#preservation_of_injec
tive_objects)
-/
lemma EnoughInjectives.of_adjunction {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.PreservesMonomorphisms] [L.ReflectsMonomorphisms]
    [EnoughInjectives D] : EnoughInjectives C where
  presentation _ :=
    ⟨adj.injectivePresentationOfMap _ (EnoughInjectives.presentation _).some⟩

/-- An equivalence of categories transfers enough injectives. -/
/-
**CategoryTheory.EnoughInjectives.of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.EnoughInjectives`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (e : CategoryTheory.Functor C D)
 [e.IsEquivalence] [CategoryTheory.EnoughInjectives D],   CategoryTheory.EnoughI
njectives C
参数：e : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnoughInjectives.of_adjunction`：∀ {C : Type u₁} {D : Type
 u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
An equivalence of categories transfers enough injectives.
-/
lemma EnoughInjectives.of_equivalence {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (e : C ⥤ D) [e.IsEquivalence] [EnoughInjectives D] : EnoughInjectives C :=
  EnoughInjectives.of_adjunction (adj := e.asEquivalence.toAdjunction)

namespace Equivalence

variable {D : Type*} [Category* D] (F : C ≌ D)

/-
**CategoryTheory.Equivalence.map_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Equivalence`。
形式化陈述：map_injective_iff (P : C) : Injective (F.functor.obj P) ↔ Injective P
参数：P : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.injective_of_map_injective`：injective_of_map_i
njective (adj : F ⊣ G) [G.Full] [G.Faithful] (I : D) (hI : Injective (G.obj I)) 
: Injective I
· 使用定理 `CategoryTheory.Adjunction.map_injective`：map_injective (adj : F ⊣ G) [F.
PreservesMonomorphisms] (I : D) (hI : Injective I) : Injective (G.obj I)
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
theorem map_injective_iff (P : C) : Injective (F.functor.obj P) ↔ Injective P :=
  ⟨F.symm.toAdjunction.injective_of_map_injective P, F.symm.toAdjunction.map_injective P⟩

/-- Given an equivalence of categories `F`, an injective presentation of `F(X)` induces an
injective presentation of `X.` -/
/-
**CategoryTheory.Equivalence.injectivePresentationOfMapInjectivePresentation** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：injectivePresentationOfMapInjectivePresentation (X : C) (I : InjectivePres
entation (F.functor.obj X)) : InjectivePresentation X
参数：X : C；I : InjectivePresentation (F.functor.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equivalence of categories `F`, an injective presentation of `F(X)` indu
ces an
injective presentation of `X.`
-/
def injectivePresentationOfMapInjectivePresentation (X : C)
    (I : InjectivePresentation (F.functor.obj X)) : InjectivePresentation X :=
  F.toAdjunction.injectivePresentationOfMap _ I
/-
**CategoryTheory.Equivalence.enoughInjectives_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：enoughInjectives_iff (F : C ≌ D) : EnoughInjectives C ↔ EnoughInjectives D
参数：F : C ≌ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnoughInjectives.of_adjunction`：∀ {C : Type u₁} {D : Type
 u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem enoughInjectives_iff (F : C ≌ D) : EnoughInjectives C ↔ EnoughInjectives D :=
  ⟨fun h => h.of_adjunction F.symm.toAdjunction, fun h => h.of_adjunction F.toAdjunction⟩

end Equivalence

/-
**CategoryTheory.Retract.injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ret
ract`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (h :
 CategoryTheory.Retract X Y)   [i : CategoryTheory.Injective Y], CategoryTheory.
Injective X
参数：h : CategoryTheory.Retract X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc'`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {W X Y Z : C} (f : X ⟶ W) (g : Y ⟶ X) (h : Z ⟶ Y),   CategoryTh
eory.CategoryStruct.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Retract.retract`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X Y : C} (self : CategoryTheory.Retract X Y),   CategoryTheory
.CategoryStruct.comp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Retract.injective {X Y : C} (h : Retract X Y) [i : Injective Y] : Injective X := by
  refine Injective.mk (fun {A B} f e _ ↦ ?_)
  rcases i.factors (f ≫ h.i) e with ⟨g, hg⟩
  use g ≫ h.r
  simp [Category.assoc', hg]

end CategoryTheory

