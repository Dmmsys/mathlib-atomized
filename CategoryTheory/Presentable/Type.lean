/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Type
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Types.Set

/-!
# Presentable objects in Type

In this file, we show that if `κ : Cardinal.{u}` is a regular cardinal,
then `X : Type u` is `κ`-presentable in the category of types iff
`HasCardinalLT X κ` holds, i.e. the cardinal number of `X` is less than `κ`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ConcreteCategory

namespace HasCardinalLT

variable (X : Type u) (κ : Cardinal.{u})

set_option backward.defeqAttrib.useBackward true in
variable {X κ} in
/-
**HasCardinalLT.isCardinalPresentable** 是 Mathlib 中的一个引理，位于命名空间 `HasCardinalLT`。
形式化陈述：isCardinalPresentable (hX : HasCardinalLT X κ) [Fact κ.IsRegular] : IsCard
inalPresentable X κ where preservesColimitOfShape J _ _
参数：hX : HasCardinalLT X κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.IsCardinalFiltered.coeq_condition`：coeq_condition (k : K)
 : f k ≫ coeqHom f hK = toCoeq f hK
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
-/
lemma isCardinalPresentable (hX : HasCardinalLT X κ) [Fact κ.IsRegular] :
    IsCardinalPresentable X κ where
  preservesColimitOfShape J _ _ :=
    ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
      have := isFiltered_of_isCardinalFiltered J κ
      refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f g h ↦ ?_)
      · dsimp at f
        choose j g hg using fun x ↦ Types.jointly_surjective_of_isColimit hc (f x)
        refine ⟨IsCardinalFiltered.max j hX,
          ↾fun x ↦ F.map (IsCardinalFiltered.toMax j hX x) (g x), ?_⟩
        dsimp
        ext x
        dsimp at j g hg x ⊢
        rw [← hg]
        exact congr_hom (c.w (IsCardinalFiltered.toMax j hX x)).symm (g x)
      · choose k a hk using fun x ↦
          (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (congr_hom h x)
        dsimp at f g h k a hk ⊢
        replace hk : ∀ x, F.map (a x) (f x) = F.map (a x) (g x) := by assumption
        obtain ⟨l, b, c, hl⟩ : ∃ (l : J) (c : j ⟶ l) (b : ∀ x, k x ⟶ l),
            ∀ x, a x ≫ b x = c := by
          let φ (x : X) : j ⟶ IsCardinalFiltered.max k hX :=
            a x ≫ IsCardinalFiltered.toMax k hX x
          exact ⟨IsCardinalFiltered.coeq φ hX,
            IsCardinalFiltered.toCoeq φ hX,
            fun x ↦ IsCardinalFiltered.toMax k hX x ≫ IsCardinalFiltered.coeqHom φ hX,
            fun x ↦ by simpa [φ] using IsCardinalFiltered.coeq_condition φ hX x⟩
        refine ⟨l, b, by ext x; simp [← hl x, hk]⟩⟩⟩⟩

/-- Given `X : Type u` and `κ : Cardinal.{u} X`, this is the preordered type
of subsets of `X` of cardinality `< κ`. -/
/-
**HasCardinalLT.Set** 是 Mathlib 中的一个定义，位于命名空间 `HasCardinalLT`。
形式化陈述：Type u → Cardinal.{u} → Type (max 0 u)
参数：max 0 u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : Type u` and `κ : Cardinal.{u} X`, this is the preordered type
of subsets of `X` of cardinality `< κ`.
-/
protected abbrev Set := { A : Set X // HasCardinalLT A κ }

namespace Set

/-
**HasCardinalLT.Set.** 是 Mathlib 中的一个实例，位于命名空间 `HasCardinalLT.Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fact κ.IsRegular] :
    IsCardinalFiltered (HasCardinalLT.Set X κ) κ :=
  isCardinalFiltered_preorder _ _
    (fun ι A hι ↦ ⟨⟨⋃ (i : ι), (A i).val,
      hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun i ↦ (A i).prop)⟩,
      le_iSup (fun i ↦ (A i).1)⟩)
/-
**HasCardinalLT.Set.** 是 Mathlib 中的一个实例，位于命名空间 `HasCardinalLT.Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fact κ.IsRegular] :
    IsFiltered (HasCardinalLT.Set X κ) :=
  isFiltered_of_isCardinalFiltered _ κ
/-
**HasCardinalLT.Set.isFiltered_of_aleph0_le** 是 Mathlib 中的一个引理，位于命名空间 `HasCardin
alLT.Set`。
形式化陈述：isFiltered_of_aleph0_le (hκ : Cardinal.aleph0 <= κ) : IsFiltered (HasCardi
nalLT.Set X κ) where nonempty
参数：hκ : Cardinal.aleph0 <= κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_union`：hasCardinalLT_union {X : Type*} {S₁ S₂ : Set X} {κ 
: Cardinal} (hκ : Cardinal.aleph0 <= κ) (h₁ : HasCardinalLT S₁ κ) (h₂ : HasCardi
nalLT S₂ …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `CategoryTheory.isFilteredOrEmpty_of_directed_le`：∀ (α : Type u) [inst : 
Preorder α] [IsDirectedOrder α], CategoryTheory.IsFilteredOrEmpty α
· 使用引理 `hasCardinalLT_of_finite`：hasCardinalLT_of_finite (X : Type*) [Finite X] 
(κ : Cardinal) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT X κ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma isFiltered_of_aleph0_le (hκ : Cardinal.aleph0 ≤ κ) :
    IsFiltered (HasCardinalLT.Set X κ) where
  nonempty := ⟨⟨∅, hasCardinalLT_of_finite _ _ hκ⟩⟩
  toIsFilteredOrEmpty := by
    have : IsDirectedOrder (HasCardinalLT.Set X κ) :=
      ⟨fun A B ↦ ⟨⟨A.val ∪ B.val, hasCardinalLT_union hκ A.prop B.prop⟩,
        Set.subset_union_left, Set.subset_union_right⟩⟩
    exact isFilteredOrEmpty_of_directed_le _

/-- The functor `HasCardinalLT.Set X κ ⥤ Type u` which sends a subset of `X`
of cardinality `κ` to the corresponding subtype. -/
@[simps! +dsimpLhs]
/-
**HasCardinalLT.Set.functor** 是 Mathlib 中的一个定义，位于命名空间 `HasCardinalLT.Set`。
形式化陈述：functor : HasCardinalLT.Set X κ ⥤ Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `HasCardinalLT.Set X κ ⥤ Type u` which sends a subset of `X`
of cardinality `κ` to the corresponding subtype.
-/
def functor : HasCardinalLT.Set X κ ⥤ Type u :=
  Monotone.functor (f := Subtype.val) (by tauto) ⋙ Set.functorToTypes (X := X)

/-- The cocone for `Set.functor X κ : HasCardinalLT.Set X κ ⥤ Type u` with point `X`. -/
@[simps]
/-
**HasCardinalLT.Set.cocone** 是 Mathlib 中的一个定义，位于命名空间 `HasCardinalLT.Set`。
形式化陈述：cocone : Cocone (Set.functor X κ) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone for `Set.functor X κ : HasCardinalLT.Set X κ ⥤ Type u` with point `X`
.
-/
def cocone : Cocone (Set.functor X κ) where
  pt := X
  ι.app _ := ↾(Subtype.val)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Any type `X` is the (filtered) colimit of its subsets of cardinality `< κ`
when `κ` is an infinite cardinal. (This colimit is `κ`-filtered when `κ` is
a regular cardinal.) -/
/-
**HasCardinalLT.Set.isColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `HasCardinalLT.Set
`。
形式化陈述：isColimitCocone (hκ : Cardinal.aleph0 <= κ) : IsColimit (cocone X κ)
参数：hκ : Cardinal.aleph0 <= κ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.Set.isFiltered_of_aleph0_le`：isFiltered_of_aleph0_le (hκ :
 Cardinal.aleph0 <= κ) : IsFiltered (HasCardinalLT.Set X κ) where nonempty

--- 原说明 ---
Any type `X` is the (filtered) colimit of its subsets of cardinality `< κ`
when `κ` is an infinite cardinal. (This colimit is `κ`-filtered when `κ` is
a regular cardinal.)
-/
noncomputable def isColimitCocone
    (hκ : Cardinal.aleph0 ≤ κ) : IsColimit (cocone X κ) := by
  have := isFiltered_of_aleph0_le X κ hκ
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) ?_
  · exact ⟨⟨{x}, hasCardinalLT_of_finite _ _ hκ⟩, ⟨x, by simp⟩, rfl⟩
  · rintro A ⟨x, hx⟩ ⟨y, hy⟩ rfl
    exact ⟨A, 𝟙 _, rfl⟩

end Set

end HasCardinalLT

namespace CategoryTheory

namespace Types

variable {X : Type u}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Types.isCardinalPresentable_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Types`。
形式化陈述：isCardinalPresentable_iff (κ : Cardinal.{u}) [Fact κ.IsRegular] : IsCardin
alPresentable X κ ↔ HasCardinalLT X κ
参数：κ : Cardinal.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesColimitsOfShape_of_isCardinalPresentable`：preser
vesColimitsOfShape_of_isCardinalPresentable [IsCardinalPresentable X κ] (J : Typ
e w) [SmallCategory.{w} J] [IsCardinalFiltered J κ] : …
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `HasCardinalLT.Set.instIsCardinalFiltered`：∀ (X : Type u) (κ : Cardinal.{
u}) [inst : Fact κ.IsRegular], CategoryTheory.IsCardinalFiltered (HasCardinalLT.
Set X κ) κ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `HasCardinalLT.isCardinalPresentable`：isCardinalPresentable (hX : HasCard
inalLT X κ) [Fact κ.IsRegular] : IsCardinalPresentable X κ where preservesColimi
tOfShape J _ _
-/
lemma isCardinalPresentable_iff (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalPresentable X κ ↔ HasCardinalLT X κ := by
  refine ⟨fun _ ↦ ?_, fun hX ↦ hX.isCardinalPresentable⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ
  obtain ⟨⟨A, hA⟩, f, hf⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op X))
      (HasCardinalLT.Set.isColimitCocone X κ
        (Cardinal.IsRegular.aleph0_le Fact.out))) (𝟙 X)
  obtain rfl : A = .univ := by
    ext x
    have := congr_hom hf x
    dsimp at this
    rw [← this]
    simp
  exact (hasCardinalLT_iff_of_equiv (Equiv.Set.univ X) _).1 hA
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type u) : IsPresentable.{u} X := by
  obtain ⟨κ, hκ, hX⟩ := HasCardinalLT.exists_regular_cardinal.{u} X
  have : Fact κ.IsRegular := ⟨hκ⟩
  have := hX.isCardinalPresentable
  exact isPresentable_of_isCardinalPresentable X κ
/-
**CategoryTheory.Types.isStrongGenerator_punit** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Types`。
形式化陈述：isStrongGenerator_punit : (ObjectProperty.singleton (PUnit.{u + 1})).IsStr
ongGenerator
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isStrongGenerator_iff`：isStrongGenerator_i
ff : P.IsStrongGenerator ↔ P.IsSeparating ∧ forall ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i
], (forall (G : C) (_ : P G), Function.Su…
· 使用定理 `CategoryTheory.Types.isSeparator_punit`：CategoryTheory.IsSeparator PUnit
.{u + 1}
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
-/
lemma isStrongGenerator_punit :
    (ObjectProperty.singleton (PUnit.{u + 1})).IsStrongGenerator  := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨isSeparator_punit, fun _ _ i hi₁ hi₂ ↦ ?_⟩
  · rw [mono_iff_injective] at hi₁
    rw [isIso_iff_bijective]
    refine ⟨hi₁, fun y ↦ ?_⟩
    obtain ⟨f, hf⟩ := hi₂ PUnit ⟨.unit⟩ (↾fun _ ↦ y)
    exact ⟨f .unit, ConcreteCategory.congr_hom hf .unit⟩
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable (Type u) κ := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  exact ⟨.singleton PUnit, inferInstance, isStrongGenerator_punit, by
    simp only [ObjectProperty.singleton_le_iff,
      CategoryTheory.isCardinalPresentable_iff, isCardinalPresentable_iff]
    exact hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)⟩
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocallyPresentable.{u} (Type u) where
  exists_cardinal := ⟨_, Cardinal.fact_isRegular_aleph0, inferInstance⟩

end Types

end CategoryTheory

