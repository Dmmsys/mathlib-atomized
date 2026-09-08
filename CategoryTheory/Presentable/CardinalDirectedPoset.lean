/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.Order.Category.PartOrdEmb

/-!
# The κ-accessible category of κ-directed posets

Given a regular cardinal `κ : Cardinal.{u}`, we define the
category `CardinalDirectedPoset κ` of `κ`-directed partially ordered
types (with order embeddings as morphisms), and we show that it is
a `κ`-accessible category.

The notion of `κ`-directed partially ordered type is implemented
using the categorial notion `IsCardinalFiltered`: we may consider
"`κ`-directed" and "`κ`-filtered" as synonyms.

If `κ ≤ κ'` where `κ'` is also a regular cardinal, we characterize
the `κ'`-presentable objects of `CardinalDirectedPoset κ` as
the objects `J` such that the underlying type `J.obj` has
cardinality `< κ'`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PartOrdEmb

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The property of objects in `PartOrdEmb` that are
satisfied by `κ`-directed partially ordered types.
(Note: for partially ordered types, "`κ`-directed" and
"`κ`-filtered" are synonyms. This is implemented using the
categorical notion `IsCardinalFiltered`.) -/
/-
**PartOrdEmb.isCardinalFiltered** 是 Mathlib 中的一个缩写定义，位于命名空间 `PartOrdEmb`。
形式化陈述：isCardinalFiltered : ObjectProperty PartOrdEmb.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in `PartOrdEmb` that are
satisfied by `κ`-directed partially ordered types.
(Note: for partially ordered types, "`κ`-directed" and
"`κ`-filtered" are synonyms. This is implemented using the
categorical notion `IsCardinalFiltered`.)
-/
abbrev isCardinalFiltered : ObjectProperty PartOrdEmb.{u} :=
  fun X ↦ IsCardinalFiltered X κ

@[simp]
/-
**PartOrdEmb.isCardinalFiltered_iff** 是 Mathlib 中的一个引理，位于命名空间 `PartOrdEmb`。
形式化陈述：isCardinalFiltered_iff (X : PartOrdEmb.{u}) : isCardinalFiltered κ X ↔ IsC
ardinalFiltered X κ
参数：X : PartOrdEmb.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCardinalFiltered_iff (X : PartOrdEmb.{u}) :
    isCardinalFiltered κ X ↔ IsCardinalFiltered X κ := Iff.rfl
/-
**PartOrdEmb.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isCardinalFiltered κ).IsClosedUnderIsomorphisms where
  of_iso e _ := .of_equivalence κ (orderIsoOfIso e).equivalence

namespace Limits.CoconePt

variable {κ} {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
  {F : J ⥤ PartOrdEmb.{u}} {c : Cocone (F ⋙ forget _)} (hc : IsColimit c)

/-
**PartOrdEmb.Limits.CoconePt.isCardinalFiltered_pt** 是 Mathlib 中的一个引理，位于命名空间 `Pa
rtOrdEmb.Limits.CoconePt`。
形式化陈述：isCardinalFiltered_pt (hF : forall j, IsCardinalFiltered (F.obj j) κ) : ha
veI
参数：hF : forall j, IsCardinalFiltered (F.obj j) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用引理 `CategoryTheory.isCardinalFiltered_preorder`：isCardinalFiltered_preorder 
(J : Type w) [Preorder J] (κ : Cardinal.{w}) [Fact κ.IsRegular] (h : forall ⦃K :
 Type w⦄ (s : K -> J) (_ : Cardi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `hasCardinalLT_iff_cardinal_mk_lt`：hasCardinalLT_iff_cardinal_mk_lt (X : 
Type u) (κ : Cardinal.{u}) : HasCardinalLT X κ ↔ Cardinal.mk X < κ
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
-/
lemma isCardinalFiltered_pt (hF : ∀ j, IsCardinalFiltered (F.obj j) κ) :
    haveI := isFiltered_of_isCardinalFiltered J κ
    IsCardinalFiltered (CoconePt hc) κ := by
  have := isFiltered_of_isCardinalFiltered J κ
  refine isCardinalFiltered_preorder _ _ (fun K f hK ↦ ?_)
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
  choose j₀ x₀ hx₀ using fun k ↦ Types.jointly_surjective_of_isColimit hc (f k)
  let j := IsCardinalFiltered.max j₀ hK
  let x₁ (k : K) : F.obj j := F.map (IsCardinalFiltered.toMax j₀ hK k) (x₀ k)
  have hx₁ (k : K) : c.ι.app j (x₁ k) = c.ι.app (j₀ k) (x₀ k) :=
    ConcreteCategory.congr_hom (c.w (IsCardinalFiltered.toMax j₀ hK k)) _
  refine ⟨(cocone hc).ι.app j (IsCardinalFiltered.max x₁ hK),
    fun k ↦ ?_⟩
  rw [← hx₀, ← hx₁]
  exact ((cocone hc).ι.app j).hom.monotone
    (leOfHom (IsCardinalFiltered.toMax x₁ hK k))

end Limits.CoconePt

/-
**PartOrdEmb.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrdEmb`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type u) [SmallCategory J] [IsCardinalFiltered J κ] :
    (isCardinalFiltered κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    have := isFiltered_of_isCardinalFiltered J κ
    rintro X ⟨p⟩
    simp only [(isCardinalFiltered κ).prop_iff_of_iso
      (p.isColimit.coconePointUniqueUpToIso
        (Limits.isColimitCocone (colimit.isColimit (p.diag ⋙ forget PartOrdEmb)))),
      isCardinalFiltered_iff]
    exact Limits.CoconePt.isCardinalFiltered_pt _ p.prop_diag_obj

end PartOrdEmb

namespace CategoryTheory

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The category of `κ`-filtered partially ordered types,
with morphisms given by order embeddings. -/
/-
**CategoryTheory.CardinalDirectedPoset** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：CardinalDirectedPoset
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `κ`-filtered partially ordered types,
with morphisms given by order embeddings.
-/
abbrev CardinalDirectedPoset :=
  (PartOrdEmb.isCardinalFiltered κ).FullSubcategory

variable {κ}

/-- The embedding of the category of `κ`-directed
partially ordered types in the category of partially
ordered types. -/
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of the category of `κ`-directed
partially ordered types in the category of partially
ordered types.
-/
abbrev CardinalDirectedPoset.ι : CardinalDirectedPoset κ ⥤ PartOrdEmb :=
  ObjectProperty.ι _

namespace CardinalDirectedPoset

/-- Constructor for objects in `CardinalFilteredPoset κ`. -/
/-
**CategoryTheory.CardinalDirectedPoset.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.CardinalDirectedPoset`。
形式化陈述：of (J : PartOrdEmb.{u}) [IsCardinalFiltered J κ] : CardinalDirectedPoset κ
 where obj
参数：J : PartOrdEmb.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects in `CardinalFilteredPoset κ`.
-/
abbrev of (J : PartOrdEmb.{u}) [IsCardinalFiltered J κ] : CardinalDirectedPoset κ where
  obj := J
  property := inferInstance
/-
**CategoryTheory.CardinalDirectedPoset.Hom.injective** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.CardinalDirectedPoset.Hom`。
形式化陈述：∀ {κ : Cardinal.{u}} [inst : Fact κ.IsRegular] {J₁ J₂ : CategoryTheory.Car
dinalDirectedPoset κ} (f : J₁ ⟶ J₂),   Function.Injective ⇑(CategoryTheory.Concr
eteCategory.hom f)
参数：f : J₁ ⟶ J₂；CategoryTheory.ConcreteCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartOrdEmb.Hom.injective`：∀ {X Y : PartOrdEmb} (f : X ⟶ Y), Function.Inj
ective ⇑(CategoryTheory.ConcreteCategory.hom f)
-/
lemma Hom.injective {J₁ J₂ : CardinalDirectedPoset κ} (f : J₁ ⟶ J₂) :
    Function.Injective f := f.hom.injective
/-
**CategoryTheory.CardinalDirectedPoset.Hom.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.CardinalDirectedPoset.Hom`。
形式化陈述：∀ {κ : Cardinal.{u}} [inst : Fact κ.IsRegular] {J₁ J₂ : CategoryTheory.Car
dinalDirectedPoset κ} (f : J₁ ⟶ J₂)   (x₁ x₂ : ↑J₁.obj), (CategoryTheory.Concret
eCategory.hom f) x₁ ≤ (CategoryTheory.ConcreteCategory.hom f) x₂ ↔ x₁ ≤ x₂
参数：f : J₁ ⟶ J₂；x₁ x₂ : ↑J₁.obj；CategoryTheory.ConcreteCategory.hom f；CategoryThe
ory.ConcreteCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
lemma Hom.le_iff_le {J₁ J₂ : CardinalDirectedPoset κ} (f : J₁ ⟶ J₂) (x₁ x₂ : J₁.obj) :
    f x₁ ≤ f x₂ ↔ x₁ ≤ x₂ :=
  f.hom.hom.le_iff_le
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : CardinalDirectedPoset κ) : IsCardinalFiltered J.obj κ := J.property
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : CardinalDirectedPoset κ) : IsFiltered J.obj :=
  isFiltered_of_isCardinalFiltered _ κ
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : CardinalDirectedPoset κ) : Nonempty J.obj := IsFiltered.nonempty
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasCardinalFilteredColimits (CardinalDirectedPoset κ) κ where
  hasColimitsOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Type u) [SmallCategory A] [IsCardinalFiltered A κ] :
    PreservesColimitsOfShape A (forget (CardinalDirectedPoset κ)) := by
  have := isFiltered_of_isCardinalFiltered A κ
  change PreservesColimitsOfShape A (CardinalDirectedPoset.ι ⋙ forget _)
  infer_instance
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : CardinalDirectedPoset κ) (κ' : Cardinal.{u}) [Fact κ'.IsRegular] :
    IsCardinalFiltered (WithTop (J.obj)) κ' :=
  isCardinalFiltered_of_hasTerminal _ _

/-- The map `CardinalDirectedPoset κ → CardinalDirectedPoset κ` which sends
a partially ordered `κ`-filtered type `J` to `WithTop J`. -/
/-
**CategoryTheory.CardinalDirectedPoset.withTop** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.CardinalDirectedPoset`。
形式化陈述：withTop (J : CardinalDirectedPoset κ) : CardinalDirectedPoset κ
参数：J : CardinalDirectedPoset κ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredWithTopCarrie
rObjPartOrdEmbIsCardinalFiltered`：∀ {κ : Cardinal.{u}} [inst : Fact κ.IsRegular]
 (J : CategoryTheory.CardinalDirectedPoset κ) (κ' : Cardinal.{u})   [inst_1 : Fa
ct κ'.IsRegula…

--- 原说明 ---
The map `CardinalDirectedPoset κ → CardinalDirectedPoset κ` which sends
a partially ordered `κ`-filtered type `J` to `WithTop J`.
-/
abbrev withTop (J : CardinalDirectedPoset κ) : CardinalDirectedPoset κ :=
  .of (.of (WithTop J.obj))

section

variable {J : CardinalDirectedPoset κ} (P : Set J.obj → Prop)
  [IsDirectedOrder (Subtype P)] [Nonempty (Subtype P)]
  [∀ (S : Subtype P), IsCardinalFiltered S.val κ]

set_option backward.defeqAttrib.useBackward true in
/-- Given a predicate `P : Set J.obj → Prop` on the underlying type
of `J : CardinalDirectedPoset κ` such that all the subsets satisfying `P`
are `κ`-filtered, this is the functor `Subtype P ⥤ CardinalDirectedPoset κ`
which sends a subset `S` of `J` satisfying `P` to the induced
partially ordered type `J`, as an object in `CardinalDirectedPoset κ`. -/
@[simps!]
/-
**CategoryTheory.CardinalDirectedPoset.functorOfPredicateSet** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：functorOfPredicateSet : Subtype P ⥤ CardinalDirectedPoset κ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `P : Set J.obj → Prop` on the underlying type
of `J : CardinalDirectedPoset κ` such that all the subsets satisfying `P`
are `κ`-filtered, this is the functor `Subtype P ⥤ CardinalDirectedPoset κ`
which sends a subset `S` of `J` satisfying `P` to the induced
partially ordered type `J`, as an object in `CardinalDirectedPoset κ`.
-/
def functorOfPredicateSet : Subtype P ⥤ CardinalDirectedPoset κ :=
  ObjectProperty.lift _ (PartOrdEmb.functorOfPredicateSet P)
    (fun S ↦ by dsimp; infer_instance)

/-- Given a predicate `P : Set J.obj → Prop` on the underlying type
of `J : CardinalDirectedPoset κ` such that all the subsets satisfying `P`
are `κ`-filtered, this is the cocone with point `J` given
by all the inclusions of the subsets satisfying `P`. -/
@[simps]
/-
**CategoryTheory.CardinalDirectedPoset.coconeOfPredicateSet** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：coconeOfPredicateSet : Cocone (functorOfPredicateSet P) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `P : Set J.obj → Prop` on the underlying type
of `J : CardinalDirectedPoset κ` such that all the subsets satisfying `P`
are `κ`-filtered, this is the cocone with point `J` given
by all the inclusions of the subsets satisfying `P`.
-/
def coconeOfPredicateSet : Cocone (functorOfPredicateSet P) where
  pt := J
  ι.app j := ObjectProperty.homMk ((PartOrdEmb.coconeOfPredicateSet P).ι.app j)

/-- Let `P` be a predicate on `Set J.obj` where `J : CardinalDirectedPoset κ`.
We assume that `Subtype P` is directed and nonempty, and that any `a : J.obj`
belongs to some `S : Set J.obj` satisfying `P`. Then, `J` is the colimit in the
category `CardinalDirectedPoset κ` of these subsets. -/
/-
**CategoryTheory.CardinalDirectedPoset.isColimitCoconeOfPredicateSet** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：isColimitCoconeOfPredicateSet (hP : forall (a : J.obj), exists (S : Set J.
obj), P S ∧ a in S) : IsColimit (coconeOfPredicateSet P)
参数：hP : forall (a : J.obj), exists (S : Set J.obj), P S ∧ a in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `P` be a predicate on `Set J.obj` where `J : CardinalDirectedPoset κ`.
We assume that `Subtype P` is directed and nonempty, and that any `a : J.obj`
belongs to some `S : Set J.obj` satisfying `P`. Then, `J` is the colimit in the
category `CardinalDirectedPoset κ` of these subsets.
-/
noncomputable def isColimitCoconeOfPredicateSet
    (hP : ∀ (a : J.obj), ∃ (S : Set J.obj), P S ∧ a ∈ S) :
    IsColimit (coconeOfPredicateSet P) :=
  isColimitOfReflects CardinalDirectedPoset.ι
    (PartOrdEmb.isColimitOfPredicateSet P hP)

end

variable (κ) in
/-- The property of posets in `CardinalDirectedPoset κ` that are
of cardinality `< κ` and have terminal object. -/
/-
**CategoryTheory.CardinalDirectedPoset.hasCardinalLTWithTerminal** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：hasCardinalLTWithTerminal : ObjectProperty (CardinalDirectedPoset κ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of posets in `CardinalDirectedPoset κ` that are
of cardinality `< κ` and have terminal object.
-/
def hasCardinalLTWithTerminal : ObjectProperty (CardinalDirectedPoset κ) :=
  fun J ↦ HasCardinalLT J.obj κ ∧ HasTerminal J.obj
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ObjectProperty.EssentiallySmall.{u} (hasCardinalLTWithTerminal κ) where
  exists_small_le' := by
    obtain ⟨X, hX⟩ : ∃ (X : Type u), Cardinal.mk X = κ := ⟨κ.ord.ToType, by simp⟩
    let α : Type u := Σ (S : Set X) (_ : PartialOrder S),
      ULift.{u} (PLift (IsCardinalFiltered S κ))
    let (a : α) : PartialOrder a.1 := a.2.1
    let ι (a : α) : CardinalDirectedPoset κ :=
      { obj := .of a.1
        property := a.2.2.down.down }
    refine ⟨.ofObj ι, inferInstance, fun J ⟨hJ, _⟩ ↦ ?_⟩
    obtain ⟨f⟩ : Cardinal.mk J.obj ≤ Cardinal.mk X := by
      simpa [hX] using ((hasCardinalLT_iff_cardinal_mk_lt _ _).1 hJ).le
    let e := Equiv.ofInjective _ f.injective
    let : PartialOrder (Set.range f) := PartialOrder.lift _ e.symm.injective
    let e' : Set.range f ≃o J.obj := { toEquiv := e.symm, map_rel_iff' := by rfl }
    exact ⟨_, ⟨⟨Set.range f, inferInstance,
      ⟨⟨IsCardinalFiltered.of_equivalence κ e'.symm.equivalence⟩⟩⟩⟩,
        ⟨CardinalDirectedPoset.ι.preimageIso (PartOrdEmb.Iso.mk (by exact e'.symm))⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CardinalDirectedPoset.isCardinalPresentable_of_hasCardinalLT_of
_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：isCardinalPresentable_of_hasCardinalLT_of_le (J : CardinalDirectedPoset κ)
 {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (hJ : HasCardinalLT J.obj κ') (h : κ <=
 κ') : IsCardinalPresentable J κ' where preservesColimitOfShape A _ _
参数：J : CardinalDirectedPoset κ；hJ : HasCardinalLT J.obj κ'；h : κ <= κ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用引理 `CategoryTheory.IsCardinalFiltered.of_le`：of_le {κ' : Cardinal.{w}} [Fact
 κ'.IsRegular] (h : κ' <= κ) : IsCardinalFiltered J κ' where nonempty_cocone F h
A
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instPreservesColimitsOfShapeForgetO
rderEmbeddingCarrierObjPartOrdEmbIsCardinalFilteredOfIsCardinalFiltered`：∀ {κ : 
Cardinal.{u}} [inst : Fact κ.IsRegular] (A : Type u) [inst_1 : CategoryTheory.Sm
allCategory A]   [CategoryTheory.IsCardinalFiltered A…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `CategoryTheory.CardinalDirectedPoset.Hom.injective`：∀ {κ : Cardinal.{u}}
 [inst : Fact κ.IsRegular] {J₁ J₂ : CategoryTheory.CardinalDirectedPoset κ} (f :
 J₁ ⟶ J₂),   Function.Injective ⇑(Catego…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RelEmbedding.instEmbeddingLike`：∀ {α : Type u_1} {β : Type u_2} {r : α →
 α → Prop} {s : β → β → Prop}, EmbeddingLike (r ↪r s) α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.CardinalDirectedPoset.Hom.le_iff_le`：∀ {κ : Cardinal.{u}}
 [inst : Fact κ.IsRegular] {J₁ J₂ : CategoryTheory.CardinalDirectedPoset κ} (f :
 J₁ ⟶ J₂)   (x₁ x₂ : ↑J₁.obj), (Category…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用引理 `PartOrdEmb.hom_ext`：hom_ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (hf : f.hom
 = g.hom) : f = g
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
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
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`：isColimit
_eq_iff' {t : Cocone F} (ht : IsColimit t) {i : J} (x y : F.obj i) : t.ι.app i x
 = t.ι.app i y ↔ exists (j : _) (f : i ⟶ j), F.map …
-/
lemma isCardinalPresentable_of_hasCardinalLT_of_le (J : CardinalDirectedPoset κ)
    {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (hJ : HasCardinalLT J.obj κ') (h : κ ≤ κ') :
    IsCardinalPresentable J κ' where
  preservesColimitOfShape A _ _ := ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
  · have := isFiltered_of_isCardinalFiltered A κ'
    have := IsCardinalFiltered.of_le A h
    replace hc := isColimitOfPreserves (forget _) hc
    refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f g h ↦ ?_)
    · dsimp at f
      choose j g hg using fun (x : J.obj) ↦ Types.jointly_surjective_of_isColimit hc (f x)
      let m := IsCardinalFiltered.max j hJ
      let φ (x : J.obj) : (F.obj m).obj := F.map (IsCardinalFiltered.toMax j hJ x) (g x)
      have hφ (x : J.obj) : f x = c.ι.app _ (φ x) := by
        dsimp [φ]
        rw [← hg, ← ConcreteCategory.comp_apply, c.w]
        rfl
      refine ⟨m,
        ObjectProperty.homMk (PartOrdEmb.ofHom
          { toFun := φ
            inj' x y h := Hom.injective f (by simpa [hφ])
            map_rel_iff' {x y} := ?_ }), ?_⟩
      · simp [← Hom.le_iff_le f, hφ]
      · dsimp
        ext x
        trans c.ι.app (j x) (g x)
        · exact (hg x).symm
        · exact (ConcreteCategory.congr_hom (c.w (IsCardinalFiltered.toMax j hJ x)).symm (g x))
    · choose k a hk using fun (x : J.obj) ↦
        (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (ConcreteCategory.congr_hom h x)
      dsimp at f g h k a hk ⊢
      obtain ⟨l, b, c, hl⟩ : ∃ (l : A) (c : j ⟶ l) (b : ∀ x, k x ⟶ l),
          ∀ x, a x ≫ b x = c := by
        let φ (x : J.obj) : j ⟶ IsCardinalFiltered.max k hJ :=
          a x ≫ IsCardinalFiltered.toMax k hJ x
        exact ⟨IsCardinalFiltered.coeq φ hJ,
          IsCardinalFiltered.toCoeq φ hJ,
          fun x ↦ IsCardinalFiltered.toMax k hJ x ≫ IsCardinalFiltered.coeqHom φ hJ,
          fun x ↦ by simpa [φ] using IsCardinalFiltered.coeq_condition φ hJ x⟩
      refine ⟨l, b, ?_⟩
      ext x
      simpa only [← hl x, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
        PartOrdEmb.hom_comp, RelEmbedding.coe_trans, Function.comp_apply]
          using! congr_arg _ (hk x)⟩⟩⟩

section

variable (J : CardinalDirectedPoset κ)

-- `@[nolint unusedArguments]` allows to setup some instances which uses
-- the fact that `κ'` is regular.
/-- Given `J : CardinalFilteredPoset κ` and a regular cardinal `κ'`,
this is the predicate on `Set J.withTop.obj` that is satisfied by
subsets that are of cardinality `< κ'` and contain `⊤`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.CardinalDirectedPoset.PropSetWithTop** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.CardinalDirectedPoset`。
形式化陈述：PropSetWithTop (κ' : Cardinal.{u}) [Fact κ'.IsRegular] (S : Set J.withTop.
obj) : Prop
参数：κ' : Cardinal.{u}；S : Set J.withTop.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `J : CardinalFilteredPoset κ` and a regular cardinal `κ'`,
this is the predicate on `Set J.withTop.obj` that is satisfied by
subsets that are of cardinality `< κ'` and contain `⊤`.
-/
def PropSetWithTop (κ' : Cardinal.{u}) [Fact κ'.IsRegular]
    (S : Set J.withTop.obj) : Prop :=
  HasCardinalLT S κ' ∧ ⊤ ∈ S

variable (κ' : Cardinal.{u}) [Fact κ'.IsRegular]
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Subtype (J.PropSetWithTop κ')) : HasTerminal S :=
  IsTerminal.hasTerminal (X := ⟨⊤, S.2.2⟩)
    (IsTerminal.ofUniqueHom (fun _ ↦ homOfLE (by rw [Subtype.mk_le_mk]; exact le_top))
      (fun _ _ ↦ rfl))
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Subtype (J.PropSetWithTop κ')) : IsCardinalFiltered S κ :=
  isCardinalFiltered_of_hasTerminal _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCardinalFiltered (Subtype (J.PropSetWithTop κ')) κ' :=
  isCardinalFiltered_preorder _ _ (fun K α hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have hκ' : Cardinal.aleph0 ≤ κ' := Cardinal.IsRegular.aleph0_le Fact.out
    refine ⟨⟨(⋃ (k : K), α k) ∪ {⊤},
      hasCardinalLT_union hκ' (hasCardinalLT_iUnion _ hK (fun k ↦ (α k).property.left))
        (hasCardinalLT_of_finite _ _ hκ'), by simp⟩, fun k ↦ ?_⟩
    rw [Subtype.mk_le_mk]
    exact subset_trans (Set.subset_iUnion (fun i ↦ (α i).1) k) Set.subset_union_left)
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFiltered (Subtype (J.PropSetWithTop κ')) :=
  isFiltered_of_isCardinalFiltered _ κ'
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDirectedOrder (Subtype (J.PropSetWithTop κ')) :=
  IsFiltered.isDirectedOrder _
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (Subtype (J.PropSetWithTop κ')) :=
  IsFiltered.nonempty

variable {J} in
/-
**CategoryTheory.CardinalDirectedPoset.propSetWithTop_pair** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：propSetWithTop_pair (j : J.obj) : J.PropSetWithTop κ' {WithTop.some j, ⊤}
参数：j : J.obj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_of_finite`：hasCardinalLT_of_finite (X : Type*) [Finite X] 
(κ : Cardinal) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT X κ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma propSetWithTop_pair (j : J.obj) : J.PropSetWithTop κ' {WithTop.some j, ⊤} :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out),
    Set.mem_insert_of_mem _ (by simp)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.CardinalDirectedPoset.exists_mem_propSetWithTop** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：exists_mem_propSetWithTop (a : J.withTop.obj) : exists S, J.PropSetWithTop
 κ' S ∧ a in S
参数：a : J.withTop.obj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instNonemptyCarrierObjPartOrdEmbIsC
ardinalFiltered`：∀ {κ : Cardinal.{u}} [inst : Fact κ.IsRegular] (J : CategoryThe
ory.CardinalDirectedPoset κ), Nonempty ↑J.obj
· 使用引理 `CategoryTheory.CardinalDirectedPoset.propSetWithTop_pair`：propSetWithTop
_pair (j : J.obj) : J.PropSetWithTop κ' {WithTop.some j, ⊤}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma exists_mem_propSetWithTop (a : J.withTop.obj) :
    ∃ S, J.PropSetWithTop κ' S ∧ a ∈ S := by
  induction a with
  | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
  | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩

/-- If `J : CardinalFilteredPoset κ` and `κ'` is any regular cardinal,
this is a colimit cocone which exhibits `J.withTop` as the `κ'`-filtered
colimit of its subsets that are of cardinality `< κ'` and contain `⊤`. -/
/-
**CategoryTheory.CardinalDirectedPoset.coconeWithTop** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：coconeWithTop : Cocone (functorOfPredicateSet (J.PropSetWithTop κ'))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredElemCarrierOb
jPartOrdEmbIsCardinalFilteredWithTopValSetPropSetWithTop`：∀ {κ : Cardinal.{u}} [
inst : Fact κ.IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (κ' : Card
inal.{u})   [inst_1 : Fact κ'.IsRegula…

--- 原说明 ---
If `J : CardinalFilteredPoset κ` and `κ'` is any regular cardinal,
this is a colimit cocone which exhibits `J.withTop` as the `κ'`-filtered
colimit of its subsets that are of cardinality `< κ'` and contain `⊤`.
-/
abbrev coconeWithTop : Cocone (functorOfPredicateSet (J.PropSetWithTop κ')) :=
  coconeOfPredicateSet (PropSetWithTop J κ')

set_option backward.isDefEq.respectTransparency.types false in
/-- If `J : CardinalDirectedPoset κ` and `κ'` is any regular cardinal,
then `J.withTop` is the `κ'`-filtered colimit of its subsets that are of
cardinality `< κ'` and contain `⊤`. -/
/-
**CategoryTheory.CardinalDirectedPoset.isColimitCoconeWithTop** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：isColimitCoconeWithTop : IsColimit (coconeWithTop J κ')
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsDirectedOrderSubtypeSetCarrie
rObjPartOrdEmbIsCardinalFilteredWithTopPropSetWithTop`：∀ {κ : Cardinal.{u}} [ins
t : Fact κ.IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (κ' : Cardina
l.{u})   [inst_1 : Fact κ'.IsRegula…
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instNonemptySubtypeSetCarrierObjPar
tOrdEmbIsCardinalFilteredWithTopPropSetWithTop`：∀ {κ : Cardinal.{u}} [inst : Fac
t κ.IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (κ' : Cardinal.{u}) 
  [inst_1 : Fact κ'.IsRegula…
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredElemCarrierOb
jPartOrdEmbIsCardinalFilteredWithTopValSetPropSetWithTop`：∀ {κ : Cardinal.{u}} [
inst : Fact κ.IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (κ' : Card
inal.{u})   [inst_1 : Fact κ'.IsRegula…

--- 原说明 ---
If `J : CardinalDirectedPoset κ` and `κ'` is any regular cardinal,
then `J.withTop` is the `κ'`-filtered colimit of its subsets that are of
cardinality `< κ'` and contain `⊤`.
-/
noncomputable def isColimitCoconeWithTop : IsColimit (coconeWithTop J κ') :=
  isColimitCoconeOfPredicateSet _ (fun a ↦ by
    induction a with
    | some a => exact ⟨_, propSetWithTop_pair _ a, by aesop⟩
    | none => exact ⟨_, propSetWithTop_pair _ (Classical.arbitrary _), by aesop⟩)

variable {κ'} in
/-
**CategoryTheory.CardinalDirectedPoset.isCardinalPresentable_iff** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：∀ {κ : Cardinal.{u}} [inst : Fact κ.IsRegular] (J : CategoryTheory.Cardina
lDirectedPoset κ) {κ' : Cardinal.{u}}   [inst_1 : Fact κ'.IsRegular], κ ≤ κ' → (
CategoryTheory.IsCardinalPresentable J κ' ↔ HasCardinalLT (↑J.obj) κ')
参数：J : CategoryTheory.CardinalDirectedPoset κ；CategoryTheory.IsCardinalPresentab
le J κ' ↔ HasCardinalLT (↑J.obj) κ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredElemCarrierOb
jPartOrdEmbIsCardinalFilteredWithTopValSetPropSetWithTop`：∀ {κ : Cardinal.{u}} [
inst : Fact κ.IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (κ' : Card
inal.{u})   [inst_1 : Fact κ'.IsRegula…
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [in
st_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_thin`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [Quiver.IsThin C], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredSubtypeSetCar
rierObjPartOrdEmbIsCardinalFilteredWithTopPropSetWithTop`：∀ {κ : Cardinal.{u}} [
inst : Fact κ.IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (κ' : Card
inal.{u})   [inst_1 : Fact κ'.IsRegula…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.coe_injective`：∀ {α : Type u_1}, Function.Injective WithTop.some
· 使用引理 `CategoryTheory.CardinalDirectedPoset.isCardinalPresentable_of_hasCardina
lLT_of_le`：isCardinalPresentable_of_hasCardinalLT_of_le (J : CardinalDirectedPos
et κ) {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (hJ : HasCardinalLT J.obj…
-/
protected lemma isCardinalPresentable_iff (h : κ ≤ κ') :
    IsCardinalPresentable J κ' ↔ HasCardinalLT J.obj κ' := by
  refine ⟨fun _ ↦ ?_, fun hJ ↦ isCardinalPresentable_of_hasCardinalLT_of_le _ hJ h⟩
  obtain ⟨X, f, hf⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit κ' (isColimitCoconeWithTop J κ')
      (ObjectProperty.homMk (PartOrdEmb.ofHom WithTop.coeOrderHom))
  replace hf : OrderEmbedding.subtype (· ∈ X.1) ∘ f = WithTop.coeOrderHom := by
    ext x
    exact ConcreteCategory.congr_hom hf x
  refine X.2.1.of_injective f (Function.Injective.of_comp
    (f := OrderEmbedding.subtype (· ∈ X.1)) ?_)
  dsimp at hf ⊢
  rw [hf]
  exact WithTop.coe_injective

end

/-
**CategoryTheory.CardinalDirectedPoset.isCardinalPresentable_iff'** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：∀ {κ : Cardinal.{u}} [inst : Fact κ.IsRegular] (J : CategoryTheory.Cardina
lDirectedPoset κ),   CategoryTheory.IsCardinalPresentable J κ ↔ HasCardinalLT (↑
J.obj) κ
参数：J : CategoryTheory.CardinalDirectedPoset κ；↑J.obj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.isCardinalPresentable_iff`：∀ {κ : C
ardinal.{u}} [inst : Fact κ.IsRegular] (J : CategoryTheory.CardinalDirectedPoset
 κ) {κ' : Cardinal.{u}}   [inst_1 : Fact κ'.IsRegula…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected lemma isCardinalPresentable_iff' (J : CardinalDirectedPoset κ) :
    IsCardinalPresentable J κ ↔ HasCardinalLT J.obj κ :=
  CardinalDirectedPoset.isCardinalPresentable_iff _ (le_refl _)

section

variable (J : CardinalDirectedPoset κ)

/-- Given `J : CardinalDirectedPoset κ`, this is the predicate
on `Set J.obj` that is satisfied by subsets that are of
cardinality `< κ` and have a terminal object. -/
/-
**CategoryTheory.CardinalDirectedPoset.PropSet** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.CardinalDirectedPoset`。
形式化陈述：PropSet (S : Set J.obj) : Prop
参数：S : Set J.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `J : CardinalDirectedPoset κ`, this is the predicate
on `Set J.obj` that is satisfied by subsets that are of
cardinality `< κ` and have a terminal object.
-/
def PropSet (S : Set J.obj) : Prop :=
  HasCardinalLT S κ ∧ HasTerminal S
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Subtype J.PropSet) : HasTerminal S := S.prop.2
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Subtype J.PropSet) : IsCardinalFiltered S κ :=
  isCardinalFiltered_of_hasTerminal _ _

variable {J} in
/-
**CategoryTheory.CardinalDirectedPoset.propSet_singleton** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：propSet_singleton (j : J.obj) : J.PropSet {j}
参数：j : J.obj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasCardinalLT_of_finite`：hasCardinalLT_of_finite (X : Type*) [Finite X] 
(κ : Cardinal) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT X κ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Limits.IsTerminal.hasTerminal`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsTerminal 
X),   CategoryTheory.Limits.HasTer…
-/
lemma propSet_singleton (j : J.obj) : J.PropSet {j} :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out), by
    let : OrderTop ({j} : Set J.obj) := { top := ⟨j, rfl⟩, le_top := by simp }
    exact isTerminalTop.hasTerminal⟩
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCardinalFiltered (Subtype J.PropSet) κ :=
  isCardinalFiltered_preorder _ _ (fun K α hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    let t (k : K) : (α k).val := ⊤_ _
    let m := IsCardinalFiltered.max (fun k ↦ (t k).val) hK
    let S : Set J.obj := (⋃ (k : K), α k) ∪ {m}
    let : OrderTop S :=
      { top := ⟨m, by simp [S]⟩
        le_top := by
          rintro ⟨s, hs⟩
          simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_iUnion, S] at hs
          obtain rfl | ⟨k, hs⟩ := hs
          · simp
          · simp only [Subtype.mk_le_mk]
            exact leOfHom ((by exact terminal.from (C := (α k).val) ⟨_, hs⟩) ≫
              IsCardinalFiltered.toMax _ hK k) }
    refine ⟨⟨S, ?_, isTerminalTop.hasTerminal⟩, fun k ↦ ?_⟩
    · have hκ : Cardinal.aleph0 ≤ κ :=  Cardinal.IsRegular.aleph0_le Fact.out
      exact hasCardinalLT_union hκ (hasCardinalLT_iUnion _ hK (fun k ↦ (α k).2.1))
        (hasCardinalLT_of_finite _ _ hκ)
    · simp only [← Subtype.coe_le_coe]
      exact subset_trans (Set.subset_iUnion_of_subset k (subset_refl _)) Set.subset_union_left )
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFiltered (Subtype J.PropSet) := isFiltered_of_isCardinalFiltered _ κ
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDirectedOrder (Subtype J.PropSet) :=
  IsFiltered.isDirectedOrder _
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (Subtype J.PropSet) :=
  IsFiltered.nonempty

/-- For any object `J : CardinalDirectedPoset κ`, this is a colimit
cocone exhibiting `J` as the colimit of its subsets
that are of cardinality `< κ` and have a terminal object. -/
/-
**CategoryTheory.CardinalDirectedPoset.cocone** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.CardinalDirectedPoset`。
形式化陈述：cocone : Cocone (functorOfPredicateSet J.PropSet)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredElemCarrierOb
jPartOrdEmbIsCardinalFilteredValSetPropSet`：∀ {κ : Cardinal.{u}} [inst : Fact κ.
IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (S : Subtype J.PropSet),
   CategoryTheory.IsCard…

--- 原说明 ---
For any object `J : CardinalDirectedPoset κ`, this is a colimit
cocone exhibiting `J` as the colimit of its subsets
that are of cardinality `< κ` and have a terminal object.
-/
abbrev cocone : Cocone (functorOfPredicateSet J.PropSet) :=
  coconeOfPredicateSet J.PropSet

/-- Any object `J : CardinalDirectedPoset κ` is a colimit
of its subsets that are of cardinality `< κ` and have a terminal object. -/
/-
**CategoryTheory.CardinalDirectedPoset.isColimitCocone** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：isColimitCocone (J : CardinalDirectedPoset κ) : IsColimit (cocone J)
参数：J : CardinalDirectedPoset κ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsDirectedOrderSubtypeSetCarrie
rObjPartOrdEmbIsCardinalFilteredPropSet`：∀ {κ : Cardinal.{u}} [inst : Fact κ.IsR
egular] (J : CategoryTheory.CardinalDirectedPoset κ),   IsDirectedOrder (Subtype
 J.PropSet)
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instNonemptySubtypeSetCarrierObjPar
tOrdEmbIsCardinalFilteredPropSet`：∀ {κ : Cardinal.{u}} [inst : Fact κ.IsRegular]
 (J : CategoryTheory.CardinalDirectedPoset κ),   Nonempty (Subtype J.PropSet)
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredElemCarrierOb
jPartOrdEmbIsCardinalFilteredValSetPropSet`：∀ {κ : Cardinal.{u}} [inst : Fact κ.
IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (S : Subtype J.PropSet),
   CategoryTheory.IsCard…

--- 原说明 ---
Any object `J : CardinalDirectedPoset κ` is a colimit
of its subsets that are of cardinality `< κ` and have a terminal object.
-/
noncomputable def isColimitCocone (J : CardinalDirectedPoset κ) :
    IsColimit (cocone J) :=
  isColimitCoconeOfPredicateSet _ (fun a ↦ ⟨_, propSet_singleton a, by simp⟩)

end

variable (κ) in
/-
**CategoryTheory.CardinalDirectedPoset.isCardinalFilteredGenerator_hasCardinalLT
WithTerminal** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：isCardinalFilteredGenerator_hasCardinalLTWithTerminal : (hasCardinalLTWith
Terminal κ).IsCardinalFilteredGenerator κ where le_isCardinalPresentable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isCardinalPresentable_iff`：isCardinalPresentable_iff (X :
 C) : isCardinalPresentable C κ X ↔ IsCardinalPresentable X κ
· 使用定理 `CategoryTheory.CardinalDirectedPoset.isCardinalPresentable_iff'`：∀ {κ : 
Cardinal.{u}} [inst : Fact κ.IsRegular] (J : CategoryTheory.CardinalDirectedPose
t κ),   CategoryTheory.IsCardinalPresentable J κ ↔ Ha…
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredSubtypeSetCar
rierObjPartOrdEmbIsCardinalFilteredPropSet`：∀ {κ : Cardinal.{u}} [inst : Fact κ.
IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ),   CategoryTheory.IsCard
inalFiltered (Subtype J.…
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredElemCarrierOb
jPartOrdEmbIsCardinalFilteredValSetPropSet`：∀ {κ : Cardinal.{u}} [inst : Fact κ.
IsRegular] (J : CategoryTheory.CardinalDirectedPoset κ) (S : Subtype J.PropSet),
   CategoryTheory.IsCard…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma isCardinalFilteredGenerator_hasCardinalLTWithTerminal :
    (hasCardinalLTWithTerminal κ).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro J ⟨_, _⟩
    rwa [isCardinalPresentable_iff, J.isCardinalPresentable_iff']
  exists_colimitsOfShape J :=
    ⟨_, inferInstance, inferInstance, ⟨{
      diag := _
      ι := _
      isColimit := isColimitCocone J
      prop_diag_obj j := j.prop }⟩⟩
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCardinalAccessibleCategory (CardinalDirectedPoset κ) κ where
  exists_generator :=
    ⟨hasCardinalLTWithTerminal κ, inferInstance,
      isCardinalFilteredGenerator_hasCardinalLTWithTerminal κ⟩

variable (κ) (X : Type u)

/-- Given a cardinal `κ` and a type `X`, this is the subtype of `Set X`
consisting of subsets of `X` of cardinality `< κ`. -/
/-
**CategoryTheory.CardinalDirectedPoset.SetCardinalLT** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：SetCardinalLT
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cardinal `κ` and a type `X`, this is the subtype of `Set X`
consisting of subsets of `X` of cardinality `< κ`.
-/
abbrev SetCardinalLT := Subtype (fun (S : Set X) ↦ HasCardinalLT S κ)

variable {X} in
/-- Given a regular cardinal `κ` and `x : X`, this is the singleton `{x}`,
considered as a subset of `X` of cardinality `< κ`. -/
/-
**CategoryTheory.CardinalDirectedPoset.SetCardinalLT.singleton** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.CardinalDirectedPoset.SetCardinalLT`。
形式化陈述：(κ : Cardinal.{u}) → [Fact κ.IsRegular] → {X : Type u} → X → CategoryTheor
y.CardinalDirectedPoset.SetCardinalLT κ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a regular cardinal `κ` and `x : X`, this is the singleton `{x}`,
considered as a subset of `X` of cardinality `< κ`.
-/
abbrev SetCardinalLT.singleton (x : X) : SetCardinalLT κ X :=
  ⟨{x}, hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)⟩
/-
**CategoryTheory.CardinalDirectedPoset.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.CardinalDirectedPoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCardinalFiltered (SetCardinalLT κ X) κ :=
  isCardinalFiltered_preorder _ _
    (fun K f hK ↦
      ⟨⟨⋃ (k : K), (f k).val, hasCardinalLT_iUnion _
        (by rwa [hasCardinalLT_iff_cardinal_mk_lt]) (fun k ↦ (f k).prop)⟩,
      Set.subset_iUnion (fun k ↦ (f k).val)⟩)

/-- Given a regular cardinal `κ` and a type `X`, this is the `κ`-filtered
partially ordered type of subsets of `X` of cardinality `< κ`,
as an object of the category `CardinalDirectedPoset κ`. -/
/-
**CategoryTheory.CardinalDirectedPoset.setCardinalLT** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.CardinalDirectedPoset`。
形式化陈述：setCardinalLT : CardinalDirectedPoset κ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CardinalDirectedPoset.instIsCardinalFilteredSetCardinalLT
`：∀ (κ : Cardinal.{u}) [inst : Fact κ.IsRegular] (X : Type u),   CategoryTheory.
IsCardinalFiltered (CategoryTheory.CardinalDirectedPoset.SetCa…

--- 原说明 ---
Given a regular cardinal `κ` and a type `X`, this is the `κ`-filtered
partially ordered type of subsets of `X` of cardinality `< κ`,
as an object of the category `CardinalDirectedPoset κ`.
-/
abbrev setCardinalLT : CardinalDirectedPoset κ :=
  .of (PartOrdEmb.of (SetCardinalLT κ X))

end CardinalDirectedPoset

@[deprecated (since := "2026-06-24")] alias CardinalFilteredPoset :=
  CardinalDirectedPoset

namespace CardinalFilteredPoset

@[deprecated (since := "2026-06-24")] alias ι := CardinalDirectedPoset.ι
@[deprecated (since := "2026-06-24")] alias of := CardinalDirectedPoset.of
@[deprecated (since := "2026-06-24")] alias Hom.injective := CardinalDirectedPoset.Hom.injective
@[deprecated (since := "2026-06-24")] alias Hom.le_iff_le := CardinalDirectedPoset.Hom.le_iff_le
@[deprecated (since := "2026-06-24")] alias withTop := CardinalDirectedPoset.withTop
@[deprecated (since := "2026-06-24")]
alias functorOfPredicateSet := CardinalDirectedPoset.functorOfPredicateSet
@[deprecated (since := "2026-06-24")]
alias coconeOfPredicateSet := CardinalDirectedPoset.coconeOfPredicateSet
@[deprecated (since := "2026-06-24")]
alias isColimitCoconeOfPredicateSet := CardinalDirectedPoset.isColimitCoconeOfPredicateSet
@[deprecated (since := "2026-06-24")]
alias hasCardinalLTWithTerminal := CardinalDirectedPoset.hasCardinalLTWithTerminal
@[deprecated (since := "2026-06-24")]
alias isCardinalPresentable_of_hasCardinalLT_of_le :=
  CardinalDirectedPoset.isCardinalPresentable_of_hasCardinalLT_of_le
@[deprecated (since := "2026-06-24")]
alias PropSetWithTop := CardinalDirectedPoset.PropSetWithTop
@[deprecated (since := "2026-06-24")]
alias propSetWithTop_pair := CardinalDirectedPoset.propSetWithTop_pair
@[deprecated (since := "2026-06-24")]
alias exists_mem_propSetWithTop := CardinalDirectedPoset.exists_mem_propSetWithTop
@[deprecated (since := "2026-06-24")]
alias coconeWithTop := CardinalDirectedPoset.coconeWithTop
@[deprecated (since := "2026-06-24")]
alias isColimitCoconeWithTop := CardinalDirectedPoset.isColimitCoconeWithTop
@[deprecated (since := "2026-06-24")]
alias isCardinalPresentable_iff := CardinalDirectedPoset.isCardinalPresentable_iff
@[deprecated (since := "2026-06-24")]
alias isCardinalPresentable_iff' := CardinalDirectedPoset.isCardinalPresentable_iff'
@[deprecated (since := "2026-06-24")] alias PropSet := CardinalDirectedPoset.PropSet
@[deprecated (since := "2026-06-24")]
alias propSet_singleton := CardinalDirectedPoset.propSet_singleton
@[deprecated (since := "2026-06-24")] alias cocone := CardinalDirectedPoset.cocone
@[deprecated (since := "2026-06-24")] alias isColimitCocone := CardinalDirectedPoset.isColimitCocone

end CardinalFilteredPoset

end CategoryTheory

