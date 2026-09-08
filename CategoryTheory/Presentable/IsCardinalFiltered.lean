/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # κ-filtered category

If `κ` is a regular cardinal, we introduce the notion of `κ`-filtered
category `J`: it means that any functor `A ⥤ J` from a small category such
that `Arrow A` is of cardinality `< κ` admits a cocone.
This generalizes the notion of filtered category.
Indeed, we obtain the equivalence `IsCardinalFiltered J ℵ₀ ↔ IsFiltered J`.
The API is mostly parallel to that of filtered categories.

A preordered type `J` is a `κ`-filtered category (i.e. `κ`-directed set)
if any subset of `J` of cardinality `< κ` has an upper bound.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

/-- A category `J` is `κ`-filtered (for a regular cardinal `κ`) if
any functor `F : A ⥤ J` from a category `A` such that `HasCardinalLT (Arrow A) κ`
admits a cocone. See `isCardinalFiltered_iff` for a more
concrete characterization of `κ`-filtered categories. -/
/-
**CategoryTheory.IsCardinalFiltered** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`
。
形式化陈述：(J : Type u) → [CategoryTheory.Category.{v, u} J] → (κ : Cardinal.{w}) → [
Fact κ.IsRegular] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `J` is `κ`-filtered (for a regular cardinal `κ`) if
any functor `F : A ⥤ J` from a category `A` such that `HasCardinalLT (Arrow A) κ
`
admits a cocone. See `isCardinalFiltered_iff` for a more
concrete characterization of `κ`-filtered categories.
-/
class IsCardinalFiltered (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  nonempty_cocone {A : Type w} [SmallCategory A] (F : A ⥤ J)
    (hA : HasCardinalLT (Arrow A) κ) : Nonempty (Cocone F)
/-
**CategoryTheory.hasCardinalLT_arrow_walkingParallelFamily** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory`。
形式化陈述：hasCardinalLT_arrow_walkingParallelFamily {T : Type u} {κ : Cardinal.{w}} 
(hT : HasCardinalLT T κ) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT (Arrow (Wal
kingParallelFamily T)) κ
参数：hT : HasCardinalLT T κ；hκ : Cardinal.aleph0 <= κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
· 使用引理 `hasCardinalLT_option_iff`：hasCardinalLT_option_iff (X : Type u) (κ : Car
dinal.{w}) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT (Option X) κ ↔ HasCardina
lLT X κ
-/
lemma hasCardinalLT_arrow_walkingParallelFamily {T : Type u}
    {κ : Cardinal.{w}} (hT : HasCardinalLT T κ) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (Arrow (WalkingParallelFamily T)) κ := by
  simpa only [hasCardinalLT_iff_of_equiv (WalkingParallelFamily.arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ] using hT

namespace IsCardinalFiltered

variable {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

/-- A choice of cocone for a functor `F : A ⥤ J` such that `HasCardinalLT (Arrow A) κ`
when `J` is a `κ`-filtered category, and `Arrow A` has cardinality `< κ`. -/
/-
**CategoryTheory.IsCardinalFiltered.cocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.IsCardinalFiltered`。
形式化陈述：cocone {A : Type v'} [Category.{u'} A] (F : A ⥤ J) (hA : HasCardinalLT (Ar
row A) κ) : Cocone F
参数：F : A ⥤ J；hA : HasCardinalLT (Arrow A) κ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.small_of_small_arrow`：small_of_small_arrow (C : Type u) [
Category.{v} C] [Small.{w} (Arrow C)] : Small.{w} C
· 使用引理 `CategoryTheory.locallySmall_of_small_arrow`：locallySmall_of_small_arrow 
(C : Type u) [Category.{v} C] [Small.{w} (Arrow C)] : LocallySmall.{w} C where h
om_small X Y
· 使用定理 `CategoryTheory.Shrink.instLocallySmallShrink`：∀ (C : Type u) [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : Small.{w', u} C]   [CategoryTheory.Loca
llySmall.{w, v, u} C], CategoryThe…

--- 原说明 ---
A choice of cocone for a functor `F : A ⥤ J` such that `HasCardinalLT (Arrow A) 
κ`
when `J` is a `κ`-filtered category, and `Arrow A` has cardinality `< κ`.
-/
noncomputable def cocone {A : Type v'} [Category.{u'} A]
    (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ) :
    Cocone F := by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocone.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inverse ⋙ F) (by simpa)).some

variable (J) in
/-
**CategoryTheory.IsCardinalFiltered.of_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.IsCardinalFiltered`。
形式化陈述：of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' <= κ) : IsCardinalFi
ltered J κ' where nonempty_cocone F hA
参数：h : κ' <= κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_le`：of_le {κ' : Cardinal.{v}} (hκ' : κ <= κ') : HasCard
inalLT X κ'
-/
lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' ≤ κ) :
    IsCardinalFiltered J κ' where
  nonempty_cocone F hA := ⟨cocone F (hA.of_le h)⟩

variable (κ) in
/-
**CategoryTheory.IsCardinalFiltered.of_equivalence** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.IsCardinalFiltered`。
形式化陈述：of_equivalence {J' : Type u'} [Category.{v'} J'] (e : J ≌ J') : IsCardinal
Filtered J' κ where nonempty_cocone F hA
参数：e : J ≌ J'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma of_equivalence {J' : Type u'} [Category.{v'} J'] (e : J ≌ J') :
    IsCardinalFiltered J' κ where
  nonempty_cocone F hA := ⟨e.inverse.mapCoconeInv (cocone (F ⋙ e.inverse) hA)⟩

section max

variable {K : Type u'} (S : K → J) (hS : HasCardinalLT K κ)

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a choice of objects in `J` which is the target of a map from any of
the objects `S k`. -/
/-
**CategoryTheory.IsCardinalFiltered.max** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.IsCardinalFiltered`。
形式化陈述：max : J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered cat
egory,
this is a choice of objects in `J` which is the target of a map from any of
the objects `S k`.
-/
noncomputable def max : J :=
  (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).pt

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a choice of map `S k ⟶ max S hS` for any `k : K`. -/
/-
**CategoryTheory.IsCardinalFiltered.toMax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.IsCardinalFiltered`。
形式化陈述：toMax (k : K) : S k ⟶ max S hS
参数：k : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered cat
egory,
this is a choice of map `S k ⟶ max S hS` for any `k : K`.
-/
noncomputable def toMax (k : K) :
    S k ⟶ max S hS :=
  (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).ι.app ⟨k⟩

end max

section coeq

variable {K : Type v'} {j j' : J} (f : K → (j ⟶ j')) (hK : HasCardinalLT K κ)

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, this is an object of `J` where these morphisms
shall be equalized. -/
/-
**CategoryTheory.IsCardinalFiltered.coeq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.IsCardinalFiltered`。
形式化陈述：coeq : J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, this is an object of `J` where these morphisms
shall be equalized.
-/
noncomputable def coeq : J :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).pt

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, and `k : K`, this is a choice of morphism `j' ⟶ coeq f hK`. -/
/-
**CategoryTheory.IsCardinalFiltered.coeqHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.IsCardinalFiltered`。
形式化陈述：coeqHom : j' ⟶ coeq f hK
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, and `k : K`, this is a choice of morphism `j' ⟶ coeq f
 hK`.
-/
noncomputable def coeqHom : j' ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .one

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, this is a morphism `j ⟶ coeq f hK` which is equal
to all compositions `f k ≫ coeqHom f hK` for `k : K`. -/
/-
**CategoryTheory.IsCardinalFiltered.toCoeq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.IsCardinalFiltered`。
形式化陈述：toCoeq : j ⟶ coeq f hK
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, this is a morphism `j ⟶ coeq f hK` which is equal
to all compositions `f k ≫ coeqHom f hK` for `k : K`.
-/
noncomputable def toCoeq : j ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .zero

@[reassoc]
/-
**CategoryTheory.IsCardinalFiltered.coeq_condition** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.IsCardinalFiltered`。
形式化陈述：coeq_condition (k : K) : f k ≫ coeqHom f hK = toCoeq f hK
参数：k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用引理 `CategoryTheory.hasCardinalLT_arrow_walkingParallelFamily`：hasCardinalLT_
arrow_walkingParallelFamily {T : Type u} {κ : Cardinal.{w}} (hT : HasCardinalLT 
T κ) (hκ : Cardinal.aleph0 <= κ) : HasCardinal…
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
lemma coeq_condition (k : K) : f k ≫ coeqHom f hK = toCoeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).w
    (.line k)

end coeq

/-- Variant of `IsFiltered.span` for `κ`-filtered categories. -/
/-
**CategoryTheory.IsCardinalFiltered.wideSpan** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.IsCardinalFiltered`。
形式化陈述：wideSpan {ι : Type v'} {j : J} {k : ι -> J} (f : forall i, j ⟶ k i) (hι : 
HasCardinalLT ι κ) : exists (m : J) (a : forall i, k i ⟶ m) (b : j ⟶ m), forall 
i, f i ≫ a i = b
参数：f : forall i, j ⟶ k i；hι : HasCardinalLT ι κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.IsCardinalFiltered.coeq_condition`：coeq_condition (k : K)
 : f k ≫ coeqHom f hK = toCoeq f hK

--- 原说明 ---
Variant of `IsFiltered.span` for `κ`-filtered categories.
-/
lemma wideSpan {ι : Type v'} {j : J} {k : ι → J}
    (f : ∀ i, j ⟶ k i) (hι : HasCardinalLT ι κ) :
    ∃ (m : J) (a : ∀ i, k i ⟶ m) (b : j ⟶ m), ∀ i, f i ≫ a i = b := by
  let φ (i : ι) := f i ≫ toMax k hι i
  exact ⟨coeq φ hι, fun i ↦ toMax k hι i ≫ coeqHom φ hι,
    toCoeq φ hι, by simpa [φ] using coeq_condition φ hι⟩

end IsCardinalFiltered

open IsCardinalFiltered in
/-
**CategoryTheory.isFiltered_of_isCardinalFiltered** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：isFiltered_of_isCardinalFiltered (J : Type u) [Category.{v} J] (κ : Cardin
al.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] : IsFiltered J
参数：J : Type u；κ : Cardinal.{w}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsFiltered.iff_cocone_nonempty`：iff_cocone_nonempty : IsF
iltered C ↔ forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), N
onempty (Cocone F)
· 使用引理 `HasCardinalLT.of_le`：of_le {κ' : Cardinal.{v}} (hκ' : κ <= κ') : HasCard
inalLT X κ'
· 使用定理 `CategoryTheory.Arrow.finite`：∀ {C : Type u} [inst : CategoryTheory.Small
Category C] [CategoryTheory.FinCategory C], Finite (CategoryTheory.Arrow C)
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
lemma isFiltered_of_isCardinalFiltered (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] :
    IsFiltered J := by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : HasCardinalLT (Arrow A) κ := by
    refine HasCardinalLT.of_le ?_ hκ.out.aleph0_le
    simp only [hasCardinalLT_aleph0_iff]
    infer_instance
  exact ⟨cocone F hA⟩
/-
**CategoryTheory.IsCardinalFiltered.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.IsCardinalFiltered`。
形式化陈述：∀ (J : Type u) [inst : CategoryTheory.Category.{v, u} J] (κ : Cardinal.{w}
) [hκ : Fact κ.IsRegular]   [CategoryTheory.IsCardinalFiltered J κ], Nonempty J
参数：J : Type u；κ : Cardinal.{w}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
-/
lemma IsCardinalFiltered.nonempty (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] : Nonempty J :=
  have := isFiltered_of_isCardinalFiltered J κ
  IsFiltered.nonempty

attribute [local instance] Cardinal.fact_isRegular_aleph0
/-
**CategoryTheory.isCardinalFiltered_aleph0_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：isCardinalFiltered_aleph0_iff (J : Type u) [Category.{v} J] : IsCardinalFi
ltered J Cardinal.aleph0.{w} ↔ IsFiltered J
参数：J : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Arrow.finite_iff`：∀ (C : Type u) [inst : CategoryTheory.S
mallCategory C],   Finite (CategoryTheory.Arrow C) ↔ Nonempty (CategoryTheory.Fi
nCategory C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasCardinalLT_aleph0_iff`：hasCardinalLT_aleph0_iff (X : Type u) : HasCar
dinalLT X Cardinal.aleph0.{v} ↔ Finite X
-/
lemma isCardinalFiltered_aleph0_iff (J : Type u) [Category.{v} J] :
    IsCardinalFiltered J Cardinal.aleph0.{w} ↔ IsFiltered J := by
  constructor
  · intro
    exact isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [hasCardinalLT_aleph0_iff] at hA
    have := ((Arrow.finite_iff A).1 hA).some
    exact ⟨IsFiltered.cocone F⟩

-- TODO: make a version specialized to linear orders.
-- In a linear order, `h` is equivalent to `κ ≤ Order.cof J`
/-
**CategoryTheory.isCardinalFiltered_preorder** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：isCardinalFiltered_preorder (J : Type w) [Preorder J] (κ : Cardinal.{w}) [
Fact κ.IsRegular] (h : forall ⦃K : Type w⦄ (s : K -> J) (_ : Cardinal.mk K < κ),
 exists (j : J), forall (k : K), s k <= j) : IsCardinalFiltered J κ where nonemp
ty_cocone {A _ F hA}
参数：J : Type w；κ : Cardinal.{w}；h : forall ⦃K : Type w⦄ (s : K -> J) (_ : Cardina
l.mk K < κ), exists (j : J), forall (k : K), s k <= j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.hasCardinalLT_of_hasCardinalLT_arrow`：hasCardinalLT_of_ha
sCardinalLT_arrow {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardi
nalLT (Arrow C) κ) : HasCardinalLT C κ
-/
lemma isCardinalFiltered_preorder (J : Type w) [Preorder J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : ∀ ⦃K : Type w⦄ (s : K → J) (_ : Cardinal.mk K < κ),
      ∃ (j : J), ∀ (k : K), s k ≤ j) :
    IsCardinalFiltered J κ where
  nonempty_cocone {A _ F hA} := by
    obtain ⟨j, hj⟩ := h F.obj (by simpa only [hasCardinalLT_iff_cardinal_mk_lt] using
        hasCardinalLT_of_hasCardinalLT_arrow hA)
    exact ⟨Cocone.mk j
      { app a := homOfLE (hj a)
        naturality _ _ _ := rfl }⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] :
    IsCardinalFiltered κ.ord.ToType κ :=
  isCardinalFiltered_preorder _ _ (fun ι f hs ↦ by
    have h : Function.Surjective (fun i ↦ (⟨f i, i, rfl⟩ : Set.range f)) := fun _ ↦ by aesop
    contrapose! hs
    rw [← hκ.out.cof_ord, ← Ordinal.cof_toType]
    refine (Order.cof_le fun j ↦ ?_).trans (Cardinal.mk_le_of_surjective h)
    obtain ⟨k, hk⟩ := hs j
    exact ⟨_, Set.mem_range_self k, hk.le⟩)

open IsCardinalFiltered

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isCardinalFiltered_under** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：isCardinalFiltered_under (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) 
[Fact κ.IsRegular] [IsCardinalFiltered J κ] (j₀ : J) : IsCardinalFiltered (Under
 j₀) κ where nonempty_cocone {A _} F hA
参数：J : Type u；κ : Cardinal.{w}；j₀ : J。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用引理 `CategoryTheory.hasCardinalLT_of_hasCardinalLT_arrow`：hasCardinalLT_of_ha
sCardinalLT_arrow {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardi
nalLT (Arrow C) κ) : HasCardinalLT C κ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.IsCardinalFiltered.coeq_condition`：coeq_condition (k : K)
 : f k ≫ coeqHom f hK = toCoeq f hK
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isCardinalFiltered_under
    (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] (j₀ : J) : IsCardinalFiltered (Under j₀) κ where
  nonempty_cocone {A _} F hA := ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    let c := cocone (F ⋙ Under.forget j₀) hA
    let x (a : A) : j₀ ⟶ IsFiltered.max j₀ c.pt := (F.obj a).hom ≫ c.ι.app a ≫
      IsFiltered.rightToMax j₀ c.pt
    have hκ' : HasCardinalLT A κ := hasCardinalLT_of_hasCardinalLT_arrow hA
    exact
      { pt := Under.mk (toCoeq x hκ')
        ι :=
          { app a := Under.homMk (c.ι.app a ≫ IsFiltered.rightToMax j₀ c.pt ≫ coeqHom x hκ')
              (by simpa [x] using coeq_condition x hκ' a)
            naturality a b f := by
              ext
              have := c.w f
              dsimp at this ⊢
              simp only [reassoc_of% this, Category.comp_id] } }⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isCardinalFiltered_prod** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：isCardinalFiltered_prod (J₁ : Type u) (J₂ : Type u') [Category.{v} J₁] [Ca
tegory.{v'} J₂] (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalFiltered J₁ κ] 
[IsCardinalFiltered J₂ κ] : IsCardinalFiltered (J₁ × J₂) κ where nonempty_cocone
 F hC
参数：J₁ : Type u；J₂ : Type u'；κ : Cardinal.{w}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Prod.hom_ext`：hom_ext {X Y : C × D} {f g : X ⟶ Y} (h₁ : f
.1 = g.1) (h₂ : f.2 = g.2) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
-/
instance isCardinalFiltered_prod (J₁ : Type u) (J₂ : Type u')
    [Category.{v} J₁] [Category.{v'} J₂] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J₁ κ] [IsCardinalFiltered J₂ κ] :
    IsCardinalFiltered (J₁ × J₂) κ where
  nonempty_cocone F hC := ⟨by
    let c₁ := cocone (F ⋙ Prod.fst _ _) hC
    let c₂ := cocone (F ⋙ Prod.snd _ _) hC
    exact
      { pt := (c₁.pt, c₂.pt)
        ι.app i := (c₁.ι.app i, c₂.ι.app i)
        ι.naturality {i j} f := by
          ext
          · simpa using c₁.w f
          · simpa using c₂.w f }⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.isCardinalFiltered_pi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：isCardinalFiltered_pi {ι : Type u'} (J : ι -> Type u) [forall i, Category.
{v} (J i)] (κ : Cardinal.{w}) [Fact κ.IsRegular] [forall i, IsCardinalFiltered (
J i) κ] : IsCardinalFiltered (forall i, J i) κ where nonempty_cocone F hC
参数：J : ι -> Type u；J i；κ : Cardinal.{w}；J i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pi.ext`：ext {X Y : forall i, C i} {f g : X ⟶ Y} (w : fora
ll i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pi.eval_map`：∀ {I : Type w₀} (C : I → Type u₁) [inst : (i
 : I) → CategoryTheory.Category.{v₁, u₁} (C i)] (i : I)   {X Y : (i : I) → C i} 
(α : X ⟶ Y), (Ca…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
instance isCardinalFiltered_pi {ι : Type u'} (J : ι → Type u) [∀ i, Category.{v} (J i)]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [∀ i, IsCardinalFiltered (J i) κ] :
    IsCardinalFiltered (∀ i, J i) κ where
  nonempty_cocone F hC := ⟨by
    let c (i : ι) := cocone (F ⋙ Pi.eval J i) hC
    exact
      { pt i := (c i).pt
        ι.app X i := (c i).ι.app X
        ι.naturality {X Y} f := by
          ext i
          simpa using! (c i).ι.naturality f }⟩

section

variable {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  (h₁ : (∀ ⦃ι : Type w⦄ (j : ι → J) (_ : HasCardinalLT ι κ),
          ∃ (k : J), ∀ (i : ι), Nonempty (j i ⟶ k)))
  (h₂ : ∀ ⦃ι : Type w⦄ ⦃j k : J⦄ (f : ι → (j ⟶ k)) (_ : HasCardinalLT ι κ),
      ∃ (l : J) (a : k ⟶ l) (b : j ⟶ l), ∀ (i : ι), f i ≫ a = b)

include h₁ h₂ in
omit [Fact κ.IsRegular] in
/-
**CategoryTheory.isCardinalFiltered_iff_aux** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isCardinalFiltered_iff_aux₁ {ι : Type w} {j : J} {k : ι → J}
    (f : ∀ i, j ⟶ k i) (hι : HasCardinalLT ι κ) :
    ∃ (m : J) (a : ∀ i, k i ⟶ m) (b : j ⟶ m), ∀ i, f i ≫ a i = b := by
  obtain ⟨l, hl⟩ := h₁ k hι
  let a (i : ι) := (hl i).some
  obtain ⟨m, b, c, hm⟩ := h₂ (fun i ↦ f i ≫ a i) hι
  exact ⟨m, fun i ↦ a i ≫ b, c, by grind⟩

include h₁ h₂ in
/-
**CategoryTheory.isCardinalFiltered_iff_aux** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isCardinalFiltered_iff_aux₂ {ι : Type w} {j : ι → J} {k : J}
    (f₁ f₂ : ∀ i, j i ⟶ k) (hι : HasCardinalLT ι κ) :
    ∃ (l : J) (a : k ⟶ l), ∀ i, f₁ i ≫ a = f₂ i ≫ a := by
  have (i : ι) : ∃ (l : J) (p : k ⟶ l), f₁ i ≫ p = f₂ i ≫ p := by
    obtain ⟨l, a, b, hl⟩ := h₂ (Sum.elim (fun (_ : PUnit.{w + 1}) ↦ f₁ i)
      (fun (_ : PUnit.{w + 1}) ↦ f₂ i))
        (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
    exact ⟨l, a, (hl (Sum.inl .unit)).trans (hl (Sum.inr .unit)).symm⟩
  choose l p hp using this
  obtain ⟨l, a, b, h⟩ := isCardinalFiltered_iff_aux₁ h₁ h₂ p hι
  exact ⟨l, b, fun i ↦ by grind⟩

set_option backward.defeqAttrib.useBackward true in
variable (J κ) in
/-- A category is `κ`-filtered iff
1. any family of objects of cardinality `< κ` admits a map towards a common object, and
2. any family of morphisms `j ⟶ k` of cardinality `< κ` (between *fixed* objects
   `j` and `k`) can be coequalized by a suitable morphism `k ⟶ l`.
-/
/-
**CategoryTheory.isCardinalFiltered_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
形式化陈述：isCardinalFiltered_iff : IsCardinalFiltered J κ ↔ (forall ⦃ι : Type w⦄ (j 
: ι -> J) (_ : HasCardinalLT ι κ), exists (k : J), forall (i : ι), Nonempty (j i
 ⟶ k)) ∧ forall ⦃ι : Type w⦄ ⦃j k : J⦄ (f : ι -> (j ⟶ k)) (_ : HasCardinalLT ι κ
), exists (l : J) (a : k ⟶ l) (b : j ⟶ l), forall (i : ι), f i ≫ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsCardinalFiltered.coeq_condition`：coeq_condition (k : K)
 : f k ≫ coeqHom f hK = toCoeq f hK
· 使用引理 `CategoryTheory.hasCardinalLT_of_hasCardinalLT_arrow`：hasCardinalLT_of_ha
sCardinalLT_arrow {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} (h : HasCardi
nalLT (Arrow C) κ) : HasCardinalLT C κ
· 使用引理 `CategoryTheory.isCardinalFiltered_iff_aux₂`：isCardinalFiltered_iff_aux₂ 
{ι : Type w} {j : ι -> J} {k : J} (f₁ f₂ : forall i, j i ⟶ k) (hι : HasCardinalL
T ι κ) : exists (l : J) (a : k ⟶…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
A category is `κ`-filtered iff
1. any family of objects of cardinality `< κ` admits a map towards a common obje
ct, and
2. any family of morphisms `j ⟶ k` of cardinality `< κ` (between *fixed* objects
   `j` and `k`) can be coequalized by a suitable morphism `k ⟶ l`.
-/
lemma isCardinalFiltered_iff :
    IsCardinalFiltered J κ ↔
      (∀ ⦃ι : Type w⦄ (j : ι → J) (_ : HasCardinalLT ι κ),
        ∃ (k : J), ∀ (i : ι), Nonempty (j i ⟶ k)) ∧
      ∀ ⦃ι : Type w⦄ ⦃j k : J⦄ (f : ι → (j ⟶ k)) (_ : HasCardinalLT ι κ),
        ∃ (l : J) (a : k ⟶ l) (b : j ⟶ l), ∀ (i : ι), f i ≫ a = b := by
  refine ⟨fun _ ↦ ⟨fun ι j hι ↦ ⟨_, fun i ↦ ⟨toMax j hι i⟩⟩,
    fun ι j k f hι ↦ ⟨_, _, _, coeq_condition f hι⟩⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨fun {A _} F hA ↦ ?_⟩⟩
  obtain ⟨j, hj⟩ := h₁ F.obj (hasCardinalLT_of_hasCardinalLT_arrow hA)
  let a (i : A) : F.obj i ⟶ j := (hj i).some
  obtain ⟨l, b, hb⟩ := isCardinalFiltered_iff_aux₂ h₁ h₂
    (fun (f : Arrow A) ↦ F.map f.hom ≫ a f.right)
    (fun (f : Arrow A) ↦ a f.left) hA
  exact ⟨{
    pt := l
    ι.app i := a i ≫ b
    ι.naturality _ _ f := by simpa using hb (Arrow.mk f) }⟩

end

/-
**CategoryTheory.IsCardinalFiltered.multicoequalizer** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.IsCardinalFiltered`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {κ : Cardinal.{w}
} [inst_1 : Fact κ.IsRegular]   [CategoryTheory.IsCardinalFiltered J κ] {ι : Typ
e v'} {j : ι → J} {k : J} (f₁ f₂ : (i : ι) → j i ⟶ k),   HasCardinalLT ι κ →    
 ∃ l a, ∀ (i : ι), CategoryTheory.CategoryStruct.comp (f₁ i) a = CategoryTheory.
CategoryStruct.comp (f₂ i) a
参数：f₁ f₂ : (i : ι) → j i ⟶ k；i : ι；f₁ i；f₂ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用引理 `CategoryTheory.IsCardinalFiltered.wideSpan`：wideSpan {ι : Type v'} {j : 
J} {k : ι -> J} (f : forall i, j ⟶ k i) (hι : HasCardinalLT ι κ) : exists (m : J
) (a : forall i, k i ⟶ m) (b : j…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.IsFilteredOrEmpty C] {
j j' : C}   (f f' : j ⟶ j') {Z : C} …
-/
lemma IsCardinalFiltered.multicoequalizer
    {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {ι : Type v'} {j : ι → J} {k : J}
    (f₁ f₂ : ∀ i, j i ⟶ k) (hι : HasCardinalLT ι κ) :
    ∃ (l : J) (a : k ⟶ l), ∀ i, f₁ i ≫ a = f₂ i ≫ a := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨l, a, b, h⟩ := IsCardinalFiltered.wideSpan
    (fun i ↦ IsFiltered.coeqHom (f₁ i) (f₂ i)) hι
  exact ⟨l, b, fun i ↦ by rw [← h i, IsFiltered.coeq_condition_assoc]⟩

/-- If `F : J₁ ⥤ J₂` is final and `J₁` is `κ`-filtered, then
`J₂` is also `κ`-filtered. See also `IsFiltered.of_final`
(in `CategoryTheory.Limits.Final`) for the particular case of
filtered categories (`κ = ℵ₀`). -/
/-
**CategoryTheory.IsCardinalFiltered.of_final** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.IsCardinalFiltered`。
形式化陈述：∀ {J₁ : Type u} [inst : CategoryTheory.Category.{v, u} J₁] {J₂ : Type u'} 
[inst_1 : CategoryTheory.Category.{v', u'} J₂]   (F : CategoryTheory.Functor J₁ 
J₂) [F.Final] (κ : Cardinal.{w}) [inst_3 : Fact κ.IsRegular]   [CategoryTheory.I
sCardinalFiltered J₁ κ], CategoryTheory.IsCardinalFiltered J₂ κ
参数：F : CategoryTheory.Functor J₁ J₂；κ : Cardinal.{w}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.final_iff_of_isFiltered`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isCardinalFiltered_iff`：isCardinalFiltered_iff : IsCardin
alFiltered J κ ↔ (forall ⦃ι : Type w⦄ (j : ι -> J) (_ : HasCardinalLT ι κ), exis
ts (k : J), forall (i : ι),…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `CategoryTheory.IsCardinalFiltered.wideSpan`：wideSpan {ι : Type v'} {j : 
J} {k : ι -> J} (f : forall i, j ⟶ k i) (hι : HasCardinalLT ι κ) : exists (m : J
) (a : forall i, k i ⟶ m) (b : j…
· 使用引理 `hasCardinalLT_prod`：hasCardinalLT_prod {T₁ : Type u} {T₂ : Type u'} {κ :
 Cardinal.{w}} (hκ : Cardinal.aleph0 <= κ) (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCa
rdinalLT…
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If `F : J₁ ⥤ J₂` is final and `J₁` is `κ`-filtered, then
`J₂` is also `κ`-filtered. See also `IsFiltered.of_final`
(in `CategoryTheory.Limits.Final`) for the particular case of
filtered categories (`κ = ℵ₀`).
-/
lemma IsCardinalFiltered.of_final
    {J₁ : Type u} [Category.{v} J₁] {J₂ : Type u'} [Category.{v'} J₂]
    (F : J₁ ⥤ J₂) [F.Final] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J₁ κ] :
    IsCardinalFiltered J₂ κ := by
  have := isFiltered_of_isCardinalFiltered J₁ κ
  obtain ⟨h₁, h₂⟩ := (Functor.final_iff_of_isFiltered F).1 inferInstance
  rw [isCardinalFiltered_iff]
  refine ⟨fun ι j hι ↦ ?_, fun ι j k f hι ↦ ?_⟩
  · choose a ha using fun i ↦ h₁ (j i)
    exact ⟨F.obj (IsCardinalFiltered.max a hι),
      fun i ↦ ⟨(ha i).some ≫ F.map (toMax a hι i)⟩⟩
  · by_cases h : Nonempty ι
    · obtain ⟨l, ⟨a⟩⟩ := h₁ k
      choose m b hb using fun (i : ι × ι) ↦ h₂ (f i.1 ≫ a) (f i.2 ≫ a)
      simp only [Category.assoc, Prod.forall] at hb
      obtain ⟨n, c, d, hn⟩ := wideSpan b
        (hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out) hι hι)
      let i₀ : ι := Classical.arbitrary _
      exact ⟨F.obj n, a ≫ F.map d, f i₀ ≫ a ≫ F.map d,
        fun i ↦ by rw [← hn (i₀, i), Functor.map_comp, reassoc_of% (hb i₀ i)]⟩
    · simp only [not_nonempty_iff] at h
      obtain ⟨j', ⟨a⟩⟩ := h₁ j
      obtain ⟨k', ⟨b⟩⟩ := h₁ k
      exact ⟨F.obj (IsFiltered.max j' k'), b ≫ F.map (IsFiltered.rightToMax _ _),
        a ≫ F.map (IsFiltered.leftToMax _ _), by simp⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.IsTerminal.isCardinalFiltered** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.IsTerminal`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {X : J} (hX : Cat
egoryTheory.Limits.IsTerminal X)   (κ : Cardinal.{w}) [inst_1 : Fact κ.IsRegular
], CategoryTheory.IsCardinalFiltered J κ
参数：hX : CategoryTheory.Limits.IsTerminal X；κ : Cardinal.{w}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Limits.IsTerminal.isCardinalFiltered {J : Type u} [Category.{v} J]
    {X : J} (hX : IsTerminal X) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalFiltered J κ where
  nonempty_cocone _ _ := ⟨{ pt := X, ι.app _ := hX.from _ }⟩
/-
**CategoryTheory.isCardinalFiltered_of_hasTerminal** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：isCardinalFiltered_of_hasTerminal (J : Type u) [Category.{v} J] [HasTermin
al J] (κ : Cardinal.{w}) [Fact κ.IsRegular] : IsCardinalFiltered J κ
参数：J : Type u；κ : Cardinal.{w}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.isCardinalFiltered`：∀ {J : Type u} [ins
t : CategoryTheory.Category.{v, u} J] {X : J} (hX : CategoryTheory.Limits.IsTerm
inal X)   (κ : Cardinal.{w}) [inst_1 : Fa…
-/
lemma isCardinalFiltered_of_hasTerminal (J : Type u) [Category.{v} J]
    [HasTerminal J] (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalFiltered J κ :=
  terminalIsTerminal.isCardinalFiltered _

end CategoryTheory

