/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nima Rasekh, Aras Ergus
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Order.SuccPred.Basic

/-!
# Reedy categories

In this file, we introduce the definition of a Reedy structure
on a category `C` equipped with two classes of morphisms
`W₁` and `W₂` (these are sometimes denoted `C₋` and `C₊` in
the literature).

## TODO
* Construct the Reedy model category structure on the category of
functors `C ⥤ D` when `C` is a Reedy category and `D` a model category
https://github.com/leanprover-community/project-intentions/issues/5

## References
* [Emily Riehl and Dominic Verity, *Elements of ∞-Category Theory*, C.4][RiehlVerity2022]

-/

@[expose] public section

open CategoryTheory

namespace HomotopicalAlgebra

open MorphismProperty in
/-- A Reedy structure on a category `C` equipped with two multiplicative
classes of morphisms `W₁` and `W₂` consists of the data of a degree
map for objects `deg : C → α`, where `α` is a well ordered type. The first
two axioms `lt₁` and `lt₂` express the behaviour of the degree with
respect to morphisms in `W₁` (resp. `W₂`) that are not identities, and
the last axiom says that any morphism can be factored in a unique way
as a morphism in `W₁` followed by a morphism in `W₂`. -/
/-
**HomotopicalAlgebra.ReedyStructure** 是 Mathlib 中的一个归纳类型，位于命名空间 `HomotopicalAlge
bra`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     (W₁
 W₂ : CategoryTheory.MorphismProperty C) →       [W₁.IsMultiplicative] →        
 [W₂.IsMultiplicative] →           (α : Type u_2) →             [inst : LinearOr
der α] → [OrderBot α] → [SuccOrder α] → [WellFoundedLT α] → Type (max u_1 u_2)
参数：W₁ W₂ : CategoryTheory.MorphismProperty C；α : Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Reedy structure on a category `C` equipped with two multiplicative
classes of morphisms `W₁` and `W₂` consists of the data of a degree
map for objects `deg : C → α`, where `α` is a well ordered type. The first
two axioms `lt₁` and `lt₂` express the behaviour of the degree with
respect to morphisms in `W₁` (resp. `W₂`) that are not identities, and
the last axiom says that any morphism can be factored in a unique way
as a morphism in `W₁` followed by a morphism in `W₂`.
-/
structure ReedyStructure {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
    [W₁.IsMultiplicative] [W₂.IsMultiplicative]
    (α : Type*) [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α] where
  /-- the degree of an object -/
  deg : C → α
  lt₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) (hf' : ¬ identities C f) : deg Y < deg X
  lt₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) (hf' : ¬ identities C f) : deg X < deg Y
  nonempty_unique {X Y : C} (f : X ⟶ Y) :
    Nonempty (Unique (W₁.MapFactorizationData W₂ f))

namespace ReedyStructure

variable {C : Type*} [Category* C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure W₁ W₂ α)

/-- The opposite of a Reedy structure. -/
@[simps]
/-
**HomotopicalAlgebra.ReedyStructure.op** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlg
ebra.ReedyStructure`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W₁
 W₂ : CategoryTheory.MorphismProperty C} →       [inst_1 : W₁.IsMultiplicative] 
→         [inst_2 : W₂.IsMultiplicative] →           {α : Type u_2} →           
  [inst_3 : LinearOrder α] →               [inst_4 : OrderBot α] →              
   [inst_5 : SuccOrder α] →                   [inst_6 : WellFoundedLT α] →      
               HomotopicalAlgebra.ReedyStructure W₁ W₂ α → HomotopicalAlgebra.Re
edyStructure W₂.op W₁.op α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a Reedy structure.
-/
protected def op : ReedyStructure W₂.op W₁.op α where
  deg := r.deg ∘ Opposite.unop
  lt₁ f hf hf' := r.lt₂ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  lt₂ f hf hf' := r.lt₁ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  nonempty_unique f :=
    MorphismProperty.MapFactorizationData.opEquiv.uniqueCongr.nonempty_congr.1
      (r.nonempty_unique f.unop)
/-
**HomotopicalAlgebra.ReedyStructure.le** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlg
ebra.ReedyStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) : r.deg Y ≤ r.deg X := by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₁ f hf hf').le
/-
**HomotopicalAlgebra.ReedyStructure.le** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlg
ebra.ReedyStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) : r.deg X ≤ r.deg Y := by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₂ f hf hf').le
/-
**HomotopicalAlgebra.ReedyStructure.identities_of_prop** 是 Mathlib 中的一个引理，位于命名空间
 `HomotopicalAlgebra.ReedyStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma identities_of_prop₁_of_eq {X Y : C} {f : X ⟶ Y} (hf : W₁ f) (h : r.deg X = r.deg Y) :
    MorphismProperty.identities _ f := by
  by_contra
  exact h.not_gt (r.lt₁ _ hf this)
/-
**HomotopicalAlgebra.ReedyStructure.identities_of_prop** 是 Mathlib 中的一个引理，位于命名空间
 `HomotopicalAlgebra.ReedyStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma identities_of_prop₂_of_eq {X Y : C} {f : X ⟶ Y} (hf : W₂ f) (h : r.deg X = r.deg Y) :
    MorphismProperty.identities _ f := by
  by_contra
  exact h.not_lt (r.lt₂ _ hf this)

include r in
/-
**HomotopicalAlgebra.ReedyStructure.subsingleton_mapFactorizationData** 是 Mathli
b 中的一个引理，位于命名空间 `HomotopicalAlgebra.ReedyStructure`。
形式化陈述：subsingleton_mapFactorizationData ⦃X Y : C⦄ (f : X ⟶ Y) : Subsingleton (W₁
.MapFactorizationData W₂ f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.ReedyStructure.nonempty_unique`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.MorphismProper
ty C}   [inst_1 : W₁.IsMultiplicative] …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma subsingleton_mapFactorizationData ⦃X Y : C⦄ (f : X ⟶ Y) :
    Subsingleton (W₁.MapFactorizationData W₂ f) := by
  have := (r.nonempty_unique f).some
  infer_instance

/-- The Reedy factorization of a morphism `f : X ⟶ Y` as a morphism in `W₁`
followed by a morphism in `W₂`. -/
@[no_expose]
/-
**HomotopicalAlgebra.ReedyStructure.mapFactorizationData** 是 Mathlib 中的一个定义，位于命名
空间 `HomotopicalAlgebra.ReedyStructure`。
形式化陈述：mapFactorizationData {X Y : C} (f : X ⟶ Y) : W₁.MapFactorizationData W₂ f
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.ReedyStructure.nonempty_unique`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.MorphismProper
ty C}   [inst_1 : W₁.IsMultiplicative] …

--- 原说明 ---
The Reedy factorization of a morphism `f : X ⟶ Y` as a morphism in `W₁`
followed by a morphism in `W₂`.
-/
noncomputable def mapFactorizationData {X Y : C} (f : X ⟶ Y) :
    W₁.MapFactorizationData W₂ f := by
  letI := (r.nonempty_unique f).some
  exact default

include r in
/-
**HomotopicalAlgebra.ReedyStructure.unique_obj** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra.ReedyStructure`。
形式化陈述：unique_obj {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f)
 : fac.Z = fac'.Z
参数：fac fac' : W₁.MapFactorizationData W₂ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.ReedyStructure.subsingleton_mapFactorizationData`：sub
singleton_mapFactorizationData ⦃X Y : C⦄ (f : X ⟶ Y) : Subsingleton (W₁.MapFacto
rizationData W₂ f)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma unique_obj {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f) :
    fac.Z = fac'.Z := by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  rfl

include r in
/-
**HomotopicalAlgebra.ReedyStructure.unique** 是 Mathlib 中的一个引理，位于命名空间 `Homotopica
lAlgebra.ReedyStructure`。
形式化陈述：unique {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f) : e
xists (h : fac.Z = fac'.Z), fac.i = fac'.i ≫ eqToHom h.symm ∧ fac.p = eqToHom h 
≫ fac'.p
参数：fac fac' : W₁.MapFactorizationData W₂ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.ReedyStructure.subsingleton_mapFactorizationData`：sub
singleton_mapFactorizationData ⦃X Y : C⦄ (f : X ⟶ Y) : Subsingleton (W₁.MapFacto
rizationData W₂ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma unique {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f) :
    ∃ (h : fac.Z = fac'.Z), fac.i = fac'.i ≫ eqToHom h.symm ∧ fac.p = eqToHom h ≫ fac'.p := by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  simp

/-- The degree of a morphism for a Reedy structure. It is defined as the degree of
the intermediate object in the Reedy factorization, but it is also the smallest
degree of an intermediate object in a factorization, see the lemma `degHom_le`. -/
@[no_expose]
/-
**HomotopicalAlgebra.ReedyStructure.degHom** 是 Mathlib 中的一个定义，位于命名空间 `Homotopica
lAlgebra.ReedyStructure`。
形式化陈述：degHom {X Y : C} (f : X ⟶ Y) : α
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The degree of a morphism for a Reedy structure. It is defined as the degree of
the intermediate object in the Reedy factorization, but it is also the smallest
degree of an intermediate object in a factorization, see the lemma `degHom_le`.
-/
noncomputable def degHom {X Y : C} (f : X ⟶ Y) : α := r.deg (r.mapFactorizationData f).Z
/-
**HomotopicalAlgebra.ReedyStructure.degHom_eq** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra.ReedyStructure`。
形式化陈述：degHom_eq {X Y : C} {f : X ⟶ Y} (h : W₁.MapFactorizationData W₂ f) : r.deg
Hom f = r.deg h.Z
参数：h : W₁.MapFactorizationData W₂ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.ReedyStructure.subsingleton_mapFactorizationData`：sub
singleton_mapFactorizationData ⦃X Y : C⦄ (f : X ⟶ Y) : Subsingleton (W₁.MapFacto
rizationData W₂ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma degHom_eq {X Y : C} {f : X ⟶ Y} (h : W₁.MapFactorizationData W₂ f) :
    r.degHom f = r.deg h.Z := by
  have := r.subsingleton_mapFactorizationData
  rw [← Subsingleton.elim (r.mapFactorizationData f) h]
  rfl
/-
**HomotopicalAlgebra.ReedyStructure.exists_fac** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra.ReedyStructure`。
形式化陈述：exists_fac {X Y : C} (f : X ⟶ Y) : exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y),
 W₁ a ∧ W₂ b ∧ a ≫ b = f ∧ r.degHom f = r.deg Z
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
-/
lemma exists_fac {X Y : C} (f : X ⟶ Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), W₁ a ∧ W₂ b ∧ a ≫ b = f ∧ r.degHom f = r.deg Z :=
  ⟨_, _, _, (r.mapFactorizationData f).hi, (r.mapFactorizationData f).hp,
    (r.mapFactorizationData f).fac, rfl⟩
/-
**HomotopicalAlgebra.ReedyStructure.degHom_le** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra.ReedyStructure`。
形式化陈述：degHom_le {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) : r.degHom (f ≫ g) <= r.deg 
Z
参数：f : X ⟶ Z；g : Z ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.ReedyStructure.exists_fac`：exists_fac {X Y : C} (f : 
X ⟶ Y) : exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), W₁ a ∧ W₂ b ∧ a ≫ b = f ∧ r.deg
Hom f = r.deg Z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_eq`：degHom_eq {X Y : C} {f : X 
⟶ Y} (h : W₁.MapFactorizationData W₂ f) : r.degHom f = r.deg h.Z
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `HomotopicalAlgebra.ReedyStructure.le₁`：le₁ {X Y : C} (f : X ⟶ Y) (hf : W
₁ f) : r.deg Y <= r.deg X
· 使用引理 `HomotopicalAlgebra.ReedyStructure.le₂`：le₂ {X Y : C} (f : X ⟶ Y) (hf : W
₂ f) : r.deg X <= r.deg Y
-/
lemma degHom_le {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) :
    r.degHom (f ≫ g) ≤ r.deg Z := by
  obtain ⟨Zf, f₁, f₂, hf₁, hf₂, fac_f, eq_f⟩ := r.exists_fac f
  obtain ⟨Zg, g₁, g₂, hg₁, hg₂, fac_g, eq_g⟩ := r.exists_fac g
  obtain ⟨Zh, h₁, h₂, hh₁, hh₂, fac_h, eq_h⟩ := r.exists_fac (f₂ ≫ g₁)
  let factfg := MorphismProperty.MapFactorizationData.mk (f := f ≫ g) Zh (f₁ ≫ h₁) (h₂ ≫ g₂)
    (by simp [reassoc_of% fac_h, reassoc_of% fac_f, fac_g])
    (W₁.comp_mem _ _ hf₁ hh₁) (W₂.comp_mem _ _ hh₂ hg₂)
  rw [r.degHom_eq factfg]
  exact (r.le₁ _ hh₁).trans (r.le₂ _ hf₂)
/-
**HomotopicalAlgebra.ReedyStructure.degHom_le_deg_left** 是 Mathlib 中的一个引理，位于命名空间
 `HomotopicalAlgebra.ReedyStructure`。
形式化陈述：degHom_le_deg_left {X Y : C} (f : X ⟶ Y) : r.degHom f <= r.deg X
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_le`：degHom_le {X Z Y : C} (f : 
X ⟶ Z) (g : Z ⟶ Y) : r.degHom (f ≫ g) <= r.deg Z
-/
lemma degHom_le_deg_left {X Y : C} (f : X ⟶ Y) :
    r.degHom f ≤ r.deg X := by
  simpa using r.degHom_le (𝟙 X) f
/-
**HomotopicalAlgebra.ReedyStructure.degHom_le_deg_right** 是 Mathlib 中的一个引理，位于命名空
间 `HomotopicalAlgebra.ReedyStructure`。
形式化陈述：degHom_le_deg_right {X Y : C} (f : X ⟶ Y) : r.degHom f <= r.deg Y
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_le`：degHom_le {X Z Y : C} (f : 
X ⟶ Z) (g : Z ⟶ Y) : r.degHom (f ≫ g) <= r.deg Z
-/
lemma degHom_le_deg_right {X Y : C} (f : X ⟶ Y) :
    r.degHom f ≤ r.deg Y := by
  simpa using r.degHom_le f (𝟙 Y)
/-
**HomotopicalAlgebra.ReedyStructure.degHom_comp_le_left** 是 Mathlib 中的一个引理，位于命名空
间 `HomotopicalAlgebra.ReedyStructure`。
形式化陈述：degHom_comp_le_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : r.degHom (f ≫ g)
 <= r.degHom f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.ReedyStructure.exists_fac`：exists_fac {X Y : C} (f : 
X ⟶ Y) : exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), W₁ a ∧ W₂ b ∧ a ≫ b = f ∧ r.deg
Hom f = r.deg Z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_le`：degHom_le {X Z Y : C} (f : 
X ⟶ Z) (g : Z ⟶ Y) : r.degHom (f ≫ g) <= r.deg Z
-/
lemma degHom_comp_le_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    r.degHom (f ≫ g) ≤ r.degHom f := by
  have ⟨_, f₁, f₂, _, _, h_fac, h_deg⟩ := r.exists_fac f
  rw [h_deg, ← h_fac, Category.assoc]
  exact r.degHom_le f₁ (f₂ ≫ g)
/-
**HomotopicalAlgebra.ReedyStructure.degHom_comp_le_right** 是 Mathlib 中的一个引理，位于命名
空间 `HomotopicalAlgebra.ReedyStructure`。
形式化陈述：degHom_comp_le_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : r.degHom (f ≫ g
) <= r.degHom g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.ReedyStructure.exists_fac`：exists_fac {X Y : C} (f : 
X ⟶ Y) : exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), W₁ a ∧ W₂ b ∧ a ≫ b = f ∧ r.deg
Hom f = r.deg Z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_le`：degHom_le {X Z Y : C} (f : 
X ⟶ Z) (g : Z ⟶ Y) : r.degHom (f ≫ g) <= r.deg Z
-/
lemma degHom_comp_le_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    r.degHom (f ≫ g) ≤ r.degHom g := by
  have ⟨_, g₁, g₂, _, _, h_fac, h_deg⟩ := r.exists_fac g
  rw [h_deg, ← h_fac, ← Category.assoc]
  exact r.degHom_le (f ≫ g₁) g₂
/-
**HomotopicalAlgebra.ReedyStructure.prop** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra.ReedyStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop₂_of_degHom_eq_deg_left {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg X) :
    W₂ f := by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₁_of_eq hp (by aesop)
  obtain rfl : i = f := by simpa using fac
  exact hi
/-
**HomotopicalAlgebra.ReedyStructure.prop** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra.ReedyStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop₁_of_degHom_eq_deg_right {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg Y) :
    W₁ f := by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₂_of_eq hi (by aesop)
  obtain rfl : p = f := by simpa using fac
  exact hp
/-
**HomotopicalAlgebra.ReedyStructure.degHom_lt_or_of_degHom_comp_lt** 是 Mathlib 中
的一个引理，位于命名空间 `HomotopicalAlgebra.ReedyStructure`。
形式化陈述：degHom_lt_or_of_degHom_comp_lt {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) (hfg : 
r.degHom (f ≫ g) < r.deg Z) : r.degHom f < r.deg Z ∨ r.degHom g < r.deg Z
参数：f : X ⟶ Z；g : Z ⟶ Y；hfg : r.degHom (f ≫ g) < r.deg Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomotopicalAlgebra.ReedyStructure.prop₁_of_degHom_eq_deg_right`：prop₁_of
_degHom_eq_deg_right {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg Y) : W₁ f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_le_deg_right`：degHom_le_deg_rig
ht {X Y : C} (f : X ⟶ Y) : r.degHom f <= r.deg Y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `HomotopicalAlgebra.ReedyStructure.prop₂_of_degHom_eq_deg_left`：prop₂_of_
degHom_eq_deg_left {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg X) : W₂ f
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_le_deg_left`：degHom_le_deg_left
 {X Y : C} (f : X ⟶ Y) : r.degHom f <= r.deg X
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_eq`：degHom_eq {X Y : C} {f : X 
⟶ Y} (h : W₁.MapFactorizationData W₂ f) : r.degHom f = r.deg h.Z
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma degHom_lt_or_of_degHom_comp_lt
    {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) (hfg : r.degHom (f ≫ g) < r.deg Z) :
    r.degHom f < r.deg Z ∨ r.degHom g < r.deg Z := by
  contrapose! hfg
  let φ := MorphismProperty.MapFactorizationData.mk Z f g rfl
    (r.prop₁_of_degHom_eq_deg_right (le_antisymm (r.degHom_le_deg_right f) hfg.left))
    (r.prop₂_of_degHom_eq_deg_left (le_antisymm (r.degHom_le_deg_left g) hfg.right))
  rw [r.degHom_eq φ]

@[simp]
/-
**HomotopicalAlgebra.ReedyStructure.degHom_id** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra.ReedyStructure`。
形式化陈述：degHom_id (X : C) : r.degHom (𝟙 X) = r.deg X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_eq`：degHom_eq {X Y : C} {f : X 
⟶ Y} (h : W₁.MapFactorizationData W₂ f) : r.degHom f = r.deg h.Z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
-/
lemma degHom_id (X : C) : r.degHom (𝟙 X) = r.deg X :=
  r.degHom_eq (MorphismProperty.MapFactorizationData.mk X (𝟙 X) (𝟙 X) (by simp) (W₁.id_mem _)
  (W₂.id_mem _))
/-
**HomotopicalAlgebra.ReedyStructure.deg_eq_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Hom
otopicalAlgebra.ReedyStructure`。
形式化陈述：deg_eq_of_iso {X Y : C} (e : X ≅ Y) : r.deg X = r.deg Y
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_id`：degHom_id (X : C) : r.degHo
m (𝟙 X) = r.deg X
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用引理 `HomotopicalAlgebra.ReedyStructure.degHom_le`：degHom_le {X Z Y : C} (f : 
X ⟶ Z) (g : Z ⟶ Y) : r.degHom (f ≫ g) <= r.deg Z
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma deg_eq_of_iso {X Y : C} (e : X ≅ Y) : r.deg X = r.deg Y := by
  have {X Y : C} (e : X ≅ Y) : r.deg X ≤ r.deg Y := by
    rw [← r.degHom_id X, ← e.hom_inv_id]
    apply r.degHom_le
  exact le_antisymm (this e) (this e.symm)

include r in
/-
**HomotopicalAlgebra.ReedyStructure.prop** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra.ReedyStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop₁_of_iso {X Y : C} (e : X ≅ Y) : W₁ e.hom :=
  r.prop₁_of_degHom_eq_deg_right (by
    refine le_antisymm ?_ ?_
    · simpa using r.degHom_comp_le_right e.hom (𝟙 Y)
    · simpa using r.degHom_comp_le_right e.inv e.hom)

include r in
/-
**HomotopicalAlgebra.ReedyStructure.prop** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalA
lgebra.ReedyStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prop₂_of_iso {X Y : C} (e : X ≅ Y) : W₂ e.hom :=
  (r.op.prop₁_of_iso e.op)

include r in
/-
**HomotopicalAlgebra.ReedyStructure.skeletal** 是 Mathlib 中的一个引理，位于命名空间 `Homotopi
calAlgebra.ReedyStructure`。
形式化陈述：skeletal : Skeletal C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用引理 `HomotopicalAlgebra.ReedyStructure.prop₂_of_iso`：prop₂_of_iso {X Y : C} (
e : X ≅ Y) : W₂ e.hom
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomotopicalAlgebra.ReedyStructure.prop₁_of_iso`：prop₁_of_iso {X Y : C} (
e : X ≅ Y) : W₁ e.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.ReedyStructure.unique`：unique {X Y : C} {f : X ⟶ Y} (
fac fac' : W₁.MapFactorizationData W₂ f) : exists (h : fac.Z = fac'.Z), fac.i = 
fac'.i ≫ eqToHom h.symm ∧ fac.…
-/
lemma skeletal : Skeletal C := by
  intro X Y ⟨e⟩
  exact (r.unique (f := e.hom)
    (.mk X (𝟙 X) e.hom (by simp) (W₁.id_mem X) (r.prop₂_of_iso e))
    (.mk Y e.hom (𝟙 Y) (by simp) (r.prop₁_of_iso e) (W₂.id_mem Y))).choose

end ReedyStructure

end HomotopicalAlgebra

