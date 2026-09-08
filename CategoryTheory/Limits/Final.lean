/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Grothendieck

/-!
# Final and initial functors

A functor `F : C ⥤ D` is final if for every `d : D`,
the comma category of morphisms `d ⟶ F.obj c` is connected.

Dually, a functor `F : C ⥤ D` is initial if for every `d : D`,
the comma category of morphisms `F.obj c ⟶ d` is connected.

We show that right adjoints are examples of final functors, while
left adjoints are examples of initial functors.

For final functors, we prove that the following three statements are equivalent:
1. `F : C ⥤ D` is final.
2. Every functor `G : D ⥤ E` has a colimit if and only if `F ⋙ G` does,
   and these colimits are isomorphic via `colimit.pre G F`.
3. `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit`.

Starting at 1. we show (in `coconesEquiv`) that
the categories of cocones over `G : D ⥤ E` and over `F ⋙ G` are equivalent.
(In fact, via an equivalence which does not change the cocone point.)
This readily implies 2., as `comp_hasColimit`, `hasColimit_of_comp`, and `colimitIso`.

From 2. we can specialize to `G = coyoneda.obj (op d)` to obtain 3., as `colimitCompCoyonedaIso`.

From 3., we prove 1. directly in `final_of_colimit_comp_coyoneda_iso_pUnit`.

Dually, we prove that if a functor `F : C ⥤ D` is initial, then any functor `G : D ⥤ E` has a
limit if and only if `F ⋙ G` does, and these limits are isomorphic via `limit.pre G F`.

In the end of the file, we characterize the finality of some important induced functors on the
(co)structured arrow category (`StructuredArrow.pre` and `CostructuredArrow.pre`) and on the
Grothendieck construction (`Grothendieck.pre` and `Grothendieck.map`).

## Naming
There is some discrepancy in the literature about naming; some say 'cofinal' instead of 'final'.
The explanation for this is that the 'co' prefix here is *not* the usual category-theoretic one
indicating duality, but rather indicating the sense of "along with".

## See also
In `CategoryTheory.Filtered.Final` we give additional equivalent conditions in the case that
`C` is filtered.

## Future work
Dualise condition 3 above and the implications 2 ⇒ 3 and 3 ⇒ 1 to initial functors.

## References
* https://stacks.math.columbia.edu/tag/09WN
* https://ncatlab.org/nlab/show/final+functor
* Borceux, Handbook of Categorical Algebra I, Section 2.11.
  (Note he reverses the roles of definition and main result relative to here!)
-/

@[expose] public section


noncomputable section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

namespace Functor

open Opposite

open CategoryTheory.Limits

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/--
A functor `F : C ⥤ D` is final if for every `d : D`, the comma category of morphisms `d ⟶ F.obj c`
is connected. -/
@[stacks 04E6]
/-
**CategoryTheory.Functor.Final** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is final if for every `d : D`, the comma category of morph
isms `d ⟶ F.obj c`
is connected.
-/
class Final (F : C ⥤ D) : Prop where
  out (d : D) : IsConnected (StructuredArrow d F)

attribute [instance] Final.out

/-- A functor `F : C ⥤ D` is initial if for every `d : D`, the comma category of morphisms
`F.obj c ⟶ d` is connected.
-/
/-
**CategoryTheory.Functor.Initial** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is initial if for every `d : D`, the comma category of mor
phisms
`F.obj c ⟶ d` is connected.
-/
class Initial (F : C ⥤ D) : Prop where
  out (d : D) : IsConnected (CostructuredArrow F d)

attribute [instance] Initial.out
/-
**CategoryTheory.Functor.final_op_of_initial** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Functor`。
形式化陈述：final_op_of_initial (F : C ⥤ D) [Initial F] : Final F.op where out d
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
-/
instance final_op_of_initial (F : C ⥤ D) [Initial F] : Final F.op where
  out d := isConnected_of_equivalent (costructuredArrowOpEquivalence F (unop d))
/-
**CategoryTheory.Functor.initial_op_of_final** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Functor`。
形式化陈述：initial_op_of_final (F : C ⥤ D) [Final F] : Initial F.op where out d
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
-/
instance initial_op_of_final (F : C ⥤ D) [Final F] : Initial F.op where
  out d := isConnected_of_equivalent (structuredArrowOpEquivalence F (unop d))
/-
**CategoryTheory.Functor.final_of_initial_op** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：final_of_initial_op (F : C ⥤ D) [Initial F.op] : Final F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_isConnected_op`：isConnected_of_isConnected
_op [IsConnected Jᵒᵖ] : IsConnected J
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
-/
theorem final_of_initial_op (F : C ⥤ D) [Initial F.op] : Final F :=
  {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (structuredArrowOpEquivalence F d).symm) }
/-
**CategoryTheory.Functor.initial_of_final_op** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：initial_of_final_op (F : C ⥤ D) [Final F.op] : Initial F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_isConnected_op`：isConnected_of_isConnected
_op [IsConnected Jᵒᵖ] : IsConnected J
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
-/
theorem initial_of_final_op (F : C ⥤ D) [Final F.op] : Initial F :=
  {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (costructuredArrowOpEquivalence F d).symm) }

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

/-- If a functor `R : D ⥤ C` is a right adjoint, it is final. -/
/-
**CategoryTheory.Functor.final_of_adjunction** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：final_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Final R
参数：adj : L ⊣ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a functor `R : D ⥤ C` is a right adjoint, it is final.
-/
theorem final_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Final R :=
  { out := fun c =>
      let u : StructuredArrow c R := StructuredArrow.mk (adj.unit.app c)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inr ⟨StructuredArrow.homMk ((adj.homEquiv c f.right).symm f.hom) (by simp [u])⟩))
          (Relation.ReflTransGen.single
            (show Zag u g from
              Or.inl ⟨StructuredArrow.homMk ((adj.homEquiv c g.right).symm g.hom) (by simp [u])⟩)) }

set_option backward.defeqAttrib.useBackward true in
/-- If a functor `L : C ⥤ D` is a left adjoint, it is initial. -/
/-
**CategoryTheory.Functor.initial_of_adjunction** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：initial_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Initial L
参数：adj : L ⊣ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a functor `L : C ⥤ D` is a left adjoint, it is initial.
-/
theorem initial_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Initial L :=
  { out := fun d =>
      let u : CostructuredArrow L d := CostructuredArrow.mk (adj.counit.app d)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inl ⟨CostructuredArrow.homMk (adj.homEquiv f.left d f.hom) (by simp [u])⟩))
          (Relation.ReflTransGen.single
            (show Zag u g from
              Or.inr ⟨CostructuredArrow.homMk (adj.homEquiv g.left d g.hom) (by simp [u])⟩)) }
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) final_of_isRightAdjoint (F : C ⥤ D) [IsRightAdjoint F] : Final F :=
  final_of_adjunction (Adjunction.ofIsRightAdjoint F)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) initial_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] : Initial F :=
  initial_of_adjunction (Adjunction.ofIsLeftAdjoint F)
/-
**CategoryTheory.Functor.final_of_natIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：final_of_natIso {F F' : C ⥤ D} [Final F] (i : F ≅ F') : Final F' where out
 _
参数：i : F ≅ F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
-/
theorem final_of_natIso {F F' : C ⥤ D} [Final F] (i : F ≅ F') : Final F' where
  out _ := isConnected_of_equivalent (StructuredArrow.mapNatIso i)
/-
**CategoryTheory.Functor.final_natIso_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：final_natIso_iff {F F' : C ⥤ D} (i : F ≅ F') : Final F ↔ Final F'
参数：i : F ≅ F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
-/
theorem final_natIso_iff {F F' : C ⥤ D} (i : F ≅ F') : Final F ↔ Final F' :=
  ⟨fun _ => final_of_natIso i, fun _ => final_of_natIso i.symm⟩
/-
**CategoryTheory.Functor.initial_of_natIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：initial_of_natIso {F F' : C ⥤ D} [Initial F] (i : F ≅ F') : Initial F' whe
re out _
参数：i : F ≅ F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
-/
theorem initial_of_natIso {F F' : C ⥤ D} [Initial F] (i : F ≅ F') : Initial F' where
  out _ := isConnected_of_equivalent (CostructuredArrow.mapNatIso i)
/-
**CategoryTheory.Functor.initial_natIso_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：initial_natIso_iff {F F' : C ⥤ D} (i : F ≅ F') : Initial F ↔ Initial F'
参数：i : F ≅ F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_natIso`：initial_of_natIso {F F' : C ⥤ 
D} [Initial F] (i : F ≅ F') : Initial F' where out _
-/
theorem initial_natIso_iff {F F' : C ⥤ D} (i : F ≅ F') : Initial F ↔ Initial F' :=
  ⟨fun _ => initial_of_natIso i, fun _ => initial_of_natIso i.symm⟩

namespace Final

variable (F : C ⥤ D) [Final F]

/-
**CategoryTheory.Functor.Final.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functo
r.Final`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (d : D) : Nonempty (StructuredArrow d F) :=
  IsConnected.is_nonempty

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
When `F : C ⥤ D` is final, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `d ⟶ F.obj (lift F d)`.
-/
/-
**CategoryTheory.Functor.Final.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor.Final`。
形式化陈述：lift (d : D) : C
参数：d : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.instNonemptyStructuredArrow`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
When `F : C ⥤ D` is final, we denote by `lift F d` an arbitrary choice of object
 in `C` such that
there exists a morphism `d ⟶ F.obj (lift F d)`.
-/
def lift (d : D) : C :=
  (Classical.arbitrary (StructuredArrow d F)).right

/-- When `F : C ⥤ D` is final, we denote by `homToLift` an arbitrary choice of morphism
`d ⟶ F.obj (lift F d)`.
-/
/-
**CategoryTheory.Functor.Final.homToLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.Final`。
形式化陈述：homToLift (d : D) : d ⟶ F.obj (lift F d)
参数：d : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.instNonemptyStructuredArrow`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
When `F : C ⥤ D` is final, we denote by `homToLift` an arbitrary choice of morph
ism
`d ⟶ F.obj (lift F d)`.
-/
def homToLift (d : D) : d ⟶ F.obj (lift F d) :=
  (Classical.arbitrary (StructuredArrow d F)).hom

/-- We provide an induction principle for reasoning about `lift` and `homToLift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `homToLift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : d ⟶ F.obj X₀` below),
and to show how to transport such a construction
*both* directions along a morphism between such choices.
-/
/-
**CategoryTheory.Functor.Final.induction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.Final`。
形式化陈述：induction {d : D} (Z : forall (X : C) (_ : d ⟶ F.obj X), Sort*) (h₁ : fora
ll (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂), k₁ ≫ F.map f =
 k₂ -> Z X₁ k₁ -> Z X₂ k₂) (h₂ : forall (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.
obj X₂) (f : X₁ ⟶ X₂), k₁ ≫ F.map f = k₂ -> Z X₂ k₂ -> Z X₁ k₁) {X₀ : C} {k₀ : d
 ⟶ F.obj X₀} (z : Z X₀ k₀) : Z (lift F d) (homToLift F d)
参数：Z : forall (X : C) (_ : d ⟶ F.obj X), Sort*；h₁ : forall (X₁ X₂) (k₁ : d ⟶ F.o
bj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂), k₁ ≫ F.map f = k₂ -> Z X₁ k₁ -> Z X₂ k
₂；h₂ : forall (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂), k₁ 
≫ F.map f = k₂ -> Z X₂ k₂ -> Z X₁ k₁；z : Z X₀ k₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We provide an induction principle for reasoning about `lift` and `homToLift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `homToLift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : d ⟶ F.obj X₀` below),
and to show how to transport such a construction
*both* directions along a morphism between such choices.
-/
def induction {d : D} (Z : ∀ (X : C) (_ : d ⟶ F.obj X), Sort*)
    (h₁ :
      ∀ (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
        k₁ ≫ F.map f = k₂ → Z X₁ k₁ → Z X₂ k₂)
    (h₂ :
      ∀ (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
        k₁ ≫ F.map f = k₂ → Z X₂ k₂ → Z X₁ k₁)
    {X₀ : C} {k₀ : d ⟶ F.obj X₀} (z : Z X₀ k₀) : Z (lift F d) (homToLift F d) := by
  apply Nonempty.some
  refine isPreconnected_induction (Z := fun Y : StructuredArrow d F => Z Y.right Y.hom)
    ?_ ?_ (j₀ := StructuredArrow.mk k₀) z _
  · exact fun f a ↦ h₁ _ _ _ _ f.right f.w a
  · exact fun f a ↦ h₂ _ _ _ _ f.right f.w a

variable {F G}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a cocone over `F ⋙ G`, we can construct a `Cocone G` with the same cocone point.
-/
@[simps]
/-
**CategoryTheory.Functor.Final.extendCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.Final`。
形式化陈述：extendCocone : Cocone (F ⋙ G) ⥤ Cocone G where obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cocone over `F ⋙ G`, we can construct a `Cocone G` with the same cocone 
point.
-/
def extendCocone : Cocone (F ⋙ G) ⥤ Cocone G where
  obj c :=
    { pt := c.pt
      ι :=
        { app := fun X => G.map (homToLift F X) ≫ c.ι.app (lift F X)
          naturality := fun X Y f => by
            dsimp; simp only [Category.comp_id]
            -- This would be true if we'd chosen `lift F X` to be `lift F Y`
            -- and `homToLift F X` to be `f ≫ homToLift F Y`.
            apply
              induction F fun Z k =>
                G.map f ≫ G.map (homToLift F Y) ≫ c.ι.app (lift F Y) = G.map k ≫ c.ι.app Z
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a, Functor.map_comp, Category.assoc, ← Functor.comp_map, c.w, z]
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a, Functor.map_comp, Category.assoc, ← Functor.comp_map, c.w] at z
              rw [z]
            · rw [← Functor.map_comp_assoc] } }
  map f := { hom := f.hom }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Alternative equational lemma for `(extendCocone c).ι.app` in case a lift of the object
is given explicitly. -/
/-
**CategoryTheory.Functor.Final.extendCocone_obj_** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor.Final`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative equational lemma for `(extendCocone c).ι.app` in case a lift of the 
object
is given explicitly.
-/
lemma extendCocone_obj_ι_app' (c : Cocone (F ⋙ G)) {X : D} {Y : C} (f : X ⟶ F.obj Y) :
    (extendCocone.obj c).ι.app X = G.map f ≫ c.ι.app Y := by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    G.map g ≫ c.ι.app Z = G.map f ≫ c.ι.app Y
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, c.ι.naturality, h₂]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map, c.ι.naturality]

@[simp]
/-
**CategoryTheory.Functor.Final.colimit_cocone_comp_aux** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.Final`。
形式化陈述：colimit_cocone_comp_aux (s : Cocone (F ⋙ G)) (j : C) : G.map (homToLift F 
(F.obj j)) ≫ s.ι.app (lift F (F.obj j)) = s.ι.app j
参数：s : Cocone (F ⋙ G)；j : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
-/
theorem colimit_cocone_comp_aux (s : Cocone (F ⋙ G)) (j : C) :
    G.map (homToLift F (F.obj j)) ≫ s.ι.app (lift F (F.obj j)) = s.ι.app j := by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => G.map k ≫ s.ι.app X = (s.ι.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w]
    rw [← s.w f] at h
    simpa using! h
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w] at h
    rw [← s.w f]
    simpa using! h
  · exact s.w (𝟙 _)

variable (F G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is final,
the category of cocones on `F ⋙ G` is equivalent to the category of cocones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
/-
**CategoryTheory.Functor.Final.coconesEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.Final`。
形式化陈述：coconesEquiv : Cocone (F ⋙ G) ≌ Cocone G where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is final,
the category of cocones on `F ⋙ G` is equivalent to the category of cocones on `
G`,
for any `G : D ⥤ E`.
-/
def coconesEquiv : Cocone (F ⋙ G) ≌ Cocone G where
  functor := extendCocone
  inverse := Cocone.whiskering F
  unitIso := NatIso.ofComponents fun c => Cocone.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cocone.ext (Iso.refl _)

variable {G}

/-- When `F : C ⥤ D` is final, and `t : Cocone G` for some `G : D ⥤ E`,
`t.whisker F` is a colimit cocone exactly when `t` is.
-/
/-
**CategoryTheory.Functor.Final.isColimitWhiskerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.Final`。
形式化陈述：isColimitWhiskerEquiv (t : Cocone G) : IsColimit (t.whisker F) ≃ IsColimit
 t
参数：t : Cocone G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F : C ⥤ D` is final, and `t : Cocone G` for some `G : D ⥤ E`,
`t.whisker F` is a colimit cocone exactly when `t` is.
-/
def isColimitWhiskerEquiv (t : Cocone G) : IsColimit (t.whisker F) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv (coconesEquiv F G).symm

/-- When `F` is final, and `t : Cocone (F ⋙ G)`,
`extendCocone.obj t` is a colimit cocone exactly when `t` is.
-/
/-
**CategoryTheory.Functor.Final.isColimitExtendCoconeEquiv** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.Final`。
形式化陈述：isColimitExtendCoconeEquiv (t : Cocone (F ⋙ G)) : IsColimit (extendCocone.
obj t) ≃ IsColimit t
参数：t : Cocone (F ⋙ G)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is final, and `t : Cocone (F ⋙ G)`,
`extendCocone.obj t` is a colimit cocone exactly when `t` is.
-/
def isColimitExtendCoconeEquiv (t : Cocone (F ⋙ G)) :
    IsColimit (extendCocone.obj t) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv (coconesEquiv F G)

/-- Given a colimit cocone over `G : D ⥤ E` we can construct a colimit cocone over `F ⋙ G`. -/
@[simps]
/-
**CategoryTheory.Functor.Final.colimitCoconeComp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.Final`。
形式化陈述：colimitCoconeComp (t : ColimitCocone G) : ColimitCocone (F ⋙ G) where coco
ne
参数：t : ColimitCocone G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a colimit cocone over `G : D ⥤ E` we can construct a colimit cocone over `
F ⋙ G`.
-/
def colimitCoconeComp (t : ColimitCocone G) : ColimitCocone (F ⋙ G) where
  cocone := _
  isColimit := (isColimitWhiskerEquiv F _).symm t.isColimit
/-
**CategoryTheory.Functor.Final.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functo
r.Final`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) comp_hasColimit [HasColimit G] : HasColimit (F ⋙ G) :=
  HasColimit.mk (colimitCoconeComp F (getColimitCocone G))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Final.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functo
r.Final`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) comp_preservesColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesColimit G H] : PreservesColimit (F ⋙ G) H where
  preserves {c} hc := by
    refine ⟨isColimitExtendCoconeEquiv (G := G ⋙ H) F (H.mapCocone c) ?_⟩
    let hc' := isColimitOfPreserves H ((isColimitExtendCoconeEquiv F c).symm hc)
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Final.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functo
r.Final`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) comp_reflectsColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsColimit G H] : ReflectsColimit (F ⋙ G) H where
  reflects {c} hc := by
    refine ⟨isColimitExtendCoconeEquiv F _ (isColimitOfReflects H ?_)⟩
    let hc' := (isColimitExtendCoconeEquiv (G := G ⋙ H) F _).symm hc
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))
/-
**CategoryTheory.Functor.Final.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functo
r.Final`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) compCreatesColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesColimit G H] : CreatesColimit (F ⋙ G) H where
  lifts {c} hc := by
    refine ⟨(liftColimit ((isColimitExtendCoconeEquiv F (G := G ⋙ H) _).symm hc)).whisker F, ?_⟩
    let i := liftedColimitMapsToOriginal ((isColimitExtendCoconeEquiv F (G := G ⋙ H) _).symm hc)
    exact (Cocone.whiskering F).mapIso i ≪≫ ((coconesEquiv F (G ⋙ H)).unitIso.app _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Final.colimit_pre_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Functor.Final`。
形式化陈述：colimit_pre_isIso [HasColimit G] : IsIso (colimit.pre G F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.comp_hasColimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.colimit.pre_eq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} K]   {C : Type u} [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsColimit.desc_self`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{
v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance colimit_pre_isIso [HasColimit G] : IsIso (colimit.pre G F) := by
  simp only [colimit.pre_eq (colimitCoconeComp F (getColimitCocone G)) (getColimitCocone G),
    colimitCoconeComp_cocone, IsColimit.desc_self]
  infer_instance

section

variable (G)

/-- When `F : C ⥤ D` is final, and `G : D ⥤ E` has a colimit, then `F ⋙ G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`. -/
@[simps! -isSimp, stacks 04E7]
/-
**CategoryTheory.Functor.Final.colimitIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.Final`。
形式化陈述：colimitIso [HasColimit G] : colimit (F ⋙ G) ≅ colimit G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.comp_hasColimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
When `F : C ⥤ D` is final, and `G : D ⥤ E` has a colimit, then `F ⋙ G` has a col
imit also and
`colimit (F ⋙ G) ≅ colimit G`.
-/
def colimitIso [HasColimit G] : colimit (F ⋙ G) ≅ colimit G :=
  asIso (colimit.pre G F)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Final.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functo
r.Final`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_colimitIso_hom [HasColimit G] (X : C) :
    colimit.ι (F ⋙ G) X ≫ (colimitIso F G).hom = colimit.ι G (F.obj X) := by
  simp [colimitIso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Final.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functo
r.Final`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_colimitIso_inv [HasColimit G] (X : C) :
    colimit.ι G (F.obj X) ≫ (colimitIso F G).inv = colimit.ι (F ⋙ G) X := by
  simp [colimitIso]

set_option backward.defeqAttrib.useBackward true in
/-- A pointfree version of `colimitIso`, stating that whiskering by `F` followed by taking the
colimit is isomorphic to taking the colimit on the codomain of `F`. -/
/-
**CategoryTheory.Functor.Final.colimIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor.Final`。
形式化陈述：colimIso [HasColimitsOfShape D E] [HasColimitsOfShape C E] : (whiskeringLe
ft _ _ _).obj F ⋙ colim ≅ colim (J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
A pointfree version of `colimitIso`, stating that whiskering by `F` followed by 
taking the
colimit is isomorphic to taking the colimit on the codomain of `F`.
-/
def colimIso [HasColimitsOfShape D E] [HasColimitsOfShape C E] :
    (whiskeringLeft _ _ _).obj F ⋙ colim ≅ colim (J := D) (C := E) :=
  NatIso.ofComponents (fun G => colimitIso F G) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, colim_obj, comp_map, whiskeringLeft_obj_map,
      colim_map, colimitIso_hom]
    ext
    simp only [comp_obj, ι_colimMap_assoc, whiskerLeft_app, colimit.ι_pre, colimit.ι_pre_assoc,
      ι_colimMap]

end

/-- Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`. -/
@[simps]
/-
**CategoryTheory.Functor.Final.colimitCoconeOfComp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.Final`。
形式化陈述：colimitCoconeOfComp (t : ColimitCocone (F ⋙ G)) : ColimitCocone G where co
cone
参数：t : ColimitCocone (F ⋙ G)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`.
-/
def colimitCoconeOfComp (t : ColimitCocone (F ⋙ G)) : ColimitCocone G where
  cocone := extendCocone.obj t.cocone
  isColimit := (isColimitExtendCoconeEquiv F _).symm t.isColimit

/-- When `F` is final, and `F ⋙ G` has a colimit, then `G` has a colimit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_hasColimit`.)
-/
/-
**CategoryTheory.Functor.Final.hasColimit_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor.Final`。
形式化陈述：hasColimit_of_comp [HasColimit (F ⋙ G)] : HasColimit G
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
When `F` is final, and `F ⋙ G` has a colimit, then `G` has a colimit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_hasColimit`.)
-/
theorem hasColimit_of_comp [HasColimit (F ⋙ G)] : HasColimit G :=
  HasColimit.mk (colimitCoconeOfComp F (getColimitCocone (F ⋙ G)))
/-
**CategoryTheory.Functor.Final.hasColimit_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor.Final`。
形式化陈述：hasColimit_comp_iff : HasColimit (F ⋙ G) ↔ HasColimit G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.hasColimit_of_comp`：hasColimit_of_comp [Has
Colimit (F ⋙ G)] : HasColimit G
· 使用定理 `CategoryTheory.Functor.Final.comp_hasColimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma hasColimit_comp_iff :
    HasColimit (F ⋙ G) ↔ HasColimit G :=
  ⟨fun _ ↦ Functor.Final.hasColimit_of_comp F, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Final.preservesColimit_of_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor.Final`。
形式化陈述：preservesColimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [Pres
ervesColimit (F ⋙ G) H] : PreservesColimit G H where preserves {c} hc
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem preservesColimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesColimit (F ⋙ G) H] : PreservesColimit G H where
  preserves {c} hc := by
    refine ⟨isColimitWhiskerEquiv F _ ?_⟩
    let hc' := isColimitOfPreserves H ((isColimitWhiskerEquiv F _).symm hc)
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Final.reflectsColimit_of_comp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.Final`。
形式化陈述：reflectsColimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [Refle
ctsColimit (F ⋙ G) H] : ReflectsColimit G H where reflects {c} hc
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem reflectsColimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsColimit (F ⋙ G) H] : ReflectsColimit G H where
  reflects {c} hc := by
    refine ⟨isColimitWhiskerEquiv F _ (isColimitOfReflects H ?_)⟩
    let hc' := (isColimitWhiskerEquiv F _).symm hc
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is final and `F ⋙ G` creates colimits of `H`, then so does `G`. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.Final.createsColimitOfComp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.Final`。
形式化陈述：createsColimitOfComp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [CreatesC
olimit (F ⋙ G) H] : CreatesColimit G H where reflects
参数：F ⋙ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` is final and `F ⋙ G` creates colimits of `H`, then so does `G`.
-/
def createsColimitOfComp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesColimit (F ⋙ G) H] : CreatesColimit G H where
  reflects := (reflectsColimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCocone (F := F)).obj (liftColimit ((isColimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedColimitMapsToOriginal (K := (F ⋙ G)) ((isColimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCocone (F := F)).mapIso i) ≪≫ ((coconesEquiv F (G ⋙ H)).counitIso.app _)
    exact Cocone.ext (Iso.refl _)

include F in
/-
**CategoryTheory.Functor.Final.hasColimitsOfShape_of_final** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor.Final`。
形式化陈述：hasColimitsOfShape_of_final [HasColimitsOfShape C E] : HasColimitsOfShape 
D E where has_colimit
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.hasColimit_of_comp`：hasColimit_of_comp [Has
Colimit (F ⋙ G)] : HasColimit G
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasColimitsOfShape_of_final [HasColimitsOfShape C E] : HasColimitsOfShape D E where
  has_colimit := fun _ => hasColimit_of_comp F

include F in
/-
**CategoryTheory.Functor.Final.preservesColimitsOfShape_of_final** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Functor.Final`。
形式化陈述：preservesColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤
 B) [PreservesColimitsOfShape C H] : PreservesColimitsOfShape D H where preserve
sColimit
参数：H : E ⥤ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.preservesColimit_of_comp`：preservesColimit_
of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [PreservesColimit (F ⋙ G) H]
 : PreservesColimit G H where preserves {c}…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
theorem preservesColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [PreservesColimitsOfShape C H] : PreservesColimitsOfShape D H where
  preservesColimit := preservesColimit_of_comp F

include F in
/-
**CategoryTheory.Functor.Final.reflectsColimitsOfShape_of_final** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor.Final`。
形式化陈述：reflectsColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ 
B) [ReflectsColimitsOfShape C H] : ReflectsColimitsOfShape D H where reflectsCol
imit
参数：H : E ⥤ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.reflectsColimit_of_comp`：reflectsColimit_of
_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [ReflectsColimit (F ⋙ G) H] : 
ReflectsColimit G H where reflects {c} hc
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
theorem reflectsColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [ReflectsColimitsOfShape C H] : ReflectsColimitsOfShape D H where
  reflectsColimit := reflectsColimit_of_comp F

include F in
/-- If `H` creates colimits of shape `C` and `F : C ⥤ D` is final, then `H` creates colimits of
shape `D`. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.Final.createsColimitsOfShapeOfFinal** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.Final`。
形式化陈述：createsColimitsOfShapeOfFinal {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B) 
[CreatesColimitsOfShape C H] : CreatesColimitsOfShape D H where CreatesColimit
参数：H : E ⥤ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `H` creates colimits of shape `C` and `F : C ⥤ D` is final, then `H` creates 
colimits of
shape `D`.
-/
def createsColimitsOfShapeOfFinal {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [CreatesColimitsOfShape C H] : CreatesColimitsOfShape D H where
  CreatesColimit := createsColimitOfComp F

end Final

end ArbitraryUniverse

section LocallySmall

variable {C : Type v} [Category.{v} C] {D : Type u₁} [Category.{v} D] (F : C ⥤ D)

namespace Final

/-
**CategoryTheory.Functor.Final.zigzag_of_eqvGen_colimitTypeRel** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Functor.Final`。
形式化陈述：zigzag_of_eqvGen_colimitTypeRel {F : C ⥤ D} {d : D} {f₁ f₂ : Σ X, d ⟶ F.ob
j X} (t : Relation.EqvGen (Functor.ColimitTypeRel (F ⋙ coyoneda.obj (op d))) f₁ 
f₂) : Zigzag (StructuredArrow.mk f₁.2) (StructuredArrow.mk f₂.2)
参数：t : Relation.EqvGen (Functor.ColimitTypeRel (F ⋙ coyoneda.obj (op d))) f₁ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Zigzag.symm`：∀ {J : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.Zigz
ag j₂ j₁
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
-/
theorem zigzag_of_eqvGen_colimitTypeRel {F : C ⥤ D} {d : D} {f₁ f₂ : Σ X, d ⟶ F.obj X}
    (t : Relation.EqvGen (Functor.ColimitTypeRel (F ⋙ coyoneda.obj (op d))) f₁ f₂) :
    Zigzag (StructuredArrow.mk f₁.2) (StructuredArrow.mk f₂.2) := by
  induction t with
  | rel x y r =>
    obtain ⟨f, w⟩ := r
    fconstructor
    swap
    · fconstructor
    left; fconstructor
    exact StructuredArrow.homMk f
  | refl => fconstructor
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Final

/-- If `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit` for all `d : D`, then `F` is final.
-/
/-
**CategoryTheory.Functor.final_of_colimit_comp_coyoneda_iso_pUnit** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：final_of_colimit_comp_coyoneda_iso_pUnit (I : forall d, colimit (F ⋙ coyon
eda.obj (op d)) ≅ PUnit) : Final F
参数：I : forall d, colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective'`：jointly_surjective' (x 
: colimit F) : exists (j : J) (y : F.obj j), colimit.ι F j y = x
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `PUnit.ext`：∀ (a b : PUnit.{u_1}), a = b
· 使用定理 `CategoryTheory.Limits.Types.colimit_eq`：colimit_eq {j j' : J} {x : F.obj
 j} {x' : F.obj j'} (w : colimit.ι F j x = colimit.ι F j' x') : Relation.EqvGen 
F.ColimitTypeRel ⟨j, x⟩ ⟨j',…
· 使用定理 `CategoryTheory.Functor.Final.zigzag_of_eqvGen_colimitTypeRel`：zigzag_of_
eqvGen_colimitTypeRel {F : C ⥤ D} {d : D} {f₁ f₂ : Σ X, d ⟶ F.obj X} (t : Relati
on.EqvGen (Functor.ColimitTypeRel (F ⋙ coyoneda.ob…

--- 原说明 ---
If `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit` for all `d : D`, then `F` is fina
l.
-/
theorem final_of_colimit_comp_coyoneda_iso_pUnit
    (I : ∀ d, colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit) : Final F :=
  ⟨fun d => by
    have : Nonempty (StructuredArrow d F) := by
      have := (I d).inv PUnit.unit
      obtain ⟨j, y, rfl⟩ := Limits.Types.jointly_surjective'.{v, v} this
      exact ⟨StructuredArrow.mk y⟩
    apply zigzag_isConnected
    rintro ⟨⟨⟨⟩⟩, X₁, f₁⟩ ⟨⟨⟨⟩⟩, X₂, f₂⟩
    let y₁ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₁ f₁
    let y₂ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₂ f₂
    have e : y₁ = y₂ := by
      apply (I d).toEquiv.injective
      ext
    have t := Types.colimit_eq.{v, v} e
    clear e y₁ y₂
    exact Final.zigzag_of_eqvGen_colimitTypeRel t⟩

/-- A variant of `final_of_colimit_comp_coyoneda_iso_pUnit` where we bind the various claims
about `colimit (F ⋙ coyoneda.obj (Opposite.op d))` for each `d : D` into a single claim about
the presheaf `colimit (F ⋙ yoneda)`. -/
/-
**CategoryTheory.Functor.final_of_isTerminal_colimit_comp_yoneda** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：final_of_isTerminal_colimit_comp_yoneda (h : IsTerminal (colimit (F ⋙ yone
da))) : Final F
参数：h : IsTerminal (colimit (F ⋙ yoneda))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Functor.final_of_colimit_comp_coyoneda_iso_pUnit`：final_o
f_colimit_comp_coyoneda_iso_pUnit (I : forall d, colimit (F ⋙ coyoneda.obj (op d
)) ≅ PUnit) : Final F
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)

--- 原说明 ---
A variant of `final_of_colimit_comp_coyoneda_iso_pUnit` where we bind the variou
s claims
about `colimit (F ⋙ coyoneda.obj (Opposite.op d))` for each `d : D` into a singl
e claim about
the presheaf `colimit (F ⋙ yoneda)`.
-/
theorem final_of_isTerminal_colimit_comp_yoneda
    (h : IsTerminal (colimit (F ⋙ yoneda))) : Final F := by
  refine final_of_colimit_comp_coyoneda_iso_pUnit _ (fun d => ?_)
  refine Types.isTerminalEquivIsoPUnit _ ?_
  let b := IsTerminal.isTerminalObj ((evaluation _ _).obj (Opposite.op d)) _ h
  exact b.ofIso <| preservesColimitIso ((evaluation _ _).obj (Opposite.op d)) (F ⋙ yoneda)

/-- If the universal morphism `colimit (F ⋙ coyoneda.obj (op d)) ⟶ colimit (coyoneda.obj (op d))`
is an isomorphism (as it always is when `F` is final),
then `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit`
(simply because `colimit (coyoneda.obj (op d)) ≅ PUnit`).
-/
/-
**CategoryTheory.Functor.Final.colimitCompCoyonedaIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.Final`。
形式化陈述：{C : Type v} →   [inst : CategoryTheory.Category.{v, v} C] →     {D : Type
 u₁} →       [inst_1 : CategoryTheory.Category.{v, u₁} D] →         (F : Categor
yTheory.Functor C D) →           (d : D) →             [CategoryTheory.IsIso (Ca
tegoryTheory.Limits.colimit.pre (CategoryTheory.coyoneda.obj (Opposite.op d)) F)
] →               CategoryTheory.Limits.colimit (F.comp (CategoryTheory.coyoneda
.obj (Opposite.op d))) ≅ PUnit.{v + 1}
参数：F : CategoryTheory.Functor C D；d : D；CategoryTheory.Limits.colimit.pre (Categ
oryTheory.coyoneda.obj (Opposite.op d)) F；F.comp (CategoryTheory.coyoneda.obj (O
pposite.op d))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the universal morphism `colimit (F ⋙ coyoneda.obj (op d)) ⟶ colimit (coyoneda
.obj (op d))`
is an isomorphism (as it always is when `F` is final),
then `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit`
(simply because `colimit (coyoneda.obj (op d)) ≅ PUnit`).
-/
def Final.colimitCompCoyonedaIso (d : D) [IsIso (colimit.pre (coyoneda.obj (op d)) F)] :
    colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit :=
  asIso (colimit.pre (coyoneda.obj (op d)) F) ≪≫ Coyoneda.colimitCoyonedaIso (op d)

end LocallySmall

section SmallCategory

variable {C : Type v} [Category.{v} C] {D : Type v} [Category.{v} D] (F : C ⥤ D)

/-
**CategoryTheory.Functor.final_iff_isIso_colimit_pre** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：final_iff_isIso_colimit_pre : Final F ↔ forall G : D ⥤ Type v, IsIso (coli
mit.pre G F)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Functor.final_of_colimit_comp_coyoneda_iso_pUnit`：final_o
f_colimit_comp_coyoneda_iso_pUnit (I : forall d, colimit (F ⋙ coyoneda.obj (op d
)) ≅ PUnit) : Final F
-/
theorem final_iff_isIso_colimit_pre : Final F ↔ ∀ G : D ⥤ Type v, IsIso (colimit.pre G F) :=
  ⟨fun _ => inferInstance,
   fun _ => final_of_colimit_comp_coyoneda_iso_pUnit _ fun _ => Final.colimitCompCoyonedaIso _ _⟩

end SmallCategory

namespace Initial

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) [Initial F]

/-
**CategoryTheory.Functor.Initial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Func
tor.Initial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (d : D) : Nonempty (CostructuredArrow F d) :=
  IsConnected.is_nonempty

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
When `F : C ⥤ D` is initial, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `F.obj (lift F d) ⟶ d`.
-/
/-
**CategoryTheory.Functor.Initial.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor.Initial`。
形式化陈述：lift (d : D) : C
参数：d : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.instNonemptyCostructuredArrow`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
When `F : C ⥤ D` is initial, we denote by `lift F d` an arbitrary choice of obje
ct in `C` such that
there exists a morphism `F.obj (lift F d) ⟶ d`.
-/
def lift (d : D) : C :=
  (Classical.arbitrary (CostructuredArrow F d)).left

/-- When `F : C ⥤ D` is initial, we denote by `homToLift` an arbitrary choice of morphism
`F.obj (lift F d) ⟶ d`.
-/
/-
**CategoryTheory.Functor.Initial.homToLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor.Initial`。
形式化陈述：homToLift (d : D) : F.obj (lift F d) ⟶ d
参数：d : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.instNonemptyCostructuredArrow`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
When `F : C ⥤ D` is initial, we denote by `homToLift` an arbitrary choice of mor
phism
`F.obj (lift F d) ⟶ d`.
-/
def homToLift (d : D) : F.obj (lift F d) ⟶ d :=
  (Classical.arbitrary (CostructuredArrow F d)).hom

set_option backward.defeqAttrib.useBackward true in
/-- We provide an induction principle for reasoning about `lift` and `homToLift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `homToLift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : F.obj X₀ ⟶ d` below),
and to show how to transport such a construction
*both* directions along a morphism between such choices.
-/
/-
**CategoryTheory.Functor.Initial.induction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor.Initial`。
形式化陈述：induction {d : D} (Z : forall (X : C) (_ : F.obj X ⟶ d), Sort*) (h₁ : fora
ll (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂), F.map f ≫ k₂ =
 k₁ -> Z X₁ k₁ -> Z X₂ k₂) (h₂ : forall (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj 
X₂ ⟶ d) (f : X₁ ⟶ X₂), F.map f ≫ k₂ = k₁ -> Z X₂ k₂ -> Z X₁ k₁) {X₀ : C} {k₀ : F
.obj X₀ ⟶ d} (z : Z X₀ k₀) : Z (lift F d) (homToLift F d)
参数：Z : forall (X : C) (_ : F.obj X ⟶ d), Sort*；h₁ : forall (X₁ X₂) (k₁ : F.obj X
₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂), F.map f ≫ k₂ = k₁ -> Z X₁ k₁ -> Z X₂ k
₂；h₂ : forall (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂), F.m
ap f ≫ k₂ = k₁ -> Z X₂ k₂ -> Z X₁ k₁；z : Z X₀ k₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We provide an induction principle for reasoning about `lift` and `homToLift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `homToLift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : F.obj X₀ ⟶ d` below),
and to show how to transport such a construction
*both* directions along a morphism between such choices.
-/
def induction {d : D} (Z : ∀ (X : C) (_ : F.obj X ⟶ d), Sort*)
    (h₁ :
      ∀ (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂),
        F.map f ≫ k₂ = k₁ → Z X₁ k₁ → Z X₂ k₂)
    (h₂ :
      ∀ (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂),
        F.map f ≫ k₂ = k₁ → Z X₂ k₂ → Z X₁ k₁)
    {X₀ : C} {k₀ : F.obj X₀ ⟶ d} (z : Z X₀ k₀) : Z (lift F d) (homToLift F d) := by
  apply Nonempty.some
  apply
    @isPreconnected_induction _ _ _ (fun Y : CostructuredArrow F d => Z Y.left Y.hom) _ _
      (CostructuredArrow.mk k₀) z
  · intro j₁ j₂ f a
    fapply h₁ _ _ _ _ f.left _ a
    convert! f.w
    simp
  · intro j₁ j₂ f a
    fapply h₂ _ _ _ _ f.left _ a
    convert! f.w
    simp

variable {F G}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a cone over `F ⋙ G`, we can construct a `Cone G` with the same cocone point.
-/
@[simps]
/-
**CategoryTheory.Functor.Initial.extendCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.Initial`。
形式化陈述：extendCone : Cone (F ⋙ G) ⥤ Cone G where obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cone over `F ⋙ G`, we can construct a `Cone G` with the same cocone poin
t.
-/
def extendCone : Cone (F ⋙ G) ⥤ Cone G where
  obj c :=
    { pt := c.pt
      π :=
        { app := fun d => c.π.app (lift F d) ≫ G.map (homToLift F d)
          naturality := fun X Y f => by
            dsimp; simp only [Category.id_comp, Category.assoc]
            -- This would be true if we'd chosen `lift F Y` to be `lift F X`
            -- and `homToLift F Y` to be `homToLift F X ≫ f`.
            apply
              induction F fun Z k =>
                (c.π.app Z ≫ G.map k : c.pt ⟶ _) =
                  c.π.app (lift F X) ≫ G.map (homToLift F X) ≫ G.map f
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a, Functor.map_comp, ← Functor.comp_map, ← Category.assoc, ← Category.assoc,
                c.w] at z
              rw [z, Category.assoc]
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a, Functor.map_comp, ← Functor.comp_map, ← Category.assoc, ← Category.assoc,
                c.w, z, Category.assoc]
            · rw [← Functor.map_comp] } }
  map f := { hom := f.hom }

set_option backward.isDefEq.respectTransparency false in
/-- Alternative equational lemma for `(extendCone c).π.app` in case a lift of the object
is given explicitly. -/
/-
**CategoryTheory.Functor.Initial.extendCone_obj_** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor.Initial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative equational lemma for `(extendCone c).π.app` in case a lift of the ob
ject
is given explicitly.
-/
lemma extendCone_obj_π_app' (c : Cone (F ⋙ G)) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    (extendCone.obj c).π.app Y = c.π.app X ≫ G.map f := by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    c.π.app Z ≫ G.map g = c.π.app X ≫ G.map f
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, h₂]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Functor.Initial.limit_cone_comp_aux** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor.Initial`。
形式化陈述：limit_cone_comp_aux (s : Cone (F ⋙ G)) (j : C) : s.π.app (lift F (F.obj j)
) ≫ G.map (homToLift F (F.obj j)) = s.π.app j
参数：s : Cone (F ⋙ G)；j : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem limit_cone_comp_aux (s : Cone (F ⋙ G)) (j : C) :
    s.π.app (lift F (F.obj j)) ≫ G.map (homToLift F (F.obj j)) = s.π.app j := by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => s.π.app X ≫ G.map k = (s.π.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f]
    rw [← w] at h
    simpa using h
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f] at h
    rw [← w]
    simpa using h
  · exact s.w (𝟙 _)

variable (F G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is initial,
the category of cones on `F ⋙ G` is equivalent to the category of cones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
/-
**CategoryTheory.Functor.Initial.conesEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.Initial`。
形式化陈述：conesEquiv : Cone (F ⋙ G) ≌ Cone G where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is initial,
the category of cones on `F ⋙ G` is equivalent to the category of cones on `G`,
for any `G : D ⥤ E`.
-/
def conesEquiv : Cone (F ⋙ G) ≌ Cone G where
  functor := extendCone
  inverse := Cone.whiskering F
  unitIso := NatIso.ofComponents fun c => Cone.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cone.ext (Iso.refl _)

variable {G}

/-- When `F : C ⥤ D` is initial, and `t : Cone G` for some `G : D ⥤ E`,
`t.whisker F` is a limit cone exactly when `t` is.
-/
/-
**CategoryTheory.Functor.Initial.isLimitWhiskerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.Initial`。
形式化陈述：isLimitWhiskerEquiv (t : Cone G) : IsLimit (t.whisker F) ≃ IsLimit t
参数：t : Cone G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F : C ⥤ D` is initial, and `t : Cone G` for some `G : D ⥤ E`,
`t.whisker F` is a limit cone exactly when `t` is.
-/
def isLimitWhiskerEquiv (t : Cone G) : IsLimit (t.whisker F) ≃ IsLimit t :=
  IsLimit.ofConeEquiv (conesEquiv F G).symm

/-- When `F` is initial, and `t : Cone (F ⋙ G)`,
`extendCone.obj t` is a limit cone exactly when `t` is.
-/
/-
**CategoryTheory.Functor.Initial.isLimitExtendConeEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor.Initial`。
形式化陈述：isLimitExtendConeEquiv (t : Cone (F ⋙ G)) : IsLimit (extendCone.obj t) ≃ I
sLimit t
参数：t : Cone (F ⋙ G)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `F` is initial, and `t : Cone (F ⋙ G)`,
`extendCone.obj t` is a limit cone exactly when `t` is.
-/
def isLimitExtendConeEquiv (t : Cone (F ⋙ G)) : IsLimit (extendCone.obj t) ≃ IsLimit t :=
  IsLimit.ofConeEquiv (conesEquiv F G)

/-- Given a limit cone over `G : D ⥤ E` we can construct a limit cone over `F ⋙ G`. -/
@[simps]
/-
**CategoryTheory.Functor.Initial.limitConeComp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.Initial`。
形式化陈述：limitConeComp (t : LimitCone G) : LimitCone (F ⋙ G) where cone
参数：t : LimitCone G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a limit cone over `G : D ⥤ E` we can construct a limit cone over `F ⋙ G`.
-/
def limitConeComp (t : LimitCone G) : LimitCone (F ⋙ G) where
  cone := _
  isLimit := (isLimitWhiskerEquiv F _).symm t.isLimit
/-
**CategoryTheory.Functor.Initial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Func
tor.Initial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) comp_hasLimit [HasLimit G] : HasLimit (F ⋙ G) :=
  HasLimit.mk (limitConeComp F (getLimitCone G))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Initial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Func
tor.Initial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) comp_preservesLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesLimit G H] : PreservesLimit (F ⋙ G) H where
  preserves {c} hc := by
    refine ⟨isLimitExtendConeEquiv (G := G ⋙ H) F (H.mapCone c) ?_⟩
    let hc' := isLimitOfPreserves H ((isLimitExtendConeEquiv F c).symm hc)
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Initial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Func
tor.Initial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) comp_reflectsLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsLimit G H] : ReflectsLimit (F ⋙ G) H where
  reflects {c} hc := by
    refine ⟨isLimitExtendConeEquiv F _ (isLimitOfReflects H ?_)⟩
    let hc' := (isLimitExtendConeEquiv (G := G ⋙ H) F _).symm hc
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))
/-
**CategoryTheory.Functor.Initial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Func
tor.Initial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) compCreatesLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesLimit G H] : CreatesLimit (F ⋙ G) H where
  lifts {c} hc := by
    refine ⟨(liftLimit ((isLimitExtendConeEquiv F (G := G ⋙ H) _).symm hc)).whisker F, ?_⟩
    let i := liftedLimitMapsToOriginal ((isLimitExtendConeEquiv F (G := G ⋙ H) _).symm hc)
    exact (Cone.whiskering F).mapIso i ≪≫ ((conesEquiv F (G ⋙ H)).unitIso.app _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Initial.limit_pre_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Functor.Initial`。
形式化陈述：limit_pre_isIso [HasLimit G] : IsIso (limit.pre G F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.comp_hasLimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.pre_eq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 K]   {C : Type u} [inst…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsLimit.lift_self`：lift_self {c : Cone F} (t : IsL
imit c) : t.lift c = 𝟙 c.pt
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance limit_pre_isIso [HasLimit G] : IsIso (limit.pre G F) := by
  rw [limit.pre_eq (limitConeComp F (getLimitCone G)) (getLimitCone G)]
  simp only [limitConeComp_cone, Cone.whisker_pt, limitConeComp_isLimit, IsLimit.lift_self,
    Category.id_comp, isIso_comp_left_iff]
  infer_instance

section

variable (G)

/-- When `F : C ⥤ D` is initial, and `G : D ⥤ E` has a limit, then `F ⋙ G` has a limit also and
`limit (F ⋙ G) ≅ limit G`. -/
@[simps! -isSimp, stacks 04E7]
/-
**CategoryTheory.Functor.Initial.limitIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.Initial`。
形式化陈述：limitIso [HasLimit G] : limit (F ⋙ G) ≅ limit G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.comp_hasLimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
When `F : C ⥤ D` is initial, and `G : D ⥤ E` has a limit, then `F ⋙ G` has a lim
it also and
`limit (F ⋙ G) ≅ limit G`.
-/
def limitIso [HasLimit G] : limit (F ⋙ G) ≅ limit G :=
  (asIso (limit.pre G F)).symm

set_option backward.defeqAttrib.useBackward true in
/-- A pointfree version of `limitIso`, stating that whiskering by `F` followed by taking the
limit is isomorphic to taking the limit on the codomain of `F`. -/
/-
**CategoryTheory.Functor.Initial.limIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor.Initial`。
形式化陈述：limIso [HasLimitsOfShape D E] [HasLimitsOfShape C E] : (whiskeringLeft _ _
 _).obj F ⋙ lim ≅ lim (J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
A pointfree version of `limitIso`, stating that whiskering by `F` followed by ta
king the
limit is isomorphic to taking the limit on the codomain of `F`.
-/
def limIso [HasLimitsOfShape D E] [HasLimitsOfShape C E] :
    (whiskeringLeft _ _ _).obj F ⋙ lim ≅ lim (J := D) (C := E) :=
  Iso.symm <| NatIso.ofComponents (fun G => (limitIso F G).symm) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, lim_obj, comp_map, whiskeringLeft_obj_map, lim_map,
      Iso.symm_hom, limitIso_inv]
    ext
    simp

end

/-- Given a limit cone over `F ⋙ G` we can construct a limit cone over `G`. -/
@[simps]
/-
**CategoryTheory.Functor.Initial.limitConeOfComp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.Initial`。
形式化陈述：limitConeOfComp (t : LimitCone (F ⋙ G)) : LimitCone G where cone
参数：t : LimitCone (F ⋙ G)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a limit cone over `F ⋙ G` we can construct a limit cone over `G`.
-/
def limitConeOfComp (t : LimitCone (F ⋙ G)) : LimitCone G where
  cone := extendCone.obj t.cone
  isLimit := (isLimitExtendConeEquiv F _).symm t.isLimit

/-- When `F` is initial, and `F ⋙ G` has a limit, then `G` has a limit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_hasLimit`.)
-/
/-
**CategoryTheory.Functor.Initial.hasLimit_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor.Initial`。
形式化陈述：hasLimit_of_comp [HasLimit (F ⋙ G)] : HasLimit G
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
When `F` is initial, and `F ⋙ G` has a limit, then `G` has a limit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_hasLimit`.)
-/
theorem hasLimit_of_comp [HasLimit (F ⋙ G)] : HasLimit G :=
  HasLimit.mk (limitConeOfComp F (getLimitCone (F ⋙ G)))
/-
**CategoryTheory.Functor.Initial.hasLimit_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor.Initial`。
形式化陈述：hasLimit_comp_iff : HasLimit (F ⋙ G) ↔ HasLimit G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.hasLimit_of_comp`：hasLimit_of_comp [HasLi
mit (F ⋙ G)] : HasLimit G
· 使用定理 `CategoryTheory.Functor.Initial.comp_hasLimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma hasLimit_comp_iff :
    HasLimit (F ⋙ G) ↔ HasLimit G :=
  ⟨fun _ ↦ Functor.Initial.hasLimit_of_comp F, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Initial.preservesLimit_of_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor.Initial`。
形式化陈述：preservesLimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [Preser
vesLimit (F ⋙ G) H] : PreservesLimit G H where preserves {c} hc
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem preservesLimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesLimit (F ⋙ G) H] : PreservesLimit G H where
  preserves {c} hc := by
    refine ⟨isLimitWhiskerEquiv F _ ?_⟩
    let hc' := isLimitOfPreserves H ((isLimitWhiskerEquiv F _).symm hc)
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Initial.reflectsLimit_of_comp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.Initial`。
形式化陈述：reflectsLimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [Reflect
sLimit (F ⋙ G) H] : ReflectsLimit G H where reflects {c} hc
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem reflectsLimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsLimit (F ⋙ G) H] : ReflectsLimit G H where
  reflects {c} hc := by
    refine ⟨isLimitWhiskerEquiv F _ (isLimitOfReflects H ?_)⟩
    let hc' := (isLimitWhiskerEquiv F _).symm hc
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is initial and `F ⋙ G` creates limits of `H`, then so does `G`. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.Initial.createsLimitOfComp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.Initial`。
形式化陈述：createsLimitOfComp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [CreatesLim
it (F ⋙ G) H] : CreatesLimit G H where reflects
参数：F ⋙ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` is initial and `F ⋙ G` creates limits of `H`, then so does `G`.
-/
def createsLimitOfComp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesLimit (F ⋙ G) H] : CreatesLimit G H where
  reflects := (reflectsLimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCone (F := F)).obj (liftLimit ((isLimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedLimitMapsToOriginal (K := (F ⋙ G)) ((isLimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCone (F := F)).mapIso i) ≪≫ ((conesEquiv F (G ⋙ H)).counitIso.app _)
    exact Cone.ext (Iso.refl _)

include F in
/-
**CategoryTheory.Functor.Initial.hasLimitsOfShape_of_initial** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor.Initial`。
形式化陈述：hasLimitsOfShape_of_initial [HasLimitsOfShape C E] : HasLimitsOfShape D E 
where has_limit
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.hasLimit_of_comp`：hasLimit_of_comp [HasLi
mit (F ⋙ G)] : HasLimit G
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasLimitsOfShape_of_initial [HasLimitsOfShape C E] : HasLimitsOfShape D E where
  has_limit := fun _ => hasLimit_of_comp F

include F in
/-
**CategoryTheory.Functor.Initial.preservesLimitsOfShape_of_initial** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Functor.Initial`。
形式化陈述：preservesLimitsOfShape_of_initial {B : Type u₄} [Category.{v₄} B] (H : E ⥤
 B) [PreservesLimitsOfShape C H] : PreservesLimitsOfShape D H where preservesLim
it
参数：H : E ⥤ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.preservesLimit_of_comp`：preservesLimit_of
_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [PreservesLimit (F ⋙ G) H] : P
reservesLimit G H where preserves {c} hc
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
theorem preservesLimitsOfShape_of_initial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [PreservesLimitsOfShape C H] : PreservesLimitsOfShape D H where
  preservesLimit := preservesLimit_of_comp F

include F in
/-
**CategoryTheory.Functor.Initial.reflectsLimitsOfShape_of_initial** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Functor.Initial`。
形式化陈述：reflectsLimitsOfShape_of_initial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ 
B) [ReflectsLimitsOfShape C H] : ReflectsLimitsOfShape D H where reflectsLimit
参数：H : E ⥤ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.reflectsLimit_of_comp`：reflectsLimit_of_c
omp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B} [ReflectsLimit (F ⋙ G) H] : Refl
ectsLimit G H where reflects {c} hc
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
-/
theorem reflectsLimitsOfShape_of_initial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [ReflectsLimitsOfShape C H] : ReflectsLimitsOfShape D H where
  reflectsLimit := reflectsLimit_of_comp F

include F in
/-- If `H` creates limits of shape `C` and `F : C ⥤ D` is initial, then `H` creates limits of shape
`D`. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.Initial.createsLimitsOfShapeOfInitial** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Functor.Initial`。
形式化陈述：createsLimitsOfShapeOfInitial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B) 
[CreatesLimitsOfShape C H] : CreatesLimitsOfShape D H where CreatesLimit
参数：H : E ⥤ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `H` creates limits of shape `C` and `F : C ⥤ D` is initial, then `H` creates 
limits of shape
`D`.
-/
def createsLimitsOfShapeOfInitial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [CreatesLimitsOfShape C H] : CreatesLimitsOfShape D H where
  CreatesLimit := createsLimitOfComp F

end Initial

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)

/-- The hypotheses also imply that `G` is final, see `final_of_comp_full_faithful'`. -/
/-
**CategoryTheory.Functor.final_of_comp_full_faithful** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：final_of_comp_full_faithful [Full G] [Faithful G] [Final (F ⋙ G)] : Final 
F where out d
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.StructuredArrow.isEquivalence_post`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {B : Type u₄} [ins…
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…

--- 原说明 ---
The hypotheses also imply that `G` is final, see `final_of_comp_full_faithful'`.
-/
theorem final_of_comp_full_faithful [Full G] [Faithful G] [Final (F ⋙ G)] : Final F where
  out d := isConnected_of_equivalent (StructuredArrow.post d F G).asEquivalence.symm

/-- The hypotheses also imply that `G` is initial, see `initial_of_comp_full_faithful'`. -/
/-
**CategoryTheory.Functor.initial_of_comp_full_faithful** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：initial_of_comp_full_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : In
itial F where out d
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.CostructuredArrow.isEquivalence_post`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {B : Type u₄} [ins…
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…

--- 原说明 ---
The hypotheses also imply that `G` is initial, see `initial_of_comp_full_faithfu
l'`.
-/
theorem initial_of_comp_full_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial F where
  out d := isConnected_of_equivalent (CostructuredArrow.post F G d).asEquivalence.symm

/-- See also the strictly more general `final_comp` below. -/
/-
**CategoryTheory.Functor.final_comp_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：final_comp_equivalence [Final F] [IsEquivalence G] : Final (F ⋙ G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
· 使用定理 `CategoryTheory.Functor.final_of_comp_full_faithful`：final_of_comp_full_f
aithful [Full G] [Faithful G] [Final (F ⋙ G)] : Final F where out d
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
See also the strictly more general `final_comp` below.
-/
theorem final_comp_equivalence [Final F] [IsEquivalence G] : Final (F ⋙ G) :=
  let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Final ((F ⋙ G) ⋙ G.inv) := final_of_natIso i
  final_of_comp_full_faithful (F ⋙ G) G.inv

/-- See also the strictly more general `initial_comp` below. -/
/-
**CategoryTheory.Functor.initial_comp_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：initial_comp_equivalence [Initial F] [IsEquivalence G] : Initial (F ⋙ G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_natIso`：initial_of_natIso {F F' : C ⥤ 
D} [Initial F] (i : F ≅ F') : Initial F' where out _
· 使用定理 `CategoryTheory.Functor.initial_of_comp_full_faithful`：initial_of_comp_fu
ll_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial F where out d
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
See also the strictly more general `initial_comp` below.
-/
theorem initial_comp_equivalence [Initial F] [IsEquivalence G] : Initial (F ⋙ G) :=
  let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Initial ((F ⋙ G) ⋙ G.inv) := initial_of_natIso i
  initial_of_comp_full_faithful (F ⋙ G) G.inv

/-- See also the strictly more general `final_comp` below. -/
/-
**CategoryTheory.Functor.final_equivalence_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：final_equivalence_comp [IsEquivalence F] [Final G] : Final (F ⋙ G) where o
ut d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…

--- 原说明 ---
See also the strictly more general `final_comp` below.
-/
theorem final_equivalence_comp [IsEquivalence F] [Final G] : Final (F ⋙ G) where
  out d := isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence.symm

/-- See also the strictly more general `initial_comp` below. -/
/-
**CategoryTheory.Functor.initial_equivalence_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：initial_equivalence_comp [IsEquivalence F] [Initial G] : Initial (F ⋙ G) w
here out d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…

--- 原说明 ---
See also the strictly more general `initial_comp` below.
-/
theorem initial_equivalence_comp [IsEquivalence F] [Initial G] : Initial (F ⋙ G) where
  out d := isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence.symm

/-- See also the strictly more general `final_of_final_comp` below. -/
/-
**CategoryTheory.Functor.final_of_equivalence_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：final_of_equivalence_comp [IsEquivalence F] [Final (F ⋙ G)] : Final G wher
e out d
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…

--- 原说明 ---
See also the strictly more general `final_of_final_comp` below.
-/
theorem final_of_equivalence_comp [IsEquivalence F] [Final (F ⋙ G)] : Final G where
  out d := isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence

/-- See also the strictly more general `initial_of_initial_comp` below. -/
/-
**CategoryTheory.Functor.initial_of_equivalence_comp** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：initial_of_equivalence_comp [IsEquivalence F] [Initial (F ⋙ G)] : Initial 
G where out d
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isConnected_of_equivalent`：isConnected_of_equivalent {K :
 Type u₂} [Category.{v₂} K] (e : J ≌ K) [IsConnected J] : IsConnected K
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…

--- 原说明 ---
See also the strictly more general `initial_of_initial_comp` below.
-/
theorem initial_of_equivalence_comp [IsEquivalence F] [Initial (F ⋙ G)] : Initial G where
  out d := isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence

/-- See also the strictly more general `final_iff_comp_final_full_faithful` below. -/
/-
**CategoryTheory.Functor.final_iff_comp_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：final_iff_comp_equivalence [IsEquivalence G] : Final F ↔ Final (F ⋙ G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_comp_equivalence`：final_comp_equivalence [F
inal F] [IsEquivalence G] : Final (F ⋙ G)
· 使用定理 `CategoryTheory.Functor.final_of_comp_full_faithful`：final_of_comp_full_f
aithful [Full G] [Faithful G] [Final (F ⋙ G)] : Final F where out d
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
See also the strictly more general `final_iff_comp_final_full_faithful` below.
-/
theorem final_iff_comp_equivalence [IsEquivalence G] : Final F ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp_equivalence _ _, fun _ => final_of_comp_full_faithful _ G⟩

/-- See also the strictly more general `final_iff_final_comp` below. -/
/-
**CategoryTheory.Functor.final_iff_equivalence_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：final_iff_equivalence_comp [IsEquivalence F] : Final G ↔ Final (F ⋙ G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_equivalence_comp`：final_equivalence_comp [I
sEquivalence F] [Final G] : Final (F ⋙ G) where out d
· 使用定理 `CategoryTheory.Functor.final_of_equivalence_comp`：final_of_equivalence_c
omp [IsEquivalence F] [Final (F ⋙ G)] : Final G where out d

--- 原说明 ---
See also the strictly more general `final_iff_final_comp` below.
-/
theorem final_iff_equivalence_comp [IsEquivalence F] : Final G ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_equivalence_comp _ _, fun _ => final_of_equivalence_comp F _⟩

/-- See also the strictly more general `initial_iff_comp_initial_full_faithful` below. -/
/-
**CategoryTheory.Functor.initial_iff_comp_equivalence** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：initial_iff_comp_equivalence [IsEquivalence G] : Initial F ↔ Initial (F ⋙ 
G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_comp_equivalence`：initial_comp_equivalenc
e [Initial F] [IsEquivalence G] : Initial (F ⋙ G)
· 使用定理 `CategoryTheory.Functor.initial_of_comp_full_faithful`：initial_of_comp_fu
ll_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial F where out d
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
See also the strictly more general `initial_iff_comp_initial_full_faithful` belo
w.
-/
theorem initial_iff_comp_equivalence [IsEquivalence G] : Initial F ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp_equivalence _ _, fun _ => initial_of_comp_full_faithful _ G⟩

/-- See also the strictly more general `initial_iff_initial_comp` below. -/
/-
**CategoryTheory.Functor.initial_iff_equivalence_comp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：initial_iff_equivalence_comp [IsEquivalence F] : Initial G ↔ Initial (F ⋙ 
G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_equivalence_comp`：initial_equivalence_com
p [IsEquivalence F] [Initial G] : Initial (F ⋙ G) where out d
· 使用定理 `CategoryTheory.Functor.initial_of_equivalence_comp`：initial_of_equivalen
ce_comp [IsEquivalence F] [Initial (F ⋙ G)] : Initial G where out d

--- 原说明 ---
See also the strictly more general `initial_iff_initial_comp` below.
-/
theorem initial_iff_equivalence_comp [IsEquivalence F] : Initial G ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_equivalence_comp _ _, fun _ => initial_of_equivalence_comp F _⟩
/-
**CategoryTheory.Functor.final_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：final_comp [hF : Final F] [hG : Final G] : Final (F ⋙ G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.final_iff_comp_equivalence`：final_iff_comp_equiva
lence [IsEquivalence G] : Final F ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.final_iff_equivalence_comp`：final_iff_equivalence
_comp [IsEquivalence F] : Final G ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.final_natIso_iff`：final_natIso_iff {F F' : C ⥤ D}
 (i : F ≅ F') : Final F ↔ Final F'
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Functor.final_iff_isIso_colimit_pre`：final_iff_isIso_coli
mit_pre : Final F ↔ forall G : D ⥤ Type v, IsIso (colimit.pre G F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.pre_pre`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} K]   {C : Type u} [inst…
-/
instance final_comp [hF : Final F] [hG : Final G] : Final (F ⋙ G) := by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ G ⋙ s₃.functor) :=
    isoWhiskerLeft (s₁.inverse ⋙ F) (isoWhiskerRight s₂.unitIso (G ⋙ s₃.functor))
  rw [final_iff_comp_equivalence (F ⋙ G) s₃.functor, final_iff_equivalence_comp s₁.inverse,
    final_natIso_iff i, final_iff_isIso_colimit_pre]
  rw [final_iff_comp_equivalence F s₂.functor, final_iff_equivalence_comp s₁.inverse,
    final_iff_isIso_colimit_pre] at hF
  rw [final_iff_comp_equivalence G s₃.functor, final_iff_equivalence_comp s₂.inverse,
    final_iff_isIso_colimit_pre] at hG
  intro H
  rw [← colimit.pre_pre]
  infer_instance
/-
**CategoryTheory.Functor.initial_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：initial_comp [Initial F] [Initial G] : Initial (F ⋙ G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_final_op`：initial_of_final_op (F : C ⥤
 D) [Final F.op] : Initial F
-/
instance initial_comp [Initial F] [Initial G] : Initial (F ⋙ G) := by
  suffices Final (F ⋙ G).op from initial_of_final_op _
  exact final_comp F.op G.op
/-
**CategoryTheory.Functor.final_of_final_comp** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：final_of_final_comp [hF : Final F] [hFG : Final (F ⋙ G)] : Final G
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.final_iff_comp_equivalence`：final_iff_comp_equiva
lence [IsEquivalence G] : Final F ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.final_iff_equivalence_comp`：final_iff_equivalence
_comp [IsEquivalence F] : Final G ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Functor.final_iff_isIso_colimit_pre`：final_iff_isIso_coli
mit_pre : Final F ↔ forall G : D ⥤ Type v, IsIso (colimit.pre G F)
· 使用定理 `CategoryTheory.Functor.final_natIso_iff`：final_natIso_iff {F F' : C ⥤ D}
 (i : F ≅ F') : Final F ↔ Final F'
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_left`：of_isIso_comp_left {X Y Z : C} 
(f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.pre_pre`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} K]   {C : Type u} [inst…
-/
theorem final_of_final_comp [hF : Final F] [hFG : Final (F ⋙ G)] : Final G := by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let _i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ G ⋙ s₃.functor) :=
    isoWhiskerLeft (s₁.inverse ⋙ F) (isoWhiskerRight s₂.unitIso (G ⋙ s₃.functor))
  rw [final_iff_comp_equivalence G s₃.functor, final_iff_equivalence_comp s₂.inverse,
    final_iff_isIso_colimit_pre]
  rw [final_iff_comp_equivalence F s₂.functor, final_iff_equivalence_comp s₁.inverse,
    final_iff_isIso_colimit_pre] at hF
  rw [final_iff_comp_equivalence (F ⋙ G) s₃.functor, final_iff_equivalence_comp s₁.inverse,
    final_natIso_iff _i, final_iff_isIso_colimit_pre] at hFG
  intro H
  replace hFG := hFG H
  rw [← colimit.pre_pre] at hFG
  exact IsIso.of_isIso_comp_left (colimit.pre _ (s₁.inverse ⋙ F ⋙ s₂.functor)) _
/-
**CategoryTheory.Functor.initial_of_initial_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：initial_of_initial_comp [Initial F] [Initial (F ⋙ G)] : Initial G
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_final_comp`：final_of_final_comp [hF : Fi
nal F] [hFG : Final (F ⋙ G)] : Final G
· 使用定理 `CategoryTheory.Functor.initial_of_final_op`：initial_of_final_op (F : C ⥤
 D) [Final F.op] : Initial F
-/
theorem initial_of_initial_comp [Initial F] [Initial (F ⋙ G)] : Initial G := by
  suffices Final G.op from initial_of_final_op _
  have : Final (F.op ⋙ G.op) := show Final (F ⋙ G).op from inferInstance
  exact final_of_final_comp F.op G.op

/-- The hypotheses also imply that `F` is final, see `final_of_comp_full_faithful`. -/
/-
**CategoryTheory.Functor.final_of_comp_full_faithful'** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：final_of_comp_full_faithful' [Full G] [Faithful G] [Final (F ⋙ G)] : Final
 G
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_comp_full_faithful`：final_of_comp_full_f
aithful [Full G] [Faithful G] [Final (F ⋙ G)] : Final F where out d
· 使用定理 `CategoryTheory.Functor.final_of_final_comp`：final_of_final_comp [hF : Fi
nal F] [hFG : Final (F ⋙ G)] : Final G

--- 原说明 ---
The hypotheses also imply that `F` is final, see `final_of_comp_full_faithful`.
-/
theorem final_of_comp_full_faithful' [Full G] [Faithful G] [Final (F ⋙ G)] : Final G :=
  have := final_of_comp_full_faithful F G
  final_of_final_comp F G

/-- The hypotheses also imply that `F` is initial, see `initial_of_comp_full_faithful`. -/
/-
**CategoryTheory.Functor.initial_of_comp_full_faithful'** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：initial_of_comp_full_faithful' [Full G] [Faithful G] [Initial (F ⋙ G)] : I
nitial G
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_comp_full_faithful`：initial_of_comp_fu
ll_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial F where out d
· 使用定理 `CategoryTheory.Functor.initial_of_initial_comp`：initial_of_initial_comp 
[Initial F] [Initial (F ⋙ G)] : Initial G

--- 原说明 ---
The hypotheses also imply that `F` is initial, see `initial_of_comp_full_faithfu
l`.
-/
theorem initial_of_comp_full_faithful' [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial G :=
  have := initial_of_comp_full_faithful F G
  initial_of_initial_comp F G
/-
**CategoryTheory.Functor.final_iff_comp_final_full_faithful** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：final_iff_comp_final_full_faithful [Final G] [Full G] [Faithful G] : Final
 F ↔ Final (F ⋙ G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_comp_full_faithful`：final_of_comp_full_f
aithful [Full G] [Faithful G] [Final (F ⋙ G)] : Final F where out d
-/
theorem final_iff_comp_final_full_faithful [Final G] [Full G] [Faithful G] :
    Final F ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp _ _, fun _ => final_of_comp_full_faithful F G⟩
/-
**CategoryTheory.Functor.initial_iff_comp_initial_full_faithful** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：initial_iff_comp_initial_full_faithful [Initial G] [Full G] [Faithful G] :
 Initial F ↔ Initial (F ⋙ G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_comp_full_faithful`：initial_of_comp_fu
ll_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial F where out d
-/
theorem initial_iff_comp_initial_full_faithful [Initial G] [Full G] [Faithful G] :
    Initial F ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp _ _, fun _ => initial_of_comp_full_faithful F G⟩
/-
**CategoryTheory.Functor.final_iff_final_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：final_iff_final_comp [Final F] : Final G ↔ Final (F ⋙ G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.final_of_final_comp`：final_of_final_comp [hF : Fi
nal F] [hFG : Final (F ⋙ G)] : Final G
-/
theorem final_iff_final_comp [Final F] : Final G ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp _ _, fun _ => final_of_final_comp F G⟩
/-
**CategoryTheory.Functor.initial_iff_initial_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：initial_iff_initial_comp [Initial F] : Initial G ↔ Initial (F ⋙ G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_initial_comp`：initial_of_initial_comp 
[Initial F] [Initial (F ⋙ G)] : Initial G
-/
theorem initial_iff_initial_comp [Initial F] : Initial G ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp _ _, fun _ => initial_of_initial_comp F G⟩

end

section

variable {C : Type u₁} [Category.{v₁} C] {c : C}

/-
**CategoryTheory.Functor.final_fromPUnit_of_isTerminal** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：final_fromPUnit_of_isTerminal (hc : Limits.IsTerminal c) : (fromPUnit c).F
inal where out c'
参数：hc : Limits.IsTerminal c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.obj_ext`：obj_ext (x y : StructuredArrow S
 T) (hr : x.right = y.right) (hh : x.hom ≫ T.map (eqToHom hr) = y.hom) : x = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Discrete.instSubsingleton`：∀ {α : Type u₁} [Subsingleton 
α], Subsingleton (CategoryTheory.Discrete α)
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `CategoryTheory.isConnected_of_nonempty_and_subsingleton`：∀ {J : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} J] [Nonempty J] [Subsingleton J], Cate
goryTheory.IsConnected J
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma final_fromPUnit_of_isTerminal (hc : Limits.IsTerminal c) : (fromPUnit c).Final where
  out c' := by
    let : Inhabited (StructuredArrow c' (fromPUnit c)) := ⟨.mk (Y := default) (hc.from c')⟩
    let : Subsingleton (StructuredArrow c' (fromPUnit c)) :=
      ⟨fun i j ↦ StructuredArrow.obj_ext _ _ (by cat_disch) (hc.hom_ext _ _)⟩
    infer_instance
/-
**CategoryTheory.Functor.initial_fromPUnit_of_isInitial** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：initial_fromPUnit_of_isInitial (hc : Limits.IsInitial c) : (fromPUnit c).I
nitial where out c'
参数：hc : Limits.IsInitial c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.obj_ext`：obj_ext (x y : CostructuredArr
ow S T) (hl : x.left = y.left) (hh : S.map (eqToHom hl) ≫ y.hom = x.hom) : x = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Discrete.instSubsingleton`：∀ {α : Type u₁} [Subsingleton 
α], Subsingleton (CategoryTheory.Discrete α)
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.isConnected_of_nonempty_and_subsingleton`：∀ {J : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} J] [Nonempty J] [Subsingleton J], Cate
goryTheory.IsConnected J
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma initial_fromPUnit_of_isInitial (hc : Limits.IsInitial c) : (fromPUnit c).Initial where
  out c' := by
    let : Inhabited (CostructuredArrow (fromPUnit c) c') := ⟨.mk (Y := default) (hc.to c')⟩
    let : Subsingleton (CostructuredArrow (fromPUnit c) c') :=
      ⟨fun i j ↦ CostructuredArrow.obj_ext _ _ (by cat_disch) (hc.hom_ext _ _)⟩
    infer_instance
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasTerminal C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesLimit (Functor.empty.{0} C) F] : F.Final :=
  have : (fromPUnit.{0} (⊤_ C)).Final := final_fromPUnit_of_isTerminal terminalIsTerminal
  have : (fromPUnit.{0} (F.obj (⊤_ C))).Final := final_fromPUnit_of_isTerminal
    (terminalIsTerminal.isTerminalObj F (⊤_ C))
  have : ((fromPUnit.{0} (⊤_ C)) ⋙ F).Final := final_of_natIso (F := fromPUnit.{0} (F.obj (⊤_ C)))
    (Discrete.natIso (fun _ => Iso.refl _))
  final_of_final_comp (fromPUnit.{0} (⊤_ C)) F
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasInitial C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesColimit (Functor.empty.{0} C) F] : F.Initial :=
  have : (fromPUnit.{0} (⊥_ C)).Initial := initial_fromPUnit_of_isInitial initialIsInitial
  have : (fromPUnit.{0} (F.obj (⊥_ C))).Initial := initial_fromPUnit_of_isInitial
    (initialIsInitial.isInitialObj F (⊥_ C))
  have : ((fromPUnit.{0} (⊥_ C)) ⋙ F).Initial := initial_of_natIso
    (F := fromPUnit.{0} (F.obj (⊥_ C))) (Discrete.natIso (fun _ => Iso.refl _))
  initial_of_initial_comp (fromPUnit.{0} (⊥_ C)) F

end

section

variable {C D : Type*} [Category* C] [Category* D]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ Dᵒᵖ) [Initial F] : F.leftOp.Final :=
  inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).Final
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ Dᵒᵖ) [Final F] : F.leftOp.Initial :=
  inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).Initial
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : Cᵒᵖ ⥤ D) [Initial F] : F.rightOp.Final :=
  inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).Final
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : Cᵒᵖ ⥤ D) [Final F] : F.rightOp.Initial :=
  inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).Initial

end


end Functor

section Filtered
open CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency false in
/-- Final functors preserve filteredness.

This can be seen as a generalization of `IsFiltered.of_right_adjoint` (which states that right
adjoints preserve filteredness), as right adjoints are always final, see `final_of_adjunction`.
-/
/-
**CategoryTheory.IsFilteredOrEmpty.of_final** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsFilteredOrEmpty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.Final] [CategoryTheory.IsFilteredOrEmpty C], CategoryTheory.IsFilteredOrEmpt
y D
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.isPreconnected_induction`：isPreconnected_induction [IsPre
connected J] (Z : J -> Sort*) (h₁ : forall {j₁ j₂ : J} (_ : j₁ ⟶ j₂), Z j₁ -> Z 
j₂) (h₂ : forall {j₁ j₂ : J} …
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.span`：span {i j j' : C} (f : i ⟶ j) (f' : i ⟶ 
j') : exists (k : C) (g : j ⟶ k) (g' : j' ⟶ k), f ≫ g = f' ≫ g'
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.StructuredArrow.w_assoc`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {S : D} {T : Categ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'

--- 原说明 ---
Final functors preserve filteredness.

This can be seen as a generalization of `IsFiltered.of_right_adjoint` (which sta
tes that right
adjoints preserve filteredness), as right adjoints are always final, see `final_
of_adjunction`.
-/
theorem IsFilteredOrEmpty.of_final (F : C ⥤ D) [Final F] [IsFilteredOrEmpty C] :
    IsFilteredOrEmpty D where
  cocone_objs X Y := ⟨F.obj (IsFiltered.max (Final.lift F X) (Final.lift F Y)),
    Final.homToLift F X ≫ F.map (IsFiltered.leftToMax _ _),
    ⟨Final.homToLift F Y ≫ F.map (IsFiltered.rightToMax _ _), trivial⟩⟩
  cocone_maps {X Y} f g := by
    let P : StructuredArrow X F → Prop := fun h => ∃ (Z : C) (q₁ : h.right ⟶ Z)
      (q₂ : Final.lift F Y ⟶ Z), h.hom ≫ F.map q₁ = f ≫ Final.homToLift F Y ≫ F.map q₂
    rsuffices ⟨Z, q₁, q₂, h⟩ : Nonempty (P (StructuredArrow.mk (g ≫ Final.homToLift F Y)))
    · refine ⟨F.obj (IsFiltered.coeq q₁ q₂),
        Final.homToLift F Y ≫ F.map (q₁ ≫ IsFiltered.coeqHom q₁ q₂), ?_⟩
      conv_lhs => rw [IsFiltered.coeq_condition]
      simp only [F.map_comp, ← reassoc_of% h, StructuredArrow.mk_hom_eq_self, Category.assoc]
    have h₀ : P (StructuredArrow.mk (f ≫ Final.homToLift F Y)) := ⟨_, 𝟙 _, 𝟙 _, by simp⟩
    refine isPreconnected_induction P ?_ ?_ h₀ _
    · rintro U V h ⟨Z, q₁, q₂, hq⟩
      obtain ⟨W, q₃, q₄, hq'⟩ := IsFiltered.span q₁ h.right
      refine ⟨W, q₄, q₂ ≫ q₃, ?_⟩
      rw [F.map_comp, ← reassoc_of% hq, ← F.map_comp, hq', F.map_comp, StructuredArrow.w_assoc]
    · rintro U V h ⟨Z, q₁, q₂, hq⟩
      exact ⟨Z, h.right ≫ q₁, q₂, by simp only [F.map_comp, StructuredArrow.w_assoc, hq]⟩

/-- Final functors preserve filteredness.

This can be seen as a generalization of `IsFiltered.of_right_adjoint` (which states that right
adjoints preserve filteredness), as right adjoints are always final, see `final_of_adjunction`.
-/
/-
**CategoryTheory.IsFiltered.of_final** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sFiltered`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.Final] [CategoryTheory.IsFiltered C], CategoryTheory.IsFiltered D
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.of_final`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C

--- 原说明 ---
Final functors preserve filteredness.

This can be seen as a generalization of `IsFiltered.of_right_adjoint` (which sta
tes that right
adjoints preserve filteredness), as right adjoints are always final, see `final_
of_adjunction`.
-/
theorem IsFiltered.of_final (F : C ⥤ D) [Final F] [IsFiltered C] : IsFiltered D :=
{ IsFilteredOrEmpty.of_final F with
  nonempty := Nonempty.map F.obj IsFiltered.nonempty }

/-- Initial functors preserve cofilteredness.

This can be seen as a generalization of `IsCofiltered.of_left_adjoint` (which states that left
adjoints preserve cofilteredness), as right adjoints are always initial,
see `initial_of_adjunction`.
-/
/-
**CategoryTheory.IsCofilteredOrEmpty.of_initial** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsCofilteredOrEmpty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.Initial] [CategoryTheory.IsCofilteredOrEmpty C],   CategoryTheory.IsCofilter
edOrEmpty D
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.of_final`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.isCofilteredOrEmpty_of_isFilteredOrEmpty_op`：isCofiltered
OrEmpty_of_isFilteredOrEmpty_op [IsFilteredOrEmpty Cᵒᵖ] : IsCofilteredOrEmpty C

--- 原说明 ---
Initial functors preserve cofilteredness.

This can be seen as a generalization of `IsCofiltered.of_left_adjoint` (which st
ates that left
adjoints preserve cofilteredness), as right adjoints are always initial,
see `initial_of_adjunction`.
-/
theorem IsCofilteredOrEmpty.of_initial (F : C ⥤ D) [Initial F] [IsCofilteredOrEmpty C] :
    IsCofilteredOrEmpty D :=
  have : IsFilteredOrEmpty Dᵒᵖ := IsFilteredOrEmpty.of_final F.op
  isCofilteredOrEmpty_of_isFilteredOrEmpty_op _

/-- Initial functors preserve cofilteredness.

This can be seen as a generalization of `IsCofiltered.of_left_adjoint` (which states that left
adjoints preserve cofilteredness), as right adjoints are always initial,
see `initial_of_adjunction`.
-/
/-
**CategoryTheory.IsCofiltered.of_initial** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsCofiltered`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.Initial] [CategoryTheory.IsCofiltered C], CategoryTheory.IsCofiltered D
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.of_final`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.isCofiltered_of_isFiltered_op`：isCofiltered_of_isFiltered
_op [IsFiltered Cᵒᵖ] : IsCofiltered C

--- 原说明 ---
Initial functors preserve cofilteredness.

This can be seen as a generalization of `IsCofiltered.of_left_adjoint` (which st
ates that left
adjoints preserve cofilteredness), as right adjoints are always initial,
see `initial_of_adjunction`.
-/
theorem IsCofiltered.of_initial (F : C ⥤ D) [Initial F] [IsCofiltered C] : IsCofiltered D :=
  have : IsFiltered Dᵒᵖ := IsFiltered.of_final F.op
  isCofiltered_of_isFiltered_op _

end Filtered

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

open CategoryTheory.Functor

/-- The functor `StructuredArrow.pre X T S` is final if `T` is final. -/
/-
**CategoryTheory.StructuredArrow.final_pre** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.StructuredArrow`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (T : CategoryTheory.Functor C D) [T.Final]   (S : Ca
tegoryTheory.Functor D E) (X : E), (CategoryTheory.StructuredArrow.pre X T S).Fi
nal
参数：T : CategoryTheory.Functor C D；S : CategoryTheory.Functor D E；X : E；CategoryT
heory.StructuredArrow.pre X T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…

--- 原说明 ---
The functor `StructuredArrow.pre X T S` is final if `T` is final.
-/
instance StructuredArrow.final_pre (T : C ⥤ D) [Final T] (S : D ⥤ E) (X : E) :
    Final (pre X T S) := by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (StructuredArrow.preEquivalence T f)]
  exact Final.out f.right

/-- The functor `CostructuredArrow.pre X T S` is initial if `T` is initial. -/
/-
**CategoryTheory.CostructuredArrow.initial_pre** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.CostructuredArrow`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (T : CategoryTheory.Functor C D) [T.Initial]   (S : 
CategoryTheory.Functor D E) (X : E), (CategoryTheory.CostructuredArrow.pre T S X
).Initial
参数：T : CategoryTheory.Functor C D；S : CategoryTheory.Functor D E；X : E；CategoryT
heory.CostructuredArrow.pre T S X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…

--- 原说明 ---
The functor `CostructuredArrow.pre X T S` is initial if `T` is initial.
-/
instance CostructuredArrow.initial_pre (T : C ⥤ D) [Initial T] (S : D ⥤ E) (X : E) :
    Initial (CostructuredArrow.pre T S X) := by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (CostructuredArrow.preEquivalence T f)]
  exact Initial.out f.left

end

section Grothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : D ⥤ Cat) (G : C ⥤ D)

open CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
/-- A prefunctor mapping structured arrows on `G` to structured arrows on `pre F G` with their
action on fibers being the identity. -/
/-
**CategoryTheory.Grothendieck.structuredArrowToStructuredArrowPre** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Grothendieck`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor D CategoryTheory.Cat) →           (G : CategoryTheory.Functo
r C D) →             (d : D) →               (f : ↑(F.obj d)) →                 
CategoryTheory.StructuredArrow d G ⥤q                   CategoryTheory.Structure
dArrow { base := d, fiber := f } (CategoryTheory.Grothendieck.pre F G)
参数：F : CategoryTheory.Functor D CategoryTheory.Cat；G : CategoryTheory.Functor C 
D；d : D；f : ↑(F.obj d)；CategoryTheory.Grothendieck.pre F G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prefunctor mapping structured arrows on `G` to structured arrows on `pre F G` 
with their
action on fibers being the identity.
-/
def Grothendieck.structuredArrowToStructuredArrowPre (d : D) (f : F.obj d) :
    StructuredArrow d G ⥤q StructuredArrow ⟨d, f⟩ (pre F G) where
  obj := fun X => StructuredArrow.mk (Y := ⟨X.right, (F.map X.hom).toFunctor.obj f⟩)
    (Grothendieck.Hom.mk (by exact X.hom) (by dsimp; exact 𝟙 _))
  map := fun g => StructuredArrow.homMk
    (Grothendieck.Hom.mk (by exact g.right)
      (eqToHom (by
        dsimp +instances
        rw [← StructuredArrow.w g, map_comp, Cat.Hom.comp_obj])))
    (by
      simp only [StructuredArrow.mk_right]
      generalize_proofs
      apply Grothendieck.ext <;> simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Grothendieck.final_pre** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Grothendieck`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor D Ca
tegoryTheory.Cat) (G : CategoryTheory.Functor C D) [hG : G.Final],   (CategoryTh
eory.Grothendieck.pre F G).Final
参数：F : CategoryTheory.Functor D CategoryTheory.Cat；G : CategoryTheory.Functor C 
D；CategoryTheory.Grothendieck.pre F G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.instNonemptyStructuredArrow`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_zag`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J},   CategoryTheory.Zag j₁ j₂ → CategoryTheory.Zigza
g j₁ j₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Grothendieck.ext`：ext {X Y : Grothendieck F} (f g : Hom X
 Y) (w_base : f.base = g.base) (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g
.fiber) : f = g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.eqToHom_naturality_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {β : Sort u_1} {f g : β → C} (z : (b : β) → f b ⟶ g
 b)   {j j' : β} (w : j = j')…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.zigzag_prefunctor_obj_of_zigzag`：zigzag_prefunctor_obj_of
_zigzag (F : J ⥤q K) {j₁ j₂ : J} (h : Zigzag j₁ j₂) : Zigzag (F.obj j₁) (F.obj j
₂)
· 使用定理 `CategoryTheory.isPreconnected_zigzag`：isPreconnected_zigzag [IsPreconnec
ted J] (j₁ j₂ : J) : Zigzag j₁ j₂
· 使用定理 `CategoryTheory.IsConnected.toIsPreconnected`：∀ {J : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J],   Catego
ryTheory.IsPreconnected J
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
-/
instance Grothendieck.final_pre [hG : Final G] : (Grothendieck.pre F G).Final := by
  constructor
  rintro ⟨d, f⟩
  let ⟨u, c, g⟩ : Nonempty (StructuredArrow d G) := inferInstance
  let : Nonempty (StructuredArrow ⟨d, f⟩ (pre F G)) :=
    ⟨u, ⟨c, (F.map g).toFunctor.obj f⟩, ⟨(by exact g), (by exact 𝟙 _)⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨⟨⟩⟩, ⟨bi, fi⟩, ⟨gbi, gfi⟩⟩ ⟨⟨⟨⟩⟩, ⟨bj, fj⟩, ⟨gbj, gfj⟩⟩
  dsimp +instances at fj fi gfi gbi gbj gfj
  apply Zigzag.trans (j₂ := StructuredArrow.mk (Y := ⟨bi, ((F.map gbi).toFunctor.obj f)⟩)
      (Grothendieck.Hom.mk gbi (𝟙 _)))
    (.of_zag (.inr ⟨StructuredArrow.homMk (Grothendieck.Hom.mk (by dsimp; exact 𝟙 _)
      (eqToHom (by simp) ≫ gfi)) (by apply Grothendieck.ext <;> simp)⟩))
  refine Zigzag.trans (j₂ := StructuredArrow.mk (Y := ⟨bj, ((F.map gbj).toFunctor.obj f)⟩)
      (Grothendieck.Hom.mk gbj (𝟙 _))) ?_
    (.of_zag (.inl ⟨StructuredArrow.homMk (Grothendieck.Hom.mk (by dsimp; exact 𝟙 _)
      (eqToHom (by simp) ≫ gfj)) (by apply Grothendieck.ext <;> simp)⟩))
  exact zigzag_prefunctor_obj_of_zigzag (Grothendieck.structuredArrowToStructuredArrowPre F G d f)
    (isPreconnected_zigzag (.mk gbi) (.mk gbj))

open Limits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation `α : F ⟶ G` between functors `F G : C ⥤ Cat` which is final on each
fiber `(α.app X)` induces an equivalence of fiberwise colimits of `map α ⋙ H` and `H` for each
functor `H : Grothendieck G ⥤ Type`. -/
/-
**CategoryTheory.Grothendieck.fiberwiseColimitMapCompEquivalence** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Grothendieck`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {F G :
 CategoryTheory.Functor C CategoryTheory.Cat} →       (α : F ⟶ G) →         [∀ (
X : C), (α.app X).toFunctor.Final] →           (H : CategoryTheory.Functor (Cate
goryTheory.Grothendieck G) (Type u₂)) →             CategoryTheory.Limits.fiberw
iseColimit ((CategoryTheory.Grothendieck.map α).comp H) ≅               Category
Theory.Limits.fiberwiseColimit H
参数：α : F ⟶ G；X : C；α.app X；H : CategoryTheory.Functor (CategoryTheory.Grothendie
ck G) (Type u₂)；(CategoryTheory.Grothendieck.map α).comp H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation `α : F ⟶ G` between functors `F G : C ⥤ Cat` which is f
inal on each
fiber `(α.app X)` induces an equivalence of fiberwise colimits of `map α ⋙ H` an
d `H` for each
functor `H : Grothendieck G ⥤ Type`.
-/
def Grothendieck.fiberwiseColimitMapCompEquivalence {C : Type u₁} [Category.{v₁} C]
    {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) [∀ X, Final (α.app X).toFunctor]
    (H : Grothendieck G ⥤ Type u₂) : fiberwiseColimit (map α ⋙ H) ≅ fiberwiseColimit H :=
  NatIso.ofComponents
    (fun X =>
      HasColimit.isoOfNatIso ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (ιCompMap α X) H ≪≫ Functor.associator _ _ _) ≪≫
      Final.colimitIso (α.app X).toFunctor (ι G X ⋙ H))
    (fun f => colimit.hom_ext <| fun d => by
      simp only [map, Cat.Hom.comp_toFunctor, comp_obj, ι_obj,
        fiberwiseColimit_map, ιNatTrans, ιCompMap, Iso.trans_hom, Category.assoc, ι_colimMap_assoc,
        NatTrans.comp_app, whiskerRight_app, Functor.comp_map, Cat.Hom₂.eqToHom_toNatTrans,
        eqToHom_app, map_id, Category.comp_id, associator_hom_app, colimit.ι_pre_assoc,
        HasColimit.isoOfNatIso_ι_hom_assoc, Iso.symm_hom, isoWhiskerRight_hom, associator_inv_app,
        NatIso.ofComponents_hom_app, Iso.refl_hom, Final.ι_colimitIso_hom, Category.id_comp,
        Final.ι_colimitIso_hom_assoc, colimit.ι_pre]
      have := Functor.congr_obj congr($(α.naturality f).toFunctor) d
      dsimp at this
      congr
      apply eqToHom_heq_id_dom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- This is the small version of the more general lemma `Grothendieck.final_map` below. -/
/-
**CategoryTheory.Grothendieck.final_map_small** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the small version of the more general lemma `Grothendieck.final_map` bel
ow.
-/
private lemma Grothendieck.final_map_small {C : Type u₁} [SmallCategory C] {F G : C ⥤ Cat.{u₁, u₁}}
    (α : F ⟶ G) [hα : ∀ X, Final (α.app X).toFunctor] : Final (map α) := by
  rw [final_iff_isIso_colimit_pre]
  intro H
  let i := (colimitFiberwiseColimitIso _).symm ≪≫
    HasColimit.isoOfNatIso (fiberwiseColimitMapCompEquivalence α H) ≪≫ colimitFiberwiseColimitIso _
  convert! Iso.isIso_hom i
  apply colimit.hom_ext
  intro X
  simp [i, fiberwiseColimitMapCompEquivalence]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `Grothendieck.map α` for a natural transformation `α : F ⟶ G`, with
`F G : C ⥤ Cat`, is final if for each `X : C`, the functor `α.app X` is final. -/
/-
**CategoryTheory.Grothendieck.final_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Grothendieck`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F G : Categor
yTheory.Functor C CategoryTheory.Cat}   (α : F ⟶ G) [hα : ∀ (X : C), (α.app X).t
oFunctor.Final], (CategoryTheory.Grothendieck.map α).Final
参数：α : F ⟶ G；X : C；α.app X；CategoryTheory.Grothendieck.map α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Limits.Final.0.CategoryTheory.Grothendie
ck.final_map_small`：∀ {C : Type u₁} [inst : CategoryTheory.SmallCategory C] {F G
 : CategoryTheory.Functor C CategoryTheory.Cat} (α : F ⟶ G)   [hα : ∀ (X : C), (
…
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.final_iff_comp_equivalence`：final_iff_comp_equiva
lence [IsEquivalence G] : Final F ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.final_iff_equivalence_comp`：final_iff_equivalence
_comp [IsEquivalence F] : Final G ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
The functor `Grothendieck.map α` for a natural transformation `α : F ⟶ G`, with
`F G : C ⥤ Cat`, is final if for each `X : C`, the functor `α.app X` is final.
-/
lemma Grothendieck.final_map {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G)
    [hα : ∀ X, Final (α.app X).toFunctor] : Final (map α) := by
  let sC : C ≌ AsSmall.{max u₁ u₂ v₁ v₂} C := AsSmall.equiv
  let F' : AsSmall C ⥤ Cat := sC.inverse ⋙ F ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let G' : AsSmall C ⥤ Cat := sC.inverse ⋙ G ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let α' : F' ⟶ G' := whiskerLeft _ (whiskerRight α _)
  have : ∀ X, Final (α'.app X).toFunctor := fun X =>
    inferInstanceAs (AsSmall.equiv.inverse ⋙ _ ⋙ AsSmall.equiv.functor).Final
  have hα' : (map α').Final := final_map_small _
  dsimp only [α', ← Equivalence.symm_functor] at hα'
  have i := mapWhiskerLeftIsoConjPreMap sC.symm (whiskerRight α Cat.asSmallFunctor)
    ≪≫ isoWhiskerLeft _ (isoWhiskerRight (mapWhiskerRightAsSmallFunctor α) _)
  have := final_of_natIso i
  rwa [← final_iff_equivalence_comp, ← final_iff_comp_equivalence,
    ← final_iff_equivalence_comp, ← final_iff_comp_equivalence] at this

end Grothendieck

section Prod

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {C' : Type u₃} [Category.{v₃} C']
variable {D' : Type u₄} [Category.{v₄} D']
variable (F : C ⥤ D) (G : C' ⥤ D')

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Final] [G.Final] : (F.prod G).Final where
  out := fun ⟨d, d'⟩ => isConnected_of_equivalent (StructuredArrow.prodEquivalence d d' F G).symm
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Initial] [G.Initial] : (F.prod G).Initial where
  out := fun ⟨d, d'⟩ => isConnected_of_equivalent (CostructuredArrow.prodEquivalence F G d d').symm

end Prod

namespace ObjectProperty

set_option backward.isDefEq.respectTransparency.types false in
/-- For the full subcategory induced by an object property `P` on `C`, to show initiality of
the inclusion functor it is enough to consider arrows to objects outside of the subcategory. -/
/-
**CategoryTheory.ObjectProperty.initial_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For the full subcategory induced by an object property `P` on `C`, to show initi
ality of
the inclusion functor it is enough to consider arrows to objects outside of the 
subcategory.
-/
theorem initial_ι {C : Type u₁} [Category.{v₁} C] (P : ObjectProperty C)
    (h : ∀ d, ¬ P d → IsConnected (CostructuredArrow P.ι d)) :
    P.ι.Initial := .mk <| fun d => by
  by_cases hd : P d
  · have : Nonempty (CostructuredArrow P.ι d) := ⟨⟨d, hd⟩, ⟨⟨⟩⟩, 𝟙 _⟩
    refine zigzag_isConnected (fun j₁ j₂ ↦ Zigzag.trans
      (j₂ := by exact CostructuredArrow.mk (Y := ⟨d, hd⟩) (𝟙 _)) (.of_hom ?_) (.of_inv ?_))
    · exact CostructuredArrow.homMk (InducedCategory.homMk j₁.hom)
    · exact CostructuredArrow.homMk (InducedCategory.homMk j₂.hom)
  · exact h d hd

end ObjectProperty

section Restriction

variable {J C : Type*} [Category* J] [Category* C] {D : J ⥤ C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `Over j ⥤ J` is initial, restricting a limit cone to the diagram above `j`,
preserves the limit. -/
/-
**CategoryTheory.Limits.IsLimit.overPost** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.IsLimit`。
形式化陈述：{J : Type u_1} →   {C : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} J] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C] →         {D
 : CategoryTheory.Functor J C} →           {c : CategoryTheory.Limits.Cone D} → 
            CategoryTheory.Limits.IsLimit c →               (j : J) → [(Category
Theory.Over.forget j).Initial] → CategoryTheory.Limits.IsLimit (c.overPost j)
参数：j : J；CategoryTheory.Over.forget j；c.overPost j。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `Over j ⥤ J` is initial, restricting a limit cone to the diagram above `j`,
preserves the limit.
-/
noncomputable def Limits.IsLimit.overPost {c : Cone D} (hc : IsLimit c) (j : J)
    [(CategoryTheory.Over.forget j).Initial] : IsLimit (c.overPost j) := by
  haveI : Nonempty (Over j) := ⟨Over.mk (𝟙 j)⟩
  letI c'' := Over.liftCone (Over.forget j ⋙ D) (X := D.obj j)
    (Functor.whiskerRight (Over.forgetCocone j).ι D ≫ (Functor.constComp _ _ _).hom)
    (c.whisker (CategoryTheory.Over.forget j)) (c.π.app j) (by cat_disch)
  letI hc'' : IsLimit c'' :=
    Over.isLimitLiftCone _ _ _ _ _ <| (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ hc''
  · exact NatIso.ofComponents (fun k ↦ CategoryTheory.Over.isoMk (Iso.refl _))
  · exact Cone.ext (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `Over j ⥤ J` is final, restricting a colimit cocone to the diagram below `j`,
preserves the limit. -/
/-
**CategoryTheory.Limits.IsColimit.underPost** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.IsColimit`。
形式化陈述：{J : Type u_1} →   {C : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} J] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C] →         {D
 : CategoryTheory.Functor J C} →           {c : CategoryTheory.Limits.Cocone D} 
→             CategoryTheory.Limits.IsColimit c →               (j : J) → [(Cate
goryTheory.Under.forget j).Final] → CategoryTheory.Limits.IsColimit (c.underPost
 j)
参数：j : J；CategoryTheory.Under.forget j；c.underPost j。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `Over j ⥤ J` is final, restricting a colimit cocone to the diagram below `j`,
preserves the limit.
-/
noncomputable def Limits.IsColimit.underPost {c : Cocone D} (hc : IsColimit c) (j : J)
    [(CategoryTheory.Under.forget j).Final] : IsColimit (c.underPost j) := by
  haveI : Nonempty (Under j) := ⟨CategoryTheory.Under.mk (𝟙 j)⟩
  letI c'' := Under.liftCocone (CategoryTheory.Under.forget j ⋙ D) (X := D.obj j)
    ((Functor.constComp _ _ _).inv ≫ Functor.whiskerRight ((Under.forgetCone j).π) D)
    (c.whisker (CategoryTheory.Under.forget j)) (c.ι.app j) (by cat_disch)
  letI hc'' : IsColimit c'' :=
    Under.isColimitLiftCocone _ _ _ _ _ <| (Functor.Final.isColimitWhiskerEquiv _ _).symm hc
  refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ hc''
  · exact NatIso.ofComponents (fun k ↦ CategoryTheory.Under.isoMk (Iso.refl _))
  · exact Cocone.ext (Iso.refl _)

end Restriction

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C₀ C : Type*} [Category* C₀] [Category* C]
    (F : C₀ ⥤ C) (X : C) [F.Initial] :
    (CostructuredArrow.toOver F X).Initial where
  out Y := by
    rw [isConnected_iff_of_equivalence
      (CostructuredArrow.costructuredArrowToOverEquivalence F Y)]
    infer_instance

end CategoryTheory

