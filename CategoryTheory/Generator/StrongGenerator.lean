/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Strong generators

If `P : ObjectProperty C`, we say that `P` is a strong generator if it is a
generator (in the sense that `IsSeparating P` holds) such that for any
proper subobject `A ⊂ X`, there exists a morphism `G ⟶ X` which does not factor
through `A` from an object satisfying `P`.

The main result is the lemma `isStrongGenerator_iff_exists_extremalEpi` which
says that if `P` is `w`-small, `C` is locally `w`-small and
has coproducts of size `w`, then `P` is a strong generator iff any
object of `C` is the target of an extremal epimorphism from a coproduct of
objects satisfying `P`.

We also show that if any object in `C` is a colimit of objects in `S`,
then `S` is a strong generator.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Limits


namespace ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- A property `P : ObjectProperty C` is a strong generator
if it is separating and for any proper subobject `A ⊂ X`, there exists
a morphism `G ⟶ X` which does not factor through `A` from an object
such that `P G` holds. -/
/-
**CategoryTheory.ObjectProperty.IsStrongGenerator** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：IsStrongGenerator : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P : ObjectProperty C` is a strong generator
if it is separating and for any proper subobject `A ⊂ X`, there exists
a morphism `G ⟶ X` which does not factor through `A` from an object
such that `P G` holds.
-/
def IsStrongGenerator : Prop :=
  P.IsSeparating ∧ ∀ ⦃X : C⦄ (A : Subobject X),
    (∀ (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f) → A = ⊤

variable {P}
/-
**CategoryTheory.ObjectProperty.isStrongGenerator_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：isStrongGenerator_iff : P.IsStrongGenerator ↔ P.IsSeparating ∧ forall ⦃X Y
 : C⦄ (i : X ⟶ Y) [Mono i], (forall (G : C) (_ : P G), Function.Surjective (fun 
(f : G ⟶ X) => f ≫ i)) -> IsIso i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.isIso_iff_mk_eq_top`：isIso_iff_mk_eq_top {X Y :
 C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤
· 使用定理 `CategoryTheory.Subobject.mk_factors_iff`：mk_factors_iff {X Y Z : C} (f :
 Y ⟶ X) [Mono f] (g : Z ⟶ X) : (Subobject.mk f).Factors g ↔ (MonoOver.mk f).Fact
ors g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.isIso_arrow_iff_eq_top`：isIso_arrow_iff_eq_top 
{Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
-/
lemma isStrongGenerator_iff :
    P.IsStrongGenerator ↔ P.IsSeparating ∧
      ∀ ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i],
        (∀ (G : C) (_ : P G), Function.Surjective (fun (f : G ⟶ X) ↦ f ≫ i)) → IsIso i := by
  refine ⟨fun ⟨hS₁, hS₂⟩ ↦ ⟨hS₁, fun X Y i _ h ↦ ?_⟩,
    fun ⟨hS₁, hS₂⟩ ↦ ⟨hS₁, fun X A hA ↦ ?_⟩⟩
  · rw [Subobject.isIso_iff_mk_eq_top]
    refine hS₂ _ (fun G hG g ↦ ?_)
    rw [Subobject.mk_factors_iff]
    exact h G hG g
  · rw [← Subobject.isIso_arrow_iff_eq_top]
    exact hS₂ A.arrow (fun G hG g ↦ ⟨_, Subobject.factorThru_arrow _ _ (hA G hG g)⟩)

namespace IsStrongGenerator

section

variable (hP : P.IsStrongGenerator)

include hP

/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.isSeparating** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrongGenerator`。
形式化陈述：isSeparating : P.IsSeparating
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma isSeparating : P.IsSeparating := hP.1
/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.subobject_eq_top** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrongGenerator`。
形式化陈述：subobject_eq_top {X : C} {A : Subobject X} (hA : forall (G : C) (_ : P G) 
(f : G ⟶ X), Subobject.Factors A f) : A = ⊤
参数：hA : forall (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma subobject_eq_top {X : C} {A : Subobject X}
    (hA : ∀ (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f) :
    A = ⊤ :=
  hP.2 _ hA
/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.isIso_of_mono** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrongGenerator`。
形式化陈述：isIso_of_mono ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i] (hi : forall (G : C) (_ : P G
), Function.Surjective (fun (f : G ⟶ X) => f ≫ i)) : IsIso i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.isStrongGenerator_iff`：isStrongGenerator_i
ff : P.IsStrongGenerator ↔ P.IsSeparating ∧ forall ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i
], (forall (G : C) (_ : P G), Function.Su…
-/
lemma isIso_of_mono ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i]
    (hi : ∀ (G : C) (_ : P G), Function.Surjective (fun (f : G ⟶ X) ↦ f ≫ i)) : IsIso i :=
  (isStrongGenerator_iff.1 hP).2 i hi
/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.exists_of_subobject_ne_top** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrongGenerator`。
形式化陈述：exists_of_subobject_ne_top {X : C} {A : Subobject X} (hA : A != ⊤) : exist
s (G : C) (_ : P G) (f : G ⟶ X), ¬ Subobject.Factors A f
参数：hA : A != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `CategoryTheory.ObjectProperty.IsStrongGenerator.subobject_eq_top`：subobj
ect_eq_top {X : C} {A : Subobject X} (hA : forall (G : C) (_ : P G) (f : G ⟶ X),
 Subobject.Factors A f) : A = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma exists_of_subobject_ne_top {X : C} {A : Subobject X} (hA : A ≠ ⊤) :
    ∃ (G : C) (_ : P G) (f : G ⟶ X), ¬ Subobject.Factors A f := by
  by_contra!
  exact hA (hP.subobject_eq_top this)
/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.exists_of_mono_not_isIso** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrongGenerator`。
形式化陈述：exists_of_mono_not_isIso {X Y : C} (i : X ⟶ Y) [Mono i] (hi : ¬ IsIso i) :
 exists (G : C) (_ : P G) (g : G ⟶ Y), forall (f : G ⟶ X), f ≫ i != g
参数：i : X ⟶ Y；hi : ¬ IsIso i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `CategoryTheory.ObjectProperty.IsStrongGenerator.isIso_of_mono`：isIso_of_
mono ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i] (hi : forall (G : C) (_ : P G), Function.Sur
jective (fun (f : G ⟶ X) => f ≫ i)) : IsIso i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma exists_of_mono_not_isIso {X Y : C} (i : X ⟶ Y) [Mono i] (hi : ¬ IsIso i) :
    ∃ (G : C) (_ : P G) (g : G ⟶ Y), ∀ (f : G ⟶ X), f ≫ i ≠ g := by
  by_contra!
  exact hi (hP.isIso_of_mono i this)

end

end IsStrongGenerator

namespace IsStrongGenerator

/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.mk_of_exists_extremalEpi** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrongGenerator`。
形式化陈述：mk_of_exists_extremalEpi (hS : forall (X : C), exists (ι : Type w) (s : ι 
-> C) (_ : forall i, P (s i)) (c : Cofan s) (_ : IsColimit c) (p : c.pt ⟶ X), Ex
tremalEpi p) : P.IsStrongGenerator
参数：hS : forall (X : C), exists (ι : Type w) (s : ι -> C) (_ : forall i, P (s i))
 (c : Cofan s) (_ : IsColimit c) (p : c.pt ⟶ X), ExtremalEpi p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isStrongGenerator_iff`：isStrongGenerator_i
ff : P.IsStrongGenerator ↔ P.IsSeparating ∧ forall ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i
], (forall (G : C) (_ : P G), Function.Su…
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.mk_of_exists_epi`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectPrope
rty C},   (∀ (X : C), ∃ ι s, ∃ (_ : ∀ (i : ι), P …
· 使用定理 `CategoryTheory.ExtremalEpi.toEpi`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.ExtremalEpi f], 
  CategoryTheory.Epi f
· 使用定理 `CategoryTheory.ExtremalEpi.isIso`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C} {X Y : C} (f : X ⟶ Y) [self : CategoryTheory.ExtremalEpi f]  
 {Z : C} (p : X ⟶ Z) (…
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac_assoc`：∀ {β : Type w} {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma mk_of_exists_extremalEpi
    (hS : ∀ (X : C), ∃ (ι : Type w) (s : ι → C) (_ : ∀ i, P (s i)) (c : Cofan s) (_ : IsColimit c)
      (p : c.pt ⟶ X), ExtremalEpi p) :
    P.IsStrongGenerator := by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_epi.{w} (fun X ↦ ?_), fun X Y i _ hi ↦ ?_⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS X
    exact ⟨ι, s, hs, c, hc, p, inferInstance⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS Y
    replace hi (j : ι) := hi (s j) (hs j) (c.inj j ≫ p)
    choose φ hφ using hi
    exact ExtremalEpi.isIso p (Cofan.IsColimit.desc hc φ) _
      (Cofan.IsColimit.hom_ext hc _ _ (by simp [hφ]))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.extremalEpi_coproductFrom** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrongGenerator`。
形式化陈述：extremalEpi_coproductFrom (hP : IsStrongGenerator P) (X : C) [HasCoproduct
 (P.coproductFromFamily X)] : ExtremalEpi (P.coproductFrom X) where toEpi
参数：hP : IsStrongGenerator P；X : C；P.coproductFromFamily X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.epi_coproductFrom`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProp
erty C},   P.IsSeparating →     ∀ (X : C) [inst_1 …
· 使用引理 `CategoryTheory.ObjectProperty.IsStrongGenerator.isSeparating`：isSeparati
ng : P.IsSeparating
· 使用引理 `CategoryTheory.ObjectProperty.IsStrongGenerator.isIso_of_mono`：isIso_of_
mono ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i] (hi : forall (G : C) (_ : P G), Function.Sur
jective (fun (f : G ⟶ X) => f ≫ i)) : IsIso i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extremalEpi_coproductFrom
    (hP : IsStrongGenerator P) (X : C) [HasCoproduct (P.coproductFromFamily X)] :
    ExtremalEpi (P.coproductFrom X) where
  toEpi := hP.isSeparating.epi_coproductFrom X
  isIso p i fac _ := hP.isIso_of_mono _ (fun G hG f ↦ ⟨P.ιCoproductFrom f hG ≫ p, by simp [fac]⟩)

end IsStrongGenerator

/-
**CategoryTheory.ObjectProperty.isStrongGenerator_iff_exists_extremalEpi** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isStrongGenerator_iff_exists_extremalEpi [HasCoproducts.{w} C] [LocallySma
ll.{w} C] [ObjectProperty.Small.{w} P] : P.IsStrongGenerator ↔ forall (X : C), e
xists (ι : Type w) (s : ι -> C) (_ : forall i, P (s i)) (c : Cofan s) (_ : IsCol
imit c) (p : c.pt ⟶ X), ExtremalEpi p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_small`：hasCoproductsOfShap
e_of_small (β : Type w₂) [Small.{w₁} β] [HasCoproducts.{w₁} C] : HasCoproductsOf
Shape β C
· 使用定理 `CategoryTheory.CostructuredArrow.instSmallOfLocallySmall`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {S : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallFullSubcategoryOfSmall`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [CategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.ObjectProperty.IsStrongGenerator.extremalEpi_coproductFro
m`：extremalEpi_coproductFrom (hP : IsStrongGenerator P) (X : C) [HasCoproduct (P
.coproductFromFamily X)] : ExtremalEpi (P.coproductFrom X) wher…
· 使用引理 `CategoryTheory.ObjectProperty.IsStrongGenerator.mk_of_exists_extremalEpi
`：mk_of_exists_extremalEpi (hS : forall (X : C), exists (ι : Type w) (s : ι -> C
) (_ : forall i, P (s i)) (c : Cofan s) (_ : IsColimit c) (p :…
-/
lemma isStrongGenerator_iff_exists_extremalEpi
    [HasCoproducts.{w} C] [LocallySmall.{w} C] [ObjectProperty.Small.{w} P] :
    P.IsStrongGenerator ↔
      ∀ (X : C), ∃ (ι : Type w) (s : ι → C) (_ : ∀ i, P (s i)) (c : Cofan s) (_ : IsColimit c)
        (p : c.pt ⟶ X), ExtremalEpi p := by
  refine ⟨fun hP X ↦ ?_, fun hP ↦ .mk_of_exists_extremalEpi hP⟩
  have := hasCoproductsOfShape_of_small.{w} C (CostructuredArrow P.ι X)
  have := (coproductIsCoproduct (P.coproductFromFamily X)).whiskerEquivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm
  refine ⟨_, fun j ↦ ((equivShrink.{w} (CostructuredArrow P.ι X)).symm j).left.1,
    fun j ↦ ((equivShrink.{w} _).symm j).1.2, _,
    (coproductIsCoproduct (P.coproductFromFamily X)).whiskerEquivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm, _, hP.extremalEpi_coproductFrom X⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.IsStrongGenerator.mk_of_exists_colimitsOfShape**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrongGenerator`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.ObjectProperty C},   (∀ (X : C), ∃ J x, P.colimitsOfShape J X) → P.IsStrongGe
nerator
参数：∀ (X : C), ∃ J x, P.colimitsOfShape J X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isStrongGenerator_iff`：isStrongGenerator_i
ff : P.IsStrongGenerator ↔ P.IsSeparating ∧ forall ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i
], (forall (G : C) (_ : P G), Function.Su…
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.mk_of_exists_colimitsOfShape`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory
.ObjectProperty C},   (∀ (X : C), ∃ J x, P.colimitsOfShape J …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac_assoc`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{
v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma IsStrongGenerator.mk_of_exists_colimitsOfShape
    (hP : ∀ (X : C), ∃ (J : Type w) (_ : Category.{w'} J), P.colimitsOfShape J X) :
    P.IsStrongGenerator := by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_colimitsOfShape hP, fun X Y i _ hi ↦ ?_⟩
  suffices IsSplitEpi i by
    obtain ⟨r, fac⟩ := this
    exact ⟨r, by simp [← cancel_mono i, fac]⟩
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  choose φ hφ using fun j ↦ hi _ (p.prop_diag_obj j) (p.ι.app j)
  let c : Cocone p.diag := Cocone.mk _
    { app := φ
      naturality j₁ j₂ f := by simp [← cancel_mono i, hφ] }
  refine ⟨p.isColimit.desc c, p.isColimit.hom_ext (fun j ↦ ?_)⟩
  dsimp at hφ ⊢
  rw [p.isColimit.fac_assoc, hφ, Category.comp_id]

end ObjectProperty

end CategoryTheory

