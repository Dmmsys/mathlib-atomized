/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.NatInt

/-!
# Preadditive categories

A preadditive category is a category in which `X ⟶ Y` is an abelian group in such a way that
composition of morphisms is linear in both variables.

This file contains a definition of preadditive category that directly encodes the definition given
above. The definition could also be phrased as follows: A preadditive category is a category
enriched over the category of Abelian groups. Once the general framework to state this in Lean is
available, the contents of this file should become obsolete.

## Main results

* Definition of preadditive categories and basic properties
* In a preadditive category, `f : Q ⟶ R` is mono if and only if `g ≫ f = 0 → g = 0` for all
  composable `g`.
* A preadditive category with kernels has equalizers.

## Implementation notes

The simp normal form for negation and composition is to push negations as far as possible to
the outside. For example, `f ≫ (-g)` and `(-f) ≫ g` both become `-(f ≫ g)`, and `(-f) ≫ (-g)`
is simplified to `f ≫ g`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

## Tags

additive, preadditive, Hom group, Ab-category, Ab-enriched
-/

@[expose] public section


universe v u

open CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
linear in both variables. -/
@[stacks 00ZY]
/-
**CategoryTheory.Preadditive** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：Preadditive where homGroup : forall P Q : C, AddCommGroup (P ⟶ Q)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is called preadditive if `P ⟶ Q` is an abelian group such that compos
ition is
linear in both variables.
-/
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g := by
    cat_disch
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g' := by
    cat_disch

attribute [inherit_doc Preadditive] Preadditive.homGroup Preadditive.add_comp Preadditive.comp_add

attribute [instance_reducible, instance] Preadditive.homGroup

-- simp can already prove reassoc version
attribute [reassoc, simp] Preadditive.add_comp

attribute [reassoc] Preadditive.comp_add

attribute [simp] Preadditive.comp_add

end CategoryTheory

open CategoryTheory

namespace CategoryTheory

namespace Preadditive

section Preadditive

open AddMonoidHom

variable {C : Type u} [Category.{v} C] [Preadditive C]

section InducedCategory

universe u'

variable {D : Type u'} (F : D → C)

/-
**CategoryTheory.Preadditive.inducedCategory** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Preadditive`。
形式化陈述：inducedCategory : Preadditive.{v} (InducedCategory C F) where homGroup P Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inducedCategory : Preadditive.{v} (InducedCategory C F) where
  homGroup P Q := InducedCategory.homEquiv.addCommGroup
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add

variable {F} in
/-- The additive equivalence `(X ⟶ Y) ≃+ (F X ⟶ F Y)` when `F : D → C` and
`C` is a preadditive category. -/
@[simps!]
/-
**CategoryTheory.Preadditive._root_.CategoryTheory.InducedCategory.homAddEquiv**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Preadditive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `(X ⟶ Y) ≃+ (F X ⟶ F Y)` when `F : D → C` and
`C` is a preadditive category.
-/
def _root_.CategoryTheory.InducedCategory.homAddEquiv
    {X Y : InducedCategory C F} :
    (X ⟶ Y) ≃+ (F X ⟶ F Y) where
  toEquiv := InducedCategory.homEquiv
  map_add' := by aesop_cat

end InducedCategory

/-
**CategoryTheory.Preadditive.fullSubcategory** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Preadditive`。
形式化陈述：fullSubcategory (Z : ObjectProperty C) : Preadditive Z.FullSubcategory whe
re homGroup P Q
参数：Z : ObjectProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fullSubcategory (Z : ObjectProperty C) : Preadditive Z.FullSubcategory where
  homGroup P Q := {
      -- Note: Add zero field explicitly for a better transparency of definitional properties
      zero := Z.homMk 0
      __ := InducedCategory.homEquiv.addCommGroup }
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : AddCommGroup (End X) :=
  inferInstanceAs <| AddCommGroup (X ⟶ X)

/-- Composition by a fixed left argument as a group homomorphism -/
/-
**CategoryTheory.Preadditive.leftComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Preadditive`。
形式化陈述：leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) ->+ (P ⟶ R)
参数：R : C；f : P ⟶ Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition by a fixed left argument as a group homomorphism
-/
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp

/-- Composition by a fixed right argument as a group homomorphism -/
/-
**CategoryTheory.Preadditive.rightComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Preadditive`。
形式化陈述：rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) ->+ (P ⟶ R)
参数：P : C；g : Q ⟶ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition by a fixed right argument as a group homomorphism
-/
def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  mk' (fun f => f ≫ g) fun f f' => by simp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

/-- Composition as a bilinear group homomorphism -/
/-
**CategoryTheory.Preadditive.compHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
readditive`。
形式化陈述：compHom : (P ⟶ Q) ->+ (Q ⟶ R) ->+ (P ⟶ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition as a bilinear group homomorphism
-/
def compHom : (P ⟶ Q) →+ (Q ⟶ R) →+ (P ⟶ R) :=
  AddMonoidHom.mk' (fun f => leftComp _ f) fun f₁ f₂ =>
    AddMonoidHom.ext fun g => (rightComp _ g).map_add f₁ f₂

-- simp can prove the reassoc version
@[reassoc, simp]
/-
**CategoryTheory.Preadditive.sub_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Preadditive`。
形式化陈述：sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'

-- simp can prove the reassoc version
@[reassoc, simp]
/-
**CategoryTheory.Preadditive.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Preadditive`。
形式化陈述：comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (leftComp R f) g g'

-- simp can prove the reassoc version
@[reassoc, simp]
/-
**CategoryTheory.Preadditive.neg_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Preadditive`。
形式化陈述：neg_comp : (-f) ≫ g = -f ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f

-- simp can prove the reassoc version
@[reassoc, simp]
/-
**CategoryTheory.Preadditive.comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Preadditive`。
形式化陈述：comp_neg : f ≫ (-g) = -f ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem comp_neg : f ≫ (-g) = -f ≫ g :=
  map_neg (leftComp R f) g

@[reassoc]
/-
**CategoryTheory.Preadditive.neg_comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Preadditive`。
形式化陈述：neg_comp_neg : (-f) ≫ (-g) = f ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_comp_neg : (-f) ≫ (-g) = f ≫ g := by simp
/-
**CategoryTheory.Preadditive.nsmul_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Preadditive`。
形式化陈述：nsmul_comp (n : Nat) : (n • f) ≫ g = n • f ≫ g
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem nsmul_comp (n : ℕ) : (n • f) ≫ g = n • f ≫ g :=
  map_nsmul (rightComp P g) n f
/-
**CategoryTheory.Preadditive.comp_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Preadditive`。
形式化陈述：comp_nsmul (n : Nat) : f ≫ (n • g) = n • f ≫ g
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem comp_nsmul (n : ℕ) : f ≫ (n • g) = n • f ≫ g :=
  map_nsmul (leftComp R f) n g
/-
**CategoryTheory.Preadditive.zsmul_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Preadditive`。
形式化陈述：zsmul_comp (n : Int) : (n • f) ≫ g = n • f ≫ g
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem zsmul_comp (n : ℤ) : (n • f) ≫ g = n • f ≫ g :=
  map_zsmul (rightComp P g) n f
/-
**CategoryTheory.Preadditive.comp_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Preadditive`。
形式化陈述：comp_zsmul (n : Int) : f ≫ (n • g) = n • f ≫ g
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem comp_zsmul (n : ℤ) : f ≫ (n • g) = n • f ≫ g :=
  map_zsmul (leftComp R f) n g

@[reassoc]
/-
**CategoryTheory.Preadditive.comp_sum** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Preadditive`。
形式化陈述：comp_sum {P Q R : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶
 R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f ≫ g j
参数：s : Finset J；f : P ⟶ Q；g : J -> (Q ⟶ R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem comp_sum {P Q R : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
    (f ≫ ∑ j ∈ s, g j) = ∑ j ∈ s, f ≫ g j :=
  map_sum (leftComp R f) _ _

@[reassoc]
/-
**CategoryTheory.Preadditive.sum_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Preadditive`。
形式化陈述：sum_comp {P Q R : C} {J : Type*} (s : Finset J) (f : J -> (P ⟶ Q)) (g : Q 
⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f j ≫ g
参数：s : Finset J；f : J -> (P ⟶ Q)；g : Q ⟶ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem sum_comp {P Q R : C} {J : Type*} (s : Finset J) (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
    (∑ j ∈ s, f j) ≫ g = ∑ j ∈ s, f j ≫ g :=
  map_sum (rightComp P g) _ _

@[reassoc]
/-
**CategoryTheory.Preadditive.sum_comp'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Preadditive`。
形式化陈述：sum_comp' {P Q R S : C} {J : Type*} (s : Finset J) (f : J -> (P ⟶ Q)) (g :
 J -> (Q ⟶ R)) (h : R ⟶ S) : (∑ j in s, f j ≫ g j) ≫ h = ∑ j in s, f j ≫ g j ≫ h
参数：s : Finset J；f : J -> (P ⟶ Q)；g : J -> (Q ⟶ R)；h : R ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
-/
theorem sum_comp' {P Q R S : C} {J : Type*} (s : Finset J) (f : J → (P ⟶ Q)) (g : J → (Q ⟶ R))
    (h : R ⟶ S) : (∑ j ∈ s, f j ≫ g j) ≫ h = ∑ j ∈ s, f j ≫ g j ≫ h := by
  simp only [← Category.assoc]
  apply sum_comp
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : C} {f : P ⟶ Q} [Epi f] : Epi (-f) :=
  ⟨fun g g' H => by rwa [neg_comp, neg_comp, ← comp_neg, ← comp_neg, cancel_epi, neg_inj] at H⟩
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P Q : C} {f : P ⟶ Q} [Mono f] : Mono (-f) :=
  ⟨fun g g' H => by rwa [comp_neg, comp_neg, ← neg_comp, ← neg_comp, cancel_mono, neg_inj] at H⟩
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  zero := inferInstance
  comp_zero f R := show leftComp R f 0 = 0 from map_zero _
  zero_comp P _ _ f := show rightComp P f 0 = 0 from map_zero _

/-- This instance is split off from the `Ring (End X)` instance to speed up instance search. -/
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is split off from the `Ring (End X)` instance to speed up instance
 search.
-/
instance {X : C} : Semiring (End X) :=
  { End.monoid with
    zero_mul := fun f => by dsimp [mul]; exact HasZeroMorphisms.comp_zero f _
    mul_zero := fun f => by dsimp [mul]; exact HasZeroMorphisms.zero_comp _ f
    left_distrib := fun f g h => Preadditive.add_comp X X X g h f
    right_distrib := fun f g h => Preadditive.comp_add X X X h f g }
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : Ring (End X) :=
  { (inferInstance : Semiring (End X)),
    (inferInstance : AddCommGroup (End X)) with
    neg_add_cancel := neg_add_cancel }
/-
**CategoryTheory.Preadditive.moduleEndRight** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Preadditive`。
形式化陈述：moduleEndRight {X Y : C} : Module (End Y) (X ⟶ Y) where smul_add _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
-/
instance moduleEndRight {X Y : C} : Module (End Y) (X ⟶ Y) where
  smul_add _ _ _ := add_comp _ _ _ _ _ _
  smul_zero _ := zero_comp
  add_smul _ _ _ := comp_add _ _ _ _ _ _
  zero_smul _ := comp_zero
/-
**CategoryTheory.Preadditive.mono_of_cancel_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Preadditive`。
形式化陈述：mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q),
 g ≫ f = 0 -> g = 0) : Mono f where right_cancellation
参数：f : Q ⟶ R；h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : ∀ {P : C} (g : P ⟶ Q), g ≫ f = 0 → g = 0) :
    Mono f where
  right_cancellation := fun {Z} g₁ g₂ hg =>
    sub_eq_zero.1 <| h _ <| (map_sub (rightComp Z f) g₁ g₂).trans <| sub_eq_zero.2 hg
/-
**CategoryTheory.Preadditive.mono_iff_cancel_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Preadditive`。
形式化陈述：mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) : Mono f ↔ forall (P : C) (g : 
P ⟶ Q), g ≫ f = 0 -> g = 0
参数：f : Q ⟶ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_comp_mono`：zero_of_comp_mono {X Y Z : C} {
f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0) : f = 0
· 使用定理 `CategoryTheory.Preadditive.mono_of_cancel_zero`：mono_of_cancel_zero {Q R
 : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0) : Mono f 
where right_cancellation
-/
theorem mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) :
    Mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
  ⟨fun _ _ _ => zero_of_comp_mono _, mono_of_cancel_zero f⟩
/-
**CategoryTheory.Preadditive.mono_of_kernel_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Preadditive`。
形式化陈述：mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)] (w
 : kernel.ι f = 0) : Mono f
参数：parallelPair f 0；w : kernel.ι f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.mono_of_cancel_zero`：mono_of_cancel_zero {Q R
 : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0) : Mono f 
where right_cancellation
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
    (w : kernel.ι f = 0) : Mono f :=
  mono_of_cancel_zero f fun g h => by rw [← kernel.lift_ι f g h, w, Limits.comp_zero]
/-
**CategoryTheory.Preadditive.mono_of_isZero_kernel'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Preadditive`。
形式化陈述：mono_of_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLi
mit c) (h : IsZero c.pt) : Mono f
参数：c : KernelFork f；hc : IsLimit c；h : IsZero c.pt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.mono_of_cancel_zero`：mono_of_cancel_zero {Q R
 : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0) : Mono f 
where right_cancellation
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma mono_of_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c)
    (h : IsZero c.pt) : Mono f := mono_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hc _ hg
  rw [← ha, h.eq_of_tgt a 0, Limits.zero_comp])
/-
**CategoryTheory.Preadditive.mono_iff_isZero_kernel'** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Preadditive`。
形式化陈述：mono_iff_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsL
imit c) : Mono f ↔ IsZero c.pt
参数：c : KernelFork f；hc : IsLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.KernelFork.IsLimit.isZero_of_mono`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {X Y : C}   {f : X ⟶ Y} {c : Ca…
· 使用引理 `CategoryTheory.Preadditive.mono_of_isZero_kernel'`：mono_of_isZero_kernel
' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c) (h : IsZero c.pt) : 
Mono f
-/
lemma mono_iff_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c) :
    Mono f ↔ IsZero c.pt :=
  ⟨fun _ ↦ KernelFork.IsLimit.isZero_of_mono hc, mono_of_isZero_kernel' c hc⟩
/-
**CategoryTheory.Preadditive.mono_of_isZero_kernel** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Preadditive`。
形式化陈述：mono_of_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : IsZero (ker
nel f)) : Mono f
参数：f : X ⟶ Y；h : IsZero (kernel f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Preadditive.mono_of_isZero_kernel'`：mono_of_isZero_kernel
' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c) (h : IsZero c.pt) : 
Mono f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma mono_of_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : IsZero (kernel f)) :
    Mono f :=
  mono_of_isZero_kernel' _ (kernelIsKernel _) h
/-
**CategoryTheory.Preadditive.mono_iff_isZero_kernel** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Preadditive`。
形式化陈述：mono_iff_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] : Mono f ↔ IsZe
ro (kernel f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Preadditive.mono_iff_isZero_kernel'`：mono_iff_isZero_kern
el' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c) : Mono f ↔ IsZero 
c.pt
-/
lemma mono_iff_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    Mono f ↔ IsZero (kernel f) :=
  mono_iff_isZero_kernel' _ (limit.isLimit _)
/-
**CategoryTheory.Preadditive.epi_of_cancel_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Preadditive`。
形式化陈述：epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), 
f ≫ g = 0 -> g = 0) : Epi f
参数：f : P ⟶ Q；h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : ∀ {R : C} (g : Q ⟶ R), f ≫ g = 0 → g = 0) :
    Epi f :=
  ⟨fun {Z} g g' hg =>
    sub_eq_zero.1 <| h _ <| (map_sub (leftComp Z f) g g').trans <| sub_eq_zero.2 hg⟩
/-
**CategoryTheory.Preadditive.epi_iff_cancel_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Preadditive`。
形式化陈述：epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) : Epi f ↔ forall (R : C) (g : Q 
⟶ R), f ≫ g = 0 -> g = 0
参数：f : P ⟶ Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_epi_comp`：zero_of_epi_comp {X Y Z : C} (f 
: X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0
· 使用定理 `CategoryTheory.Preadditive.epi_of_cancel_zero`：epi_of_cancel_zero {P Q :
 C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0) : Epi f
-/
theorem epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) :
    Epi f ↔ ∀ (R : C) (g : Q ⟶ R), f ≫ g = 0 → g = 0 :=
  ⟨fun _ _ _ => zero_of_epi_comp _, epi_of_cancel_zero f⟩
/-
**CategoryTheory.Preadditive.epi_of_cokernel_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Preadditive`。
形式化陈述：epi_of_cokernel_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)]
 (w : cokernel.π f = 0) : Epi f
参数：parallelPair f 0；w : cokernel.π f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.epi_of_cancel_zero`：epi_of_cancel_zero {P Q :
 C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0) : Epi f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
theorem epi_of_cokernel_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)]
    (w : cokernel.π f = 0) : Epi f :=
  epi_of_cancel_zero f fun g h => by rw [← cokernel.π_desc f g h, w, Limits.zero_comp]
/-
**CategoryTheory.Preadditive.epi_of_isZero_cokernel'** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Preadditive`。
形式化陈述：epi_of_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc :
 IsColimit c) (h : IsZero c.pt) : Epi f
参数：c : CokernelCofork f；hc : IsColimit c；h : IsZero c.pt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.epi_of_cancel_zero`：epi_of_cancel_zero {P Q :
 C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0) : Epi f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma epi_of_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c)
    (h : IsZero c.pt) : Epi f := epi_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hc _ hg
  rw [← ha, h.eq_of_src a 0, Limits.comp_zero])
/-
**CategoryTheory.Preadditive.epi_iff_isZero_cokernel'** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Preadditive`。
形式化陈述：epi_iff_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc 
: IsColimit c) : Epi f ↔ IsZero c.pt
参数：c : CokernelCofork f；hc : IsColimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CokernelCofork.IsColimit.isZero_of_epi`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C] {X Y : C}   {f : X ⟶ Y} {c : Ca…
· 使用引理 `CategoryTheory.Preadditive.epi_of_isZero_cokernel'`：epi_of_isZero_cokern
el' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c) (h : IsZero 
c.pt) : Epi f
-/
lemma epi_iff_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c) :
    Epi f ↔ IsZero c.pt :=
  ⟨fun _ ↦ CokernelCofork.IsColimit.isZero_of_epi hc, epi_of_isZero_cokernel' c hc⟩
/-
**CategoryTheory.Preadditive.epi_of_isZero_cokernel** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Preadditive`。
形式化陈述：epi_of_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] (h : IsZero (
cokernel f)) : Epi f
参数：f : X ⟶ Y；h : IsZero (cokernel f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Preadditive.epi_of_isZero_cokernel'`：epi_of_isZero_cokern
el' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c) (h : IsZero 
c.pt) : Epi f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma epi_of_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] (h : IsZero (cokernel f)) :
    Epi f :=
  epi_of_isZero_cokernel' _ (cokernelIsCokernel _) h
/-
**CategoryTheory.Preadditive.epi_iff_isZero_cokernel** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Preadditive`。
形式化陈述：epi_iff_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] : Epi f ↔ Is
Zero (cokernel f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Preadditive.epi_iff_isZero_cokernel'`：epi_iff_isZero_coke
rnel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c) : Epi f ↔ 
IsZero c.pt
-/
lemma epi_iff_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] :
    Epi f ↔ IsZero (cokernel f) :=
  epi_iff_isZero_cokernel' _ (colimit.isColimit _)

namespace IsIso

@[simp]
/-
**CategoryTheory.Preadditive.IsIso.comp_left_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Preadditive.IsIso`。
形式化陈述：comp_left_eq_zero [IsIso f] : f ≫ g = 0 ↔ g = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comp_left_eq_zero [IsIso f] : f ≫ g = 0 ↔ g = 0 := by
  rw [← IsIso.eq_inv_comp, Limits.comp_zero]

@[simp]
/-
**CategoryTheory.Preadditive.IsIso.comp_right_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Preadditive.IsIso`。
形式化陈述：comp_right_eq_zero [IsIso g] : f ≫ g = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comp_right_eq_zero [IsIso g] : f ≫ g = 0 ↔ f = 0 := by
  rw [← IsIso.eq_comp_inv, Limits.zero_comp]

end IsIso

open ZeroObject

variable [HasZeroObject C]

/-
**CategoryTheory.Preadditive.mono_of_kernel_iso_zero** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Preadditive`。
形式化陈述：mono_of_kernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)
] (w : kernel f ≅ 0) : Mono f
参数：parallelPair f 0；w : kernel f ≅ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.mono_of_kernel_zero`：mono_of_kernel_zero {X Y
 : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)] (w : kernel.ι f = 0) : Mono f
· 使用定理 `CategoryTheory.Limits.zero_of_source_iso_zero`：zero_of_source_iso_zero {
X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0
-/
theorem mono_of_kernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
    (w : kernel f ≅ 0) : Mono f :=
  mono_of_kernel_zero (zero_of_source_iso_zero _ w)
/-
**CategoryTheory.Preadditive.epi_of_cokernel_iso_zero** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Preadditive`。
形式化陈述：epi_of_cokernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f
 0)] (w : cokernel f ≅ 0) : Epi f
参数：parallelPair f 0；w : cokernel f ≅ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.epi_of_cokernel_zero`：epi_of_cokernel_zero {X
 Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)] (w : cokernel.π f = 0) : Epi
 f
· 使用定理 `CategoryTheory.Limits.zero_of_target_iso_zero`：zero_of_target_iso_zero {
X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0
-/
theorem epi_of_cokernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)]
    (w : cokernel f ≅ 0) : Epi f :=
  epi_of_cokernel_zero (zero_of_target_iso_zero _ w)

end Preadditive

section Equalizers

variable {C : Type u} [Category.{v} C] [Preadditive C]

section

variable {X Y : C} {f : X ⟶ Y} {g : X ⟶ Y}

/-- Map a kernel cone on the difference of two morphisms to the equalizer fork. -/
@[simps! pt]
/-
**CategoryTheory.forkOfKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a kernel cone on the difference of two morphisms to the equalizer fork.
-/
def forkOfKernelFork (c : KernelFork (f - g)) : Fork f g :=
  Fork.ofι c.ι <| by rw [← sub_eq_zero, ← comp_sub, c.condition]

@[simp]
/-
**CategoryTheory.forkOfKernelFork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forkOfKernelFork_ι (c : KernelFork (f - g)) : (forkOfKernelFork c).ι = c.ι :=
  rfl

/-- Map any equalizer fork to a cone on the difference of the two morphisms. -/
/-
**CategoryTheory.kernelForkOfFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map any equalizer fork to a cone on the difference of the two morphisms.
-/
def kernelForkOfFork (c : Fork f g) : KernelFork (f - g) :=
  Fork.ofι c.ι <| by rw [comp_sub, comp_zero, sub_eq_zero, c.condition]

@[simp]
/-
**CategoryTheory.kernelForkOfFork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelForkOfFork_ι (c : Fork f g) : (kernelForkOfFork c).ι = c.ι :=
  rfl

@[simp]
/-
**CategoryTheory.kernelForkOfFork_of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernelForkOfFork_ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
    kernelForkOfFork (Fork.ofι ι w) = KernelFork.ofι ι (by simp [w]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
/-
**CategoryTheory.isLimitForkOfKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel of `f - g` is an equalizer of `f` and `g`.
-/
def isLimitForkOfKernelFork {c : KernelFork (f - g)} (i : IsLimit c) :
    IsLimit (forkOfKernelFork c) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (kernelForkOfFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

@[simp]
/-
**CategoryTheory.isLimitForkOfKernelFork_lift** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLimitForkOfKernelFork_lift {c : KernelFork (f - g)} (i : IsLimit c) (s : Fork f g) :
    (isLimitForkOfKernelFork i).lift s = i.lift (kernelForkOfFork s) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- An equalizer of `f` and `g` is a kernel of `f - g`. -/
/-
**CategoryTheory.isLimitKernelForkOfFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equalizer of `f` and `g` is a kernel of `f - g`.
-/
def isLimitKernelForkOfFork {c : Fork f g} (i : IsLimit c) : IsLimit (kernelForkOfFork c) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (forkOfKernelFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

variable (f g)

/-- A preadditive category has an equalizer for `f` and `g` if it has a kernel for `f - g`. -/
/-
**CategoryTheory.hasEqualizer_of_hasKernel** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preadditive category has an equalizer for `f` and `g` if it has a kernel for `
f - g`.
-/
theorem hasEqualizer_of_hasKernel [HasKernel (f - g)] : HasEqualizer f g :=
  HasLimit.mk
    { cone := forkOfKernelFork _
      isLimit := isLimitForkOfKernelFork (equalizerIsEqualizer (f - g) 0) }

/-- A preadditive category has a kernel for `f - g` if it has an equalizer for `f` and `g`. -/
/-
**CategoryTheory.hasKernel_of_hasEqualizer** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preadditive category has a kernel for `f - g` if it has an equalizer for `f` a
nd `g`.
-/
theorem hasKernel_of_hasEqualizer [HasEqualizer f g] : HasKernel (f - g) :=
  HasLimit.mk
    { cone := kernelForkOfFork (equalizer.fork f g)
      isLimit := isLimitKernelForkOfFork (limit.isLimit (parallelPair f g)) }

variable {f g}

/-- Map a cokernel cocone on the difference of two morphisms to the coequalizer cofork. -/
@[simps! pt]
/-
**CategoryTheory.coforkOfCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a cokernel cocone on the difference of two morphisms to the coequalizer cofo
rk.
-/
def coforkOfCokernelCofork (c : CokernelCofork (f - g)) : Cofork f g :=
  Cofork.ofπ c.π <| by rw [← sub_eq_zero, ← sub_comp, c.condition]

@[simp]
/-
**CategoryTheory.coforkOfCokernelCofork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coforkOfCokernelCofork_π (c : CokernelCofork (f - g)) :
    (coforkOfCokernelCofork c).π = c.π :=
  rfl

/-- Map any coequalizer cofork to a cocone on the difference of the two morphisms. -/
/-
**CategoryTheory.cokernelCoforkOfCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map any coequalizer cofork to a cocone on the difference of the two morphisms.
-/
def cokernelCoforkOfCofork (c : Cofork f g) : CokernelCofork (f - g) :=
  Cofork.ofπ c.π <| by rw [sub_comp, zero_comp, sub_eq_zero, c.condition]

@[simp]
/-
**CategoryTheory.cokernelCoforkOfCofork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cokernelCoforkOfCofork_π (c : Cofork f g) : (cokernelCoforkOfCofork c).π = c.π :=
  rfl

@[simp]
/-
**CategoryTheory.cokernelCoforkOfCofork_of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cokernelCoforkOfCofork_ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
    cokernelCoforkOfCofork (Cofork.ofπ π w) = CokernelCofork.ofπ π (by simp [w]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
/-
**CategoryTheory.isColimitCoforkOfCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cokernel of `f - g` is a coequalizer of `f` and `g`.
-/
def isColimitCoforkOfCokernelCofork {c : CokernelCofork (f - g)} (i : IsColimit c) :
    IsColimit (coforkOfCokernelCofork c) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (cokernelCoforkOfCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; cat_disch⟩

@[simp]
/-
**CategoryTheory.isColimitCoforkOfCokernelCofork_desc** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isColimitCoforkOfCokernelCofork_desc {c : CokernelCofork (f - g)} (i : IsColimit c)
    (s : Cofork f g) :
    (isColimitCoforkOfCokernelCofork i).desc s = i.desc (cokernelCoforkOfCofork s) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A coequalizer of `f` and `g` is a cokernel of `f - g`. -/
/-
**CategoryTheory.isColimitCokernelCoforkOfCofork** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coequalizer of `f` and `g` is a cokernel of `f - g`.
-/
def isColimitCokernelCoforkOfCofork {c : Cofork f g} (i : IsColimit c) :
    IsColimit (cokernelCoforkOfCofork c) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (coforkOfCokernelCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; cat_disch⟩

variable (f g)

/-- A preadditive category has a coequalizer for `f` and `g` if it has a cokernel for `f - g`. -/
/-
**CategoryTheory.hasCoequalizer_of_hasCokernel** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preadditive category has a coequalizer for `f` and `g` if it has a cokernel fo
r `f - g`.
-/
theorem hasCoequalizer_of_hasCokernel [HasCokernel (f - g)] : HasCoequalizer f g :=
  HasColimit.mk
    { cocone := coforkOfCokernelCofork _
      isColimit := isColimitCoforkOfCokernelCofork (coequalizerIsCoequalizer (f - g) 0) }

/-- A preadditive category has a cokernel for `f - g` if it has a coequalizer for `f` and `g`. -/
/-
**CategoryTheory.hasCokernel_of_hasCoequalizer** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preadditive category has a cokernel for `f - g` if it has a coequalizer for `f
` and `g`.
-/
theorem hasCokernel_of_hasCoequalizer [HasCoequalizer f g] : HasCokernel (f - g) :=
  HasColimit.mk
    { cocone := cokernelCoforkOfCofork (coequalizer.cofork f g)
      isColimit := isColimitCokernelCoforkOfCofork (colimit.isColimit (parallelPair f g)) }

end

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
/-
**CategoryTheory.hasEqualizers_of_hasKernels** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a preadditive category has all kernels, then it also has all equalizers.
-/
theorem hasEqualizers_of_hasKernels [HasKernels C] : HasEqualizers C :=
  @hasEqualizers_of_hasLimit_parallelPair _ _ fun {_} {_} f g => hasEqualizer_of_hasKernel f g

/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
/-
**CategoryTheory.hasCoequalizers_of_hasCokernels** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a preadditive category has all cokernels, then it also has all coequalizers.
-/
theorem hasCoequalizers_of_hasCokernels [HasCokernels C] : HasCoequalizers C :=
  @hasCoequalizers_of_hasColimit_parallelPair _ _ fun {_} {_} f g =>
    hasCoequalizer_of_hasCokernel f g

end Equalizers

section

variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (Units ℤ) (X ≅ Y) where
  smul a e :=
    { hom := (a : ℤ) • e.hom
      inv := ((a⁻¹ : Units ℤ) : ℤ) • e.inv
      hom_inv_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.inv_mul, one_smul, e.hom_inv_id]
      inv_hom_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.mul_inv, one_smul, e.inv_hom_id] }

@[simp]
/-
**CategoryTheory.smul_iso_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_iso_hom (a : Units ℤ) (e : X ≅ Y) : (a • e).hom = a • e.hom := rfl

@[simp]
/-
**CategoryTheory.smul_iso_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_iso_inv (a : Units ℤ) (e : X ≅ Y) : (a • e).inv = a⁻¹ • e.inv := rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (X ≅ Y) where
  neg e :=
    { hom := -e.hom
      inv := -e.inv }

@[simp]
/-
**CategoryTheory.neg_iso_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_iso_hom (e : X ≅ Y) : (-e).hom = -e.hom := rfl

@[simp]
/-
**CategoryTheory.neg_iso_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_iso_inv (e : X ≅ Y) : (-e).inv = -e.inv := rfl

end

end Preadditive

end CategoryTheory

