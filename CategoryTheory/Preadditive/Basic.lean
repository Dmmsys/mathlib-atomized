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
/--
Definition of `Preadditive` / `Preadditive` 的定义

English:
class Preadditive
  parameters: where
  axioms and operations (3):
    - homGroup : forall P Q : C, AddCommGroup (P ⟶ Q)  [default: by infer_instance]
    - add_comp : forall (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g  [default: by cat_disch]
    - comp_add : forall (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'  [default: by cat_disch]

中文:
类 预加性
  参数: where
  公理与运算 (3 个):
    - homGroup : 对任意 P Q : C, 加法交换群 (P ⟶ Q)  [默认: by infer_instance]
    - add_comp : 对任意 (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g  [默认: by cat_disch]
    - comp_add : 对任意 (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'  [默认: by cat_disch]

Depends on / 依赖: add_comp, cat_disch, comp_add, infer_instance
-/
class Preadditive where
  homGroup : forall P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : forall (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g := by
    cat_disch
  comp_add : forall (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g' := by
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

variable {D : Type u'} (F : D -> C)

/--
Instance `inducedCategory` / 实例 `inducedCategory`

English:
instance inducedCategory
  signature: : Preadditive.{v} (InducedCategory C F) where
  body: InducedCategory.homEquiv.addCommGroup
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add

中文:
实例 inducedCategory
  签名: : 预加性.{v} (InducedCategory C F) where
  定义体: InducedCategory.homEquiv.addCommGroup
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add

Depends on / 依赖: InducedCategory, InducedCategory.homEquiv.addCommGroup, addCommGroup, homEquiv
-/
instance inducedCategory : Preadditive.{v} (InducedCategory C F) where
  homGroup P Q := InducedCategory.homEquiv.addCommGroup
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add

variable {F} in
/-- The additive equivalence `(X ⟶ Y) ≃+ (F X ⟶ F Y)` when `F : D → C` and
`C` is a preadditive category. -/
@[simps!]
/--
Definition of `_root_.CategoryTheory.InducedCategory.homAddEquiv` / `_root_.CategoryTheory.InducedCategory.homAddEquiv` 的定义

English:
definition _root_.CategoryTheory.InducedCategory.homAddEquiv
  body: InducedCategory.homEquiv
  map_add' := by aesop_cat

中文:
定义 _root_.范畴论.InducedCategory.homAddEquiv
  定义体: InducedCategory.homEquiv
  map_add' := by aesop_cat

Depends on / 依赖: InducedCategory, InducedCategory.homEquiv, homEquiv
-/
def _root_.CategoryTheory.InducedCategory.homAddEquiv
    {X Y : InducedCategory C F} :
    (X ⟶ Y) ≃+ (F X ⟶ F Y) where
  toEquiv := InducedCategory.homEquiv
  map_add' := by aesop_cat

end InducedCategory

/--
Instance `fullSubcategory` / 实例 `fullSubcategory`

English:
instance fullSubcategory
  signature: (Z : ObjectProperty C)
  body: {
      -- Note: Add zero field explicitly for a better transparency of definitional properties
      zero := Z.homMk 0
      __ := InducedCategory.homEquiv.addCommGroup }
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add

中文:
实例 fullSubcategory
  签名: (Z : ObjectProperty C)
  定义体: {
      -- Note: Add zero field explicitly for a better transparency of definitional properties
      zero := Z.homMk 0
      __ := InducedCategory.homEquiv.addCommGroup }
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add
-/
instance fullSubcategory (Z : ObjectProperty C) : Preadditive Z.FullSubcategory where
  homGroup P Q := {
      -- Note: Add zero field explicitly for a better transparency of definitional properties
      zero := Z.homMk 0
      __ := InducedCategory.homEquiv.addCommGroup }
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add

instance (X : C) : AddCommGroup (End X) :=
inferInstanceAs AddCommGroup (X ⟶ X)

/--
Definition of `leftComp` / `leftComp` 的定义

English:
definition leftComp
  signature: {P Q : C} (R : C) (f : P ⟶ Q)
  body: mk' (fun g => f ≫ g) fun g g' => by simp

中文:
定义 leftComp
  签名: {P Q : C} (R : C) (f : P ⟶ Q)
  定义体: mk' (fun g => f ≫ g) fun g g' => by simp
-/
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) ->+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp

/--
Definition of `rightComp` / `rightComp` 的定义

English:
definition rightComp
  signature: (P : C) {Q R : C} (g : Q ⟶ R)
  body: mk' (fun f => f ≫ g) fun f f' => by simp

中文:
定义 rightComp
  签名: (P : C) {Q R : C} (g : Q ⟶ R)
  定义体: mk' (fun f => f ≫ g) fun f f' => by simp
-/
def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) ->+ (P ⟶ R) :=
  mk' (fun f => f ≫ g) fun f f' => by simp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

/--
Definition of `compHom` / `compHom` 的定义

English:
definition compHom
  signature: : (P ⟶ Q) ->+ (Q ⟶ R) ->+ (P ⟶ R)
  body: AddMonoidHom.mk' (fun f => leftComp _ f) fun f₁ f₂ =>
    AddMonoidHom.ext fun g => (rightComp _ g).map_add f₁ f₂

中文:
定义 compHom
  签名: : (P ⟶ Q) ->+ (Q ⟶ R) ->+ (P ⟶ R)
  定义体: AddMonoidHom.mk' (fun f => leftComp _ f) fun f₁ f₂ =>
    AddMonoidHom.ext fun g => (rightComp _ g).map_add f₁ f₂

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, AddMonoidHom.mk, leftComp, map_add, rightComp
-/
def compHom : (P ⟶ Q) ->+ (Q ⟶ R) ->+ (P ⟶ R) :=
  AddMonoidHom.mk' (fun f => leftComp _ f) fun f₁ f₂ =>
    AddMonoidHom.ext fun g => (rightComp _ g).map_add f₁ f₂

-- simp can prove the reassoc version
@[reassoc, simp]
/--
theorem `sub_comp` / 定理 `sub_comp`

English:
theorem sub_comp
  statement: (f - f') ≫ g = f ≫ g - f' ≫ g
  proof: map_sub (rightComp P g) f f'

中文:
定理 sub_comp
  结论: (f - f') ≫ g = f ≫ g - f' ≫ g
  证明: map_sub (rightComp P g) f f'

Depends on / 依赖: map_sub, rightComp
-/
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'

-- simp can prove the reassoc version
@[reassoc, simp]
/--
theorem `comp_sub` / 定理 `comp_sub`

English:
theorem comp_sub
  statement: f ≫ (g - g') = f ≫ g - f ≫ g'
  proof: map_sub (leftComp R f) g g'

中文:
定理 comp_sub
  结论: f ≫ (g - g') = f ≫ g - f ≫ g'
  证明: map_sub (leftComp R f) g g'

Depends on / 依赖: leftComp, map_sub
-/
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (leftComp R f) g g'

-- simp can prove the reassoc version
@[reassoc, simp]
/--
theorem `neg_comp` / 定理 `neg_comp`

English:
theorem neg_comp
  statement: (-f) ≫ g = -f ≫ g
  proof: map_neg (rightComp P g) f

中文:
定理 neg_comp
  结论: (-f) ≫ g = -f ≫ g
  证明: map_neg (rightComp P g) f

Depends on / 依赖: map_neg, rightComp
-/
theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f

-- simp can prove the reassoc version
@[reassoc, simp]
/--
theorem `comp_neg` / 定理 `comp_neg`

English:
theorem comp_neg
  statement: f ≫ (-g) = -f ≫ g
  proof: map_neg (leftComp R f) g

@[reassoc]

中文:
定理 comp_neg
  结论: f ≫ (-g) = -f ≫ g
  证明: map_neg (leftComp R f) g

@[reassoc]

Depends on / 依赖: leftComp, map_neg
-/
theorem comp_neg : f ≫ (-g) = -f ≫ g :=
  map_neg (leftComp R f) g

@[reassoc]
/--
theorem `neg_comp_neg` / 定理 `neg_comp_neg`

English:
theorem neg_comp_neg
  statement: (-f) ≫ (-g) = f ≫ g
  proof: by simp

中文:
定理 neg_comp_neg
  结论: (-f) ≫ (-g) = f ≫ g
  证明: by simp
-/
theorem neg_comp_neg : (-f) ≫ (-g) = f ≫ g := by simp

/--
theorem `nsmul_comp` / 定理 `nsmul_comp`

English:
theorem nsmul_comp
  given: (n : Nat)
  statement: (n • f) ≫ g = n • f ≫ g
  proof: map_nsmul (rightComp P g) n f

中文:
定理 nsmul_comp
  条件: (n : 自然数)
  结论: (n • f) ≫ g = n • f ≫ g
  证明: map_nsmul (rightComp P g) n f

Depends on / 依赖: map_nsmul, rightComp
-/
theorem nsmul_comp (n : Nat) : (n • f) ≫ g = n • f ≫ g :=
  map_nsmul (rightComp P g) n f

/--
theorem `comp_nsmul` / 定理 `comp_nsmul`

English:
theorem comp_nsmul
  given: (n : Nat)
  statement: f ≫ (n • g) = n • f ≫ g
  proof: map_nsmul (leftComp R f) n g

中文:
定理 comp_nsmul
  条件: (n : 自然数)
  结论: f ≫ (n • g) = n • f ≫ g
  证明: map_nsmul (leftComp R f) n g

Depends on / 依赖: leftComp, map_nsmul
-/
theorem comp_nsmul (n : Nat) : f ≫ (n • g) = n • f ≫ g :=
  map_nsmul (leftComp R f) n g

/--
theorem `zsmul_comp` / 定理 `zsmul_comp`

English:
theorem zsmul_comp
  given: (n : Int)
  statement: (n • f) ≫ g = n • f ≫ g
  proof: map_zsmul (rightComp P g) n f

中文:
定理 zsmul_comp
  条件: (n : 整数)
  结论: (n • f) ≫ g = n • f ≫ g
  证明: map_zsmul (rightComp P g) n f

Depends on / 依赖: map_zsmul, rightComp
-/
theorem zsmul_comp (n : Int) : (n • f) ≫ g = n • f ≫ g :=
  map_zsmul (rightComp P g) n f

/--
theorem `comp_zsmul` / 定理 `comp_zsmul`

English:
theorem comp_zsmul
  given: (n : Int)
  statement: f ≫ (n • g) = n • f ≫ g
  proof: map_zsmul (leftComp R f) n g

@[reassoc]

中文:
定理 comp_zsmul
  条件: (n : 整数)
  结论: f ≫ (n • g) = n • f ≫ g
  证明: map_zsmul (leftComp R f) n g

@[reassoc]

Depends on / 依赖: leftComp, map_zsmul
-/
theorem comp_zsmul (n : Int) : f ≫ (n • g) = n • f ≫ g :=
  map_zsmul (leftComp R f) n g

@[reassoc]
/--
theorem `comp_sum` / 定理 `comp_sum`

English:
theorem comp_sum
  given: {P Q R : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R))
  proof: map_sum (leftComp R f) _ _

@[reassoc]

中文:
定理 comp_sum
  条件: {P Q R : C} {J : 类型} (s : 有限集 J) (f : P ⟶ Q) (g : J -> (Q ⟶ R))
  证明: map_sum (leftComp R f) _ _

@[reassoc]

Depends on / 依赖: leftComp, map_sum
-/
theorem comp_sum {P Q R : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) :
    (f ≫ ∑ j in s, g j) = ∑ j in s, f ≫ g j :=
  map_sum (leftComp R f) _ _

@[reassoc]
/--
theorem `sum_comp` / 定理 `sum_comp`

English:
theorem sum_comp
  given: {P Q R : C} {J : Type*} (s : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R)
  proof: map_sum (rightComp P g) _ _

@[reassoc]

中文:
定理 sum_comp
  条件: {P Q R : C} {J : 类型} (s : 有限集 J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R)
  证明: map_sum (rightComp P g) _ _

@[reassoc]

Depends on / 依赖: map_sum, rightComp
-/
theorem sum_comp {P Q R : C} {J : Type*} (s : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) :
    (∑ j in s, f j) ≫ g = ∑ j in s, f j ≫ g :=
  map_sum (rightComp P g) _ _

@[reassoc]
/--
theorem `sum_comp'` / 定理 `sum_comp'`

English:
theorem sum_comp'
  statement: {P Q R S : C} {J : Type*} (s : Finset J) (f : J -> (P ⟶ Q)) (g : J -> (Q ⟶ R))
  proof: by
  simp only [← Category.assoc]
  apply sum_comp

中文:
定理 sum_comp'
  结论: {P Q R S : C} {J : 类型} (s : 有限集 J) (f : J -> (P ⟶ Q)) (g : J -> (Q ⟶ R))
  证明: by
  simp only [← Category.assoc]
  apply sum_comp

Depends on / 依赖: Category, Category.assoc, sum_comp
-/
theorem sum_comp' {P Q R S : C} {J : Type*} (s : Finset J) (f : J -> (P ⟶ Q)) (g : J -> (Q ⟶ R))
    (h : R ⟶ S) : (∑ j in s, f j ≫ g j) ≫ h = ∑ j in s, f j ≫ g j ≫ h := by
  simp only [← Category.assoc]
  apply sum_comp

instance {P Q : C} {f : P ⟶ Q} [Epi f] : Epi (-f) :=
  ⟨fun g g' H => by rwa [neg_comp, neg_comp, ← comp_neg, ← comp_neg, cancel_epi, neg_inj] at H⟩

instance {P Q : C} {f : P ⟶ Q} [Mono f] : Mono (-f) :=
  ⟨fun g g' H => by rwa [comp_neg, comp_neg, ← neg_comp, ← neg_comp, cancel_mono, neg_inj] at H⟩

instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  zero := inferInstance
  comp_zero f R := show leftComp R f 0 = 0 from map_zero _
  zero_comp P _ _ f := show rightComp P f 0 = 0 from map_zero _

/-- This instance is split off from the `Ring (End X)` instance to speed up instance search. -/
instance {X : C} : Semiring (End X) :=
  { End.monoid with
    zero_mul := fun f => by dsimp [mul]; exact HasZeroMorphisms.comp_zero f _
    mul_zero := fun f => by dsimp [mul]; exact HasZeroMorphisms.zero_comp _ f
    left_distrib := fun f g h => Preadditive.add_comp X X X g h f
    right_distrib := fun f g h => Preadditive.comp_add X X X h f g }

instance {X : C} : Ring (End X) :=
  { (inferInstance : Semiring (End X)),
    (inferInstance : AddCommGroup (End X)) with
    neg_add_cancel := neg_add_cancel }

/--
Instance `moduleEndRight` / 实例 `moduleEndRight`

English:
instance moduleEndRight
  signature: {X Y : C}
  body: add_comp _ _ _ _ _ _
  smul_zero _ := zero_comp
  add_smul _ _ _ := comp_add _ _ _ _ _ _
  zero_smul _ := comp_zero

中文:
实例 moduleEndRight
  签名: {X Y : C}
  定义体: add_comp _ _ _ _ _ _
  smul_zero _ := zero_comp
  add_smul _ _ _ := comp_add _ _ _ _ _ _
  zero_smul _ := comp_zero

Depends on / 依赖: add_comp
-/
instance moduleEndRight {X Y : C} : Module (End Y) (X ⟶ Y) where
  smul_add _ _ _ := add_comp _ _ _ _ _ _
  smul_zero _ := zero_comp
  add_smul _ _ _ := comp_add _ _ _ _ _ _
  zero_smul _ := comp_zero

/--
theorem `mono_of_cancel_zero` / 定理 `mono_of_cancel_zero`

English:
theorem mono_of_cancel_zero
  given: {Q R : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0)
  proof: fun {Z} g₁ g₂ hg =>
sub_eq_zero.1 h _ (map_sub (rightComp Z f) g₁ g₂).trans sub_eq_zero.2 hg

中文:
定理 mono_of_cancel_zero
  条件: {Q R : C} (f : Q ⟶ R) (h : 对任意 {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0)
  证明: fun {Z} g₁ g₂ hg =>
sub_eq_zero.1 h _ (map_sub (rightComp Z f) g₁ g₂).trans sub_eq_zero.2 hg
-/
theorem mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0) :
    Mono f where
  right_cancellation := fun {Z} g₁ g₂ hg =>
sub_eq_zero.1 h _ (map_sub (rightComp Z f) g₁ g₂).trans sub_eq_zero.2 hg

/--
theorem `mono_iff_cancel_zero` / 定理 `mono_iff_cancel_zero`

English:
theorem mono_iff_cancel_zero
  given: {Q R : C} (f : Q ⟶ R)
  proof: ⟨fun _ _ _ => zero_of_comp_mono _, mono_of_cancel_zero f⟩

中文:
定理 mono_iff_cancel_zero
  条件: {Q R : C} (f : Q ⟶ R)
  证明: ⟨fun _ _ _ => zero_of_comp_mono _, mono_of_cancel_zero f⟩

Depends on / 依赖: mono_of_cancel_zero, zero_of_comp_mono
-/
theorem mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) :
    Mono f ↔ forall (P : C) (g : P ⟶ Q), g ≫ f = 0 -> g = 0 :=
  ⟨fun _ _ _ => zero_of_comp_mono _, mono_of_cancel_zero f⟩

/--
theorem `mono_of_kernel_zero` / 定理 `mono_of_kernel_zero`

English:
theorem mono_of_kernel_zero
  statement: {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
  proof: mono_of_cancel_zero f fun g h => by rw [← kernel.lift_ι f g h, w, Limits.comp_zero]

中文:
定理 mono_of_kernel_zero
  结论: {X Y : C} {f : X ⟶ Y} [有极限 (parallelPair f 0)]
  证明: mono_of_cancel_zero f fun g h => by rw [← kernel.lift_ι f g h, w, Limits.comp_zero]

Depends on / 依赖: Limits, Limits.comp_zero, comp_zero, kernel, kernel.lift_, mono_of_cancel_zero
-/
theorem mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
    (w : kernel.ι f = 0) : Mono f :=
  mono_of_cancel_zero f fun g h => by rw [← kernel.lift_ι f g h, w, Limits.comp_zero]

/--
lemma `mono_of_isZero_kernel'` / 引理 `mono_of_isZero_kernel'`

English:
lemma mono_of_isZero_kernel'
  statement: {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c)
  proof: mono_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hc _ hg
  rw [← ha]; rw [h.eq_of_tgt a 0]; rw [Limits.zero_comp])

中文:
引理 mono_of_isZero_kernel'
  结论: {X Y : C} {f : X ⟶ Y} (c : 核叉 f) (hc : 是极限 c)
  证明: mono_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hc _ hg
  rw [← ha]; rw [h.eq_of_tgt a 0]; rw [Limits.zero_comp])

Depends on / 依赖: IsLimit, KernelFork, KernelFork.IsLimit.lift, Limits, Limits.zero_comp, eq_of_tgt, h.eq_of_tgt, mono_of_cancel_zero, zero_comp
-/
lemma mono_of_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c)
    (h : IsZero c.pt) : Mono f := mono_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hc _ hg
  rw [← ha]; rw [h.eq_of_tgt a 0]; rw [Limits.zero_comp])

/--
lemma `mono_iff_isZero_kernel'` / 引理 `mono_iff_isZero_kernel'`

English:
lemma mono_iff_isZero_kernel'
  given: {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c)
  proof: ⟨fun _ => KernelFork.IsLimit.isZero_of_mono hc, mono_of_isZero_kernel' c hc⟩

中文:
引理 mono_iff_isZero_kernel'
  条件: {X Y : C} {f : X ⟶ Y} (c : 核叉 f) (hc : 是极限 c)
  证明: ⟨fun _ => KernelFork.IsLimit.isZero_of_mono hc, mono_of_isZero_kernel' c hc⟩

Depends on / 依赖: IsLimit, KernelFork, KernelFork.IsLimit.isZero_of_mono, isZero_of_mono, mono_of_isZero_kernel
-/
lemma mono_iff_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c) :
    Mono f ↔ IsZero c.pt :=
  ⟨fun _ => KernelFork.IsLimit.isZero_of_mono hc, mono_of_isZero_kernel' c hc⟩

/--
lemma `mono_of_isZero_kernel` / 引理 `mono_of_isZero_kernel`

English:
lemma mono_of_isZero_kernel
  given: {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : IsZero (kernel f))
  proof: mono_of_isZero_kernel' _ (kernelIsKernel _) h

中文:
引理 mono_of_isZero_kernel
  条件: {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : 是零 (kernel f))
  证明: mono_of_isZero_kernel' _ (kernelIsKernel _) h

Depends on / 依赖: kernelIsKernel, mono_of_isZero_kernel
-/
lemma mono_of_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : IsZero (kernel f)) :
    Mono f :=
  mono_of_isZero_kernel' _ (kernelIsKernel _) h

/--
lemma `mono_iff_isZero_kernel` / 引理 `mono_iff_isZero_kernel`

English:
lemma mono_iff_isZero_kernel
  given: {X Y : C} (f : X ⟶ Y) [HasKernel f]
  proof: mono_iff_isZero_kernel' _ (limit.isLimit _)

中文:
引理 mono_iff_isZero_kernel
  条件: {X Y : C} (f : X ⟶ Y) [HasKernel f]
  证明: mono_iff_isZero_kernel' _ (limit.isLimit _)

Depends on / 依赖: isLimit, limit.isLimit, mono_iff_isZero_kernel
-/
lemma mono_iff_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    Mono f ↔ IsZero (kernel f) :=
  mono_iff_isZero_kernel' _ (limit.isLimit _)

/--
theorem `epi_of_cancel_zero` / 定理 `epi_of_cancel_zero`

English:
theorem epi_of_cancel_zero
  given: {P Q : C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0)
  proof: ⟨fun {Z} g g' hg =>
sub_eq_zero.1 h _ (map_sub (leftComp Z f) g g').trans sub_eq_zero.2 hg⟩

中文:
定理 epi_of_cancel_zero
  条件: {P Q : C} (f : P ⟶ Q) (h : 对任意 {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0)
  证明: ⟨fun {Z} g g' hg =>
sub_eq_zero.1 h _ (map_sub (leftComp Z f) g g').trans sub_eq_zero.2 hg⟩

Depends on / 依赖: leftComp, map_sub, sub_eq_zero
-/
theorem epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : forall {R : C} (g : Q ⟶ R), f ≫ g = 0 -> g = 0) :
    Epi f :=
  ⟨fun {Z} g g' hg =>
sub_eq_zero.1 h _ (map_sub (leftComp Z f) g g').trans sub_eq_zero.2 hg⟩

/--
theorem `epi_iff_cancel_zero` / 定理 `epi_iff_cancel_zero`

English:
theorem epi_iff_cancel_zero
  given: {P Q : C} (f : P ⟶ Q)
  proof: ⟨fun _ _ _ => zero_of_epi_comp _, epi_of_cancel_zero f⟩

中文:
定理 epi_iff_cancel_zero
  条件: {P Q : C} (f : P ⟶ Q)
  证明: ⟨fun _ _ _ => zero_of_epi_comp _, epi_of_cancel_zero f⟩

Depends on / 依赖: epi_of_cancel_zero, zero_of_epi_comp
-/
theorem epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) :
    Epi f ↔ forall (R : C) (g : Q ⟶ R), f ≫ g = 0 -> g = 0 :=
  ⟨fun _ _ _ => zero_of_epi_comp _, epi_of_cancel_zero f⟩

/--
theorem `epi_of_cokernel_zero` / 定理 `epi_of_cokernel_zero`

English:
theorem epi_of_cokernel_zero
  statement: {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)]
  proof: epi_of_cancel_zero f fun g h => by rw [← cokernel.π_desc f g h, w, Limits.zero_comp]

中文:
定理 epi_of_cokernel_zero
  结论: {X Y : C} {f : X ⟶ Y} [有余极限 (parallelPair f 0)]
  证明: epi_of_cancel_zero f fun g h => by rw [← cokernel.π_desc f g h, w, Limits.zero_comp]

Depends on / 依赖: Limits, Limits.zero_comp, cokernel, epi_of_cancel_zero, zero_comp
-/
theorem epi_of_cokernel_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)]
    (w : cokernel.π f = 0) : Epi f :=
  epi_of_cancel_zero f fun g h => by rw [← cokernel.π_desc f g h, w, Limits.zero_comp]

/--
lemma `epi_of_isZero_cokernel'` / 引理 `epi_of_isZero_cokernel'`

English:
lemma epi_of_isZero_cokernel'
  statement: {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c)
  proof: epi_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hc _ hg
  rw [← ha]; rw [h.eq_of_src a 0]; rw [Limits.comp_zero])

中文:
引理 epi_of_isZero_cokernel'
  结论: {X Y : C} {f : X ⟶ Y} (c : 余核余叉 f) (hc : 是余极限 c)
  证明: epi_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hc _ hg
  rw [← ha]; rw [h.eq_of_src a 0]; rw [Limits.comp_zero])

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, Limits, Limits.comp_zero, comp_zero, epi_of_cancel_zero, eq_of_src, h.eq_of_src
-/
lemma epi_of_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c)
    (h : IsZero c.pt) : Epi f := epi_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hc _ hg
  rw [← ha]; rw [h.eq_of_src a 0]; rw [Limits.comp_zero])

/--
lemma `epi_iff_isZero_cokernel'` / 引理 `epi_iff_isZero_cokernel'`

English:
lemma epi_iff_isZero_cokernel'
  given: {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c)
  proof: ⟨fun _ => CokernelCofork.IsColimit.isZero_of_epi hc, epi_of_isZero_cokernel' c hc⟩

中文:
引理 epi_iff_isZero_cokernel'
  条件: {X Y : C} {f : X ⟶ Y} (c : 余核余叉 f) (hc : 是余极限 c)
  证明: ⟨fun _ => CokernelCofork.IsColimit.isZero_of_epi hc, epi_of_isZero_cokernel' c hc⟩

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.isZero_of_epi, IsColimit, epi_of_isZero_cokernel, isZero_of_epi
-/
lemma epi_iff_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c) :
    Epi f ↔ IsZero c.pt :=
  ⟨fun _ => CokernelCofork.IsColimit.isZero_of_epi hc, epi_of_isZero_cokernel' c hc⟩

/--
lemma `epi_of_isZero_cokernel` / 引理 `epi_of_isZero_cokernel`

English:
lemma epi_of_isZero_cokernel
  given: {X Y : C} (f : X ⟶ Y) [HasCokernel f] (h : IsZero (cokernel f))
  proof: epi_of_isZero_cokernel' _ (cokernelIsCokernel _) h

中文:
引理 epi_of_isZero_cokernel
  条件: {X Y : C} (f : X ⟶ Y) [HasCokernel f] (h : 是零 (cokernel f))
  证明: epi_of_isZero_cokernel' _ (cokernelIsCokernel _) h

Depends on / 依赖: cokernelIsCokernel, epi_of_isZero_cokernel
-/
lemma epi_of_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] (h : IsZero (cokernel f)) :
    Epi f :=
  epi_of_isZero_cokernel' _ (cokernelIsCokernel _) h

/--
lemma `epi_iff_isZero_cokernel` / 引理 `epi_iff_isZero_cokernel`

English:
lemma epi_iff_isZero_cokernel
  given: {X Y : C} (f : X ⟶ Y) [HasCokernel f]
  proof: epi_iff_isZero_cokernel' _ (colimit.isColimit _)

中文:
引理 epi_iff_isZero_cokernel
  条件: {X Y : C} (f : X ⟶ Y) [HasCokernel f]
  证明: epi_iff_isZero_cokernel' _ (colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, epi_iff_isZero_cokernel, isColimit
-/
lemma epi_iff_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] :
    Epi f ↔ IsZero (cokernel f) :=
  epi_iff_isZero_cokernel' _ (colimit.isColimit _)

namespace IsIso

@[simp]
/--
theorem `comp_left_eq_zero` / 定理 `comp_left_eq_zero`

English:
theorem comp_left_eq_zero
  given: [IsIso f]
  statement: f ≫ g = 0 ↔ g = 0
  proof: by
  rw [← IsIso.eq_inv_comp]; rw [Limits.comp_zero]

@[simp]

中文:
定理 comp_left_eq_zero
  条件: [是同构 f]
  结论: f ≫ g = 0 ↔ g = 0
  证明: by
  rw [← IsIso.eq_inv_comp]; rw [Limits.comp_zero]

@[simp]

Depends on / 依赖: IsIso.eq_inv_comp, Limits, Limits.comp_zero, comp_zero, eq_inv_comp
-/
theorem comp_left_eq_zero [IsIso f] : f ≫ g = 0 ↔ g = 0 := by
  rw [← IsIso.eq_inv_comp]; rw [Limits.comp_zero]

@[simp]
/--
theorem `comp_right_eq_zero` / 定理 `comp_right_eq_zero`

English:
theorem comp_right_eq_zero
  given: [IsIso g]
  statement: f ≫ g = 0 ↔ f = 0
  proof: by
  rw [← IsIso.eq_comp_inv]; rw [Limits.zero_comp]

中文:
定理 comp_right_eq_zero
  条件: [是同构 g]
  结论: f ≫ g = 0 ↔ f = 0
  证明: by
  rw [← IsIso.eq_comp_inv]; rw [Limits.zero_comp]

Depends on / 依赖: IsIso.eq_comp_inv, Limits, Limits.zero_comp, eq_comp_inv, zero_comp
-/
theorem comp_right_eq_zero [IsIso g] : f ≫ g = 0 ↔ f = 0 := by
  rw [← IsIso.eq_comp_inv]; rw [Limits.zero_comp]

end IsIso

open ZeroObject

variable [HasZeroObject C]

/--
theorem `mono_of_kernel_iso_zero` / 定理 `mono_of_kernel_iso_zero`

English:
theorem mono_of_kernel_iso_zero
  statement: {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
  proof: mono_of_kernel_zero (zero_of_source_iso_zero _ w)

中文:
定理 mono_of_kernel_iso_zero
  结论: {X Y : C} {f : X ⟶ Y} [有极限 (parallelPair f 0)]
  证明: mono_of_kernel_zero (zero_of_source_iso_zero _ w)

Depends on / 依赖: mono_of_kernel_zero, zero_of_source_iso_zero
-/
theorem mono_of_kernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
    (w : kernel f ≅ 0) : Mono f :=
  mono_of_kernel_zero (zero_of_source_iso_zero _ w)

/--
theorem `epi_of_cokernel_iso_zero` / 定理 `epi_of_cokernel_iso_zero`

English:
theorem epi_of_cokernel_iso_zero
  statement: {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)]
  proof: epi_of_cokernel_zero (zero_of_target_iso_zero _ w)

中文:
定理 epi_of_cokernel_iso_zero
  结论: {X Y : C} {f : X ⟶ Y} [有余极限 (parallelPair f 0)]
  证明: epi_of_cokernel_zero (zero_of_target_iso_zero _ w)

Depends on / 依赖: epi_of_cokernel_zero, zero_of_target_iso_zero
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
/--
Definition of `forkOfKernelFork` / `forkOfKernelFork` 的定义

English:
definition forkOfKernelFork
  signature: (c : KernelFork (f - g))
  body: Fork.ofι c.ι by rw [← sub_eq_zero, ← comp_sub, c.condition]

@[simp]

中文:
定义 forkOfKernelFork
  签名: (c : 核叉 (f - g))
  定义体: Fork.ofι c.ι by rw [← sub_eq_zero, ← comp_sub, c.condition]

@[simp]

Depends on / 依赖: Fork.of, c.condition, comp_sub, condition, sub_eq_zero
-/
def forkOfKernelFork (c : KernelFork (f - g)) : Fork f g :=
Fork.ofι c.ι by rw [← sub_eq_zero, ← comp_sub, c.condition]

@[simp]
/--
theorem `forkOfKernelFork_ι` / 定理 `forkOfKernelFork_ι`

English:
theorem forkOfKernelFork_ι
  given: (c : KernelFork (f - g))
  statement: (forkOfKernelFork c).ι = c.ι
  proof: rfl

中文:
定理 forkOfKernelFork_ι
  条件: (c : 核叉 (f - g))
  结论: (forkOfKernelFork c).ι = c.ι
  证明: rfl
-/
theorem forkOfKernelFork_ι (c : KernelFork (f - g)) : (forkOfKernelFork c).ι = c.ι :=
  rfl

/--
Definition of `kernelForkOfFork` / `kernelForkOfFork` 的定义

English:
definition kernelForkOfFork
  signature: (c : Fork f g)
  body: Fork.ofι c.ι by rw [comp_sub, comp_zero, sub_eq_zero, c.condition]

@[simp]

中文:
定义 kernelForkOfFork
  签名: (c : 叉 f g)
  定义体: Fork.ofι c.ι by rw [comp_sub, comp_zero, sub_eq_zero, c.condition]

@[simp]

Depends on / 依赖: Fork.of, c.condition, comp_sub, comp_zero, condition, sub_eq_zero
-/
def kernelForkOfFork (c : Fork f g) : KernelFork (f - g) :=
Fork.ofι c.ι by rw [comp_sub, comp_zero, sub_eq_zero, c.condition]

@[simp]
/--
theorem `kernelForkOfFork_ι` / 定理 `kernelForkOfFork_ι`

English:
theorem kernelForkOfFork_ι
  given: (c : Fork f g)
  statement: (kernelForkOfFork c).ι = c.ι
  proof: rfl

@[simp]

中文:
定理 kernelForkOfFork_ι
  条件: (c : 叉 f g)
  结论: (kernelForkOfFork c).ι = c.ι
  证明: rfl

@[simp]
-/
theorem kernelForkOfFork_ι (c : Fork f g) : (kernelForkOfFork c).ι = c.ι :=
  rfl

@[simp]
/--
theorem `kernelForkOfFork_ofι` / 定理 `kernelForkOfFork_ofι`

English:
theorem kernelForkOfFork_ofι
  given: {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  proof: rfl

中文:
定理 kernelForkOfFork_ofι
  条件: {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  证明: rfl
-/
theorem kernelForkOfFork_ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
    kernelForkOfFork (Fork.ofι ι w) = KernelFork.ofι ι (by simp [w]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitForkOfKernelFork` / `isLimitForkOfKernelFork` 的定义

English:
definition isLimitForkOfKernelFork
  signature: {c : KernelFork (f - g)} (i : IsLimit c)
  body: Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (kernelForkOfFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

@[simp]

中文:
定义 isLimitForkOfKernelFork
  签名: {c : 核叉 (f - g)} (i : 是极限 c)
  定义体: Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (kernelForkOfFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

@[simp]

Depends on / 依赖: Fork.IsLimit.hom_ext, Fork.IsLimit.mk, IsLimit, cat_disch, hom_ext, i.fac, i.lift, kernelForkOfFork
-/
def isLimitForkOfKernelFork {c : KernelFork (f - g)} (i : IsLimit c) :
    IsLimit (forkOfKernelFork c) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (kernelForkOfFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

@[simp]
/--
theorem `isLimitForkOfKernelFork_lift` / 定理 `isLimitForkOfKernelFork_lift`

English:
theorem isLimitForkOfKernelFork_lift
  given: {c : KernelFork (f - g)} (i : IsLimit c) (s : Fork f g)
  proof: rfl

中文:
定理 isLimitForkOfKernelFork_lift
  条件: {c : 核叉 (f - g)} (i : 是极限 c) (s : 叉 f g)
  证明: rfl
-/
theorem isLimitForkOfKernelFork_lift {c : KernelFork (f - g)} (i : IsLimit c) (s : Fork f g) :
    (isLimitForkOfKernelFork i).lift s = i.lift (kernelForkOfFork s) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitKernelForkOfFork` / `isLimitKernelForkOfFork` 的定义

English:
definition isLimitKernelForkOfFork
  signature: {c : Fork f g} (i : IsLimit c)
  body: Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (forkOfKernelFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

中文:
定义 isLimitKernelForkOfFork
  签名: {c : 叉 f g} (i : 是极限 c)
  定义体: Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (forkOfKernelFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

Depends on / 依赖: Fork.IsLimit.hom_ext, Fork.IsLimit.mk, IsLimit, cat_disch, forkOfKernelFork, hom_ext, i.fac, i.lift
-/
def isLimitKernelForkOfFork {c : Fork f g} (i : IsLimit c) : IsLimit (kernelForkOfFork c) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (forkOfKernelFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

variable (f g)

/--
theorem `hasEqualizer_of_hasKernel` / 定理 `hasEqualizer_of_hasKernel`

English:
theorem hasEqualizer_of_hasKernel
  given: [HasKernel (f - g)]
  statement: HasEqualizer f g
  proof: HasLimit.mk
    { cone := forkOfKernelFork _
      isLimit := isLimitForkOfKernelFork (equalizerIsEqualizer (f - g) 0) }

中文:
定理 hasEqualizer_of_hasKernel
  条件: [HasKernel (f - g)]
  结论: HasEqualizer f g
  证明: HasLimit.mk
    { cone := forkOfKernelFork _
      isLimit := isLimitForkOfKernelFork (equalizerIsEqualizer (f - g) 0) }

Depends on / 依赖: HasLimit, HasLimit.mk, equalizerIsEqualizer, forkOfKernelFork, isLimit, isLimitForkOfKernelFork
-/
theorem hasEqualizer_of_hasKernel [HasKernel (f - g)] : HasEqualizer f g :=
  HasLimit.mk
    { cone := forkOfKernelFork _
      isLimit := isLimitForkOfKernelFork (equalizerIsEqualizer (f - g) 0) }

/--
theorem `hasKernel_of_hasEqualizer` / 定理 `hasKernel_of_hasEqualizer`

English:
theorem hasKernel_of_hasEqualizer
  given: [HasEqualizer f g]
  statement: HasKernel (f - g)
  proof: HasLimit.mk
    { cone := kernelForkOfFork (equalizer.fork f g)
      isLimit := isLimitKernelForkOfFork (limit.isLimit (parallelPair f g)) }

中文:
定理 hasKernel_of_hasEqualizer
  条件: [HasEqualizer f g]
  结论: HasKernel (f - g)
  证明: HasLimit.mk
    { cone := kernelForkOfFork (equalizer.fork f g)
      isLimit := isLimitKernelForkOfFork (limit.isLimit (parallelPair f g)) }

Depends on / 依赖: HasLimit, HasLimit.mk, equalizer, equalizer.fork, isLimit, isLimitKernelForkOfFork, kernelForkOfFork, limit.isLimit, parallelPair
-/
theorem hasKernel_of_hasEqualizer [HasEqualizer f g] : HasKernel (f - g) :=
  HasLimit.mk
    { cone := kernelForkOfFork (equalizer.fork f g)
      isLimit := isLimitKernelForkOfFork (limit.isLimit (parallelPair f g)) }

variable {f g}

/-- Map a cokernel cocone on the difference of two morphisms to the coequalizer cofork. -/
@[simps! pt]
/--
Definition of `coforkOfCokernelCofork` / `coforkOfCokernelCofork` 的定义

English:
definition coforkOfCokernelCofork
  signature: (c : CokernelCofork (f - g))
  body: Cofork.ofπ c.π by rw [← sub_eq_zero, ← sub_comp, c.condition]

@[simp]

中文:
定义 coforkOfCokernelCofork
  签名: (c : 余核余叉 (f - g))
  定义体: Cofork.ofπ c.π by rw [← sub_eq_zero, ← sub_comp, c.condition]

@[simp]

Depends on / 依赖: Cofork, Cofork.of, c.condition, condition, sub_comp, sub_eq_zero
-/
def coforkOfCokernelCofork (c : CokernelCofork (f - g)) : Cofork f g :=
Cofork.ofπ c.π by rw [← sub_eq_zero, ← sub_comp, c.condition]

@[simp]
/--
theorem `coforkOfCokernelCofork_π` / 定理 `coforkOfCokernelCofork_π`

English:
theorem coforkOfCokernelCofork_π
  given: (c : CokernelCofork (f - g))
  proof: rfl

中文:
定理 coforkOfCokernelCofork_π
  条件: (c : 余核余叉 (f - g))
  证明: rfl
-/
theorem coforkOfCokernelCofork_π (c : CokernelCofork (f - g)) :
    (coforkOfCokernelCofork c).π = c.π :=
  rfl

/--
Definition of `cokernelCoforkOfCofork` / `cokernelCoforkOfCofork` 的定义

English:
definition cokernelCoforkOfCofork
  signature: (c : Cofork f g)
  body: Cofork.ofπ c.π by rw [sub_comp, zero_comp, sub_eq_zero, c.condition]

@[simp]

中文:
定义 cokernelCoforkOfCofork
  签名: (c : 余叉 f g)
  定义体: Cofork.ofπ c.π by rw [sub_comp, zero_comp, sub_eq_zero, c.condition]

@[simp]

Depends on / 依赖: Cofork, Cofork.of, c.condition, condition, sub_comp, sub_eq_zero, zero_comp
-/
def cokernelCoforkOfCofork (c : Cofork f g) : CokernelCofork (f - g) :=
Cofork.ofπ c.π by rw [sub_comp, zero_comp, sub_eq_zero, c.condition]

@[simp]
/--
theorem `cokernelCoforkOfCofork_π` / 定理 `cokernelCoforkOfCofork_π`

English:
theorem cokernelCoforkOfCofork_π
  given: (c : Cofork f g)
  statement: (cokernelCoforkOfCofork c).π = c.π
  proof: rfl

@[simp]

中文:
定理 cokernelCoforkOfCofork_π
  条件: (c : 余叉 f g)
  结论: (cokernelCoforkOfCofork c).π = c.π
  证明: rfl

@[simp]
-/
theorem cokernelCoforkOfCofork_π (c : Cofork f g) : (cokernelCoforkOfCofork c).π = c.π :=
  rfl

@[simp]
/--
theorem `cokernelCoforkOfCofork_ofπ` / 定理 `cokernelCoforkOfCofork_ofπ`

English:
theorem cokernelCoforkOfCofork_ofπ
  given: {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π)
  proof: rfl

中文:
定理 cokernelCoforkOfCofork_ofπ
  条件: {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π)
  证明: rfl
-/
theorem cokernelCoforkOfCofork_ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
    cokernelCoforkOfCofork (Cofork.ofπ π w) = CokernelCofork.ofπ π (by simp [w]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCoforkOfCokernelCofork` / `isColimitCoforkOfCokernelCofork` 的定义

English:
definition isColimitCoforkOfCokernelCofork
  signature: {c : CokernelCofork (f - g)} (i : IsColimit c)
  body: Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (cokernelCoforkOfCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; cat_disch⟩

@[simp]

中文:
定义 isColimitCoforkOfCokernelCofork
  签名: {c : 余核余叉 (f - g)} (i : 是余极限 c)
  定义体: Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (cokernelCoforkOfCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; cat_disch⟩

@[simp]

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, Cofork.IsColimit.mk, IsColimit, cat_disch, cokernelCoforkOfCofork, hom_ext, i.desc, i.fac
-/
def isColimitCoforkOfCokernelCofork {c : CokernelCofork (f - g)} (i : IsColimit c) :
    IsColimit (coforkOfCokernelCofork c) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (cokernelCoforkOfCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; cat_disch⟩

@[simp]
/--
theorem `isColimitCoforkOfCokernelCofork_desc` / 定理 `isColimitCoforkOfCokernelCofork_desc`

English:
theorem isColimitCoforkOfCokernelCofork_desc
  statement: {c : CokernelCofork (f - g)} (i : IsColimit c)
  proof: rfl

中文:
定理 isColimitCoforkOfCokernelCofork_desc
  结论: {c : 余核余叉 (f - g)} (i : 是余极限 c)
  证明: rfl
-/
theorem isColimitCoforkOfCokernelCofork_desc {c : CokernelCofork (f - g)} (i : IsColimit c)
    (s : Cofork f g) :
    (isColimitCoforkOfCokernelCofork i).desc s = i.desc (cokernelCoforkOfCofork s) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCokernelCoforkOfCofork` / `isColimitCokernelCoforkOfCofork` 的定义

English:
definition isColimitCokernelCoforkOfCofork
  signature: {c : Cofork f g} (i : IsColimit c)
  body: Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (coforkOfCokernelCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; cat_disch⟩

中文:
定义 isColimitCokernelCoforkOfCofork
  签名: {c : 余叉 f g} (i : 是余极限 c)
  定义体: Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (coforkOfCokernelCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; cat_disch⟩

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, Cofork.IsColimit.mk, IsColimit, cat_disch, coforkOfCokernelCofork, hom_ext, i.desc, i.fac
-/
def isColimitCokernelCoforkOfCofork {c : Cofork f g} (i : IsColimit c) :
    IsColimit (cokernelCoforkOfCofork c) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (coforkOfCokernelCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; cat_disch⟩

variable (f g)

/--
theorem `hasCoequalizer_of_hasCokernel` / 定理 `hasCoequalizer_of_hasCokernel`

English:
theorem hasCoequalizer_of_hasCokernel
  given: [HasCokernel (f - g)]
  statement: HasCoequalizer f g
  proof: HasColimit.mk
    { cocone := coforkOfCokernelCofork _
      isColimit := isColimitCoforkOfCokernelCofork (coequalizerIsCoequalizer (f - g) 0) }

中文:
定理 hasCoequalizer_of_hasCokernel
  条件: [HasCokernel (f - g)]
  结论: HasCoequalizer f g
  证明: HasColimit.mk
    { cocone := coforkOfCokernelCofork _
      isColimit := isColimitCoforkOfCokernelCofork (coequalizerIsCoequalizer (f - g) 0) }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, coequalizerIsCoequalizer, coforkOfCokernelCofork, isColimit, isColimitCoforkOfCokernelCofork
-/
theorem hasCoequalizer_of_hasCokernel [HasCokernel (f - g)] : HasCoequalizer f g :=
  HasColimit.mk
    { cocone := coforkOfCokernelCofork _
      isColimit := isColimitCoforkOfCokernelCofork (coequalizerIsCoequalizer (f - g) 0) }

/--
theorem `hasCokernel_of_hasCoequalizer` / 定理 `hasCokernel_of_hasCoequalizer`

English:
theorem hasCokernel_of_hasCoequalizer
  given: [HasCoequalizer f g]
  statement: HasCokernel (f - g)
  proof: HasColimit.mk
    { cocone := cokernelCoforkOfCofork (coequalizer.cofork f g)
      isColimit := isColimitCokernelCoforkOfCofork (colimit.isColimit (parallelPair f g)) }

中文:
定理 hasCokernel_of_hasCoequalizer
  条件: [HasCoequalizer f g]
  结论: HasCokernel (f - g)
  证明: HasColimit.mk
    { cocone := cokernelCoforkOfCofork (coequalizer.cofork f g)
      isColimit := isColimitCokernelCoforkOfCofork (colimit.isColimit (parallelPair f g)) }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, coequalizer, coequalizer.cofork, cofork, cokernelCoforkOfCofork, colimit, colimit.isColimit, isColimit, isColimitCokernelCoforkOfCofork, parallelPair
-/
theorem hasCokernel_of_hasCoequalizer [HasCoequalizer f g] : HasCokernel (f - g) :=
  HasColimit.mk
    { cocone := cokernelCoforkOfCofork (coequalizer.cofork f g)
      isColimit := isColimitCokernelCoforkOfCofork (colimit.isColimit (parallelPair f g)) }

end

/--
theorem `hasEqualizers_of_hasKernels` / 定理 `hasEqualizers_of_hasKernels`

English:
theorem hasEqualizers_of_hasKernels
  given: [HasKernels C]
  statement: HasEqualizers C
  proof: @hasEqualizers_of_hasLimit_parallelPair _ _ fun {_} {_} f g => hasEqualizer_of_hasKernel f g

中文:
定理 hasEqualizers_of_hasKernels
  条件: [有Kernels C]
  结论: HasEqualizers C
  证明: @hasEqualizers_of_hasLimit_parallelPair _ _ fun {_} {_} f g => hasEqualizer_of_hasKernel f g

Depends on / 依赖: hasEqualizer_of_hasKernel, hasEqualizers_of_hasLimit_parallelPair
-/
theorem hasEqualizers_of_hasKernels [HasKernels C] : HasEqualizers C :=
  @hasEqualizers_of_hasLimit_parallelPair _ _ fun {_} {_} f g => hasEqualizer_of_hasKernel f g

/--
theorem `hasCoequalizers_of_hasCokernels` / 定理 `hasCoequalizers_of_hasCokernels`

English:
theorem hasCoequalizers_of_hasCokernels
  given: [HasCokernels C]
  statement: HasCoequalizers C
  proof: @hasCoequalizers_of_hasColimit_parallelPair _ _ fun {_} {_} f g =>
    hasCoequalizer_of_hasCokernel f g

中文:
定理 hasCoequalizers_of_hasCokernels
  条件: [有余kernels C]
  结论: HasCoequalizers C
  证明: @hasCoequalizers_of_hasColimit_parallelPair _ _ fun {_} {_} f g =>
    hasCoequalizer_of_hasCokernel f g

Depends on / 依赖: hasCoequalizer_of_hasCokernel, hasCoequalizers_of_hasColimit_parallelPair
-/
theorem hasCoequalizers_of_hasCokernels [HasCokernels C] : HasCoequalizers C :=
  @hasCoequalizers_of_hasColimit_parallelPair _ _ fun {_} {_} f g =>
    hasCoequalizer_of_hasCokernel f g

end Equalizers

section

variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (Units Int) (X ≅ Y)
  body: { hom := (a : Int) • e.hom
      inv := ((a⁻¹ : Units Int) : Int) • e.inv
      hom_inv_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.inv_mul, one_smul, e.hom_inv_id]
      inv_hom_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.mul_inv, one_smul, e.inv_hom_id] }

@[simp]

中文:
实例 :
  签名: 标量乘法 (单位群 整数) (X ≅ Y)
  定义体: { hom := (a : Int) • e.hom
      inv := ((a⁻¹ : Units Int) : Int) • e.inv
      hom_inv_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.inv_mul, one_smul, e.hom_inv_id]
      inv_hom_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.mul_inv, one_smul, e.inv_hom_id] }

@[simp]

Depends on / 依赖: Units.inv_mul, Units.mul_inv, comp_zsmul, e.hom, e.hom_inv_id, e.inv, e.inv_hom_id, hom_inv_id, inv_hom_id, inv_mul, mul_inv, one_smul, smul_smul, zsmul_comp
-/
instance : SMul (Units Int) (X ≅ Y) where
  smul a e :=
    { hom := (a : Int) • e.hom
      inv := ((a⁻¹ : Units Int) : Int) • e.inv
      hom_inv_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.inv_mul, one_smul, e.hom_inv_id]
      inv_hom_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.mul_inv, one_smul, e.inv_hom_id] }

@[simp]
/--
lemma `smul_iso_hom` / 引理 `smul_iso_hom`

English:
lemma smul_iso_hom
  given: (a : Units Int) (e : X ≅ Y)
  statement: (a • e).hom = a • e.hom
  proof: rfl

@[simp]

中文:
引理 smul_iso_hom
  条件: (a : 单位群 整数) (e : X ≅ Y)
  结论: (a • e).hom = a • e.hom
  证明: rfl

@[simp]
-/
lemma smul_iso_hom (a : Units Int) (e : X ≅ Y) : (a • e).hom = a • e.hom := rfl

@[simp]
/--
lemma `smul_iso_inv` / 引理 `smul_iso_inv`

English:
lemma smul_iso_inv
  given: (a : Units Int) (e : X ≅ Y)
  statement: (a • e).inv = a⁻¹ • e.inv
  proof: rfl

中文:
引理 smul_iso_inv
  条件: (a : 单位群 整数) (e : X ≅ Y)
  结论: (a • e).inv = a⁻¹ • e.inv
  证明: rfl
-/
lemma smul_iso_inv (a : Units Int) (e : X ≅ Y) : (a • e).inv = a⁻¹ • e.inv := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (X ≅ Y)
  body: { hom := -e.hom
      inv := -e.inv }

@[simp]

中文:
实例 :
  签名: 取负 (X ≅ Y)
  定义体: { hom := -e.hom
      inv := -e.inv }

@[simp]

Depends on / 依赖: e.hom, e.inv
-/
instance : Neg (X ≅ Y) where
  neg e :=
    { hom := -e.hom
      inv := -e.inv }

@[simp]
/--
lemma `neg_iso_hom` / 引理 `neg_iso_hom`

English:
lemma neg_iso_hom
  given: (e : X ≅ Y)
  statement: (-e).hom = -e.hom
  proof: rfl

@[simp]

中文:
引理 neg_iso_hom
  条件: (e : X ≅ Y)
  结论: (-e).hom = -e.hom
  证明: rfl

@[simp]
-/
lemma neg_iso_hom (e : X ≅ Y) : (-e).hom = -e.hom := rfl

@[simp]
/--
lemma `neg_iso_inv` / 引理 `neg_iso_inv`

English:
lemma neg_iso_inv
  given: (e : X ≅ Y)
  statement: (-e).inv = -e.inv
  proof: rfl

中文:
引理 neg_iso_inv
  条件: (e : X ≅ Y)
  结论: (-e).inv = -e.inv
  证明: rfl
-/
lemma neg_iso_inv (e : X ≅ Y) : (-e).inv = -e.inv := rfl

end

end Preadditive

end CategoryTheory
