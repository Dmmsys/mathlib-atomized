/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Tactic.AdaptationNote

/-!
# Abelian categories with enough injectives have injective resolutions

## Main results
When the underlying category is abelian:
* `CategoryTheory.InjectiveResolution.desc`: Given `I : InjectiveResolution X` and
  `J : InjectiveResolution Y`, any morphism `X ⟶ Y` admits a descent to a cochain map
  `J.cocomplex ⟶ I.cocomplex`. It is a descent in the sense that `I.ι` intertwines the descent and
  the original morphism, see `CategoryTheory.InjectiveResolution.desc_commutes`.
* `CategoryTheory.InjectiveResolution.descHomotopy`: Any two such descents are homotopic.
* `CategoryTheory.InjectiveResolution.homotopyEquiv`: Any two injective resolutions of the same
  object are homotopy equivalent.
* `CategoryTheory.injectiveResolutions`: If every object admits an injective resolution, we can
  construct a functor `injectiveResolutions C : C ⥤ HomotopyCategory C`.

* `CategoryTheory.exact_f_d`: `f` and `Injective.d f` are exact.
* `CategoryTheory.InjectiveResolution.of`: Hence, starting from a monomorphism `X ⟶ J`, where `J`
  is injective, we can apply `Injective.d` repeatedly to obtain an injective resolution of `X`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Injective

namespace InjectiveResolution

section

variable [HasZeroObject C] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary construction for `desc`. -/
/-
**CategoryTheory.InjectiveResolution.descFZero** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.InjectiveResolution`。
形式化陈述：descFZero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : Injective
Resolution Z) : J.cocomplex.X 0 ⟶ I.cocomplex.X 0
参数：f : Z ⟶ Y；I : InjectiveResolution Y；J : InjectiveResolution Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction for `desc`.
-/
def descFZero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex.X 0 ⟶ I.cocomplex.X 0 :=
  factorThru (f ≫ I.ι.f 0) (J.ι.f 0)

end

section Abelian

variable [Abelian C]

/-
**CategoryTheory.InjectiveResolution.exact** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₀ {Z : C} (I : InjectiveResolution Z) :
    (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
  ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary construction for `desc`. -/
/-
**CategoryTheory.InjectiveResolution.descFOne** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.InjectiveResolution`。
形式化陈述：descFOne {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveR
esolution Z) : J.cocomplex.X 1 ⟶ I.cocomplex.X 1
参数：f : Z ⟶ Y；I : InjectiveResolution Y；J : InjectiveResolution Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.InjectiveResolution.exact₀`：exact₀ {Z : C} (I : Injective
Resolution Z) : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact

--- 原说明 ---
Auxiliary construction for `desc`.
-/
def descFOne {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex.X 1 ⟶ I.cocomplex.X 1 :=
  J.exact₀.descToInjective (descFZero f I J ≫ I.cocomplex.d 0 1)
    (by dsimp; simp only [← assoc, descFZero]; simp [assoc])

@[simp]
/-
**CategoryTheory.InjectiveResolution.descFOne_zero_comm** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.InjectiveResolution`。
形式化陈述：descFOne_zero_comm {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : 
InjectiveResolution Z) : J.cocomplex.d 0 1 ≫ descFOne f I J = descFZero f I J ≫ 
I.cocomplex.d 0 1
参数：f : Z ⟶ Y；I : InjectiveResolution Y；J : InjectiveResolution Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.ShortComplex.Exact.comp_descToInjective`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian 
C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.InjectiveResolution.ι_f_zero_comp_complex_d`：ι_f_zero_com
p_complex_d : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0
· 使用引理 `CategoryTheory.InjectiveResolution.exact₀`：exact₀ {Z : C} (I : Injective
Resolution Z) : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact
-/
theorem descFOne_zero_comm {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) :
    J.cocomplex.d 0 1 ≫ descFOne f I J = descFZero f I J ≫ I.cocomplex.d 0 1 := by
  apply J.exact₀.comp_descToInjective

/-- Auxiliary construction for `desc`. -/
/-
**CategoryTheory.InjectiveResolution.descFSucc** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.InjectiveResolution`。
形式化陈述：descFSucc {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z
) (n : Nat) (g : J.cocomplex.X n ⟶ I.cocomplex.X n) (g' : J.cocomplex.X (n + 1) 
⟶ I.cocomplex.X (n + 1)) (w : J.cocomplex.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n
 (n + 1)) : Σ' g'' : J.cocomplex.X (n + 2) ⟶ I.cocomplex.X (n + 2), J.cocomplex.
d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2)
参数：I : InjectiveResolution Y；J : InjectiveResolution Z；n : Nat；g : J.cocomplex.X
 n ⟶ I.cocomplex.X n；g' : J.cocomplex.X (n + 1) ⟶ I.cocomplex.X (n + 1)；w : J.co
complex.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Auxiliary construction for `desc`.
-/
def descFSucc {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z) (n : ℕ)
    (g : J.cocomplex.X n ⟶ I.cocomplex.X n) (g' : J.cocomplex.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : J.cocomplex.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ' g'' : J.cocomplex.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      J.cocomplex.d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨(J.exact_succ n).descToInjective
    (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      (J.exact_succ n).comp_descToInjective _ _⟩

/-- A morphism in `C` descends to a cochain map between injective resolutions. -/
/-
**CategoryTheory.InjectiveResolution.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.InjectiveResolution`。
形式化陈述：desc {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResol
ution Z) : J.cocomplex ⟶ I.cocomplex
参数：f : Z ⟶ Y；I : InjectiveResolution Y；J : InjectiveResolution Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
A morphism in `C` descends to a cochain map between injective resolutions.
-/
def desc {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (descFZero f _ _) (descFOne f _ _) (descFOne_zero_comm f I J).symm
    fun n ⟨g, g', w⟩ => ⟨(descFSucc I J n g g' w.symm).1, (descFSucc I J n g g' w.symm).2.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution maps intertwine the descent of a morphism and that morphism. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.desc_commutes** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.InjectiveResolution`。
形式化陈述：desc_commutes {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : Injec
tiveResolution Z) : J.ι ≫ desc f I J = (CochainComplex.single₀ C).map f ≫ I.ι
参数：f : Z ⟶ Y；I : InjectiveResolution Y；J : InjectiveResolution Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `HomologicalComplex.from_single_hom_ext`：from_single_hom_ext {K : Homolog
icalComplex V c} {j : ι} {A : V} {f g : (single V c j).obj A ⟶ K} (hfg : f.f j =
 g.f j) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Injective.comp_factorThru`：comp_factorThru {J X Y : C} [I
njective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.single₀_map_f_zero`：single₀_map_f_zero {A B : V} (f : A ⟶
 B) : ((single₀ V).map f).f 0 = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The resolution maps intertwine the descent of a morphism and that morphism.
-/
theorem desc_commutes {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) : J.ι ≫ desc f I J = (CochainComplex.single₀ C).map f ≫ I.ι := by
  ext
  simp [desc, descFOne, descFZero]

@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.desc_commutes_zero** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.InjectiveResolution`。
形式化陈述：desc_commutes_zero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : 
InjectiveResolution Z) : J.ι.f 0 ≫ (desc f I J).f 0 = f ≫ I.ι.f 0
参数：f : Z ⟶ Y；I : InjectiveResolution Y；J : InjectiveResolution Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `CategoryTheory.InjectiveResolution.desc_commutes`：desc_commutes {Y Z : C
} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) : J.ι ≫ de
sc f I J = (CochainComplex.single₀ C).…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.single₀_map_f_zero`：single₀_map_f_zero {A B : V} (f : A ⟶
 B) : ((single₀ V).map f).f 0 = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma desc_commutes_zero {Y Z : C} (f : Z ⟶ Y)
    (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.ι.f 0 ≫ (desc f I J).f 0 = f ≫ I.ι.f 0 :=
  (HomologicalComplex.congr_hom (desc_commutes f I J) 0).trans (by simp)

-- Now that we've checked this property of the descent, we can seal away the actual definition.
/-- An auxiliary definition for `descHomotopyZero`. -/
/-
**CategoryTheory.InjectiveResolution.descHomotopyZeroZero** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveR
esolution Z} (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : I.cocomplex.
X 1 ⟶ J.cocomplex.X 0
参数：f : I.cocomplex ⟶ J.cocomplex；comm : I.ι ≫ f = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.InjectiveResolution.exact₀`：exact₀ {Z : C} (I : Injective
Resolution Z) : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact

--- 原说明 ---
An auxiliary definition for `descHomotopyZero`.
-/
def descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : I.cocomplex.X 1 ⟶ J.cocomplex.X 0 :=
  I.exact₀.descToInjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.comp_descHomotopyZeroZero** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：comp_descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : Injec
tiveResolution Z} (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : I.cocom
plex.d 0 1 ≫ descHomotopyZeroZero f comm = f.f 0
参数：f : I.cocomplex ⟶ J.cocomplex；comm : I.ι ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ShortComplex.Exact.comp_descToInjective`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian 
C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `CategoryTheory.InjectiveResolution.ι_f_zero_comp_complex_d`：ι_f_zero_com
p_complex_d : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0
· 使用引理 `CategoryTheory.InjectiveResolution.exact₀`：exact₀ {Z : C} (I : Injective
Resolution Z) : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact
-/
lemma comp_descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) :
    I.cocomplex.d 0 1 ≫ descHomotopyZeroZero f comm = f.f 0 :=
  I.exact₀.comp_descToInjective _ _

/-- An auxiliary definition for `descHomotopyZero`. -/
/-
**CategoryTheory.InjectiveResolution.descHomotopyZeroOne** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveRe
solution Z} (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocompl
ex)) : I.cocomplex.X 2 ⟶ J.cocomplex.X 1
参数：f : I.cocomplex ⟶ J.cocomplex；comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
An auxiliary definition for `descHomotopyZero`.
-/
def descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
  (I.exact_succ 0).descToInjective (f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1)
    (by rw [Preadditive.comp_sub, comp_descHomotopyZeroZero_assoc f comm,
          HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.comp_descHomotopyZeroOne** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：comp_descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : Inject
iveResolution Z} (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.co
complex)) : I.cocomplex.d 1 2 ≫ descHomotopyZeroOne f comm = f.f 1 - descHomotop
yZeroZero f comm ≫ J.cocomplex.d 0 1
参数：f : I.cocomplex ⟶ J.cocomplex；comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ShortComplex.Exact.comp_descToInjective`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian 
C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用引理 `CategoryTheory.InjectiveResolution.exact_succ`：exact_succ (n : Nat) : (S
hortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact
-/
lemma comp_descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.d 1 2 ≫ descHomotopyZeroOne f comm =
      f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1 :=
  (I.exact_succ 0).comp_descToInjective _ _

/-- An auxiliary definition for `descHomotopyZero`. -/
/-
**CategoryTheory.InjectiveResolution.descHomotopyZeroSucc** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveR
esolution Z} (f : I.cocomplex ⟶ J.cocomplex) (n : Nat) (g : I.cocomplex.X (n + 1
) ⟶ J.cocomplex.X n) (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1)) (w : f
.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
 I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2)
参数：f : I.cocomplex ⟶ J.cocomplex；n : Nat；g : I.cocomplex.X (n + 1) ⟶ J.cocomplex
.X n；g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1)；w : f.f (n + 1) = I.coco
mplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
An auxiliary definition for `descHomotopyZero`.
-/
def descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
  (I.exact_succ (n + 1)).descToInjective (f.f (n + 2) - g' ≫ J.cocomplex.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        add_zero, sub_self])

@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.comp_descHomotopyZeroSucc** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：comp_descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : Injec
tiveResolution Z} (f : I.cocomplex ⟶ J.cocomplex) (n : Nat) (g : I.cocomplex.X (
n + 1) ⟶ J.cocomplex.X n) (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1)) (
w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 
1)) : I.cocomplex.d (n + 2) (n + 3) ≫ descHomotopyZeroSucc f n g g' w = f.f (n +
 2) - g' ≫ J.cocomplex.d _ _
参数：f : I.cocomplex ⟶ J.cocomplex；n : Nat；g : I.cocomplex.X (n + 1) ⟶ J.cocomplex
.X n；g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1)；w : f.f (n + 1) = I.coco
mplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ShortComplex.Exact.comp_descToInjective`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian 
C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用引理 `CategoryTheory.InjectiveResolution.exact_succ`：exact_succ (n : Nat) : (S
hortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact
-/
lemma comp_descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.d (n + 2) (n + 3) ≫ descHomotopyZeroSucc f n g g' w =
      f.f (n + 2) - g' ≫ J.cocomplex.d _ _ :=
  (I.exact_succ (n + 1)).comp_descToInjective _ _

/-- Any descent of the zero morphism is homotopic to zero. -/
/-
**CategoryTheory.InjectiveResolution.descHomotopyZero** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.InjectiveResolution`。
形式化陈述：descHomotopyZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResol
ution Z} (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : Homotopy f 0
参数：f : I.cocomplex ⟶ J.cocomplex；comm : I.ι ≫ f = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Any descent of the zero morphism is homotopic to zero.
-/
def descHomotopyZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (descHomotopyZeroZero f comm) (by simp)
    (descHomotopyZeroOne f comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨descHomotopyZeroSucc f n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Two descents of the same morphism are homotopic. -/
/-
**CategoryTheory.InjectiveResolution.descHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.InjectiveResolution`。
形式化陈述：descHomotopy {Y Z : C} (f : Y ⟶ Z) {I : InjectiveResolution Y} {J : Inject
iveResolution Z} (g h : I.cocomplex ⟶ J.cocomplex) (g_comm : I.ι ≫ g = (CochainC
omplex.single₀ C).map f ≫ J.ι) (h_comm : I.ι ≫ h = (CochainComplex.single₀ C).ma
p f ≫ J.ι) : Homotopy g h
参数：f : Y ⟶ Z；g h : I.cocomplex ⟶ J.cocomplex；g_comm : I.ι ≫ g = (CochainComplex.
single₀ C).map f ≫ J.ι；h_comm : I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι
。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Two descents of the same morphism are homotopic.
-/
def descHomotopy {Y Z : C} (f : Y ⟶ Z) {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (g h : I.cocomplex ⟶ J.cocomplex) (g_comm : I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι)
    (h_comm : I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (descHomotopyZero _ (by simp [g_comm, h_comm]))

/-- The descent of the identity morphism is homotopic to the identity cochain map. -/
/-
**CategoryTheory.InjectiveResolution.descIdHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.InjectiveResolution`。
形式化陈述：descIdHomotopy (X : C) (I : InjectiveResolution X) : Homotopy (desc (𝟙 X) 
I I) (𝟙 I.cocomplex)
参数：X : C；I : InjectiveResolution X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The descent of the identity morphism is homotopic to the identity cochain map.
-/
def descIdHomotopy (X : C) (I : InjectiveResolution X) :
    Homotopy (desc (𝟙 X) I I) (𝟙 I.cocomplex) := by
  apply descHomotopy (𝟙 X) <;> simp

/-- The descent of a composition is homotopic to the composition of the descents. -/
/-
**CategoryTheory.InjectiveResolution.descCompHomotopy** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.InjectiveResolution`。
形式化陈述：descCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (I : InjectiveResolut
ion X) (J : InjectiveResolution Y) (K : InjectiveResolution Z) : Homotopy (desc 
(f ≫ g) K I) (desc f J I ≫ desc g K J)
参数：f : X ⟶ Y；g : Y ⟶ Z；I : InjectiveResolution X；J : InjectiveResolution Y；K : I
njectiveResolution Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The descent of a composition is homotopic to the composition of the descents.
-/
def descCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (K : InjectiveResolution Z) :
    Homotopy (desc (f ≫ g) K I) (desc f J I ≫ desc g K J) := by
  apply descHomotopy (f ≫ g) <;> simp

-- We don't care about the actual definitions of these homotopies.
/-- Any two injective resolutions are homotopy equivalent. -/
/-
**CategoryTheory.InjectiveResolution.homotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.InjectiveResolution`。
形式化陈述：homotopyEquiv {X : C} (I J : InjectiveResolution X) : HomotopyEquiv I.coco
mplex J.cocomplex where hom
参数：I J : InjectiveResolution X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Any two injective resolutions are homotopy equivalent.
-/
def homotopyEquiv {X : C} (I J : InjectiveResolution X) :
    HomotopyEquiv I.cocomplex J.cocomplex where
  hom := desc (𝟙 X) J I
  inv := desc (𝟙 X) I J
  homotopyHomInvId := (descCompHomotopy (𝟙 X) (𝟙 X) I J I).symm.trans <| by
    simpa [id_comp] using descIdHomotopy _ _
  homotopyInvHomId := (descCompHomotopy (𝟙 X) (𝟙 X) J I J).symm.trans <| by
    simpa [id_comp] using descIdHomotopy _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.homotopyEquiv_hom_** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homotopyEquiv_hom_ι {X : C} (I J : InjectiveResolution X) :
    I.ι ≫ (homotopyEquiv I J).hom = J.ι := by simp [homotopyEquiv]

@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.homotopyEquiv_inv_** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homotopyEquiv_inv_ι {X : C} (I J : InjectiveResolution X) :
    J.ι ≫ (homotopyEquiv I J).inv = I.ι := by simp [homotopyEquiv]

end Abelian

end InjectiveResolution

section

variable [Abelian C]

/-- An arbitrarily chosen injective resolution of an object. -/
/-
**CategoryTheory.injectiveResolution** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
`。
形式化陈述：injectiveResolution (Z : C) [HasInjectiveResolution Z] : InjectiveResoluti
on Z
参数：Z : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
An arbitrarily chosen injective resolution of an object.
-/
abbrev injectiveResolution (Z : C) [HasInjectiveResolution Z] : InjectiveResolution Z :=
  (HasInjectiveResolution.out (Z := Z)).some

variable (C)
variable [HasInjectiveResolutions C]

/-- Taking injective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed cochain complexes and cochain maps up to homotopy).
-/
/-
**CategoryTheory.injectiveResolutions** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：injectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.up Nat) where 
obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Taking injective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed cochain complexes and cochain maps up to homotopy).
-/
def injectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.up ℕ) where
  obj X := (HomotopyCategory.quotient _ _).obj (injectiveResolution X).cocomplex
  map f := (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descCompHomotopy
variable {C}

/-- If `I : InjectiveResolution X`, then the chosen `(injectiveResolutions C).obj X`
is isomorphic (in the homotopy category) to `I.cocomplex`. -/
/-
**CategoryTheory.InjectiveResolution.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.InjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : CategoryTheory.HasInjectiveResoluti
ons C] →         {X : C} →           (I : CategoryTheory.InjectiveResolution X) 
→             (CategoryTheory.injectiveResolutions C).obj X ≅               (Hom
otopyCategory.quotient C (ComplexShape.up ℕ)).obj I.cocomplex
参数：I : CategoryTheory.InjectiveResolution X；CategoryTheory.injectiveResolutions 
C；HomotopyCategory.quotient C (ComplexShape.up ℕ)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
If `I : InjectiveResolution X`, then the chosen `(injectiveResolutions C).obj X`
is isomorphic (in the homotopy category) to `I.cocomplex`.
-/
def InjectiveResolution.iso {X : C} (I : InjectiveResolution X) :
    (injectiveResolutions C).obj X ≅
      (HomotopyCategory.quotient _ _).obj I.cocomplex :=
  HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.InjectiveResolution.iso_hom_naturality** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasInjectiveResolutions C] {X Y : 
C} (f : X ⟶ Y) (I : CategoryTheory.InjectiveResolution X)   (J : CategoryTheory.
InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex),   CategoryTheory.Categor
yStruct.comp (I.ι.f 0) (φ.f 0) = CategoryTheory.CategoryStruct.comp f (J.ι.f 0) 
→     CategoryTheory.CategoryStruct.comp ((CategoryTheory.injectiveResolutions C
).map f) J.iso.hom =       CategoryTheory.CategoryStruct.comp I.iso.hom ((Homoto
pyCategory.quotient C (ComplexShape.up ℕ)).map φ)
参数：f : X ⟶ Y；I : CategoryTheory.InjectiveResolution X；J : CategoryTheory.Injecti
veResolution Y；φ : I.cocomplex ⟶ J.cocomplex；I.ι.f 0；φ.f 0；J.ι.f 0；(CategoryTheo
ry.injectiveResolutions C).map f；(HomotopyCategory.quotient C (ComplexShape.up ℕ
)).map φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomotopyCategory.eq_of_homotopy`：eq_of_homotopy {C D : HomologicalComple
x V c} (f g : C ⟶ D) (h : Homotopy f g) : (quotient V c).map f = (quotient V c).
map g
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.InjectiveResolution.desc_commutes_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {Y 
Z : C} (f : Z ⟶ Y)   (I : CategoryTheory.Inj…
· 使用定理 `CategoryTheory.InjectiveResolution.homotopyEquiv_hom_ι`：homotopyEquiv_ho
m_ι {X : C} (I J : InjectiveResolution X) : I.ι ≫ (homotopyEquiv I J).hom = J.ι
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.InjectiveResolution.homotopyEquiv_hom_ι_assoc`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian 
C] {X : C}   (I J : CategoryTheory.InjectiveResolu…
· 使用引理 `HomologicalComplex.from_single_hom_ext`：from_single_hom_ext {K : Homolog
icalComplex V c} {j : ι} {A : V} {f g : (single V c j).obj A ⟶ K} (hfg : f.f j =
 g.f j) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.single₀_map_f_zero`：single₀_map_f_zero {A B : V} (f : A ⟶
 B) : ((single₀ V).map f).f 0 = f
-/
lemma InjectiveResolution.iso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    (injectiveResolutions C).map f ≫ J.iso.hom =
      I.iso.hom ≫ (HomotopyCategory.quotient _ _).map φ := by
  apply HomotopyCategory.eq_of_homotopy
  apply descHomotopy f
  all_goals aesop

@[reassoc]
/-
**CategoryTheory.InjectiveResolution.iso_inv_naturality** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasInjectiveResolutions C] {X Y : 
C} (f : X ⟶ Y) (I : CategoryTheory.InjectiveResolution X)   (J : CategoryTheory.
InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex),   CategoryTheory.Categor
yStruct.comp (I.ι.f 0) (φ.f 0) = CategoryTheory.CategoryStruct.comp f (J.ι.f 0) 
→     CategoryTheory.CategoryStruct.comp I.iso.inv ((CategoryTheory.injectiveRes
olutions C).map f) =       CategoryTheory.CategoryStruct.comp ((HomotopyCategory
.quotient C (ComplexShape.up ℕ)).map φ) J.iso.inv
参数：f : X ⟶ Y；I : CategoryTheory.InjectiveResolution X；J : CategoryTheory.Injecti
veResolution Y；φ : I.cocomplex ⟶ J.cocomplex；I.ι.f 0；φ.f 0；J.ι.f 0；(CategoryTheo
ry.injectiveResolutions C).map f；(HomotopyCategory.quotient C (ComplexShape.up ℕ
)).map φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.InjectiveResolution.iso_hom_naturality`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [i
nst_2 : CategoryTheory.HasInjectiveResoluti…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma InjectiveResolution.iso_inv_naturality {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    I.iso.inv ≫ (injectiveResolutions C).map f =
      (HomotopyCategory.quotient _ _).map φ ≫ J.iso.inv := by
  rw [← cancel_mono (J.iso).hom, Category.assoc, iso_hom_naturality f I J φ comm,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

section

variable [Abelian C] [EnoughInjectives C]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.exact_f_d** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：exact_f_d {X Y : C} (f : X ⟶ Y) : (ShortComplex.mk f (d f) (by simp)).Exac
t
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.cokernel.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`：exact_iff
_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : S₁.
Exact ↔ S₂.Exact
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
theorem exact_f_d {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk f (d f) (by simp)).Exact := by
  let α : ShortComplex.mk f (cokernel.π f) (by simp) ⟶ ShortComplex.mk f (d f) (by simp) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Injective.ι _ }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_g_is_cokernel
  apply cokernelIsCokernel

end

namespace InjectiveResolution

/-!
Our goal is to define `InjectiveResolution.of Z : InjectiveResolution Z`.
The `0`-th object in this resolution will just be `Injective.under Z`,
i.e. an arbitrarily chosen injective object with a map from `Z`.
After that, we build the `n+1`-st object as `Injective.syzygies`
applied to the previously constructed morphism,
and the map from the `n`-th object as `Injective.d`.
-/


variable [Abelian C] [EnoughInjectives C] (Z : C)

-- The construction of the injective resolution `of` would be very, very slow
-- if it were not broken into separate definitions and lemmas

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `InjectiveResolution.of`. -/
/-
**CategoryTheory.InjectiveResolution.ofCocomplex** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.InjectiveResolution`。
形式化陈述：ofCocomplex : CochainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `InjectiveResolution.of`.
-/
def ofCocomplex : CochainComplex C ℕ :=
  CochainComplex.mk' (Injective.under Z) (Injective.syzygies (Injective.ι Z))
    (Injective.d (Injective.ι Z)) fun f => ⟨_, Injective.d f, by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.InjectiveResolution.ofCocomplex_d_0_1** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.InjectiveResolution`。
形式化陈述：ofCocomplex_d_0_1 : (ofCocomplex Z).d 0 1 = d (Injective.ι Z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.mk'_d_1_0`：∀ {V : Type u} [inst : CategoryTheory.Category
.{v, u} V] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀
 : X₀ ⟶ X₁)   …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofCocomplex_d_0_1 :
    (ofCocomplex Z).d 0 1 = d (Injective.ι Z) := by
  simp [ofCocomplex]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.InjectiveResolution.ofCocomplex_exactAt_succ** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：ofCocomplex_exactAt_succ (n : Nat) : (ofCocomplex Z).ExactAt (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.exactAt_iff'`：exactAt_iff' (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ (K.sc' i j k).Exact
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CochainComplex.prev_nat_succ`：prev_nat_succ (i : Nat) : (ComplexShape.up
 Nat).prev (i + 1) = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `CochainComplex.of_d`：of_d (j : α) : of.d X d j (j + 1) = d j
· 使用定理 `CategoryTheory.ShortComplex.mk.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {X₁ X₂ X₃ : C} (f f_1 :…
· 使用定理 `CategoryTheory.exact_f_d`：exact_f_d {X Y : C} (f : X ⟶ Y) : (ShortComple
x.mk f (d f) (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
-/
lemma ofCocomplex_exactAt_succ (n : ℕ) :
    (ofCocomplex Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofCocomplex,
    CochainComplex.mk', CochainComplex.mk, CochainComplex.of_d]
  match n with
  | 0 => apply exact_f_d ((CochainComplex.mkAux _ _ _
      (d (Injective.ι Z)) (d (d (Injective.ι Z))) _ _ 0).f)
  | n + 1 => apply exact_f_d ((CochainComplex.mkAux _ _ _
      (d (Injective.ι Z)) (d (d (Injective.ι Z))) _ _ (n + 1)).f)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Injective ((ofCocomplex Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply Injective.injective_under

set_option backward.isDefEq.respectTransparency false in
/-- In any abelian category with enough injectives,
`InjectiveResolution.of Z` constructs an injective resolution of the object `Z`.
-/
irreducible_def of : InjectiveResolution Z where
  cocomplex := ofCocomplex Z
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨Injective.ι Z,
    by rw [ofCocomplex_d_0_1, cokernel.condition_assoc, zero_comp]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨exact_f_d (Injective.ι Z), by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
          (by simp [ofCocomplex])
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt]
      · apply ofCocomplex_exactAt_succ
      · apply CochainComplex.exactAt_succ_single_obj⟩

/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (Z : C) : HasInjectiveResolution Z where out := ⟨of Z⟩
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : HasInjectiveResolutions C where out _ := inferInstance

end InjectiveResolution

variable [Abelian C]

/-- Given an injective presentation `M → I`, the short complex `0 → M → I → N → 0`. -/
/-
**CategoryTheory.InjectivePresentation.shortComplex** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.InjectivePresentation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       {X : C} → CategoryTheory.InjectivePresentatio
n X → CategoryTheory.ShortComplex C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an injective presentation `M → I`, the short complex `0 → M → I → N → 0`.
-/
noncomputable abbrev InjectivePresentation.shortComplex
    {X : C} (ip : InjectivePresentation X) : ShortComplex C :=
  ShortComplex.mk ip.f (Limits.cokernel.π ip.f) (Limits.cokernel.condition ip.f)
/-
**CategoryTheory.InjectivePresentation.shortExact_shortComplex** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.InjectivePresentation`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {X : C}   (ip : CategoryTheory.InjectivePresentation X), ip.s
hortComplex.ShortExact
参数：ip : CategoryTheory.InjectivePresentation X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.exact_cokernel`：exact_cokernel {X Y : C} (f 
: X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact
· 使用定理 `CategoryTheory.InjectivePresentation.mono`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.InjectivePresentat
ion X),   CategoryTheory.Mono s…
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
-/
theorem InjectivePresentation.shortExact_shortComplex {X : C}
    (ip : InjectivePresentation X) : ip.shortComplex.ShortExact :=
  { exact := ShortComplex.exact_cokernel ip.f }

end CategoryTheory

