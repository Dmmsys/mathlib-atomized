/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison, Jakob von Raumer, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Tactic.SuppressCompilation

/-!
# Abelian categories with enough projectives have projective resolutions

## Main results
When the underlying category is abelian:
* `CategoryTheory.ProjectiveResolution.lift`: Given `P : ProjectiveResolution X` and
  `Q : ProjectiveResolution Y`, any morphism `X ⟶ Y` admits a lifting to a chain map
  `P.complex ⟶ Q.complex`. It is a lifting in the sense that `P.ι` intertwines the lift and
  the original morphism, see `CategoryTheory.ProjectiveResolution.lift_commutes`.
* `CategoryTheory.ProjectiveResolution.liftHomotopy`: Any two such lifts are homotopic.
* `CategoryTheory.ProjectiveResolution.homotopyEquiv`: Any two projective resolutions of the same
  object are homotopy equivalent.
* `CategoryTheory.projectiveResolutions`: If every object admits a projective resolution, we can
  construct a functor `projectiveResolutions C : C ⥤ HomotopyCategory C (ComplexShape.down ℕ)`.

* `CategoryTheory.exact_d_f`: `Projective.d f` and `f` are exact.
* `CategoryTheory.ProjectiveResolution.of`: Hence, starting from an epimorphism `P ⟶ X`, where `P`
  is projective, we can apply `Projective.d` repeatedly to obtain a projective resolution of `X`.
-/

@[expose] public section

suppress_compilation

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Category Limits Projective


namespace ProjectiveResolution

section

variable [HasZeroObject C] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary construction for `lift`. -/
/-
**CategoryTheory.ProjectiveResolution.liftFZero** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ProjectiveResolution`。
形式化陈述：liftFZero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : Projecti
veResolution Z) : P.complex.X 0 ⟶ Q.complex.X 0
参数：f : Y ⟶ Z；P : ProjectiveResolution Y；Q : ProjectiveResolution Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction for `lift`.
-/
def liftFZero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 :=
  Projective.factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

end

section Abelian

variable [Abelian C]

/-
**CategoryTheory.ProjectiveResolution.exact** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₀ {Z : C} (P : ProjectiveResolution Z) :
    (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary construction for `lift`. -/
/-
**CategoryTheory.ProjectiveResolution.liftFOne** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ProjectiveResolution`。
形式化陈述：liftFOne {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : Projectiv
eResolution Z) : P.complex.X 1 ⟶ Q.complex.X 1
参数：f : Y ⟶ Z；P : ProjectiveResolution Y；Q : ProjectiveResolution Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.ProjectiveResolution.exact₀`：exact₀ {Z : C} (P : Projecti
veResolution Z) : (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact

--- 原说明 ---
Auxiliary construction for `lift`.
-/
def liftFOne {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P Q) (by simp [liftFZero])

@[simp]
/-
**CategoryTheory.ProjectiveResolution.liftFOne_zero_comm** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftFOne_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q :
 ProjectiveResolution Z) : liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ 
liftFZero f P Q
参数：f : Y ⟶ Z；P : ProjectiveResolution Y；Q : ProjectiveResolution Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.ShortComplex.Exact.liftFromProjective_comp`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ProjectiveResolution.complex_d_comp_π_f_zero`：complex_d_c
omp_π_f_zero : P.complex.d 1 0 ≫ P.π.f 0 = 0
· 使用引理 `CategoryTheory.ProjectiveResolution.exact₀`：exact₀ {Z : C} (P : Projecti
veResolution Z) : (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact
-/
theorem liftFOne_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) :
    liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero f P Q := by
  apply Q.exact₀.liftFromProjective_comp

/-- Auxiliary construction for `lift`. -/
/-
**CategoryTheory.ProjectiveResolution.liftFSucc** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ProjectiveResolution`。
形式化陈述：liftFSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution
 Z) (n : Nat) (g : P.complex.X n ⟶ Q.complex.X n) (g' : P.complex.X (n + 1) ⟶ Q.
complex.X (n + 1)) (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) 
: Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2), g'' ≫ Q.complex.d (n + 2) 
(n + 1) = P.complex.d (n + 2) (n + 1) ≫ g'
参数：P : ProjectiveResolution Y；Q : ProjectiveResolution Z；n : Nat；g : P.complex.X
 n ⟶ Q.complex.X n；g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1)；w : g' ≫ Q.com
plex.d (n + 1) n = P.complex.d (n + 1) n ≫ g。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Auxiliary construction for `lift`.
-/
def liftFSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X n) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(Q.exact_succ n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
      (Q.exact_succ n).liftFromProjective_comp _ _⟩

/-- A morphism in `C` lifts to a chain map between projective resolutions. -/
/-
**CategoryTheory.ProjectiveResolution.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ProjectiveResolution`。
形式化陈述：lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveRes
olution Z) : P.complex ⟶ Q.complex
参数：f : Y ⟶ Z；P : ProjectiveResolution Y；Q : ProjectiveResolution Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.ProjectiveResolution.liftFOne_zero_comm`：liftFOne_zero_co
mm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution 
Z) : liftFOne f P Q ≫ Q.complex.d 1 0 = P.co…

--- 原说明 ---
A morphism in `C` lifts to a chain map between projective resolutions.
-/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftFZero f _ _) (liftFOne f _ _) (liftFOne_zero_comm f P Q)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc P Q n g g' w).1, (liftFSucc P Q n g g' w).2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution maps intertwine the lift of a morphism and that morphism. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.lift_commutes** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ProjectiveResolution`。
形式化陈述：lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : Proj
ectiveResolution Z) : lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f
参数：f : Y ⟶ Z；P : ProjectiveResolution Y；Q : ProjectiveResolution Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `HomologicalComplex.to_single_hom_ext`：to_single_hom_ext {K : Homological
Complex V c} {j : ι} {A : V} {f g : K ⟶ (single V c j).obj A} (hfg : f.f j = g.f
 j) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Projective.factorThru_comp`：factorThru_comp {P X E : C} [
Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : factorThru f e ≫ e = f
· 使用引理 `ChainComplex.single₀_map_f_zero`：single₀_map_f_zero {A B : V} (f : A ⟶ B
) : ((single₀ V).map f).f 0 = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The resolution maps intertwine the lift of a morphism and that morphism.
-/
theorem lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) : lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  ext
  simp [lift, liftFZero, liftFOne]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.lift_commutes_zero** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：lift_commutes_zero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q :
 ProjectiveResolution Z) : (lift f P Q).f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f
参数：f : Y ⟶ Z；P : ProjectiveResolution Y；Q : ProjectiveResolution Z。
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
· 使用定理 `CategoryTheory.ProjectiveResolution.lift_commutes`：lift_commutes {Y Z : 
C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) : lift 
f P Q ≫ Q.π = P.π ≫ (ChainComplex.singl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ChainComplex.single₀_map_f_zero`：single₀_map_f_zero {A B : V} (f : A ⟶ B
) : ((single₀ V).map f).f 0 = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_commutes_zero {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    (lift f P Q).f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f :=
  (HomologicalComplex.congr_hom (lift_commutes f P Q) 0).trans (by simp)

/-- An auxiliary definition for `liftHomotopyZero`. -/
/-
**CategoryTheory.ProjectiveResolution.liftHomotopyZeroZero** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftHomotopyZeroZero {Y Z : C} {P : ProjectiveResolution Y} {Q : Projectiv
eResolution Z} (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 0 
⟶ Q.complex.X 1
参数：f : P.complex ⟶ Q.complex；comm : f ≫ Q.π = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.ProjectiveResolution.exact₀`：exact₀ {Z : C} (P : Projecti
veResolution Z) : (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact

--- 原说明 ---
An auxiliary definition for `liftHomotopyZero`.
-/
def liftHomotopyZeroZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 0 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.liftHomotopyZeroZero_comp** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftHomotopyZeroZero_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : Proj
ectiveResolution Z} (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : liftHomot
opyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0
参数：f : P.complex ⟶ Q.complex；comm : f ≫ Q.π = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ShortComplex.Exact.liftFromProjective_comp`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `CategoryTheory.ProjectiveResolution.complex_d_comp_π_f_zero`：complex_d_c
omp_π_f_zero : P.complex.d 1 0 ≫ P.π.f 0 = 0
· 使用引理 `CategoryTheory.ProjectiveResolution.exact₀`：exact₀ {Z : C} (P : Projecti
veResolution Z) : (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact
-/
lemma liftHomotopyZeroZero_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 :=
  Q.exact₀.liftFromProjective_comp _ _

/-- An auxiliary definition for `liftHomotopyZero`. -/
/-
**CategoryTheory.ProjectiveResolution.liftHomotopyZeroOne** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftHomotopyZeroOne {Y Z : C} {P : ProjectiveResolution Y} {Q : Projective
Resolution Z} (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 1 ⟶
 Q.complex.X 2
参数：f : P.complex ⟶ Q.complex；comm : f ≫ Q.π = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
An auxiliary definition for `liftHomotopyZero`.
-/
def liftHomotopyZeroOne {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    P.complex.X 1 ⟶ Q.complex.X 2 :=
  (Q.exact_succ 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
              liftHomotopyZeroZero_comp, sub_self])

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.liftHomotopyZeroOne_comp** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftHomotopyZeroOne_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : Proje
ctiveResolution Z} (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : liftHomoto
pyZeroOne f comm ≫ Q.complex.d 2 1 = f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZ
ero f comm
参数：f : P.complex ⟶ Q.complex；comm : f ≫ Q.π = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ShortComplex.Exact.liftFromProjective_comp`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用引理 `CategoryTheory.ProjectiveResolution.exact_succ`：exact_succ (n : Nat) : (
ShortComplex.mk _ _ (P.complex.d_comp_d (n + 2) (n + 1) n)).Exact
-/
lemma liftHomotopyZeroOne_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroOne f comm ≫ Q.complex.d 2 1 =
      f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm :=
  (Q.exact_succ 0).liftFromProjective_comp _ _

/-- An auxiliary definition for `liftHomotopyZero`. -/
/-
**CategoryTheory.ProjectiveResolution.liftHomotopyZeroSucc** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftHomotopyZeroSucc {Y Z : C} {P : ProjectiveResolution Y} {Q : Projectiv
eResolution Z} (f : P.complex ⟶ Q.complex) (n : Nat) (g : P.complex.X n ⟶ Q.comp
lex.X (n + 1)) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2)) (w : f.f (n + 1)
 = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) : P.complex.X (
n + 2) ⟶ Q.complex.X (n + 3)
参数：f : P.complex ⟶ Q.complex；n : Nat；g : P.complex.X n ⟶ Q.complex.X (n + 1)；g' 
: P.complex.X (n + 1) ⟶ Q.complex.X (n + 2)；w : f.f (n + 1) = P.complex.d (n + 1
) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
An auxiliary definition for `liftHomotopyZero`.
-/
def liftHomotopyZeroSucc {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    P.complex.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  (Q.exact_succ (n + 1)).liftFromProjective (f.f (n + 2) - P.complex.d _ _ ≫ g') (by simp [w])

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.liftHomotopyZeroSucc_comp** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftHomotopyZeroSucc_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : Proj
ectiveResolution Z} (f : P.complex ⟶ Q.complex) (n : Nat) (g : P.complex.X n ⟶ Q
.complex.X (n + 1)) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2)) (w : f.f (n
 + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) : liftHomo
topyZeroSucc f n g g' w ≫ Q.complex.d (n + 3) (n + 2) = f.f (n + 2) - P.complex.
d _ _ ≫ g'
参数：f : P.complex ⟶ Q.complex；n : Nat；g : P.complex.X n ⟶ Q.complex.X (n + 1)；g' 
: P.complex.X (n + 1) ⟶ Q.complex.X (n + 2)；w : f.f (n + 1) = P.complex.d (n + 1
) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ShortComplex.Exact.liftFromProjective_comp`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用引理 `CategoryTheory.ProjectiveResolution.exact_succ`：exact_succ (n : Nat) : (
ShortComplex.mk _ _ (P.complex.d_comp_d (n + 2) (n + 1) n)).Exact
-/
lemma liftHomotopyZeroSucc_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    liftHomotopyZeroSucc f n g g' w ≫ Q.complex.d (n + 3) (n + 2) =
      f.f (n + 2) - P.complex.d _ _ ≫ g' :=
  (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

/-- Any lift of the zero morphism is homotopic to zero. -/
/-
**CategoryTheory.ProjectiveResolution.liftHomotopyZero** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftHomotopyZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveRes
olution Z} (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : Homotopy f 0
参数：f : P.complex ⟶ Q.complex；comm : f ≫ Q.π = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Any lift of the zero morphism is homotopic to zero.
-/
def liftHomotopyZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by simp)
    (liftHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by simp⟩

/-- Two lifts of the same morphism are homotopic. -/
/-
**CategoryTheory.ProjectiveResolution.liftHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ProjectiveResolution`。
形式化陈述：liftHomotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : Proje
ctiveResolution Z} (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (Chai
nComplex.single₀ C).map f) (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).ma
p f) : Homotopy g h
参数：f : Y ⟶ Z；g h : P.complex ⟶ Q.complex；g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.
single₀ C).map f；h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Two lifts of the same morphism are homotopic.
-/
def liftHomotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (liftHomotopyZero _ (by simp [g_comm, h_comm]))

/-- The lift of the identity morphism is homotopic to the identity chain map. -/
/-
**CategoryTheory.ProjectiveResolution.liftIdHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ProjectiveResolution`。
形式化陈述：liftIdHomotopy (X : C) (P : ProjectiveResolution X) : Homotopy (lift (𝟙 X)
 P P) (𝟙 P.complex)
参数：X : C；P : ProjectiveResolution X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The lift of the identity morphism is homotopic to the identity chain map.
-/
def liftIdHomotopy (X : C) (P : ProjectiveResolution X) :
    Homotopy (lift (𝟙 X) P P) (𝟙 P.complex) := by
  apply liftHomotopy (𝟙 X) <;> simp

/-- The lift of a composition is homotopic to the composition of the lifts. -/
/-
**CategoryTheory.ProjectiveResolution.liftCompHomotopy** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ProjectiveResolution`。
形式化陈述：liftCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolu
tion X) (Q : ProjectiveResolution Y) (R : ProjectiveResolution Z) : Homotopy (li
ft (f ≫ g) P R) (lift f P Q ≫ lift g Q R)
参数：f : X ⟶ Y；g : Y ⟶ Z；P : ProjectiveResolution X；Q : ProjectiveResolution Y；R :
 ProjectiveResolution Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The lift of a composition is homotopic to the composition of the lifts.
-/
def liftCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolution X)
    (Q : ProjectiveResolution Y) (R : ProjectiveResolution Z) :
    Homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) := by
  apply liftHomotopy (f ≫ g) <;> simp

-- We don't care about the actual definitions of these homotopies.
/-- Any two projective resolutions are homotopy equivalent. -/
/-
**CategoryTheory.ProjectiveResolution.homotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ProjectiveResolution`。
形式化陈述：homotopyEquiv {X : C} (P Q : ProjectiveResolution X) : HomotopyEquiv P.com
plex Q.complex where hom
参数：P Q : ProjectiveResolution X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Any two projective resolutions are homotopy equivalent.
-/
def homotopyEquiv {X : C} (P Q : ProjectiveResolution X) :
    HomotopyEquiv P.complex Q.complex where
  hom := lift (𝟙 X) P Q
  inv := lift (𝟙 X) Q P
  homotopyHomInvId := (liftCompHomotopy (𝟙 X) (𝟙 X) P Q P).symm.trans <| by
    simpa [id_comp] using liftIdHomotopy _ _
  homotopyInvHomId := (liftCompHomotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans <| by
    simpa [id_comp] using liftIdHomotopy _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.homotopyEquiv_hom_** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homotopyEquiv_hom_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).hom ≫ Q.π = P.π := by simp [homotopyEquiv]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.homotopyEquiv_inv_** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homotopyEquiv_inv_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).inv ≫ P.π = Q.π := by simp [homotopyEquiv]

end Abelian

end ProjectiveResolution

/-- An arbitrarily chosen projective resolution of an object. -/
/-
**CategoryTheory.projectiveResolution** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：projectiveResolution (Z : C) [HasZeroObject C] [HasZeroMorphisms C] [HasPr
ojectiveResolution Z] : ProjectiveResolution Z
参数：Z : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasProjectiveResolution.out`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroObject C}   
{inst_2 : CategoryTheory.Limits.…

--- 原说明 ---
An arbitrarily chosen projective resolution of an object.
-/
abbrev projectiveResolution (Z : C) [HasZeroObject C]
    [HasZeroMorphisms C] [HasProjectiveResolution Z] :
    ProjectiveResolution Z :=
  (HasProjectiveResolution.out (Z := Z)).some

variable (C)
variable [Abelian C]

section
variable [HasProjectiveResolutions C]

/-- Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
/-
**CategoryTheory.projectiveResolutions** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：projectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.down Nat) whe
re obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
def projectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.down ℕ) where
  obj X := (HomotopyCategory.quotient _ _).obj (projectiveResolution X).complex
  map f := (HomotopyCategory.quotient _ _).map (ProjectiveResolution.lift f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftCompHomotopy

variable {C}

/-- If `P : ProjectiveResolution X`, then the chosen `(projectiveResolutions C).obj X`
is isomorphic (in the homotopy category) to `P.complex`. -/
/-
**CategoryTheory.ProjectiveResolution.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ProjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : CategoryTheory.HasProjectiveResolut
ions C] →         {X : C} →           (P : CategoryTheory.ProjectiveResolution X
) →             (CategoryTheory.projectiveResolutions C).obj X ≅               (
HomotopyCategory.quotient C (ComplexShape.down ℕ)).obj P.complex
参数：P : CategoryTheory.ProjectiveResolution X；CategoryTheory.projectiveResolution
s C；HomotopyCategory.quotient C (ComplexShape.down ℕ)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
If `P : ProjectiveResolution X`, then the chosen `(projectiveResolutions C).obj 
X`
is isomorphic (in the homotopy category) to `P.complex`.
-/
def ProjectiveResolution.iso {X : C} (P : ProjectiveResolution X) :
    (projectiveResolutions C).obj X ≅
      (HomotopyCategory.quotient _ _).obj P.complex :=
  HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.iso_inv_naturality** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasProjectiveResolutions C] {X Y :
 C} (f : X ⟶ Y) (P : CategoryTheory.ProjectiveResolution X)   (Q : CategoryTheor
y.ProjectiveResolution Y) (φ : P.complex ⟶ Q.complex),   CategoryTheory.Category
Struct.comp (φ.f 0) (Q.π.f 0) = CategoryTheory.CategoryStruct.comp (P.π.f 0) f →
     CategoryTheory.CategoryStruct.comp P.iso.inv ((CategoryTheory.projectiveRes
olutions C).map f) =       CategoryTheory.CategoryStruct.comp ((HomotopyCategory
.quotient C (ComplexShape.down ℕ)).map φ) Q.iso.inv
参数：f : X ⟶ Y；P : CategoryTheory.ProjectiveResolution X；Q : CategoryTheory.Projec
tiveResolution Y；φ : P.complex ⟶ Q.complex；φ.f 0；Q.π.f 0；P.π.f 0；(CategoryTheory
.projectiveResolutions C).map f；(HomotopyCategory.quotient C (ComplexShape.down 
ℕ)).map φ。
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
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ProjectiveResolution.lift_commutes`：lift_commutes {Y Z : 
C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) : lift 
f P Q ≫ Q.π = P.π ≫ (ChainComplex.singl…
· 使用定理 `CategoryTheory.ProjectiveResolution.homotopyEquiv_inv_π_assoc`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian
 C] {X : C}   (P Q : CategoryTheory.ProjectiveResol…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ProjectiveResolution.homotopyEquiv_inv_π`：homotopyEquiv_i
nv_π {X : C} (P Q : ProjectiveResolution X) : (homotopyEquiv P Q).inv ≫ P.π = Q.
π
· 使用引理 `HomologicalComplex.to_single_hom_ext`：to_single_hom_ext {K : Homological
Complex V c} {j : ι} {A : V} {f g : K ⟶ (single V c j).obj A} (hfg : f.f j = g.f
 j) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ChainComplex.single₀_map_f_zero`：single₀_map_f_zero {A B : V} (f : A ⟶ B
) : ((single₀ V).map f).f 0 = f
-/
lemma ProjectiveResolution.iso_inv_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    P.iso.inv ≫ (projectiveResolutions C).map f =
      (HomotopyCategory.quotient _ _).map φ ≫ Q.iso.inv := by
  apply HomotopyCategory.eq_of_homotopy
  apply liftHomotopy f
  all_goals
    cat_disch

@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.iso_hom_naturality** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.HasProjectiveResolutions C] {X Y :
 C} (f : X ⟶ Y) (P : CategoryTheory.ProjectiveResolution X)   (Q : CategoryTheor
y.ProjectiveResolution Y) (φ : P.complex ⟶ Q.complex),   CategoryTheory.Category
Struct.comp (φ.f 0) (Q.π.f 0) = CategoryTheory.CategoryStruct.comp (P.π.f 0) f →
     CategoryTheory.CategoryStruct.comp ((CategoryTheory.projectiveResolutions C
).map f) Q.iso.hom =       CategoryTheory.CategoryStruct.comp P.iso.hom ((Homoto
pyCategory.quotient C (ComplexShape.down ℕ)).map φ)
参数：f : X ⟶ Y；P : CategoryTheory.ProjectiveResolution X；Q : CategoryTheory.Projec
tiveResolution Y；φ : P.complex ⟶ Q.complex；φ.f 0；Q.π.f 0；P.π.f 0；(CategoryTheory
.projectiveResolutions C).map f；(HomotopyCategory.quotient C (ComplexShape.down 
ℕ)).map φ。
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
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.ProjectiveResolution.iso_inv_naturality_assoc`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian 
C]   [inst_2 : CategoryTheory.HasProjectiveResolut…
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
lemma ProjectiveResolution.iso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    (projectiveResolutions C).map f ≫ Q.iso.hom =
      P.iso.hom ≫ (HomotopyCategory.quotient _ _).map φ := by
  rw [← cancel_epi (P.iso).inv, iso_inv_naturality_assoc f P Q φ comm,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]

end

variable [EnoughProjectives C]

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-
**CategoryTheory.exact_d_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：exact_d_f {X Y : C} (f : X ⟶ Y) : (ShortComplex.mk (d f) f (by simp)).Exac
t
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`：exact_iff
_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : S₁.
Exact ↔ S₂.Exact
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
theorem exact_d_f {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (d f) f (by simp)).Exact := by
  let α : ShortComplex.mk (d f) f (by simp) ⟶ ShortComplex.mk (kernel.ι f) f (by simp) :=
    { τ₁ := Projective.π _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_f_is_kernel
  apply kernelIsKernel

namespace ProjectiveResolution

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `Projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `Projective.syzygies`
applied to the previously constructed morphism,
and the map from the `n`-th object as `Projective.d`.
-/

variable {C}
variable (Z : C)

-- The construction of the projective resolution `of` would be very, very slow
-- if it were not broken into separate definitions and lemmas

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `ProjectiveResolution.of`. -/
/-
**CategoryTheory.ProjectiveResolution.ofComplex** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ProjectiveResolution`。
形式化陈述：ofComplex : ChainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ProjectiveResolution.of`.
-/
def ofComplex : ChainComplex C ℕ :=
  ChainComplex.mk' (Projective.over Z) (Projective.syzygies (Projective.π Z))
    (Projective.d (Projective.π Z)) (fun f => ⟨_, Projective.d f, by simp⟩)
/-
**CategoryTheory.ProjectiveResolution.ofComplex_d_1_0** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ProjectiveResolution`。
形式化陈述：ofComplex_d_1_0 : (ofComplex Z).d 1 0 = d (Projective.π Z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChainComplex.mk'_d_1_0`：∀ {V : Type u} [inst : CategoryTheory.Category.{
v, u} V] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ :
 X₁ ⟶ X₀)   …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofComplex_d_1_0 :
    (ofComplex Z).d 1 0 = d (Projective.π Z) := by
  simp [ofComplex]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ProjectiveResolution.ofComplex_exactAt_succ** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：ofComplex_exactAt_succ (n : Nat) : (ofComplex Z).ExactAt (n + 1)
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
· 使用定理 `ChainComplex.prev`：prev (α : Type*) [AddRightCancelSemigroup α] [One α] 
(i : α) : (ComplexShape.down α).prev i = i + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ChainComplex.next_nat_succ`：next_nat_succ (i : Nat) : (ComplexShape.down
 Nat).next (i + 1) = i
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `ChainComplex.of_d`：of_d (j : α) : of.d X d (j + 1) j = d j
· 使用定理 `CategoryTheory.ShortComplex.mk.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {X₁ X₂ X₃ : C} (f f_1 :…
· 使用定理 `CategoryTheory.exact_d_f`：exact_d_f {X Y : C} (f : X ⟶ Y) : (ShortComple
x.mk (d f) f (by simp)).Exact
-/
lemma ofComplex_exactAt_succ (n : ℕ) :
    (ofComplex Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ofComplex,
    ChainComplex.mk', ChainComplex.mk, ChainComplex.of_d]
  -- TODO: this should just be apply exact_d_f so something is missing
  match n with
  | 0 => apply exact_d_f
  | n + 1 => apply exact_d_f

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Projective ((ofComplex Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply Projective.projective_over

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projective resolution of the object `Z`.
-/
irreducible_def of : ProjectiveResolution Z where
  complex := ofComplex Z
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨Projective.π Z, by
          rw [ofComplex_d_1_0, assoc, kernel.condition, comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨exact_d_f (Projective.π Z), by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [ofComplex]) (by simp)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply ofComplex_exactAt_succ
      · apply ChainComplex.exactAt_succ_single_obj⟩

/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (Z : C) : HasProjectiveResolution Z where out := ⟨of Z⟩
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : HasProjectiveResolutions C where out _ := inferInstance

end ProjectiveResolution

end CategoryTheory

