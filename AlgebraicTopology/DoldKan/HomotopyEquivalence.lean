/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!

# The normalized Moore complex and the alternating face map complex are homotopy equivalent

In this file, when the category `A` is abelian, we obtain the homotopy equivalence
`homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` between the
normalized Moore complex and the alternating face map complex of a simplicial object in `A`.

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Preadditive Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] (X : SimplicialObject C)

/-- Inductive construction of homotopies from `P q` to `𝟙 _` -/
/-
**AlgebraicTopology.DoldKan.homotopyPToId** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTo
pology.DoldKan`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       (X : CategoryTheory.SimplicialObjec
t C) →         (q : ℕ) →           Homotopy (AlgebraicTopology.DoldKan.P q)     
        (CategoryTheory.CategoryStruct.id (AlgebraicTopology.AlternatingFaceMapC
omplex.obj X))
参数：X : CategoryTheory.SimplicialObject C；q : ℕ；AlgebraicTopology.DoldKan.P q；Cat
egoryTheory.CategoryStruct.id (AlgebraicTopology.AlternatingFaceMapComplex.obj X
)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inductive construction of homotopies from `P q` to `𝟙 _`
-/
noncomputable def homotopyPToId : ∀ q : ℕ, Homotopy (P q : K[X] ⟶ _) (𝟙 _)
  | 0 => Homotopy.refl _
  | q + 1 => by
    refine
      Homotopy.trans (Homotopy.ofEq ?_)
        (Homotopy.trans
          (Homotopy.add (homotopyPToId q) (Homotopy.compLeft (homotopyHσToZero q) (P q)))
          (Homotopy.ofEq ?_))
    · simp only [P_succ, comp_add, comp_id]
    · simp only [add_zero, comp_zero]

/-- The complement projection `Q q` to `P q` is homotopic to zero. -/
/-
**AlgebraicTopology.DoldKan.homotopyQToZero** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Topology.DoldKan`。
形式化陈述：homotopyQToZero (q : Nat) : Homotopy (Q q : K[X] ⟶ _) 0
参数：q : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement projection `Q q` to `P q` is homotopic to zero.
-/
def homotopyQToZero (q : ℕ) : Homotopy (Q q : K[X] ⟶ _) 0 :=
  Homotopy.equivSubZero.toFun (homotopyPToId X q).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicTopology.DoldKan.homotopyPToId_eventually_constant** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：homotopyPToId_eventually_constant {q n : Nat} (hqn : n < q) : ((homotopyPT
oId X (q + 1)).hom n (n + 1) : X _⦋n⦌ ⟶ X _⦋n + 1⦌) = (homotopyPToId X q).hom n 
(n + 1)
参数：hqn : n < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homotopy.trans_hom`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory
.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape 
ι} {C D …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Homotopy.ofEq_hom`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.
Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι
} {C D …
· 使用定理 `Homotopy.add_hom`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.C
ategory.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexShape ι}
 {C D …
· 使用定理 `Homotopy.compLeft_hom`：∀ {ι : Type u_1} {V : Type u} [inst : CategoryThe
ory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : ComplexSha
pe ι} {C D …
· 使用定理 `Homotopy.nullHomotopy'_hom`：∀ {ι : Type u_1} {V : Type u} [inst : Catego
ryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   {c : Compl
exShape ι} {C D …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `ComplexShape.down_Rel`：∀ (α : Type u_2) [inst : Add α] [inst_1 : IsRight
CancelAdd α] [inst_2 : One α] (i j : α),   (ComplexShape.down α).Rel i j = (j + 
1 = i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicTopology.DoldKan.hσ'_eq_zero`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {X : Cat
egoryTheory.SimplicialObjec…
· 使用定理 `AlgebraicTopology.DoldKan.c_mk`：c_mk (i j : Nat) (h : j + 1 = i) : c.Rel
 i j
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem homotopyPToId_eventually_constant {q n : ℕ} (hqn : n < q) :
    ((homotopyPToId X (q + 1)).hom n (n + 1) : X _⦋n⦌ ⟶ X _⦋n + 1⦌) =
      (homotopyPToId X q).hom n (n + 1) := by
  simp only [homotopyHσToZero, AlternatingFaceMapComplex.obj_X, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, add_zero,
    Homotopy.nullHomotopy'_hom, ComplexShape.down_Rel, hσ'_eq_zero hqn (c_mk (n + 1) n rfl),
    dite_eq_ite, ite_self, comp_zero, zero_add, homotopyPToId]

/-- Construction of the homotopy from `PInfty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all `q` -/
@[simps]
/-
**AlgebraicTopology.DoldKan.homotopyPInftyToId** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicTopology.DoldKan`。
形式化陈述：homotopyPInftyToId : Homotopy (PInfty : K[X] ⟶ _) (𝟙 _) where hom i j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construction of the homotopy from `PInfty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all `q`
-/
def homotopyPInftyToId : Homotopy (PInfty : K[X] ⟶ _) (𝟙 _) where
  hom i j := (homotopyPToId X (j + 1)).hom i j
  zero i j hij := Homotopy.zero _ i j hij
  comm n := by
    rcases n with _ | n
    · simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        PInfty_f, P_f_0_eq, zero_add] using (homotopyPToId X 2).comm 0
    · simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
          HomologicalComplex.id_f, PInfty_f, ← P_is_eventually_constant (le_refl <| n + 1),
          homotopyPToId_eventually_constant X (Nat.lt_add_one (Nat.succ n)),
          Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        using (homotopyPToId X (n + 2)).comm (n + 1)


/-- The inclusion of the Moore complex in the alternating face map complex
is a homotopy equivalence -/
@[simps]
/-
**AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMa
pComplex** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldKan`。
形式化陈述：homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex {A : Type*} [
Category* A] [Abelian A] {Y : SimplicialObject A} : HomotopyEquiv ((normalizedMo
oreComplex A).obj Y) ((alternatingFaceMapComplex A).obj Y) where hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionO
fMooreComplexMap`：PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap
 (X : SimplicialObject A) : PInftyToNormalizedMooreComplex X ≫ inclusionOfMoor…

--- 原说明 ---
The inclusion of the Moore complex in the alternating face map complex
is a homotopy equivalence
-/
def homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex {A : Type*} [Category* A]
    [Abelian A] {Y : SimplicialObject A} :
    HomotopyEquiv ((normalizedMooreComplex A).obj Y) ((alternatingFaceMapComplex A).obj Y) where
  hom := inclusionOfMooreComplexMap Y
  inv := PInftyToNormalizedMooreComplex Y
  homotopyHomInvId := Homotopy.ofEq (splitMonoInclusionOfMooreComplexMap Y).id
  homotopyInvHomId := Homotopy.trans
      (Homotopy.ofEq (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y))
      (homotopyPInftyToId Y)

end DoldKan

end AlgebraicTopology

