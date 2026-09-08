/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Projections
public import Mathlib.CategoryTheory.Idempotents.FunctorCategories
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!

# Construction of the projection `PInfty` for the Dold-Kan correspondence

In this file, we construct the projection `PInfty : K[X] ⟶ K[X]` by passing
to the limit the projections `P q` defined in `Projections.lean`. This
projection is a critical tool in this formalisation of the Dold-Kan correspondence,
because in the case of abelian categories, `PInfty` corresponds to the
projection on the normalized Moore subcomplex, with kernel the degenerate subcomplex.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject CategoryTheory.Idempotents Opposite Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X : SimplicialObject C}

/-
**AlgebraicTopology.DoldKan.P_is_eventually_constant** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicTopology.DoldKan`。
形式化陈述：P_is_eventually_constant {q n : Nat} (hqn : n <= q) : ((P (q + 1)).f n : X
 _⦋n⦌ ⟶ _) = (P q).f n
参数：hqn : n <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicTopology.DoldKan.P_f_0_eq`：P_f_0_eq (q : Nat) : ((P q).f 0 : X 
_⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.comp_Hσ_eq_zero`：comp_Hσ_eq_
zero {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) (hqn :
 n < q) : φ ≫ (Hσ q).f (n + 1) = 0
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.of_P`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {X : CategoryTheory.SimplicialObjec…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
-/
theorem P_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
    ((P (q + 1)).f n : X _⦋n⦌ ⟶ _) = (P q).f n := by
  cases n with
  | zero => simp only [P_f_0_eq]
  | succ n =>
    simp only [P_succ, comp_add, comp_id, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      add_eq_left]
    exact (HigherFacesVanish.of_P q n).comp_Hσ_eq_zero (Nat.succ_le_iff.mp hqn)
/-
**AlgebraicTopology.DoldKan.Q_is_eventually_constant** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicTopology.DoldKan`。
形式化陈述：Q_is_eventually_constant {q n : Nat} (hqn : n <= q) : ((Q (q + 1)).f n : X
 _⦋n⦌ ⟶ _) = (Q q).f n
参数：hqn : n <= q。
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
· 使用定理 `AlgebraicTopology.DoldKan.P_is_eventually_constant`：P_is_eventually_cons
tant {q n : Nat} (hqn : n <= q) : ((P (q + 1)).f n : X _⦋n⦌ ⟶ _) = (P q).f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Q_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
    ((Q (q + 1)).f n : X _⦋n⦌ ⟶ _) = (Q q).f n := by
  simp only [Q, HomologicalComplex.sub_f_apply, P_is_eventually_constant hqn]

/-- The endomorphism `PInfty : K[X] ⟶ K[X]` obtained from the `P q` by passing to the limit. -/
/-
**AlgebraicTopology.DoldKan.PInfty** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.
DoldKan`。
形式化陈述：PInfty : K[X] ⟶ K[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The endomorphism `PInfty : K[X] ⟶ K[X]` obtained from the `P q` by passing to th
e limit.
-/
noncomputable def PInfty : K[X] ⟶ K[X] :=
  ChainComplex.ofHom (fun n => ((P n).f n : X _⦋n⦌ ⟶ _)) fun n => by
    simpa only [← P_is_eventually_constant (show n ≤ n by rfl),
      AlternatingFaceMapComplex.obj_d_eq] using (P (n + 1) : K[X] ⟶ _).comm (n + 1) n

/-- The endomorphism `QInfty : K[X] ⟶ K[X]` obtained from the `Q q` by passing to the limit. -/
/-
**AlgebraicTopology.DoldKan.QInfty** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.
DoldKan`。
形式化陈述：QInfty : K[X] ⟶ K[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The endomorphism `QInfty : K[X] ⟶ K[X]` obtained from the `Q q` by passing to th
e limit.
-/
noncomputable def QInfty : K[X] ⟶ K[X] :=
  𝟙 _ - PInfty

@[simp]
/-
**AlgebraicTopology.DoldKan.PInfty_f_0** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopol
ogy.DoldKan`。
形式化陈述：PInfty_f_0 : (PInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem PInfty_f_0 : (PInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _ := rfl
/-
**AlgebraicTopology.DoldKan.PInfty_f** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolog
y.DoldKan`。
形式化陈述：PInfty_f (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (P n).f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem PInfty_f (n : ℕ) : (PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (P n).f n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicTopology.DoldKan.QInfty_f_0** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopol
ogy.DoldKan`。
形式化陈述：QInfty_f_0 : (QInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem QInfty_f_0 : (QInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0 := by
  dsimp [QInfty]
  simp only [sub_self]
/-
**AlgebraicTopology.DoldKan.QInfty_f** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolog
y.DoldKan`。
形式化陈述：QInfty_f (n : Nat) : (QInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (Q n).f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem QInfty_f (n : ℕ) : (QInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (Q n).f n :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInfty_f_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicTopology.DoldKan`。
形式化陈述：PInfty_f_naturality (n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) : f.a
pp (op ⦋n⦌) ≫ PInfty.f n = PInfty.f n ≫ f.app (op ⦋n⦌)
参数：n : Nat；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.P_f_naturality`：P_f_naturality (q n : Nat) {X 
Y : SimplicialObject C} (f : X ⟶ Y) : f.app (op ⦋n⦌) ≫ (P q).f n = (P q).f n ≫ f
.app (op ⦋n⦌)

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem PInfty_f_naturality (n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ PInfty.f n = PInfty.f n ≫ f.app (op ⦋n⦌) :=
  P_f_naturality n n f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.QInfty_f_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicTopology.DoldKan`。
形式化陈述：QInfty_f_naturality (n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) : f.a
pp (op ⦋n⦌) ≫ QInfty.f n = QInfty.f n ≫ f.app (op ⦋n⦌)
参数：n : Nat；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.Q_f_naturality`：Q_f_naturality (q n : Nat) {X 
Y : SimplicialObject C} (f : X ⟶ Y) : f.app (op ⦋n⦌) ≫ (Q q).f n = (Q q).f n ≫ f
.app (op ⦋n⦌)

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem QInfty_f_naturality (n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ QInfty.f n = QInfty.f n ≫ f.app (op ⦋n⦌) :=
  Q_f_naturality n n f

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInfty_f_idem** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTo
pology.DoldKan`。
形式化陈述：PInfty_f_idem (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.
f n
参数：n : Nat。
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
· 使用定理 `AlgebraicTopology.DoldKan.P_f_idem`：P_f_idem (q n : Nat) : ((P q).f n : 
X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PInfty_f_idem (n : ℕ) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n := by
  simp only [PInfty_f, P_f_idem]

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInfty_idem** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopo
logy.DoldKan`。
形式化陈述：PInfty_idem : (PInfty : K[X] ⟶ _) ≫ PInfty = PInfty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f_idem`：PInfty_f_idem (n : Nat) : (PInf
ty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n
-/
theorem PInfty_idem : (PInfty : K[X] ⟶ _) ≫ PInfty = PInfty := by
  ext n
  exact PInfty_f_idem n

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.QInfty_f_idem** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTo
pology.DoldKan`。
形式化陈述：QInfty_f_idem (n : Nat) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = QInfty.
f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.Q_f_idem`：Q_f_idem (q n : Nat) : ((Q q).f n : 
X _⦋n⦌ ⟶ _) ≫ (Q q).f n = (Q q).f n
-/
theorem QInfty_f_idem (n : ℕ) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = QInfty.f n :=
  Q_f_idem _ _

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.QInfty_idem** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopo
logy.DoldKan`。
形式化陈述：QInfty_idem : (QInfty : K[X] ⟶ _) ≫ QInfty = QInfty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.QInfty_f_idem`：QInfty_f_idem (n : Nat) : (QInf
ty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = QInfty.f n
-/
theorem QInfty_idem : (QInfty : K[X] ⟶ _) ≫ QInfty = QInfty := by
  ext n
  exact QInfty_f_idem n

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInfty_f_comp_QInfty_f** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicTopology.DoldKan`。
形式化陈述：PInfty_f_comp_QInfty_f (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n 
= 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f_idem`：PInfty_f_idem (n : Nat) : (PInf
ty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PInfty_f_comp_QInfty_f (n : ℕ) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = 0 := by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, comp_id,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInfty_comp_QInfty** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicTopology.DoldKan`。
形式化陈述：PInfty_comp_QInfty : (PInfty : K[X] ⟶ _) ≫ QInfty = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f_comp_QInfty_f`：PInfty_f_comp_QInfty_f
 (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = 0
-/
theorem PInfty_comp_QInfty : (PInfty : K[X] ⟶ _) ≫ QInfty = 0 := by
  ext n
  apply PInfty_f_comp_QInfty_f

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.QInfty_f_comp_PInfty_f** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicTopology.DoldKan`。
形式化陈述：QInfty_f_comp_PInfty_f (n : Nat) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n 
= 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f_idem`：PInfty_f_idem (n : Nat) : (PInf
ty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem QInfty_f_comp_PInfty_f (n : ℕ) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = 0 := by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, sub_comp, id_comp,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.QInfty_comp_PInfty** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicTopology.DoldKan`。
形式化陈述：QInfty_comp_PInfty : (QInfty : K[X] ⟶ _) ≫ PInfty = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.QInfty_f_comp_PInfty_f`：QInfty_f_comp_PInfty_f
 (n : Nat) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = 0
-/
theorem QInfty_comp_PInfty : (QInfty : K[X] ⟶ _) ≫ PInfty = 0 := by
  ext n
  apply QInfty_f_comp_PInfty_f

@[simp]
/-
**AlgebraicTopology.DoldKan.PInfty_add_QInfty** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icTopology.DoldKan`。
形式化陈述：PInfty_add_QInfty : (PInfty : K[X] ⟶ _) + QInfty = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PInfty_add_QInfty : (PInfty : K[X] ⟶ _) + QInfty = 𝟙 _ := by
  dsimp only [QInfty]
  simp only [add_sub_cancel]
/-
**AlgebraicTopology.DoldKan.PInfty_f_add_QInfty_f** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicTopology.DoldKan`。
形式化陈述：PInfty_f_add_QInfty_f (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ _) + QInfty.f n =
 𝟙 _
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_add_QInfty`：PInfty_add_QInfty : (PInfty
 : K[X] ⟶ _) + QInfty = 𝟙 _
-/
theorem PInfty_f_add_QInfty_f (n : ℕ) : (PInfty.f n : X _⦋n⦌ ⟶ _) + QInfty.f n = 𝟙 _ :=
  HomologicalComplex.congr_hom PInfty_add_QInfty n

variable (C)

/-- `PInfty` induces a natural transformation, i.e. an endomorphism of
the functor `alternatingFaceMapComplex C`. -/
@[simps]
/-
**AlgebraicTopology.DoldKan.natTransPInfty** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicT
opology.DoldKan`。
形式化陈述：natTransPInfty : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C
 where app _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PInfty` induces a natural transformation, i.e. an endomorphism of
the functor `alternatingFaceMapComplex C`.
-/
noncomputable def natTransPInfty : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := PInfty
  naturality X Y f := by
    ext n
    exact PInfty_f_naturality n f

/-- The natural transformation in each degree that is induced by `natTransPInfty`. -/
@[simps!]
/-
**AlgebraicTopology.DoldKan.natTransPInfty_f** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cTopology.DoldKan`。
形式化陈述：natTransPInfty_f (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation in each degree that is induced by `natTransPInfty`.
-/
noncomputable def natTransPInfty_f (n : ℕ) :=
  natTransPInfty C ◫ 𝟙 (HomologicalComplex.eval _ _ n)

variable {C}

@[simp]
/-
**AlgebraicTopology.DoldKan.map_PInfty_f** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTop
ology.DoldKan`。
形式化陈述：map_PInfty_f {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Addi
tive] (X : SimplicialObject C) (n : Nat) : (PInfty : K[((whiskering C D).obj G).
obj X] ⟶ _).f n = G.map ((PInfty : AlternatingFaceMapComplex.obj X ⟶ _).f n)
参数：G : C ⥤ D；X : SimplicialObject C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicTopology.DoldKan.map_P`：map_P {D : Type*} [Category* D] [Preadd
itive D] (G : C ⥤ D) [G.Additive] (X : SimplicialObject C) (q n : Nat) : G.map (
(P q : K[X] ⟶ _).f n)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_PInfty_f {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (n : ℕ) :
    (PInfty : K[((whiskering C D).obj G).obj X] ⟶ _).f n =
      G.map ((PInfty : AlternatingFaceMapComplex.obj X ⟶ _).f n) := by
  simp only [PInfty_f, map_P]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an object `Y : Karoubi (SimplicialObject C)`, this lemma
computes `PInfty` for the associated object in `SimplicialObject (Karoubi C)`
in terms of `PInfty` for `Y.X : SimplicialObject C` and `Y.p`. -/
/-
**AlgebraicTopology.DoldKan.karoubi_PInfty_f** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cTopology.DoldKan`。
形式化陈述：karoubi_PInfty_f {Y : Karoubi (SimplicialObject C)} (n : Nat) : ((PInfty :
 K[(karoubiFunctorCategoryEmbedding _ _).obj Y] ⟶ _).f n).f = Y.p.app (op ⦋n⦌) ≫
 (PInfty : K[Y.X] ⟶ _).f n
参数：SimplicialObject C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Idempotents.Karoubi.hom_ext_iff`：hom_ext_iff {P Q : Karou
bi C} {f g : P ⟶ Q} : f = g ↔ f.f = g.f
· 使用定理 `AlgebraicTopology.DoldKan.map_PInfty_f`：map_PInfty_f {D : Type*} [Catego
ry* D] [Preadditive D] (G : C ⥤ D) [G.Additive] (X : SimplicialObject C) (n : Na
t) : (PInfty : K[((whiskerin…
· 使用定理 `CategoryTheory.Idempotents.instAdditiveKaroubiToKaroubi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddi
tive C],   (CategoryTheory.Idempotents.toKaro…
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.Idempotents.toKaroubi_comp_karoubiFunctorCategoryEmbeddin
g`：toKaroubi_comp_karoubiFunctorCategoryEmbedding : toKaroubi _ ⋙ karoubiFunctor
CategoryEmbedding J C = (Functor.whiskeringRight J _ _).obj (to…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Idempotents.natTrans_eq`：natTrans_eq {F G : Karoubi C ⥤ D
} (φ : F ⟶ G) (P : Karoubi C) : φ.app P = F.map (decompId_i P) ≫ φ.app P.X ≫ G.m
ap (decompId_p P)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f_naturality`：PInfty_f_naturality (n : 
Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) : f.app (op ⦋n⦌) ≫ PInfty.f n = PInf
ty.f n ≫ f.app (op ⦋n⦌)
· 使用定理 `CategoryTheory.Idempotents.app_idem_assoc`：∀ {J : Type u_1} {C : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_2} C] (P : Categor…

--- 原说明 ---
Given an object `Y : Karoubi (SimplicialObject C)`, this lemma
computes `PInfty` for the associated object in `SimplicialObject (Karoubi C)`
in terms of `PInfty` for `Y.X : SimplicialObject C` and `Y.p`.
-/
theorem karoubi_PInfty_f {Y : Karoubi (SimplicialObject C)} (n : ℕ) :
    ((PInfty : K[(karoubiFunctorCategoryEmbedding _ _).obj Y] ⟶ _).f n).f =
      Y.p.app (op ⦋n⦌) ≫ (PInfty : K[Y.X] ⟶ _).f n := by
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubiFunctorCategoryEmbedding _ _).obj Y
  let Y₂ := Y.X
  let Y₃ := ((whiskering _ _).obj (toKaroubi C)).obj Y.X
  let Y₄ := (karoubiFunctorCategoryEmbedding _ _).obj ((toKaroubi _).obj Y.X)
  let P₁ : K[Y₁] ⟶ _ := PInfty
  let P₂ : K[Y₂] ⟶ _ := PInfty
  let P₃ : K[Y₃] ⟶ _ := PInfty
  let P₄ : K[Y₄] ⟶ _ := PInfty
  -- The statement of lemma relates P₁ and P₂.
  change (P₁.f n).f = Y.p.app (op ⦋n⦌) ≫ P₂.f n
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n := Karoubi.hom_ext_iff.mp (map_PInfty_f (toKaroubi C) Y₂ n)
  have h₄₃ : P₄.f n = P₃.f n := by
    have h := Functor.congr_obj (toKaroubi_comp_karoubiFunctorCategoryEmbedding _ _) Y₂
    simp only [P₃, P₄, ← natTransPInfty_f_app]
    congr 1
  have h₁₄ := Idempotents.natTrans_eq
    ((𝟙 (karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C)) ◫
      (natTransPInfty_f (Karoubi C) n)) Y
  dsimp [natTransPInfty_f] at h₁₄
  rw [id_comp, id_comp, comp_id, comp_id] at h₁₄
  -- We use the three equalities h₃₂, h₄₃, h₁₄.
  rw [← h₃₂, ← h₄₃, h₁₄]
  simp only [KaroubiFunctorCategoryEmbedding.map_app_f, Karoubi.decompId_p_f,
    Karoubi.decompId_i_f, Karoubi.comp_f]
  let π : Y₄ ⟶ Y₄ := (toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding _ _).map Y.p
  have eq := Karoubi.hom_ext_iff.mp (PInfty_f_naturality n π)
  simp only [Karoubi.comp_f] at eq
  dsimp [π] at eq
  rw [← eq, app_idem_assoc Y (op ⦋n⦌)]

end DoldKan

end AlgebraicTopology

