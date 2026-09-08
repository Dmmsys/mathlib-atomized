/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Faces
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!

# Construction of projections for the Dold-Kan correspondence

In this file, we construct endomorphisms `P q : K[X] ⟶ K[X]` for all
`q : ℕ`. We study how they behave with respect to face maps with the lemmas
`HigherFacesVanish.of_P`, `HigherFacesVanish.comp_P_eq_self` and
`comp_P_eq_self_iff`.

Then, we show that they are projections (see `P_f_idem`
and `P_idem`). They are natural transformations (see `natTransP`
and `P_f_naturality`) and are compatible with the application
of additive functors (see `map_P`).

By passing to the limit, these endomorphisms `P q` shall be used in `PInfty.lean`
in order to define `PInfty : K[X] ⟶ K[X]`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject Opposite CategoryTheory.Idempotents

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X : SimplicialObject C}

/-- This is the inductive definition of the projections `P q : K[X] ⟶ K[X]`,
with `P 0 := 𝟙 _` and `P (q+1) := P q ≫ (𝟙 _ + Hσ q)`. -/
/-
**AlgebraicTopology.DoldKan.P** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldK
an`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X : CategoryTheory.SimplicialObjec
t C} →         ℕ → (AlgebraicTopology.AlternatingFaceMapComplex.obj X ⟶ Algebrai
cTopology.AlternatingFaceMapComplex.obj X)
参数：AlgebraicTopology.AlternatingFaceMapComplex.obj X ⟶ AlgebraicTopology.Alterna
tingFaceMapComplex.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the inductive definition of the projections `P q : K[X] ⟶ K[X]`,
with `P 0 := 𝟙 _` and `P (q+1) := P q ≫ (𝟙 _ + Hσ q)`.
-/
noncomputable def P : ℕ → (K[X] ⟶ K[X])
  | 0 => 𝟙 _
  | q + 1 => P q ≫ (𝟙 _ + Hσ q)
/-
**AlgebraicTopology.DoldKan.P_zero** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicTopology.
DoldKan`。
形式化陈述：P_zero : (P 0 : K[X] ⟶ K[X]) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma P_zero : (P 0 : K[X] ⟶ K[X]) = 𝟙 _ := rfl
/-
**AlgebraicTopology.DoldKan.P_succ** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicTopology.
DoldKan`。
形式化陈述：P_succ (q : Nat) : (P (q + 1) : K[X] ⟶ K[X]) = P q ≫ (𝟙 _ + Hσ q)
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma P_succ (q : ℕ) : (P (q + 1) : K[X] ⟶ K[X]) = P q ≫ (𝟙 _ + Hσ q) := rfl

/-- All the `P q` coincide with `𝟙 _` in degree 0. -/
@[simp]
/-
**AlgebraicTopology.DoldKan.P_f_0_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolog
y.DoldKan`。
形式化陈述：P_f_0_eq (q : Nat) : ((P q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
参数：q : Nat。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicTopology.DoldKan.Hσ_eq_zero`：Hσ_eq_zero (q : Nat) : (Hσ q : K[X
] ⟶ K[X]).f 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
All the `P q` coincide with `𝟙 _` in degree 0.
-/
theorem P_f_0_eq (q : ℕ) : ((P q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _ := by
  induction q with
  | zero => rfl
  | succ q hq =>
    simp only [P_succ, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, id_comp, hq, Hσ_eq_zero, add_zero]

/-- `Q q` is the complement projection associated to `P q` -/
/-
**AlgebraicTopology.DoldKan.Q** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldK
an`。
形式化陈述：Q (q : Nat) : K[X] ⟶ K[X]
参数：q : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Q q` is the complement projection associated to `P q`
-/
def Q (q : ℕ) : K[X] ⟶ K[X] :=
  𝟙 _ - P q
/-
**AlgebraicTopology.DoldKan.P_add_Q** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopology
.DoldKan`。
形式化陈述：P_add_Q (q : Nat) : P q + Q q = 𝟙 K[X]
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicTopology.DoldKan.Q.eq_1`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {X : Category
Theory.SimplicialObjec…
· 使用定理 `_private.Mathlib.AlgebraicTopology.DoldKan.Projections.0.AlgebraicTopolo
gy.DoldKan.P_add_Q._abel_1_2`：∀ {C : Type u_2} [inst : CategoryTheory.Category.{
u_1, u_2} C] [inst_1 : CategoryTheory.Preadditive C]   {X : CategoryTheory.Simpl
icialObjec…
-/
theorem P_add_Q (q : ℕ) : P q + Q q = 𝟙 K[X] := by
  rw [Q]
  abel
/-
**AlgebraicTopology.DoldKan.P_add_Q_f** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolo
gy.DoldKan`。
形式化陈述：P_add_Q_f (q n : Nat) : (P q).f n + (Q q).f n = 𝟙 (X _⦋n⦌)
参数：q n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.P_add_Q`：P_add_Q (q : Nat) : P q + Q q = 𝟙 K[X
]
-/
theorem P_add_Q_f (q n : ℕ) : (P q).f n + (Q q).f n = 𝟙 (X _⦋n⦌) :=
  HomologicalComplex.congr_hom (P_add_Q q) n

@[simp]
/-
**AlgebraicTopology.DoldKan.Q_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopology.
DoldKan`。
形式化陈述：Q_zero : (Q 0 : K[X] ⟶ _) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem Q_zero : (Q 0 : K[X] ⟶ _) = 0 :=
  sub_self _
/-
**AlgebraicTopology.DoldKan.Q_succ** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopology.
DoldKan`。
形式化陈述：Q_succ (q : Nat) : (Q (q + 1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `_private.Mathlib.AlgebraicTopology.DoldKan.Projections.0.AlgebraicTopolo
gy.DoldKan.Q_succ._abel_1_2`：∀ {C : Type u_2} [inst : CategoryTheory.Category.{u
_1, u_2} C] [inst_1 : CategoryTheory.Preadditive C]   {X : CategoryTheory.Simpli
cialObjec…
-/
theorem Q_succ (q : ℕ) : (Q (q + 1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q := by
  simp only [Q, P_succ, comp_add, comp_id]
  abel

/-- All the `Q q` coincide with `0` in degree 0. -/
@[simp]
/-
**AlgebraicTopology.DoldKan.Q_f_0_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolog
y.DoldKan`。
形式化陈述：Q_f_0_eq (q : Nat) : ((Q q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0
参数：q : Nat。
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
· 使用定理 `AlgebraicTopology.DoldKan.P_f_0_eq`：P_f_0_eq (q : Nat) : ((P q).f 0 : X 
_⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
All the `Q q` coincide with `0` in degree 0.
-/
theorem Q_f_0_eq (q : ℕ) : ((Q q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0 := by
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Q, P_f_0_eq, sub_self]

namespace HigherFacesVanish

/-- This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _⦋n+1⦌ ⟶ X _⦋n⦌` when `k≠0` and `k≥n-q+2` -/
/-
**AlgebraicTopology.DoldKan.HigherFacesVanish.of_P** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicTopology.DoldKan.HigherFacesVanish`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {X : CategoryTheory.SimplicialObject C} (q n : ℕ)
,   AlgebraicTopology.DoldKan.HigherFacesVanish q ((AlgebraicTopology.DoldKan.P 
q).f (n + 1))
参数：q n : ℕ；(AlgebraicTopology.DoldKan.P q).f (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _⦋n+1⦌ ⟶ X _⦋n⦌` when `k≠0` and `k≥n-q+2`
-/
theorem of_P : ∀ q n : ℕ, HigherFacesVanish q ((P q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌)
  | 0 => fun n j hj₁ => by lia
  | q + 1 => fun n => by
    simp only [P_succ]
    exact (of_P q n).induction

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicTopology.DoldKan.HigherFacesVanish.comp_P_eq_self** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicTopology.DoldKan.HigherFacesVanish`。
形式化陈述：comp_P_eq_self {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVa
nish q φ) : φ ≫ (P q).f (n + 1) = φ
参数：v : HigherFacesVanish q φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.of_succ`：of_succ {Y : C} {n 
q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish (q + 1) φ) : HigherFacesVan
ish q φ
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.comp_Hσ_eq_zero`：comp_Hσ_eq_
zero {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) (hqn :
 n < q) : φ ≫ (Hσ q).f (n + 1) = 0
· 使用定理 `Nat.le.dest`：∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.comp_Hσ_eq`：comp_Hσ_eq {Y : 
C} {n a q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) (hnaq : n = a 
+ q) : φ ≫ (Hσ q).f (n + 1) = -φ ≫ X.δ ⟨a + …
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_P_eq_self {Y : C} {n q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) :
    φ ≫ (P q).f (n + 1) = φ := by
  induction q with
  | zero =>
    simp only [P_zero]
    apply comp_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, ← assoc, hq v.of_succ, add_eq_left]
    by_cases! hqn : n < q
    · exact v.of_succ.comp_Hσ_eq_zero hqn
    · obtain ⟨a, ha⟩ := Nat.le.dest hqn
      have hnaq : n = a + q := by lia
      simp only [v.of_succ.comp_Hσ_eq hnaq, neg_eq_zero, ← assoc]
      have eq := v ⟨a, by lia⟩ (by
        simp only [hnaq, add_assoc]
        rfl)
      simp only [Fin.succ_mk] at eq
      simp only [eq, zero_comp]

end HigherFacesVanish

/-
**AlgebraicTopology.DoldKan.comp_P_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicTopology.DoldKan`。
形式化陈述：comp_P_eq_self_iff {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} : φ ≫ (P q).f 
(n + 1) = φ ↔ HigherFacesVanish q φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.of_comp`：of_comp {Y Z : C} {
q n : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) (f : Z ⟶ Y) : Higher
FacesVanish q (f ≫ φ)
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.of_P`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {X : CategoryTheory.SimplicialObjec…
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.comp_P_eq_self`：comp_P_eq_se
lf {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) : φ ≫ (P
 q).f (n + 1) = φ
-/
theorem comp_P_eq_self_iff {Y : C} {n q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} :
    φ ≫ (P q).f (n + 1) = φ ↔ HigherFacesVanish q φ := by
  constructor
  · intro hφ
    rw [← hφ]
    apply HigherFacesVanish.of_comp
    apply HigherFacesVanish.of_P
  · exact HigherFacesVanish.comp_P_eq_self

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.P_f_idem** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolog
y.DoldKan`。
形式化陈述：P_f_idem (q n : Nat) : ((P q).f n : X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n
参数：q n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicTopology.DoldKan.P_f_0_eq`：P_f_0_eq (q : Nat) : ((P q).f 0 : X 
_⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.comp_P_eq_self`：comp_P_eq_se
lf {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) : φ ≫ (P
 q).f (n + 1) = φ
· 使用定理 `AlgebraicTopology.DoldKan.HigherFacesVanish.of_P`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {X : CategoryTheory.SimplicialObjec…
-/
theorem P_f_idem (q n : ℕ) : ((P q).f n : X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n := by
  rcases n with (_ | n)
  · rw [P_f_0_eq q, comp_id]
  · exact (HigherFacesVanish.of_P q n).comp_P_eq_self

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.Q_f_idem** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolog
y.DoldKan`。
形式化陈述：Q_f_idem (q n : Nat) : ((Q q).f n : X _⦋n⦌ ⟶ _) ≫ (Q q).f n = (Q q).f n
参数：q n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.idem_of_id_sub_idem`：idem_of_id_sub_idem [Pre
additive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p) : (𝟙 _ - p) ≫ (𝟙 _ - p) = 𝟙 _ -
 p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.P_f_idem`：P_f_idem (q n : Nat) : ((P q).f n : 
X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n
-/
theorem Q_f_idem (q n : ℕ) : ((Q q).f n : X _⦋n⦌ ⟶ _) ≫ (Q q).f n = (Q q).f n :=
  idem_of_id_sub_idem _ (P_f_idem q n)

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.P_idem** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopology.
DoldKan`。
形式化陈述：P_idem (q : Nat) : (P q : K[X] ⟶ K[X]) ≫ P q = P q
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.P_f_idem`：P_f_idem (q n : Nat) : ((P q).f n : 
X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n
-/
theorem P_idem (q : ℕ) : (P q : K[X] ⟶ K[X]) ≫ P q = P q := by
  ext n
  exact P_f_idem q n

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.Q_idem** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopology.
DoldKan`。
形式化陈述：Q_idem (q : Nat) : (Q q : K[X] ⟶ K[X]) ≫ Q q = Q q
参数：q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AlgebraicTopology.DoldKan.Q_f_idem`：Q_f_idem (q n : Nat) : ((Q q).f n : 
X _⦋n⦌ ⟶ _) ≫ (Q q).f n = (Q q).f n
-/
theorem Q_idem (q : ℕ) : (Q q : K[X] ⟶ K[X]) ≫ Q q = Q q := by
  ext n
  exact Q_f_idem q n

set_option backward.isDefEq.respectTransparency false in
/-- For each `q`, `P q` is a natural transformation. -/
@[simps]
/-
**AlgebraicTopology.DoldKan.natTransP** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopolo
gy.DoldKan`。
形式化陈述：natTransP (q : Nat) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComp
lex C where app _
参数：q : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each `q`, `P q` is a natural transformation.
-/
def natTransP (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := P q
  naturality _ _ f := by
    induction q with
    | zero =>
      dsimp [alternatingFaceMapComplex]
      simp only [P_zero, id_comp, comp_id]
    | succ q hq =>
      simp only [P_succ, add_comp, comp_add, assoc, comp_id, hq, reassoc_of% hq]
      -- `erw` is needed to see through `natTransHσ q).app = Hσ q`
      erw [(natTransHσ q).naturality f]
      rfl

set_option backward.isDefEq.respectTransparency false in -- This is needed in AlgebraicTopology/DoldKan/Decomposition.lean
@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.P_f_naturality** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicT
opology.DoldKan`。
形式化陈述：P_f_naturality (q n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) : f.app 
(op ⦋n⦌) ≫ (P q).f n = (P q).f n ≫ f.app (op ⦋n⦌)
参数：q n : Nat；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem P_f_naturality (q n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ (P q).f n = (P q).f n ≫ f.app (op ⦋n⦌) :=
  HomologicalComplex.congr_hom ((natTransP q).naturality f) n

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.Q_f_naturality** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicT
opology.DoldKan`。
形式化陈述：Q_f_naturality (q n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) : f.app 
(op ⦋n⦌) ≫ (Q q).f n = (Q q).f n ≫ f.app (op ⦋n⦌)
参数：q n : Nat；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `AlgebraicTopology.DoldKan.P_f_naturality`：P_f_naturality (q n : Nat) {X 
Y : SimplicialObject C} (f : X ⟶ Y) : f.app (op ⦋n⦌) ≫ (P q).f n = (P q).f n ≫ f
.app (op ⦋n⦌)
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Q_f_naturality (q n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ (Q q).f n = (Q q).f n ≫ f.app (op ⦋n⦌) := by
  simp only [Q, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, P_f_naturality,
    sub_comp, sub_left_inj]
  dsimp
  simp only [comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- For each `q`, `Q q` is a natural transformation. -/
@[simps]
/-
**AlgebraicTopology.DoldKan.natTransQ** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopolo
gy.DoldKan`。
形式化陈述：natTransQ (q : Nat) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComp
lex C where app _
参数：q : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each `q`, `Q q` is a natural transformation.
-/
def natTransQ (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := Q q

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicTopology.DoldKan.map_P** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopology.D
oldKan`。
形式化陈述：map_P {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive] (
X : SimplicialObject C) (q n : Nat) : G.map ((P q : K[X] ⟶ _).f n) = (P q : K[((
whiskering C D).obj G).obj X] ⟶ _).f n
参数：G : C ⥤ D；X : SimplicialObject C；q n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `AlgebraicTopology.DoldKan.map_Hσ`：map_Hσ {D : Type*} [Category* D] [Prea
dditive D] (G : C ⥤ D) [G.Additive] (X : SimplicialObject C) (q n : Nat) : (Hσ q
 : K[((whiskering C D)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_P {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    G.map ((P q : K[X] ⟶ _).f n) = (P q : K[((whiskering C D).obj G).obj X] ⟶ _).f n := by
  induction q with
  | zero =>
    simp only [P_zero]
    apply G.map_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, Functor.map_add, Functor.map_comp, hq, map_Hσ]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicTopology.DoldKan.map_Q** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopology.D
oldKan`。
形式化陈述：map_Q {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive] (
X : SimplicialObject C) (q n : Nat) : G.map ((Q q : K[X] ⟶ _).f n) = (Q q : K[((
whiskering C D).obj G).obj X] ⟶ _).f n
参数：G : C ⥤ D；X : SimplicialObject C；q n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `AlgebraicTopology.DoldKan.map_P`：map_P {D : Type*} [Category* D] [Preadd
itive D] (G : C ⥤ D) [G.Additive] (X : SimplicialObject C) (q n : Nat) : G.map (
(P q : K[X] ⟶ _).f n)…
· 使用定理 `AlgebraicTopology.DoldKan.P_add_Q_f`：P_add_Q_f (q n : Nat) : (P q).f n +
 (Q q).f n = 𝟙 (X _⦋n⦌)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem map_Q {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    G.map ((Q q : K[X] ⟶ _).f n) = (Q q : K[((whiskering C D).obj G).obj X] ⟶ _).f n := by
  rw [← add_right_inj (G.map ((P q : K[X] ⟶ _).f n)), ← G.map_add, map_P G X q n, P_add_Q_f,
    P_add_Q_f]
  apply G.map_id

end DoldKan

end AlgebraicTopology

