/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.Split

/-!

# Split simplicial objects in preadditive categories

In this file we define a functor `nondegComplex : SimplicialObject.Split C ⥤ ChainComplex C ℕ`
when `C` is a preadditive category with finite coproducts, and get an isomorphism
`toKaroubiNondegComplexFunctorIsoN₁ : nondegComplex ⋙ toKaroubi _ ≅ forget C ⋙ DoldKan.N₁`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


namespace CategoryTheory.SimplicialObject

open AlgebraicTopology Limits Category Preadditive Idempotents Opposite DoldKan Simplicial

namespace Splitting

variable {C : Type*} [Category* C] {X : SimplicialObject C}
  (s : Splitting X)

/-- The projection on a summand of the coproduct decomposition given
by a splitting of a simplicial object. -/
/-
**CategoryTheory.SimplicialObject.Splitting.** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection on a summand of the coproduct decomposition given
by a splitting of a simplicial object.
-/
noncomputable def πSummand [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    X.obj Δ ⟶ s.N A.1.unop.len :=
  s.desc Δ (fun B => by
    by_cases h : B = A
    · exact eqToHom (by subst h; rfl)
    · exact 0)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.cofan_inj_** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cofan_inj_πSummand_eq_id [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ s.πSummand A = 𝟙 _ := by
  simp [πSummand]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.cofan_inj_** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cofan_inj_πSummand_eq_zero [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A B : IndexSet Δ)
    (h : B ≠ A) : (s.cofan Δ).inj A ≫ s.πSummand B = 0 := by
  dsimp [πSummand]
  rw [ι_desc, dif_neg h.symm]

variable [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SimplicialObject.Splitting.decomposition_id** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：decomposition_id (Δ : SimplexCategoryᵒᵖ) : 𝟙 (X.obj Δ) = ∑ A : IndexSet Δ,
 s.πSummand A ≫ (s.cofan Δ).inj A
参数：Δ : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.hom_ext'`：hom_ext' {Z : C} {Δ 
: SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z) (h : forall A : IndexSet Δ, (s.cofan Δ)
.inj A ≫ f = (s.cofan Δ).inj A ≫ g) : f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.cofan_inj_πSummand_eq_zero_ass
oc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : Category
Theory.SimplicialObject C} (s : X.Splitting)   [inst_1 : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.cofan_inj_πSummand_eq_id_assoc
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : CategoryTh
eory.SimplicialObject C} (s : X.Splitting)   [inst_1 : Categor…
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem decomposition_id (Δ : SimplexCategoryᵒᵖ) :
    𝟙 (X.obj Δ) = ∑ A : IndexSet Δ, s.πSummand A ≫ (s.cofan Δ).inj A := by
  apply s.hom_ext'
  intro A
  dsimp
  erw [comp_id, comp_sum, Finset.sum_eq_single A, cofan_inj_πSummand_eq_id_assoc]
  · intro B _ h₂
    rw [s.cofan_inj_πSummand_eq_zero_assoc _ _ h₂, zero_comp]
  · simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem σ_comp_πSummand_id_eq_zero {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ s.πSummand (IndexSet.id (op ⦋n + 1⦌)) = 0 := by
  apply s.hom_ext'
  intro A
  dsimp only [SimplicialObject.σ]
  rw [comp_zero, s.cofan_inj_epi_naturality_assoc A (SimplexCategory.σ i).op,
    cofan_inj_πSummand_eq_zero]
  rw [ne_comm]
  change ¬(A.epiComp (SimplexCategory.σ i).op).EqId
  rw [IndexSet.eqId_iff_len_eq]
  have h := SimplexCategory.len_le_of_epi A.e
  dsimp at h ⊢
  lia

set_option backward.isDefEq.respectTransparency false in
/-- If a simplicial object `X` in an additive category is split,
then `PInfty` vanishes on all the summands of `X _⦋n⦌` which do
not correspond to the identity of `⦋n⦌`. -/
/-
**CategoryTheory.SimplicialObject.Splitting.cofan_inj_comp_PInfty_eq_zero** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：cofan_inj_comp_PInfty_eq_zero {X : SimplicialObject C} (s : SimplicialObje
ct.Splitting X) {n : Nat} (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) (hA
 : ¬A.EqId) : (s.cofan _).inj A ≫ PInfty.f n = 0
参数：s : SimplicialObject.Splitting X；A : SimplicialObject.Splitting.IndexSet (op 
⦋n⦌)；hA : ¬A.EqId。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.cofan_inj_eq`：cofan_inj_eq {Δ 
: SimplexCategoryᵒᵖ} (A : IndexSet Δ) : (s.cofan Δ).inj A = s.ι A.1.unop.len ≫ X
.map A.e.op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicTopology.DoldKan.degeneracy_comp_PInfty`：degeneracy_comp_PInfty
 (X : SimplicialObject C) (n : Nat) {Δ' : SimplexCategory} (θ : ⦋n⦌ ⟶ Δ') (hθ : 
¬Mono θ) : dsimp% X.map θ.op ≫ PInfty.…
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.IndexSet.eqId_iff_mono`：eqId_i
ff_mono : A.EqId ↔ Mono A.e
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)

--- 原说明 ---
If a simplicial object `X` in an additive category is split,
then `PInfty` vanishes on all the summands of `X _⦋n⦌` which do
not correspond to the identity of `⦋n⦌`.
-/
theorem cofan_inj_comp_PInfty_eq_zero {X : SimplicialObject C} (s : SimplicialObject.Splitting X)
    {n : ℕ} (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) (hA : ¬A.EqId) :
    (s.cofan _).inj A ≫ PInfty.f n = 0 := by
  rw [SimplicialObject.Splitting.IndexSet.eqId_iff_mono] at hA
  rw [SimplicialObject.Splitting.cofan_inj_eq, assoc, degeneracy_comp_PInfty X n A.e hA, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SimplicialObject.Splitting.comp_PInfty_eq_zero_iff** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：comp_PInfty_eq_zero_iff {Z : C} {n : Nat} (f : Z ⟶ X _⦋n⦌) : f ≫ PInfty.f 
n = 0 ↔ f ≫ s.πSummand (IndexSet.id (op ⦋n⦌)) = 0
参数：f : Z ⟶ X _⦋n⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_f_add_QInfty_f`：PInfty_f_add_QInfty_f (
n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ _) + QInfty.f n = 𝟙 _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicTopology.DoldKan.QInfty_f`：QInfty_f (n : Nat) : (QInfty.f n : X
 _⦋n⦌ ⟶ X _⦋n⦌) = (Q n).f n
· 使用定理 `AlgebraicTopology.DoldKan.decomposition_Q`：decomposition_Q (n q : Nat) :
 ((Q q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌) = ∑ i : Fin (n + 1) with i.val < q,
 (P i).f (n + 1) ≫ X.δ i.rev.su…
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.σ_comp_πSummand_id_eq_zero`：σ_
comp_πSummand_id_eq_zero {n : Nat} (i : Fin (n + 1)) : X.σ i ≫ s.πSummand (Index
Set.id (op ⦋n + 1⦌)) = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.decomposition_id`：decompositio
n_id (Δ : SimplexCategoryᵒᵖ) : 𝟙 (X.obj Δ) = ∑ A : IndexSet Δ, s.πSummand A ≫ (s
.cofan Δ).inj A
· 使用定理 `Fintype.sum_eq_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] 
[inst_1 : AddCommMonoid M] (f : α → M),   (∀ (a : α), f a = 0) → ∑ a, f a = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.cofan_inj_comp_PInfty_eq_zero`
：cofan_inj_comp_PInfty_eq_zero {X : SimplicialObject C} (s : SimplicialObject.Sp
litting X) {n : Nat} (A : SimplicialObject.Splitting.IndexSet…
-/
theorem comp_PInfty_eq_zero_iff {Z : C} {n : ℕ} (f : Z ⟶ X _⦋n⦌) :
    f ≫ PInfty.f n = 0 ↔ f ≫ s.πSummand (IndexSet.id (op ⦋n⦌)) = 0 := by
  constructor
  · intro h
    rcases n with _ | n
    · dsimp at h
      rw [comp_id] at h
      rw [h, zero_comp]
    · have h' := f ≫= PInfty_f_add_QInfty_f (n + 1)
      dsimp at h'
      rw [comp_id, comp_add, h, zero_add] at h'
      rw [← h', assoc, QInfty_f, decomposition_Q, Preadditive.sum_comp, Preadditive.comp_sum,
        Finset.sum_eq_zero]
      intro i _
      simp only [assoc, σ_comp_πSummand_id_eq_zero, comp_zero]
  · intro h
    rw [← comp_id f, assoc, s.decomposition_id, Preadditive.sum_comp, Preadditive.comp_sum,
      Fintype.sum_eq_zero]
    intro A
    by_cases hA : A.EqId
    · dsimp at hA
      subst hA
      rw [assoc, reassoc_of% h, zero_comp]
    · simp only [assoc, s.cofan_inj_comp_PInfty_eq_zero A hA, comp_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.PInfty_comp_** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PInfty_comp_πSummand_id (n : ℕ) :
    PInfty.f n ≫ s.πSummand (IndexSet.id (op ⦋n⦌)) = s.πSummand (IndexSet.id (op ⦋n⦌)) := by
  conv_rhs => rw [← id_comp (s.πSummand _)]
  symm
  rw [← sub_eq_zero, ← sub_comp, ← comp_PInfty_eq_zero_iff, sub_comp, id_comp, PInfty_f_idem,
    sub_self]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty (n : ℕ) :
    s.πSummand (IndexSet.id (op ⦋n⦌)) ≫ (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) ≫ PInfty.f n =
      PInfty.f n := by
  conv_rhs => rw [← id_comp (PInfty.f n)]
  dsimp only [AlternatingFaceMapComplex.obj_X]
  rw [s.decomposition_id, Preadditive.sum_comp]
  rw [Fintype.sum_eq_single (IndexSet.id (op ⦋n⦌)), assoc]
  rintro A (hA : ¬A.EqId)
  rw [assoc, s.cofan_inj_comp_PInfty_eq_zero A hA, comp_zero]

/-- The differentials `s.d i j : s.N i ⟶ s.N j` on nondegenerate simplices of a split
simplicial object are induced by the differentials on the alternating face map complex. -/
@[simp]
/-
**CategoryTheory.SimplicialObject.Splitting.d** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SimplicialObject.Splitting`。
形式化陈述：d (i j : Nat) : s.N i ⟶ s.N j
参数：i j : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differentials `s.d i j : s.N i ⟶ s.N j` on nondegenerate simplices of a spli
t
simplicial object are induced by the differentials on the alternating face map c
omplex.
-/
noncomputable def d (i j : ℕ) : s.N i ⟶ s.N j :=
  (s.cofan _).inj (IndexSet.id (op ⦋i⦌)) ≫ K[X].d i j ≫ s.πSummand (IndexSet.id (op ⦋j⦌))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SimplicialObject.Splitting.** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ιSummand_comp_d_comp_πSummand_eq_zero (j k : ℕ) (A : IndexSet (op ⦋j⦌)) (hA : ¬A.EqId) :
    (s.cofan _).inj A ≫ K[X].d j k ≫ s.πSummand (IndexSet.id (op ⦋k⦌)) = 0 := by
  rw [A.eqId_iff_mono] at hA
  rw [← assoc, ← s.comp_PInfty_eq_zero_iff, assoc, ← PInfty.comm j k, s.cofan_inj_eq, assoc,
    degeneracy_comp_PInfty_assoc X j A.e hA, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- If `s` is a splitting of a simplicial object `X` in a preadditive category,
`s.nondegComplex` is a chain complex which is given in degree `n` by
the nondegenerate `n`-simplices of `X`. This chain complex should be thought
as the normalized chain complex of `X` because of the isomorphism
`toKaroubiNondegComplexIsoN₁`. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Splitting.nondegComplex** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：nondegComplex : ChainComplex C Nat where X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a splitting of a simplicial object `X` in a preadditive category,
`s.nondegComplex` is a chain complex which is given in degree `n` by
the nondegenerate `n`-simplices of `X`. This chain complex should be thought
as the normalized chain complex of `X` because of the isomorphism
`toKaroubiNondegComplexIsoN₁`.
-/
noncomputable def nondegComplex : ChainComplex C ℕ where
  X := s.N
  d := s.d
  shape i j hij := by simp only [d, K[X].shape i j hij, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [d, assoc]
    have eq : K[X].d i j ≫ 𝟙 (X.obj (op ⦋j⦌)) ≫ K[X].d j k ≫
        s.πSummand (IndexSet.id (op ⦋k⦌)) = 0 := by
      simp
    rw [s.decomposition_id] at eq
    classical
    rw [Fintype.sum_eq_add_sum_compl (IndexSet.id (op ⦋j⦌)), add_comp, comp_add, assoc,
      Preadditive.sum_comp, Preadditive.comp_sum, Finset.sum_eq_zero, add_zero] at eq
    swap
    · intro A hA
      simp only [Finset.mem_compl, Finset.mem_singleton] at hA
      simp only [assoc, ιSummand_comp_d_comp_πSummand_eq_zero _ _ _ _ hA, comp_zero]
    rw [eq, comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The chain complex `s.nondegComplex` attached to a splitting of a simplicial object `X`
becomes isomorphic to the normalized Moore complex `N₁.obj X` defined as a formal direct
factor in the category `Karoubi (ChainComplex C ℕ)`. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Splitting.toKaroubiNondegComplexIsoN** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chain complex `s.nondegComplex` attached to a splitting of a simplicial obje
ct `X`
becomes isomorphic to the normalized Moore complex `N₁.obj X` defined as a forma
l direct
factor in the category `Karoubi (ChainComplex C ℕ)`.
-/
noncomputable def toKaroubiNondegComplexIsoN₁ :
    (toKaroubi _).obj s.nondegComplex ≅ N₁.obj X where
  hom :=
    { f :=
        { f := fun n => (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) ≫ PInfty.f n
          comm' := fun i j _ => by
            dsimp
            rw [assoc, assoc, assoc, πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty,
              HomologicalComplex.Hom.comm] }
      comm := by
        ext n
        dsimp
        rw [id_comp, assoc, PInfty_f_idem] }
  inv :=
    { f :=
        { f := fun n => s.πSummand (IndexSet.id (op ⦋n⦌))
          comm' := fun i j _ => by
            dsimp
            slice_rhs 1 1 => rw [← id_comp (K[X].d i j)]
            dsimp only [AlternatingFaceMapComplex.obj_X]
            rw [s.decomposition_id, sum_comp, sum_comp, Finset.sum_eq_single (IndexSet.id (op ⦋i⦌)),
                assoc, assoc]
            · intro A _ hA
              simp only [assoc, s.ιSummand_comp_d_comp_πSummand_eq_zero _ _ _ hA, comp_zero]
            · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff] }
      comm := by
        ext n
        dsimp
        simp only [comp_id, PInfty_comp_πSummand_id] }
  hom_inv_id := by
    ext n
    simp only [assoc, PInfty_comp_πSummand_id, Karoubi.comp_f, HomologicalComplex.comp_f,
      cofan_inj_πSummand_eq_id]
    rfl
  inv_hom_id := by
    ext n
    simp only [πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty, Karoubi.comp_f,
      HomologicalComplex.comp_f, N₁_obj_p, Karoubi.id_f]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.toKaroubiNondegComplexIsoN** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toKaroubiNondegComplexIsoN₁_hom_f_PInfty :
    dsimp% s.toKaroubiNondegComplexIsoN₁.hom.f ≫ PInfty =
      s.toKaroubiNondegComplexIsoN₁.hom.f := by
  simpa using s.toKaroubiNondegComplexIsoN₁.hom.comm

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.toKaroubiNondegComplexIsoN** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toKaroubiNondegComplexIsoN₁_hom_inv_id_f :
    dsimp% s.toKaroubiNondegComplexIsoN₁.hom.f ≫ s.toKaroubiNondegComplexIsoN₁.inv.f = 𝟙 _ := by
  rw [← dsimp% [-Karoubi.comp_f] Karoubi.comp_f s.toKaroubiNondegComplexIsoN₁.hom
    s.toKaroubiNondegComplexIsoN₁.inv, Iso.hom_inv_id]
  simp

set_option backward.defeqAttrib.useBackward true in
/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the split epimorphism from the alternating face map complex of `X` to the chain
complex `s.nondegComplex`. -/
@[no_expose]
/-
**CategoryTheory.SimplicialObject.Splitting.toNondegComplex** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：toNondegComplex : K[X] ⟶ s.nondegComplex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the split epimorphism from the alternating face map complex of `X` to th
e chain
complex `s.nondegComplex`.
-/
noncomputable def toNondegComplex : K[X] ⟶ s.nondegComplex :=
  (fullyFaithfulToKaroubi _).preimage
    ({ f := by exact PInfty } ≫ s.toKaroubiNondegComplexIsoN₁.inv)

set_option backward.defeqAttrib.useBackward true in
/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the split monomormphism from the chain complex `s.nondegComplex` to
the alternating face map complex of `X`. -/
@[no_expose]
/-
**CategoryTheory.SimplicialObject.Splitting.fromNondegComplex** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：fromNondegComplex : s.nondegComplex ⟶ K[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the split monomormphism from the chain complex `s.nondegComplex` to
the alternating face map complex of `X`.
-/
noncomputable def fromNondegComplex : s.nondegComplex ⟶ K[X] :=
  (fullyFaithfulToKaroubi _).preimage
    (s.toKaroubiNondegComplexIsoN₁.hom ≫ { f := PInfty })

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.PInfty_toNondegComplex** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：PInfty_toNondegComplex : PInfty ≫ s.toNondegComplex = s.toNondegComplex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Idempotents.instFaithfulKaroubiToKaroubi`：∀ (C : Type u_1
) [inst : CategoryTheory.Category.{v_1, u_1} C], (CategoryTheory.Idempotents.toK
aroubi C).Faithful
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_idem_assoc`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {X
 : CategoryTheory.SimplicialObjec…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma PInfty_toNondegComplex : PInfty ≫ s.toNondegComplex = s.toNondegComplex :=
  (toKaroubi _).map_injective (by simp [toNondegComplex])

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.fromNondegComplex_toNondegComplex** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：fromNondegComplex_toNondegComplex : s.fromNondegComplex ≫ s.toNondegComple
x = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Idempotents.instFaithfulKaroubiToKaroubi`：∀ (C : Type u_1
) [inst : CategoryTheory.Category.{v_1, u_1} C], (CategoryTheory.Idempotents.toK
aroubi C).Faithful
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_idem_assoc`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {X
 : CategoryTheory.SimplicialObjec…
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.toKaroubiNondegComplexIsoN₁_ho
m_f_PInfty_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C]
 {X : CategoryTheory.SimplicialObject C} (s : X.Splitting)   [inst_1 : Categor…
· 使用引理 `CategoryTheory.SimplicialObject.Splitting.toKaroubiNondegComplexIsoN₁_ho
m_inv_id_f`：toKaroubiNondegComplexIsoN₁_hom_inv_id_f : dsimp% s.toKaroubiNondegC
omplexIsoN₁.hom.f ≫ s.toKaroubiNondegComplexIsoN₁.inv.f = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromNondegComplex_toNondegComplex :
    s.fromNondegComplex ≫ s.toNondegComplex = 𝟙 _ :=
  (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.SimplicialObject.Splitting.toNondegComplex_f** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：toNondegComplex_f (n : Nat) : s.toNondegComplex.f n = PInfty.f n ≫ s.toKar
oubiNondegComplexIsoN₁.inv.f.f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNondegComplex_f (n : ℕ) :
    s.toNondegComplex.f n = PInfty.f n ≫ s.toKaroubiNondegComplexIsoN₁.inv.f.f n := by
  simp [toNondegComplex, fullyFaithfulToKaroubi]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.SimplicialObject.Splitting.fromNondegComplex_f** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：fromNondegComplex_f (n : Nat) : s.fromNondegComplex.f n = s.ι n ≫ PInfty.f
 n
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.SimplicialObject.Splitting.toKaroubiNondegComplexIsoN₁_ho
m_f_PInfty`：toKaroubiNondegComplexIsoN₁_hom_f_PInfty : dsimp% s.toKaroubiNondegC
omplexIsoN₁.hom.f ≫ PInfty = s.toKaroubiNondegComplexIsoN₁.hom.f
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromNondegComplex_f (n : ℕ) :
    s.fromNondegComplex.f n = s.ι n ≫ PInfty.f n := by
  simp [fromNondegComplex, fullyFaithfulToKaroubi,
    cofan, IndexSet.id, IndexSet.e]
/-
**CategoryTheory.SimplicialObject.Splitting.isSplitEpi_toNondegComplex** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：isSplitEpi_toNondegComplex : IsSplitEpi s.toNondegComplex where exists_spl
itEpi
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SimplicialObject.Splitting.fromNondegComplex_toNondegComp
lex`：fromNondegComplex_toNondegComplex : s.fromNondegComplex ≫ s.toNondegComplex
 = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isSplitEpi_toNondegComplex : IsSplitEpi s.toNondegComplex where
  exists_splitEpi := ⟨⟨s.fromNondegComplex, by simp⟩⟩
/-
**CategoryTheory.SimplicialObject.Splitting.isSplitMono_fromNondegComplex** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：isSplitMono_fromNondegComplex : IsSplitMono s.fromNondegComplex where exis
ts_splitMono
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SimplicialObject.Splitting.fromNondegComplex_toNondegComp
lex`：fromNondegComplex_toNondegComplex : s.fromNondegComplex ≫ s.toNondegComplex
 = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isSplitMono_fromNondegComplex : IsSplitMono s.fromNondegComplex where
  exists_splitMono := ⟨⟨s.toNondegComplex, by simp⟩⟩

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.toNondegComplex_fromNondegComplex** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：toNondegComplex_fromNondegComplex : s.toNondegComplex ≫ s.fromNondegComple
x = PInfty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Idempotents.instFaithfulKaroubiToKaroubi`：∀ (C : Type u_1
) [inst : CategoryTheory.Category.{v_1, u_1} C], (CategoryTheory.Idempotents.toK
aroubi C).Faithful
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `AlgebraicTopology.DoldKan.PInfty_idem`：PInfty_idem : (PInfty : K[X] ⟶ _)
 ≫ PInfty = PInfty
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNondegComplex_fromNondegComplex :
    s.toNondegComplex ≫ s.fromNondegComplex = PInfty :=
  (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the homotopy equivalence from the alternating face map complex of `X`
to the chain complex `s.nondegComplex`. -/
@[simps hom inv]
/-
**CategoryTheory.SimplicialObject.Splitting.homotopyEquivNondegComplex** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：homotopyEquivNondegComplex : HomotopyEquiv K[X] s.nondegComplex where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the homotopy equivalence from the alternating face map complex of `X`
to the chain complex `s.nondegComplex`.
-/
noncomputable def homotopyEquivNondegComplex :
    HomotopyEquiv K[X] s.nondegComplex where
  hom := s.toNondegComplex
  inv := s.fromNondegComplex
  homotopyHomInvId := .trans (.ofEq (by simp)) (homotopyPInftyToId X)
  homotopyInvHomId := .ofEq (by simp)

end Splitting

namespace Split

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor which sends a split simplicial object in a preadditive category to
the chain complex which consists of nondegenerate simplices. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Split.nondegComplexFunctor** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.SimplicialObject.Split`。
形式化陈述：nondegComplexFunctor : Split C ⥤ ChainComplex C Nat where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends a split simplicial object in a preadditive category to
the chain complex which consists of nondegenerate simplices.
-/
noncomputable def nondegComplexFunctor : Split C ⥤ ChainComplex C ℕ where
  obj S := S.s.nondegComplex
  map {S₁ S₂} Φ :=
    { f := Φ.f
      comm' := fun i j _ => by
        dsimp
        erw [← cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋i⦌)),
          ((alternatingFaceMapComplex C).map Φ.F).comm_assoc i j]
        simp only [assoc]
        congr 2
        apply S₁.s.hom_ext'
        intro A
        dsimp [alternatingFaceMapComplex]
        rw [cofan_inj_naturality_symm_assoc Φ A]
        by_cases h : A.EqId
        · dsimp at h
          subst h
          rw [Splitting.cofan_inj_πSummand_eq_id]
          dsimp
          rw [comp_id, Splitting.cofan_inj_πSummand_eq_id_assoc]
        · rw [S₁.s.cofan_inj_πSummand_eq_zero_assoc _ _ (Ne.symm h),
            S₂.s.cofan_inj_πSummand_eq_zero _ _ (Ne.symm h), zero_comp, comp_zero] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism (in `Karoubi (ChainComplex C ℕ)`) between the chain complex
of nondegenerate simplices of a split simplicial object and the normalized Moore complex
defined as a formal direct factor of the alternating face map complex. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.Split.toKaroubiNondegComplexFunctorIsoN** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.SimplicialObject.Split`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism (in `Karoubi (ChainComplex C ℕ)`) between the chain comp
lex
of nondegenerate simplices of a split simplicial object and the normalized Moore
 complex
defined as a formal direct factor of the alternating face map complex.
-/
noncomputable def toKaroubiNondegComplexFunctorIsoN₁ :
    nondegComplexFunctor ⋙ toKaroubi (ChainComplex C ℕ) ≅ forget C ⋙ DoldKan.N₁ :=
  NatIso.ofComponents (fun S => S.s.toKaroubiNondegComplexIsoN₁) fun Φ => by
    ext n
    dsimp
    simp only [assoc, PInfty_f_idem_assoc]
    erw [← Split.cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋n⦌))]
    rw [PInfty_f_naturality]

end Split

end CategoryTheory.SimplicialObject

