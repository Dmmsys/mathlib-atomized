/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz, Johan Commelin
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.Idempotents.FunctorCategories
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a
functor `alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternating sums of faces.

The dual version `alternatingCofaceMapComplex : CosimplicialObject C ⥤ CochainComplex C ℕ`
is also constructed.

We also construct the natural transformation
`inclusionOfMooreComplex : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A`
when `A` is an abelian category.

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

open CategoryTheory.Preadditive CategoryTheory.Category CategoryTheory.Idempotents

open Opposite

open Simplicial

noncomputable section

namespace AlgebraicTopology

namespace AlternatingFaceMapComplex

/-!
## Construction of the alternating face map complex
-/


variable {C : Type*} [Category* C] [Preadditive C]
variable (X : SimplicialObject C)
variable (Y : SimplicialObject C)

/-- The differential on the alternating face map complex is the alternate
sum of the face maps -/
@[simp]
/-
**AlgebraicTopology.AlternatingFaceMapComplex.objD** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicTopology.AlternatingFaceMapComplex`。
形式化陈述：objD (n : Nat) : X _⦋n + 1⦌ ⟶ X _⦋n⦌
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential on the alternating face map complex is the alternate
sum of the face maps
-/
def objD (n : ℕ) : X _⦋n + 1⦌ ⟶ X _⦋n⦌ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i

/-!
## The chain complex relation `d ≫ d`
-/

/-
**AlgebraicTopology.AlternatingFaceMapComplex.d_squared** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicTopology.AlternatingFaceMapComplex`。
形式化陈述：d_squared (n : Nat) : objD X (n + 1) ≫ objD X n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `Finset.univ_product_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintyp
e α] [inst_1 : Fintype β], Finset.univ ×ˢ Finset.univ = Finset.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_sum_compl`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Finset.sum_bij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a 
: ι)…
· 使用定理 `Finset.compl_filter`：compl_filter (p : α -> Prop) [DecidablePred p] [for
all x, Decidable ¬p x] : (univ.filter p)ᶜ = univ.filter fun x => ¬p x
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Preadditive.comp_zsmul`：comp_zsmul (n : Int) : f ≫ (n • g
) = n • f ≫ g
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
## The chain complex relation `d ≫ d`
-/
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  -- we start by expanding d ≫ d as a double sum
  dsimp
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  -- then, we decompose the index set P into a subset S and its complement Sᶜ
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  /- we are reduced to showing that two sums are equal, and this is obtained
    by constructing a bijection φ : S -> Sᶜ, which maps (i,j) to (j,i+1),
    and by comparing the terms -/
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · -- φ(S) is contained in Sᶜ
    intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · -- φ : S → Sᶜ is injective
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using! congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · -- φ : S → Sᶜ is surjective
    rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · -- identification of corresponding terms in both sums
    rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · rw [CategoryTheory.SimplicialObject.δ_comp_δ'']
      simpa [S] using! hij

/-!
## Construction of the alternating face map complex functor
-/


/-- The alternating face map complex, on objects -/
@[implicit_reducible]
/-
**AlgebraicTopology.AlternatingFaceMapComplex.obj** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicTopology.AlternatingFaceMapComplex`。
形式化陈述：obj : ChainComplex C Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.AlternatingFaceMapComplex.d_squared`：d_squared (n : Na
t) : objD X (n + 1) ≫ objD X n = 0

--- 原说明 ---
The alternating face map complex, on objects
-/
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _⦋n⦌) (objD X) (d_squared X)

@[simp]
/-
**AlgebraicTopology.AlternatingFaceMapComplex.obj_X** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicTopology.AlternatingFaceMapComplex`。
形式化陈述：obj_X (X : SimplicialObject C) (n : Nat) : (AlternatingFaceMapComplex.obj 
X).X n = X _⦋n⦌
参数：X : SimplicialObject C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem obj_X (X : SimplicialObject C) (n : ℕ) : (AlternatingFaceMapComplex.obj X).X n = X _⦋n⦌ :=
  rfl

@[simp]
/-
**AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicTopology.AlternatingFaceMapComplex`。
形式化陈述：obj_d_eq (X : SimplicialObject C) (n : Nat) : (AlternatingFaceMapComplex.o
bj X).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.δ i
参数：X : SimplicialObject C；n : Nat。
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
· 使用定理 `ChainComplex.of_d`：of_d (j : α) : of.d X d (j + 1) j = d j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem obj_d_eq (X : SimplicialObject C) (n : ℕ) :
    (AlternatingFaceMapComplex.obj X).d (n + 1) n
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i := by
  simp [obj]

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
/-
**AlgebraicTopology.AlternatingFaceMapComplex.map** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicTopology.AlternatingFaceMapComplex`。
形式化陈述：map (f : X ⟶ Y) : obj X ⟶ obj Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The alternating face map complex, on morphisms
-/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom (fun n => f.app (op ⦋n⦌)) fun n => by
    simp only [obj, ChainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum, sum_comp]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [comp_zsmul, zsmul_comp]
    congr 1
    symm
    apply f.naturality

@[simp]
/-
**AlgebraicTopology.AlternatingFaceMapComplex.map_f** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicTopology.AlternatingFaceMapComplex`。
形式化陈述：map_f (f : X ⟶ Y) (n : Nat) : (map f).f n = f.app (op ⦋n⦌)
参数：f : X ⟶ Y；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem map_f (f : X ⟶ Y) (n : ℕ) : (map f).f n = f.app (op ⦋n⦌) :=
  rfl

end AlternatingFaceMapComplex

variable (C : Type*) [Category* C] [Preadditive C]

/-- The alternating face map complex, as a functor -/
@[implicit_reducible]
/-
**AlgebraicTopology.alternatingFaceMapComplex** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icTopology`。
形式化陈述：alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C Nat where 
obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The alternating face map complex, as a functor
-/
def alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := AlternatingFaceMapComplex.obj
  map f := AlternatingFaceMapComplex.map f

variable {C}

@[simp]
/-
**AlgebraicTopology.alternatingFaceMapComplex_obj_X** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicTopology`。
形式化陈述：alternatingFaceMapComplex_obj_X (X : SimplicialObject C) (n : Nat) : ((alt
ernatingFaceMapComplex C).obj X).X n = X _⦋n⦌
参数：X : SimplicialObject C；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem alternatingFaceMapComplex_obj_X (X : SimplicialObject C) (n : ℕ) :
    ((alternatingFaceMapComplex C).obj X).X n = X _⦋n⦌ :=
  rfl

@[simp]
/-
**AlgebraicTopology.alternatingFaceMapComplex_obj_d** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicTopology`。
形式化陈述：alternatingFaceMapComplex_obj_d (X : SimplicialObject C) (n : Nat) : ((alt
ernatingFaceMapComplex C).obj X).d (n + 1) n = AlternatingFaceMapComplex.objD X 
n
参数：X : SimplicialObject C；n : Nat。
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
· 使用定理 `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq`：obj_d_eq (X : Simp
licialObject C) (n : Nat) : (AlternatingFaceMapComplex.obj X).d (n + 1) n = ∑ i 
: Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatingFaceMapComplex_obj_d (X : SimplicialObject C) (n : ℕ) :
    ((alternatingFaceMapComplex C).obj X).d (n + 1) n = AlternatingFaceMapComplex.objD X n := by
  simp [alternatingFaceMapComplex]

@[simp]
/-
**AlgebraicTopology.alternatingFaceMapComplex_map_f** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicTopology`。
形式化陈述：alternatingFaceMapComplex_map_f {X Y : SimplicialObject C} (f : X ⟶ Y) (n 
: Nat) : ((alternatingFaceMapComplex C).map f).f n = f.app (op ⦋n⦌)
参数：f : X ⟶ Y；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem alternatingFaceMapComplex_map_f {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    ((alternatingFaceMapComplex C).map f).f n = f.app (op ⦋n⦌) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicTopology.map_alternatingFaceMapComplex** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicTopology`。
形式化陈述：map_alternatingFaceMapComplex {D : Type*} [Category* D] [Preadditive D] (F
 : C ⥤ D) [F.Additive] : alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex _
 = (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomologicalComplex.ext`：ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X
 = C₂.X) (h_d : forall i j : ι, c.Rel i j -> C₁.d i j ≫ eqToHom (congr_fun h_X j
) = eqToHom …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicTopology.alternatingFaceMapComplex_obj_d`：alternatingFaceMapCom
plex_obj_d (X : SimplicialObject C) (n : Nat) : ((alternatingFaceMapComplex C).o
bj X).d (n + 1) n = AlternatingFaceMapC…
· 使用定理 `CategoryTheory.Functor.map_sum`：∀ {C : Type u_1} {D : Type u_2} [inst : 
CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, 
u_2} D] [inst_2 : Ca…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Functor.map_zsmul`：map_zsmul {X Y : C} {f : X ⟶ Y} {r : I
nt} : F.map (r • f) = r • F.map f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.eqToHom_f`：eqToHom_f {C₁ C₂ : HomologicalComplex V c}
 (h : C₁ = C₂) (n : ι) : HomologicalComplex.Hom.f (eqToHom h) n = eqToHom (congr
_fun (congr_arg Ho…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_alternatingFaceMapComplex {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] :
    alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex _ =
      (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    ext n
    simp only [Functor.comp_map, HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.eqToHom_f, eqToHom_refl, comp_id,
      id_comp, SimplicialObject.whiskering_obj_map_app]
  · intro X
    apply HomologicalComplex.ext
    · rintro i j (rfl : j + 1 = i)
      dsimp only [Functor.comp_obj]
      simp only [Functor.mapHomologicalComplex_obj_d, alternatingFaceMapComplex_obj_d,
        eqToHom_refl, id_comp, comp_id, AlternatingFaceMapComplex.objD, Functor.map_sum,
        Functor.map_zsmul]
      rfl
    · ext n
      rfl
/-
**AlgebraicTopology.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (alternatingFaceMapComplex C).Additive where
/-
**AlgebraicTopology.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Limits.HasPullbacks C] : (alternatingFaceMapComplex C).PreservesMonomorphisms where
  preserves _ _ := HomologicalComplex.mono_of_mono_f _ fun _ ↦ by dsimp; infer_instance
/-
**AlgebraicTopology.karoubi_alternatingFaceMapComplex_d** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicTopology`。
形式化陈述：karoubi_alternatingFaceMapComplex_d (P : Karoubi (SimplicialObject C)) (n 
: Nat) : ((AlternatingFaceMapComplex.obj (KaroubiFunctorCategoryEmbedding.obj P)
).d (n + 1) n).f = P.p.app (op ⦋n + 1⦌) ≫ (AlternatingFaceMapComplex.obj P.X).d 
(n + 1) n
参数：P : Karoubi (SimplicialObject C)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq`：obj_d_eq (X : Simp
licialObject C) (n : Nat) : (AlternatingFaceMapComplex.obj X).d (n + 1) n = ∑ i 
: Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.…
· 使用定理 `CategoryTheory.Idempotents.Karoubi.sum_hom`：sum_hom [Preadditive C] {P Q
 : Karoubi C} {α : Type*} (s : Finset α) (f : α -> (P ⟶ Q)) : (∑ x in s, f x).f 
= ∑ x in s, (f x).f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Idempotents.Karoubi.zsmul_hom`：zsmul_hom [Preadditive C] 
{P Q : Karoubi C} (n : Int) (f : P ⟶ Q) : (n • f).f = n • f.f
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `CategoryTheory.Preadditive.comp_zsmul`：comp_zsmul (n : Int) : f ≫ (n • g
) = n • f ≫ g
-/
theorem karoubi_alternatingFaceMapComplex_d (P : Karoubi (SimplicialObject C)) (n : ℕ) :
    ((AlternatingFaceMapComplex.obj (KaroubiFunctorCategoryEmbedding.obj P)).d (n + 1) n).f =
      P.p.app (op ⦋n + 1⦌) ≫ (AlternatingFaceMapComplex.obj P.X).d (n + 1) n := by
  dsimp
  simp only [AlternatingFaceMapComplex.obj_d_eq, Karoubi.sum_hom, Preadditive.comp_sum,
    Karoubi.zsmul_hom, Preadditive.comp_zsmul]
  rfl

namespace AlternatingFaceMapComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation which gives the augmentation of the alternating face map
complex attached to an augmented simplicial object. -/
/-
**AlgebraicTopology.AlternatingFaceMapComplex.** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicTopology.AlternatingFaceMapComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation which gives the augmentation of the alternating face 
map
complex attached to an augmented simplicial object.
-/
def ε [Limits.HasZeroObject C] :
    SimplicialObject.Augmented.drop ⋙ AlgebraicTopology.alternatingFaceMapComplex C ⟶
      SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ C where
  app X := by
    refine (ChainComplex.toSingle₀Equiv _ _).symm ?_
    refine ⟨X.hom.app (op ⦋0⦌), ?_⟩
    dsimp
    rw [alternatingFaceMapComplex_obj_d, objD, Fin.sum_univ_two, Fin.val_zero,
      pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul, add_comp,
      neg_comp, SimplicialObject.δ_naturality, SimplicialObject.δ_naturality]
    apply add_neg_cancel
  naturality X Y f := by
    apply HomologicalComplex.to_single_hom_ext
    #adaptation_note /-- This proof broke at nightly-2026-04-28. It used to be:
    ```
    dsimp
    simp [ChainComplex.toSingle₀Equiv, SimplicialObject.Augmented.w₀]
    ```
    The proof below is an emergency repair, and I've asked the authors of this file to review.
    -/
    change f.left.app _ ≫ _ = _ ≫ ((ChainComplex.single₀ _).map f.right).f 0
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
      ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
      ChainComplex.single₀_map_f_zero]
    exact SimplicialObject.Augmented.w₀ f

@[simp]
/-
**AlgebraicTopology.AlternatingFaceMapComplex.** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicTopology.AlternatingFaceMapComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_app_f_zero [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C) :
    (ε.app X).f 0 = X.hom.app (op ⦋0⦌) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

@[simp]
/-
**AlgebraicTopology.AlternatingFaceMapComplex.** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicTopology.AlternatingFaceMapComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_app_f_succ [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C) (n : ℕ) :
    (ε.app X).f (n + 1) = 0 := rfl

end AlternatingFaceMapComplex

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/

variable {A : Type*} [Category* A] [Abelian A]

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion map of the Moore complex in the alternating face map complex -/
/-
**AlgebraicTopology.inclusionOfMooreComplexMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicTopology`。
形式化陈述：inclusionOfMooreComplexMap (X : SimplicialObject A) : (normalizedMooreComp
lex A).obj X ⟶ (alternatingFaceMapComplex A).obj X
参数：X : SimplicialObject A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map of the Moore complex in the alternating face map complex
-/
def inclusionOfMooreComplexMap (X : SimplicialObject A) :
    (normalizedMooreComplex A).obj X ⟶ (alternatingFaceMapComplex A).obj X :=
  ChainComplex.ofHom (fun n => (NormalizedMooreComplex.objX X n).arrow) <| fun i ↦ by
  /- we have to show the compatibility of the differentials on the alternating
           face map complex with those defined on the normalized Moore complex:
           we first get rid of the terms of the alternating sum that are obviously
           zero on the normalized_Moore_complex -/
  simp only [normalizedMooreComplex, NormalizedMooreComplex.obj, alternatingFaceMapComplex,
    AlternatingFaceMapComplex.obj, ChainComplex.of_d, AlternatingFaceMapComplex.objD, comp_sum]
  rw [Fin.sum_univ_succ, Fintype.sum_eq_zero]
  swap
  · intro j
    rw [NormalizedMooreComplex.objX_add_one, comp_zsmul,
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ _ (Finset.mem_univ j)),
      Category.assoc, kernelSubobject_arrow_comp, comp_zero, smul_zero]
  -- finally, we study the remaining term which is induced by X.δ 0
  rw [add_zero, Fin.val_zero, pow_zero, one_zsmul]
  dsimp [NormalizedMooreComplex.objD, NormalizedMooreComplex.objX]
  cases i <;> simp

@[simp]
/-
**AlgebraicTopology.inclusionOfMooreComplexMap_f** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicTopology`。
形式化陈述：inclusionOfMooreComplexMap_f (X : SimplicialObject A) (n : Nat) : (inclusi
onOfMooreComplexMap X).f n = (NormalizedMooreComplex.objX X n).arrow
参数：X : SimplicialObject A；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusionOfMooreComplexMap_f (X : SimplicialObject A) (n : ℕ) :
    (inclusionOfMooreComplexMap X).f n = (NormalizedMooreComplex.objX X n).arrow := by
  dsimp [inclusionOfMooreComplexMap]

variable (A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation -/
@[simps]
/-
**AlgebraicTopology.inclusionOfMooreComplex** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Topology`。
形式化陈述：inclusionOfMooreComplex : normalizedMooreComplex A ⟶ alternatingFaceMapCom
plex A where app
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation
-/
def inclusionOfMooreComplex : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A where
  app := inclusionOfMooreComplexMap

namespace AlternatingCofaceMapComplex

variable (X Y : CosimplicialObject C)

/-- The differential on the alternating coface map complex is the alternate
sum of the coface maps -/
@[simp]
/-
**AlgebraicTopology.AlternatingCofaceMapComplex.objD** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicTopology.AlternatingCofaceMapComplex`。
形式化陈述：objD (n : Nat) : X.obj ⦋n⦌ ⟶ X.obj ⦋n + 1⦌
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential on the alternating coface map complex is the alternate
sum of the coface maps
-/
def objD (n : ℕ) : X.obj ⦋n⦌ ⟶ X.obj ⦋n + 1⦌ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i
/-
**AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicTopology.AlternatingCofaceMapComplex`。
形式化陈述：d_eq_unop_d (n : Nat) : objD X n = (AlternatingFaceMapComplex.objD ((cosim
plicialSimplicialEquiv C).functor.obj (op X)) n).unop
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.unop_sum`：unop_sum (X Y : Cᵒᵖ) {ι : Type*} (s : Finset ι)
 (f : ι -> (X ⟶ Y)) : (s.sum f).unop = s.sum fun i => (f i).unop
-/
theorem d_eq_unop_d (n : ℕ) :
    objD X n =
      (AlternatingFaceMapComplex.objD ((cosimplicialSimplicialEquiv C).functor.obj (op X))
          n).unop := by
  simp only [objD, AlternatingFaceMapComplex.objD, unop_sum, unop_zsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicTopology.AlternatingCofaceMapComplex.d_squared** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicTopology.AlternatingCofaceMapComplex`。
形式化陈述：d_squared (n : Nat) : objD X n ≫ objD X (n + 1) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d`：d_eq_unop_d (
n : Nat) : objD X n = (AlternatingFaceMapComplex.objD ((cosimplicialSimplicialEq
uiv C).functor.obj (op X)) n).unop
· 使用定理 `AlgebraicTopology.AlternatingFaceMapComplex.d_squared`：d_squared (n : Na
t) : objD X (n + 1) ≫ objD X n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem d_squared (n : ℕ) : objD X n ≫ objD X (n + 1) = 0 := by
  simp only [d_eq_unop_d, ← unop_comp, AlternatingFaceMapComplex.d_squared, unop_zero]

/-- The alternating coface map complex, on objects -/
/-
**AlgebraicTopology.AlternatingCofaceMapComplex.obj** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicTopology.AlternatingCofaceMapComplex`。
形式化陈述：obj : CochainComplex C Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.AlternatingCofaceMapComplex.d_squared`：d_squared (n : 
Nat) : objD X n ≫ objD X (n + 1) = 0

--- 原说明 ---
The alternating coface map complex, on objects
-/
def obj : CochainComplex C ℕ :=
  CochainComplex.of (fun n => X.obj ⦋n⦌) (objD X) (d_squared X)

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
@[simp]
/-
**AlgebraicTopology.AlternatingCofaceMapComplex.map** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicTopology.AlternatingCofaceMapComplex`。
形式化陈述：map (f : X ⟶ Y) : obj X ⟶ obj Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The alternating face map complex, on morphisms
-/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  CochainComplex.ofHom (fun n => f.app ⦋n⦌) fun n => by
    simp only [obj, CochainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum, sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [comp_zsmul, zsmul_comp]
    congr 1
    symm
    apply f.naturality

end AlternatingCofaceMapComplex

variable (C)

/-- The alternating coface map complex, as a functor -/
@[simps]
/-
**AlgebraicTopology.alternatingCofaceMapComplex** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicTopology`。
形式化陈述：alternatingCofaceMapComplex : CosimplicialObject C ⥤ CochainComplex C Nat 
where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The alternating coface map complex, as a functor
-/
def alternatingCofaceMapComplex : CosimplicialObject C ⥤ CochainComplex C ℕ where
  obj := AlternatingCofaceMapComplex.obj
  map f := AlternatingCofaceMapComplex.map f

end AlgebraicTopology

