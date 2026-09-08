/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import Mathlib.AlgebraicTopology.DoldKan.PInfty

/-!

# Construction of the inverse functor of the Dold-Kan equivalence


In this file, we construct the functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`
which shall be the inverse functor of the Dold-Kan equivalence in the case of abelian categories,
and more generally pseudoabelian categories.

By definition, when `K` is a `ChainComplex`, `Γ₀.obj K` is a simplicial object which
sends `Δ : SimplexCategoryᵒᵖ` to a certain coproduct indexed by the set
`Splitting.IndexSet Δ` whose elements consists of epimorphisms `e : Δ.unop ⟶ Δ'.unop`
(with `Δ' : SimplexCategoryᵒᵖ`); the summand attached to such an `e` is `K.X Δ'.unop.len`.
By construction, `Γ₀.obj K` is a split simplicial object whose splitting is `Γ₀.splitting K`.

We also construct `Γ₂ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C)`
which shall be an equivalence for any additive category `C`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits SimplexCategory
  SimplicialObject Opposite CategoryTheory.Idempotents Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] (K K' : ChainComplex C ℕ) (f : K ⟶ K')
  {Δ Δ' Δ'' : SimplexCategory}

/-- `Isδ₀ i` is a simple condition used to check whether a monomorphism `i` in
`SimplexCategory` identifies to the coface map `δ 0`. -/
@[nolint unusedArguments]
/-
**AlgebraicTopology.DoldKan.Is** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.Dold
Kan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Isδ₀ i` is a simple condition used to check whether a monomorphism `i` in
`SimplexCategory` identifies to the coface map `δ 0`.
-/
def Isδ₀ {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] : Prop :=
  Δ.len = Δ'.len + 1 ∧ i.toOrderHom 0 ≠ 0

namespace Isδ₀

/-
**AlgebraicTopology.DoldKan.Isδ₀.iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolog
y.DoldKan.Isδ₀`。
形式化陈述：iff {j : Nat} {i : Fin (j + 2)} : Isδ₀ (SimplexCategory.δ i) ↔ i = 0
参数：j + 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.instMonoδ`：∀ {n : ℕ} {i : Fin (n + 2)}, CategoryTheory.M
ono (SimplexCategory.δ i)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `Fin.succAbove_ne_zero_zero`：succAbove_ne_zero_zero [NeZero n] {a : Fin (
n + 1)} (ha : a != 0) : a.succAbove 0 = 0
· 使用定理 `Fin.succ_ne_zero`：∀ {n : ℕ} (k : Fin n), k.succ ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iff {j : ℕ} {i : Fin (j + 2)} : Isδ₀ (SimplexCategory.δ i) ↔ i = 0 := by
  constructor
  · rintro ⟨_, h₂⟩
    by_contra h
    exact h₂ (Fin.succAbove_ne_zero_zero h)
  · rintro rfl
    exact ⟨rfl, by dsimp; exact Fin.succ_ne_zero (0 : Fin (j + 1))⟩
/-
**AlgebraicTopology.DoldKan.Isδ₀.eq_** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopolog
y.DoldKan.Isδ₀`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_δ₀ {n : ℕ} {i : ⦋n⦌ ⟶ ⦋n + 1⦌} [Mono i] (hi : Isδ₀ i) :
    i = SimplexCategory.δ 0 := by
  obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono i
  rw [iff] at hi
  rw [hi]

end Isδ₀

namespace Γ₀

namespace Obj

/-- In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : Splitting.IndexSet Δ`,
the summand `summand K Δ A` is `K.X A.1.len`. -/
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.summand** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicT
opology.DoldKan.Γ₀.Obj`。
形式化陈述：summand (Δ : SimplexCategoryᵒᵖ) (A : Splitting.IndexSet Δ) : C
参数：Δ : SimplexCategoryᵒᵖ；A : Splitting.IndexSet Δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : Splittin
g.IndexSet Δ`,
the summand `summand K Δ A` is `K.X A.1.len`.
-/
def summand (Δ : SimplexCategoryᵒᵖ) (A : Splitting.IndexSet Δ) : C :=
  K.X A.1.unop.len

/-- The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : Splitting.IndexSet Δ` -/
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.obj** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopol
ogy.DoldKan.Γ₀.Obj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : Splittin
g.IndexSet Δ`
-/
def obj₂ (K : ChainComplex C ℕ) (Δ : SimplexCategoryᵒᵖ) [HasFiniteCoproducts C] : C :=
  ∐ fun A : Splitting.IndexSet Δ => summand K Δ A

namespace Termwise

/-- A monomorphism `i : Δ' ⟶ Δ` induces a morphism `K.X Δ.len ⟶ K.X Δ'.len` which
is the identity if `Δ = Δ'`, the differential on the complex `K` if `i = δ 0`, and
zero otherwise. -/
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicTopology.DoldKan.Γ₀.Obj.Termwise`。
形式化陈述：mapMono (K : ChainComplex C Nat) {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mo
no i] : K.X Δ.len ⟶ K.X Δ'.len
参数：K : ChainComplex C Nat；i : Δ' ⟶ Δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monomorphism `i : Δ' ⟶ Δ` induces a morphism `K.X Δ.len ⟶ K.X Δ'.len` which
is the identity if `Δ = Δ'`, the differential on the complex `K` if `i = δ 0`, a
nd
zero otherwise.
-/
def mapMono (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    K.X Δ.len ⟶ K.X Δ'.len := by
  by_cases Δ = Δ'
  · exact eqToHom (by congr)
  · by_cases Isδ₀ i
    · exact K.d Δ.len Δ'.len
    · exact 0

variable (Δ) in
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_id** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise`。
形式化陈述：mapMono_id : mapMono K (𝟙 Δ) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
-/
theorem mapMono_id : mapMono K (𝟙 Δ) = 𝟙 _ := by
  unfold mapMono
  simp only [eqToHom_refl, dite_eq_ite, if_true]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMono_δ₀' (i : Δ' ⟶ Δ) [Mono i] (hi : Isδ₀ i) : mapMono K i = K.d Δ.len Δ'.len := by
  unfold mapMono
  suffices Δ ≠ Δ' by
    simp only [dif_neg this, dif_pos hi]
  rintro rfl
  simpa only [left_eq_add, Nat.one_ne_zero] using hi.1

@[simp]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMono_δ₀ {n : ℕ} : mapMono K (δ (0 : Fin (n + 2))) = K.d (n + 1) n :=
  mapMono_δ₀' K _ (by rw [Isδ₀.iff])
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise`。
形式化陈述：mapMono_eq_zero (i : Δ' ⟶ Δ) [Mono i] (h₁ : Δ != Δ') (h₂ : ¬Isδ₀ i) : mapM
ono K i = 0
参数：i : Δ' ⟶ Δ；h₁ : Δ != Δ'；h₂ : ¬Isδ₀ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
-/
theorem mapMono_eq_zero (i : Δ' ⟶ Δ) [Mono i] (h₁ : Δ ≠ Δ') (h₂ : ¬Isδ₀ i) : mapMono K i = 0 := by
  unfold mapMono
  rw [Ne] at h₁
  split_ifs
  rfl

variable {K K'}

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_naturality** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise`。
形式化陈述：mapMono_naturality (i : Δ ⟶ Δ') [Mono i] : mapMono K i ≫ f.f Δ.len = f.f Δ
'.len ≫ mapMono K' i
参数：i : Δ ⟶ Δ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem mapMono_naturality (i : Δ ⟶ Δ') [Mono i] :
    mapMono K i ≫ f.f Δ.len = f.f Δ'.len ≫ mapMono K' i := by
  unfold mapMono
  split_ifs with h
  · subst h
    simp only [id_comp, eqToHom_refl, comp_id]
  · rw [HomologicalComplex.Hom.comm]
  · rw [zero_comp, comp_zero]

variable (K)

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_comp** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise`。
形式化陈述：mapMono_comp (i' : Δ'' ⟶ Δ') (i : Δ' ⟶ Δ) [Mono i'] [Mono i] : mapMono K i
 ≫ mapMono K i' = mapMono K (i' ≫ i)
参数：i' : Δ'' ⟶ Δ'；i : Δ' ⟶ Δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimplexCategory.eq_id_of_mono`：eq_id_of_mono {x : SimplexCategory} (i : 
x ⟶ x) [Mono i] : i = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono.congr_simp`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pr
eadditive C]   (K : ChainComplex C ℕ) {Δ' Δ : Simp…
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_id`：mapMono_id : mapMo
no K (𝟙 Δ) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `SimplexCategory.len_lt_of_mono`：len_lt_of_mono {Δ' Δ : SimplexCategory} 
(i : Δ' ⟶ Δ) [Mono i] (hi' : Δ != Δ') : Δ'.len < Δ.len
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_eq_zero`：mapMono_eq_ze
ro (i : Δ' ⟶ Δ) [Mono i] (h₁ : Δ != Δ') (h₂ : ¬Isδ₀ i) : mapMono K i = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_δ₀'`：mapMono_δ₀' (i : 
Δ' ⟶ Δ) [Mono i] (hi : Isδ₀ i) : mapMono K i = K.d Δ.len Δ'.len
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
theorem mapMono_comp (i' : Δ'' ⟶ Δ') (i : Δ' ⟶ Δ) [Mono i'] [Mono i] :
    mapMono K i ≫ mapMono K i' = mapMono K (i' ≫ i) := by
  -- case where i : Δ' ⟶ Δ is the identity
  by_cases h₁ : Δ = Δ'
  · subst h₁
    simp only [SimplexCategory.eq_id_of_mono i, comp_id, id_comp, mapMono_id K]
  -- case where i' : Δ'' ⟶ Δ' is the identity
  by_cases h₂ : Δ' = Δ''
  · subst h₂
    simp only [SimplexCategory.eq_id_of_mono i', comp_id, id_comp, mapMono_id K]
  -- then the RHS is always zero
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i h₁)
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i' h₂)
  have eq : Δ.len = Δ''.len + (k + k' + 2) := by lia
  rw [mapMono_eq_zero K (i' ≫ i) _ _]; rotate_left
  · by_contra h
    simp only [left_eq_add, h, add_eq_zero, and_false, reduceCtorEq] at eq
  · by_contra h
    simp only [h.1, add_right_inj] at eq
    lia
  -- in all cases, the LHS is also zero, either by definition, or because d ≫ d = 0
  by_cases h₃ : Isδ₀ i
  · by_cases h₄ : Isδ₀ i'
    · rw [mapMono_δ₀' K i h₃, mapMono_δ₀' K i' h₄, HomologicalComplex.d_comp_d]
    · simp only [mapMono_eq_zero K i' h₂ h₄, comp_zero]
  · simp only [mapMono_eq_zero K i h₁ h₃, zero_comp]

end Termwise

variable [HasFiniteCoproducts C]

/-- The simplicial morphism on the simplicial object `Γ₀.obj K` induced by
a morphism `Δ' → Δ` in `SimplexCategory` is defined on each summand
associated to an `A : Splitting.IndexSet Δ` in terms of the epi-mono factorisation
of `θ ≫ A.e`. -/
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.map** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopol
ogy.DoldKan.Γ₀.Obj`。
形式化陈述：map (K : ChainComplex C Nat) {Δ' Δ : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') : obj
₂ K Δ ⟶ obj₂ K Δ'
参数：K : ChainComplex C Nat；θ : Δ ⟶ Δ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplicial morphism on the simplicial object `Γ₀.obj K` induced by
a morphism `Δ' → Δ` in `SimplexCategory` is defined on each summand
associated to an `A : Splitting.IndexSet Δ` in terms of the epi-mono factorisati
on
of `θ ≫ A.e`.
-/
def map (K : ChainComplex C ℕ) {Δ' Δ : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') : obj₂ K Δ ⟶ obj₂ K Δ' :=
  Sigma.desc fun A =>
    Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ Sigma.ι (summand K Δ') (A.pull θ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicTopology.DoldKan.Γ₀.Obj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   (K : ChainComplex C ℕ) [inst_2 : CategoryTheory.L
imits.HasFiniteCoproducts C] {Δ Δ' : SimplexCategoryᵒᵖ}   (A : CategoryTheory.Si
mplicialObject.Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') {Δ'' : SimplexCategory}   {e :
 Opposite.unop Δ' ⟶ Δ''} {i : Δ'' ⟶ Opposite.unop A.fst} [inst_3 : CategoryTheor
y.Epi e]   [inst_4 : CategoryTheory.Mono i],   CategoryTheory.CategoryStruct.com
p e i = CategoryTheory.CategoryStruct.comp θ.unop A.e →     CategoryTheory.Categ
oryStruct.comp (((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj A)     
    ((AlgebraicTopology.DoldKan.Γ₀.obj K).map θ) =       CategoryTheory.Category
Struct.comp (AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono K i)         (((A
lgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ').inj           (CategoryTheory
.SimplicialObject.Splitting.IndexSet.mk e))
参数：K : ChainComplex C ℕ；A : CategoryTheory.SimplicialObject.Splitting.IndexSet Δ
；θ : Δ ⟶ Δ'；((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj A；(Algebrai
cTopology.DoldKan.Γ₀.obj K).map θ；AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapM
ono K i；((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ').inj           (Cat
egoryTheory.SimplicialObject.Splitting.IndexSet.mk e)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand₀`：map_on_summand₀ {Δ Δ' 
: SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) {θ : Δ ⟶ Δ'} {Δ'' : SimplexCateg
ory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_id`：mapMono_id : mapMo
no K (𝟙 Δ) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem map_on_summand₀ {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) {θ : Δ ⟶ Δ'}
    {Δ'' : SimplexCategory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [Epi e] [Mono i]
    (fac : e ≫ i = θ.unop ≫ A.e) :
    Sigma.ι (summand K Δ) A ≫ map K θ =
      Termwise.mapMono K i ≫ Sigma.ι (summand K Δ') (Splitting.IndexSet.mk e) := by
  simp only [map, colimit.ι_desc, Cofan.mk_ι_app]
  obtain rfl := SimplexCategory.image_eq fac
  congr
  · exact SimplexCategory.image_ι_eq fac
  · dsimp only [SimplicialObject.Splitting.IndexSet.pull]
    congr
    exact SimplexCategory.factorThruImage_eq fac

set_option backward.isDefEq.respectTransparency false in -- This is needed below
@[reassoc]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicTopology.DoldKan.Γ₀.Obj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   (K : ChainComplex C ℕ) [inst_2 : CategoryTheory.L
imits.HasFiniteCoproducts C] {Δ Δ' : SimplexCategoryᵒᵖ}   (A : CategoryTheory.Si
mplicialObject.Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') {Δ'' : SimplexCategory}   {e :
 Opposite.unop Δ' ⟶ Δ''} {i : Δ'' ⟶ Opposite.unop A.fst} [inst_3 : CategoryTheor
y.Epi e]   [inst_4 : CategoryTheory.Mono i],   CategoryTheory.CategoryStruct.com
p e i = CategoryTheory.CategoryStruct.comp θ.unop A.e →     CategoryTheory.Categ
oryStruct.comp (((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj A)     
    ((AlgebraicTopology.DoldKan.Γ₀.obj K).map θ) =       CategoryTheory.Category
Struct.comp (AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono K i)         (((A
lgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ').inj           (CategoryTheory
.SimplicialObject.Splitting.IndexSet.mk e))
参数：K : ChainComplex C ℕ；A : CategoryTheory.SimplicialObject.Splitting.IndexSet Δ
；θ : Δ ⟶ Δ'；((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj A；(Algebrai
cTopology.DoldKan.Γ₀.obj K).map θ；AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapM
ono K i；((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ').inj           (Cat
egoryTheory.SimplicialObject.Splitting.IndexSet.mk e)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand₀`：map_on_summand₀ {Δ Δ' 
: SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) {θ : Δ ⟶ Δ'} {Δ'' : SimplexCateg
ory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_id`：mapMono_id : mapMo
no K (𝟙 Δ) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem map_on_summand₀' {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') :
    Sigma.ι (summand K Δ) A ≫ map K θ =
      Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫ Sigma.ι (summand K _) (A.pull θ) :=
  map_on_summand₀ K A (A.fac_pull θ)

end Obj

variable [HasFiniteCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, on objects. -/
@[simps]
/-
**AlgebraicTopology.DoldKan.Γ₀.obj** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.
DoldKan.Γ₀`。
形式化陈述：obj (K : ChainComplex C Nat) : SimplicialObject C where obj Δ
参数：K : ChainComplex C Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, on objects.
-/
def obj (K : ChainComplex C ℕ) : SimplicialObject C where
  obj Δ := Obj.obj₂ K Δ
  map θ := Obj.map K θ
  map_id Δ := colimit.hom_ext (fun ⟨A⟩ => by
    dsimp
    have fac : A.e ≫ 𝟙 A.1.unop = (𝟙 Δ).unop ≫ A.e := by rw [unop_id, comp_id, id_comp]
    rw [Obj.map_on_summand₀ K A fac, Obj.Termwise.mapMono_id, id_comp]
    dsimp only [Obj.obj₂]
    rw [comp_id]
    rfl)
  map_comp {Δ'' Δ' Δ} θ' θ := colimit.hom_ext (fun ⟨A⟩ => by
    have fac : θ.unop ≫ θ'.unop ≫ A.e = (θ' ≫ θ).unop ≫ A.e := by rw [unop_comp, assoc]
    rw [← image.fac (θ'.unop ≫ A.e), ← assoc, ←
      image.fac (θ.unop ≫ factorThruImage (θ'.unop ≫ A.e)), assoc] at fac
    simp only [Obj.map_on_summand₀'_assoc K A θ', Obj.map_on_summand₀' K _ θ,
      Obj.Termwise.mapMono_comp_assoc, Obj.map_on_summand₀ K A fac]
    rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- By construction, the simplicial `Γ₀.obj K` is equipped with a splitting. -/
/-
**AlgebraicTopology.DoldKan.Γ₀.splitting** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTop
ology.DoldKan.Γ₀`。
形式化陈述：splitting (K : ChainComplex C Nat) : SimplicialObject.Splitting (Γ₀.obj K)
 where N n
参数：K : ChainComplex C Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By construction, the simplicial `Γ₀.obj K` is equipped with a splitting.
-/
def splitting (K : ChainComplex C ℕ) : SimplicialObject.Splitting (Γ₀.obj K) where
  N n := K.X n
  ι n := Sigma.ι (Γ₀.Obj.summand K (op ⦋n⦌)) (Splitting.IndexSet.id (op ⦋n⦌))
  isColimit' Δ := IsColimit.ofIsoColimit (colimit.isColimit _) (Cofan.ext (Iso.refl _) (by
      intro A
      dsimp [Splitting.cofan']
      rw [comp_id, Γ₀.Obj.map_on_summand₀ K (SimplicialObject.Splitting.IndexSet.id A.1)
        (show A.e ≫ 𝟙 _ = A.e.op.unop ≫ 𝟙 _ by rfl), Γ₀.Obj.Termwise.mapMono_id]
      dsimp
      rw [id_comp]
      rfl))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicTopology.DoldKan.Γ₀.Obj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   (K : ChainComplex C ℕ) [inst_2 : CategoryTheory.L
imits.HasFiniteCoproducts C] {Δ Δ' : SimplexCategoryᵒᵖ}   (A : CategoryTheory.Si
mplicialObject.Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') {Δ'' : SimplexCategory}   {e :
 Opposite.unop Δ' ⟶ Δ''} {i : Δ'' ⟶ Opposite.unop A.fst} [inst_3 : CategoryTheor
y.Epi e]   [inst_4 : CategoryTheory.Mono i],   CategoryTheory.CategoryStruct.com
p e i = CategoryTheory.CategoryStruct.comp θ.unop A.e →     CategoryTheory.Categ
oryStruct.comp (((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj A)     
    ((AlgebraicTopology.DoldKan.Γ₀.obj K).map θ) =       CategoryTheory.Category
Struct.comp (AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono K i)         (((A
lgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ').inj           (CategoryTheory
.SimplicialObject.Splitting.IndexSet.mk e))
参数：K : ChainComplex C ℕ；A : CategoryTheory.SimplicialObject.Splitting.IndexSet Δ
；θ : Δ ⟶ Δ'；((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj A；(Algebrai
cTopology.DoldKan.Γ₀.obj K).map θ；AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapM
ono K i；((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ').inj           (Cat
egoryTheory.SimplicialObject.Splitting.IndexSet.mk e)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand₀`：map_on_summand₀ {Δ Δ' 
: SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) {θ : Δ ⟶ Δ'} {Δ'' : SimplexCateg
ory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_id`：mapMono_id : mapMo
no K (𝟙 Δ) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem Obj.map_on_summand {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ')
    {Δ'' : SimplexCategory} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [Epi e] [Mono i]
    (fac : e ≫ i = θ.unop ≫ A.e) :
    ((Γ₀.splitting K).cofan Δ).inj A ≫ (Γ₀.obj K).map θ =
      Γ₀.Obj.Termwise.mapMono K i ≫ ((Γ₀.splitting K).cofan Δ').inj (Splitting.IndexSet.mk e) := by
  dsimp [Splitting.cofan]
  change (_ ≫ (Γ₀.obj K).map A.e.op) ≫ (Γ₀.obj K).map θ = _
  rw [assoc, ← Functor.map_comp]
  dsimp [splitting]
  rw [Γ₀.Obj.map_on_summand₀ K (Splitting.IndexSet.id A.1)
    (show e ≫ i = ((Splitting.IndexSet.e A).op ≫ θ).unop ≫ 𝟙 _ by rw [comp_id, fac]; rfl)]
  dsimp only [Splitting.IndexSet.id_fst, Splitting.IndexSet.mk, op_unop, Splitting.IndexSet.e]
  rw [Γ₀.Obj.map_on_summand₀ K (Splitting.IndexSet.id (op Δ''))
      (show e ≫ 𝟙 Δ'' = e.op.unop ≫ 𝟙 _ by simp), Termwise.mapMono_id]
  dsimp only [Splitting.IndexSet.id_fst]
  rw [id_comp]
  rfl

@[reassoc]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand'** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicTopology.DoldKan.Γ₀.Obj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   (K : ChainComplex C ℕ) [inst_2 : CategoryTheory.L
imits.HasFiniteCoproducts C] {Δ Δ' : SimplexCategoryᵒᵖ}   (A : CategoryTheory.Si
mplicialObject.Splitting.IndexSet Δ) (θ : Δ ⟶ Δ'),   CategoryTheory.CategoryStru
ct.comp (((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj A)       ((Alg
ebraicTopology.DoldKan.Γ₀.obj K).map θ) =     CategoryTheory.CategoryStruct.comp
       (AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono K         (CategoryThe
ory.Limits.image.ι (CategoryTheory.CategoryStruct.comp θ.unop A.e)))       (((Al
gebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ').inj (A.pull θ))
参数：K : ChainComplex C ℕ；A : CategoryTheory.SimplicialObject.Splitting.IndexSet Δ
；θ : Δ ⟶ Δ'；((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj A；(Algebrai
cTopology.DoldKan.Γ₀.obj K).map θ；AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapM
ono K         (CategoryTheory.Limits.image.ι (CategoryTheory.CategoryStruct.comp
 θ.unop A.e))；((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ').inj (A.pull 
θ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  (K : ChainComplex C ℕ) [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `SimplexCategory.instHasStrongEpiMonoFactorisations`：CategoryTheory.Limit
s.HasStrongEpiMonoFactorisations SimplexCategory
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
-/
theorem Obj.map_on_summand' {Δ Δ' : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) (θ : Δ ⟶ Δ') :
    ((splitting K).cofan Δ).inj A ≫ (obj K).map θ =
      Obj.Termwise.mapMono K (image.ι (θ.unop ≫ A.e)) ≫
        ((splitting K).cofan Δ').inj (A.pull θ) := by
  apply Obj.map_on_summand
  apply image.fac

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.mapMono_on_summand_id** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicTopology.DoldKan.Γ₀.Obj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   (K : ChainComplex C ℕ) [inst_2 : CategoryTheory.L
imits.HasFiniteCoproducts C] {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ)   [inst_3 : C
ategoryTheory.Mono i],   CategoryTheory.CategoryStruct.comp       (((AlgebraicTo
pology.DoldKan.Γ₀.splitting K).cofan (Opposite.op Δ)).inj         (CategoryTheor
y.SimplicialObject.Splitting.IndexSet.id (Opposite.op Δ)))       ((AlgebraicTopo
logy.DoldKan.Γ₀.obj K).map i.op) =     CategoryTheory.CategoryStruct.comp (Algeb
raicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono K i)       (((AlgebraicTopology.Dol
dKan.Γ₀.splitting K).cofan (Opposite.op Δ')).inj         (CategoryTheory.Simplic
ialObject.Splitting.IndexSet.id (Opposite.op Δ')))
参数：K : ChainComplex C ℕ；i : Δ' ⟶ Δ；((AlgebraicTopology.DoldKan.Γ₀.splitting K).c
ofan (Opposite.op Δ)).inj         (CategoryTheory.SimplicialObject.Splitting.Ind
exSet.id (Opposite.op Δ))；(AlgebraicTopology.DoldKan.Γ₀.obj K).map i.op；Algebrai
cTopology.DoldKan.Γ₀.Obj.Termwise.mapMono K i；((AlgebraicTopology.DoldKan.Γ₀.spl
itting K).cofan (Opposite.op Δ')).inj         (CategoryTheory.SimplicialObject.S
plitting.IndexSet.id (Opposite.op Δ'))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  (K : ChainComplex C ℕ) [inst_2 : Ca…
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
-/
theorem Obj.mapMono_on_summand_id {Δ Δ' : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] :
    ((splitting K).cofan _).inj (Splitting.IndexSet.id (op Δ)) ≫ (obj K).map i.op =
      Obj.Termwise.mapMono K i ≫ ((splitting K).cofan _).inj (Splitting.IndexSet.id (op Δ')) :=
  Obj.map_on_summand K (Splitting.IndexSet.id (op Δ)) i.op (rfl : 𝟙 _ ≫ i = i ≫ 𝟙 _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicTopology.DoldKan.Γ₀.Obj.map_epi_on_summand_id** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicTopology.DoldKan.Γ₀.Obj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   (K : ChainComplex C ℕ) [inst_2 : CategoryTheory.L
imits.HasFiniteCoproducts C] {Δ Δ' : SimplexCategory} (e : Δ' ⟶ Δ)   [inst_3 : C
ategoryTheory.Epi e],   CategoryTheory.CategoryStruct.comp       (((AlgebraicTop
ology.DoldKan.Γ₀.splitting K).cofan (Opposite.op Δ)).inj         (CategoryTheory
.SimplicialObject.Splitting.IndexSet.id (Opposite.op Δ)))       ((AlgebraicTopol
ogy.DoldKan.Γ₀.obj K).map e.op) =     ((AlgebraicTopology.DoldKan.Γ₀.splitting K
).cofan (Opposite.op Δ')).inj       (CategoryTheory.SimplicialObject.Splitting.I
ndexSet.mk e)
参数：K : ChainComplex C ℕ；e : Δ' ⟶ Δ；((AlgebraicTopology.DoldKan.Γ₀.splitting K).c
ofan (Opposite.op Δ)).inj         (CategoryTheory.SimplicialObject.Splitting.Ind
exSet.id (Opposite.op Δ))；(AlgebraicTopology.DoldKan.Γ₀.obj K).map e.op；(Algebra
icTopology.DoldKan.Γ₀.splitting K).cofan (Opposite.op Δ')；CategoryTheory.Simplic
ialObject.Splitting.IndexSet.mk e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.map_on_summand`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  (K : ChainComplex C ℕ) [inst_2 : Ca…
· 使用定理 `AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_id`：mapMono_id : mapMo
no K (𝟙 Δ) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem Obj.map_epi_on_summand_id {Δ Δ' : SimplexCategory} (e : Δ' ⟶ Δ) [Epi e] :
    ((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.id (op Δ)) ≫ (Γ₀.obj K).map e.op =
      ((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.mk e) := by
  simpa only [Γ₀.Obj.map_on_summand K (Splitting.IndexSet.id (op Δ)) e.op
      (rfl : e ≫ 𝟙 Δ = e ≫ 𝟙 Δ),
    Γ₀.Obj.Termwise.mapMono_id] using! id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, on morphisms. -/
@[simps]
/-
**AlgebraicTopology.DoldKan.Γ₀.map** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.
DoldKan.Γ₀`。
形式化陈述：map {K K' : ChainComplex C Nat} (f : K ⟶ K') : obj K ⟶ obj K' where app Δ
参数：f : K ⟶ K'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, on morphisms.
-/
def map {K K' : ChainComplex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K' where
  app Δ := (Γ₀.splitting K).desc Δ fun A => f.f A.1.unop.len ≫
    ((Γ₀.splitting K').cofan _).inj A
  naturality {Δ' Δ} θ := by
    apply (Γ₀.splitting K).hom_ext'
    intro A
    simp only [(splitting K).ι_desc_assoc, Obj.map_on_summand'_assoc K _ θ, (splitting K).ι_desc,
      assoc, Obj.map_on_summand' K' _ θ]
    apply Obj.Termwise.mapMono_naturality_assoc

end Γ₀

variable [HasFiniteCoproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `Γ₀' : ChainComplex C ℕ ⥤ SimplicialObject.Split C`
that induces `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, which
shall be the inverse functor of the Dold-Kan equivalence for
abelian or pseudo-abelian categories. -/
@[simps]
/-
**AlgebraicTopology.DoldKan.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldKa
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Γ₀' : ChainComplex C ℕ ⥤ SimplicialObject.Split C`
that induces `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, which
shall be the inverse functor of the Dold-Kan equivalence for
abelian or pseudo-abelian categories.
-/
def Γ₀' : ChainComplex C ℕ ⥤ SimplicialObject.Split C where
  obj K := SimplicialObject.Split.mk' (Γ₀.splitting K)
  map {K K'} f :=
    { F := Γ₀.map f
      f := f.f
      comm := fun n => by
        dsimp
        simp only [← Splitting.cofan_inj_id, (Γ₀.splitting K).ι_desc]
        rfl }

/-- The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, which is
the inverse functor of the Dold-Kan equivalence when `C` is an abelian
category, or more generally a pseudoabelian category. -/
@[simps!]
/-
**AlgebraicTopology.DoldKan.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldKa
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`, which is
the inverse functor of the Dold-Kan equivalence when `C` is an abelian
category, or more generally a pseudoabelian category.
-/
def Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C :=
  Γ₀' ⋙ Split.forget _

/-- The extension of `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`
on the idempotent completions. It shall be an equivalence of categories
for any additive category `C`. -/
@[simps!]
/-
**AlgebraicTopology.DoldKan.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldKa
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of `Γ₀ : ChainComplex C ℕ ⥤ SimplicialObject C`
on the idempotent completions. It shall be an equivalence of categories
for any additive category `C`.
-/
def Γ₂ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  (CategoryTheory.Idempotents.functorExtension₂ _ _).obj Γ₀

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicTopology.DoldKan.HigherFacesVanish.on_** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicTopology.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HigherFacesVanish.on_Γ₀_summand_id (K : ChainComplex C ℕ) (n : ℕ) :
    @HigherFacesVanish C _ _ (Γ₀.obj K) _ n (n + 1)
      (((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.id (op ⦋n + 1⦌))) := by
  intro j _
  have eq := Γ₀.Obj.mapMono_on_summand_id K (SimplexCategory.δ j.succ)
  rw [Γ₀.Obj.Termwise.mapMono_eq_zero K, zero_comp] at eq; rotate_left
  · intro h
    exact (Nat.succ_ne_self n) (congr_arg SimplexCategory.len h)
  · exact fun h => Fin.succ_ne_zero j (by simpa only [Isδ₀.iff] using h)
  exact eq

@[reassoc (attr := simp)]
/-
**AlgebraicTopology.DoldKan.PInfty_on_** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicTopol
ogy.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PInfty_on_Γ₀_splitting_summand_eq_self (K : ChainComplex C ℕ) {n : ℕ} :
    ((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.id (op ⦋n⦌)) ≫
      (PInfty : K[Γ₀.obj K] ⟶ _).f n =
      ((Γ₀.splitting K).cofan _).inj (Splitting.IndexSet.id (op ⦋n⦌)) := by
  rw [PInfty_f]
  rcases n with _ | n
  · simpa only [P_f_0_eq] using! comp_id _
  · exact (HigherFacesVanish.on_Γ₀_summand_id K n).comp_P_eq_self

end DoldKan

end AlgebraicTopology

