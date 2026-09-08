/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
## Moore complex

We construct the normalized Moore complex, as a functor
`SimplicialObject C ⥤ ChainComplex C ℕ`,
for any abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.

This functor is one direction of the Dold-Kan equivalence, which we're still working towards.

### References

* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex
-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

open Opposite

open scoped Simplicial

namespace AlgebraicTopology

variable {C : Type*} [Category* C] [Abelian C]

attribute [local instance] Abelian.hasPullbacks

/-! The definitions in this namespace are all auxiliary definitions for `NormalizedMooreComplex`
and should usually only be accessed via that. -/


namespace NormalizedMooreComplex

open CategoryTheory.Subobject

variable (X : SimplicialObject C)

/-- The normalized Moore complex in degree `n`, as a subobject of `X n`.
-/
/-
**AlgebraicTopology.NormalizedMooreComplex.objX** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicTopology.NormalizedMooreComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [Ca
tegoryTheory.Abelian C] →       (X : CategoryTheory.SimplicialObject C) → (n : ℕ
) → CategoryTheory.Subobject (X.obj (Opposite.op { len := n }))
参数：X : CategoryTheory.SimplicialObject C；n : ℕ；X.obj (Opposite.op { len := n })。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasPullbacks`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasPul
lbacks C

--- 原说明 ---
The normalized Moore complex in degree `n`, as a subobject of `X n`.
-/
def objX : ∀ n : ℕ, Subobject (X.obj (op ⦋n⦌))
  | 0 => ⊤
  | n + 1 => Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ)
/-
**AlgebraicTopology.NormalizedMooreComplex.objX_zero** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicTopology.NormalizedMooreComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   (X : CategoryTheory.SimplicialObject C), AlgebraicTop
ology.NormalizedMooreComplex.objX X 0 = ⊤
参数：X : CategoryTheory.SimplicialObject C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem objX_zero : objX X 0 = ⊤ :=
  rfl
/-
**AlgebraicTopology.NormalizedMooreComplex.objX_add_one** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicTopology.NormalizedMooreComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   (X : CategoryTheory.SimplicialObject C) (n : ℕ),   Al
gebraicTopology.NormalizedMooreComplex.objX X (n + 1) =     Finset.univ.inf fun 
k => CategoryTheory.Limits.kernelSubobject (X.δ k.succ)
参数：X : CategoryTheory.SimplicialObject C；n : ℕ；n + 1；X.δ k.succ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem objX_add_one (n) :
    objX X (n + 1) = Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The differentials in the normalized Moore complex.
-/
@[simp]
/-
**AlgebraicTopology.NormalizedMooreComplex.objD** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicTopology.NormalizedMooreComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Abelian C] →       (X : CategoryTheory.SimplicialObject C)
 →         (n : ℕ) →           CategoryTheory.Subobject.underlying.obj (Algebrai
cTopology.NormalizedMooreComplex.objX X (n + 1)) ⟶             CategoryTheory.Su
bobject.underlying.obj (AlgebraicTopology.NormalizedMooreComplex.objX X n)
参数：X : CategoryTheory.SimplicialObject C；n : ℕ；AlgebraicTopology.NormalizedMoore
Complex.objX X (n + 1)；AlgebraicTopology.NormalizedMooreComplex.objX X n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differentials in the normalized Moore complex.
-/
def objD : ∀ n : ℕ, (objX X (n + 1) : C) ⟶ (objX X n : C)
  | 0 => Subobject.arrow _ ≫ X.δ (0 : Fin 2) ≫ inv (⊤ : Subobject _).arrow
  | n + 1 => by
    -- The differential is `Subobject.arrow _ ≫ X.δ (0 : Fin (n+3))`,
    -- factored through the intersection of the kernels.
    refine factorThru _ (arrow _ ≫ X.δ (0 : Fin (n + 3))) ?_
    -- We now need to show that it factors!
    -- A morphism factors through an intersection of subobjects if it factors through each.
    refine (finset_inf_factors _).mpr fun i _ => ?_
    -- A morphism `f` factors through the kernel of `g` exactly if `f ≫ g = 0`.
    apply kernelSubobject_factors
    dsimp [objX]
    -- Use a simplicial identity
    rw [Category.assoc, ← Fin.castSucc_zero, ← X.δ_comp_δ (Fin.zero_le i.succ)]
    -- We can rewrite the arrow out of the intersection of all the kernels as a composition
    -- of a morphism we don't care about with the arrow out of the kernel of `X.δ i.succ.succ`.
    rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i.succ (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicTopology.NormalizedMooreComplex.d_squared** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicTopology.NormalizedMooreComplex`。
形式化陈述：d_squared (n : Nat) : objD X (n + 1) ≫ objD X n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasPullbacks`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasPul
lbacks C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (P : CategoryTheory.Subobject Y) 
(f : X ⟶ Y)   (h : P.Factors f) {Z : …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_zero`：∀ {n : ℕ} [inst : NeZero n], Fin.castSucc 0 = 0
· 使用定理 `CategoryTheory.SimplicialObject.δ_comp_δ_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (X : CategoryTheory.SimplicialObject C) {n : ℕ}
   {i j : Fin (n + 2)},   i ≤ j →   …
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用定理 `CategoryTheory.Subobject.finset_inf_arrow_factors`：finset_inf_arrow_fact
ors {I : Type*} {B : C} (s : Finset I) (P : I -> Subobject B) (i : I) (m : i in 
s) : (P i).Factors (s.inf P).arrow
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Subobject.factors_of_factors_right`：factors_of_factors_ri
ght {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z} (h : P.Factors g) : P.
Factors (f ≫ g)
· 使用定理 `CategoryTheory.Subobject.factorThru_right`：factorThru_right {X Y Z : C} 
{P : Subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.Factors g) : f ≫ P.factorThru g
 h = P.factorThru (f ≫ g) (fact…
· 使用定理 `CategoryTheory.Subobject.factorThru_eq_zero`：factorThru_eq_zero [HasZero
Morphisms C] {X Y : C} {P : Subobject Y} {f : X ⟶ Y} {h : Factors P f} : P.facto
rThru f h = 0 ↔ f = 0
· 使用定理 `CategoryTheory.SimplicialObject.δ_comp_δ`：δ_comp_δ {n} {i j : Fin (n + 2
)} (H : i <= j) : X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j
-/
theorem d_squared (n : ℕ) : objD X (n + 1) ≫ objD X n = 0 := by
  -- It's a pity we need to do a case split here;
    -- after the first rw the proofs are almost identical
  rcases n with _ | n <;> dsimp [objD]
  · rw [Subobject.factorThru_arrow_assoc, Category.assoc, ← Fin.castSucc_zero,
      ← X.δ_comp_δ_assoc (Fin.zero_le (0 : Fin 2)),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin 2) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
  · rw [factorThru_right, factorThru_eq_zero, factorThru_arrow_assoc, Category.assoc,
      ← Fin.castSucc_zero,
      ← X.δ_comp_δ (Fin.zero_le (0 : Fin (n + 3))),
      ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ (0 : Fin (n + 3)) (by simp)),
      Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]

/-- The normalized Moore complex functor, on objects.
-/
@[simps!]
/-
**AlgebraicTopology.NormalizedMooreComplex.obj** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicTopology.NormalizedMooreComplex`。
形式化陈述：obj (X : SimplicialObject C) : ChainComplex C Nat
参数：X : SimplicialObject C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicTopology.NormalizedMooreComplex.d_squared`：d_squared (n : Nat) 
: objD X (n + 1) ≫ objD X n = 0

--- 原说明 ---
The normalized Moore complex functor, on objects.
-/
def obj (X : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n => (objX X n : C))
    (-- the coercion here picks a representative of the subobject
      objD X) (d_squared X)

variable {X} {Y : SimplicialObject C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized Moore complex functor, on morphisms.
-/
@[simps!]
/-
**AlgebraicTopology.NormalizedMooreComplex.map** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicTopology.NormalizedMooreComplex`。
形式化陈述：map (f : X ⟶ Y) : obj X ⟶ obj Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalized Moore complex functor, on morphisms.
-/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom
    (fun n => factorThru _ (arrow _ ≫ f.app (op ⦋n⦌)) (by
      cases n <;> dsimp
      · apply top_factors
      · refine (finset_inf_factors _).mpr fun i _ => kernelSubobject_factors _ _ ?_
        rw [Category.assoc, SimplicialObject.δ, ← f.naturality,
          ← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ i (by simp)),
          Category.assoc]
        rw [← SimplicialObject.δ_def, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]))
    fun n => by cases n <;> dsimp [objD, objX, ChainComplex.of.d] <;> cat_disch

end NormalizedMooreComplex

open NormalizedMooreComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The (normalized) Moore complex of a simplicial object `X` in an abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
-/
@[simps]
/-
**AlgebraicTopology.normalizedMooreComplex** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicT
opology`。
形式化陈述：normalizedMooreComplex : SimplicialObject C ⥤ ChainComplex C Nat where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (normalized) Moore complex of a simplicial object `X` in an abelian category
 `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
-/
def normalizedMooreComplex : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj := obj
  map f := map f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- Not `@[simp]` as `simp` can prove this.
/-
**AlgebraicTopology.normalizedMooreComplex_objD** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicTopology`。
形式化陈述：normalizedMooreComplex_objD (X : SimplicialObject C) (n : Nat) : ((normali
zedMooreComplex C).obj X).d (n + 1) n = NormalizedMooreComplex.objD X n
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
theorem normalizedMooreComplex_objD (X : SimplicialObject C) (n : ℕ) :
    ((normalizedMooreComplex C).obj X).d (n + 1) n = NormalizedMooreComplex.objD X n := by
  simp [-objD, -obj_X]

end AlgebraicTopology

