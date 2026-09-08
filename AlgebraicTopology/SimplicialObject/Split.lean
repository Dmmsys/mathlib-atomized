/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Data.Fintype.Sigma

/-!

# Split simplicial objects

In this file, we introduce the notion of split simplicial object.
If `C` is a category that has finite coproducts, a splitting
`s : Splitting X` of a simplicial object `X` in `C` consists
of the datum of a sequence of objects `s.N : ℕ → C` (which
we shall refer to as "nondegenerate simplices") and a
sequence of morphisms `s.ι n : s.N n → X _⦋n⦌` that have
the property that a certain canonical map identifies `X _⦋n⦌`
with the coproduct of objects `s.N i` indexed by all possible
epimorphisms `⦋n⦌ ⟶ ⦋i⦌` in `SimplexCategory`. (We do not
assume that the morphisms `s.ι n` are monomorphisms: in the
most common categories, this would be a consequence of the
axioms.)

Simplicial objects equipped with a splitting form a category
`SimplicialObject.Split C`.

## References
* [Stacks: Splitting simplicial objects] https://stacks.math.columbia.edu/tag/017O

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite SimplexCategory

open Simplicial

universe u

variable {C D : Type*} [Category* C] [Category* D]

namespace CategoryTheory.SimplicialObject

namespace Splitting

/-- The index set which appears in the definition of split simplicial objects. -/
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：IndexSet (Δ : SimplexCategoryᵒᵖ)
参数：Δ : SimplexCategoryᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index set which appears in the definition of split simplicial objects.
-/
def IndexSet (Δ : SimplexCategoryᵒᵖ) :=
  Σ Δ' : SimplexCategoryᵒᵖ, { α : Δ.unop ⟶ Δ'.unop // Epi α }

namespace IndexSet

/-- The element in `Splitting.IndexSet Δ` attached to an epimorphism `f : Δ ⟶ Δ'`. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.mk** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：mk {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') [Epi f] : IndexSet (op Δ)
参数：f : Δ ⟶ Δ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The element in `Splitting.IndexSet Δ` attached to an epimorphism `f : Δ ⟶ Δ'`.
-/
def mk {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') [Epi f] : IndexSet (op Δ) :=
  ⟨op Δ', f, inferInstance⟩

variable {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)

/-- The epimorphism in `SimplexCategory` associated to `A : Splitting.IndexSet Δ` -/
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.e** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：e
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The epimorphism in `SimplexCategory` associated to `A : Splitting.IndexSet Δ`
-/
def e :=
  A.2.1
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.SimplicialObject.Splitting.IndexSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi A.e :=
  A.2.2
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.ext'** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.ext** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：ext (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h
₁]) = A₂.e) : A₁ = A₂
参数：A₁ A₂ : IndexSet Δ；h₁ : A₁.1 = A₂.1；h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ext (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e) :
    A₁ = A₂ := by
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩
  simp only at h₁
  subst h₁
  simp only [eqToHom_refl, comp_id, IndexSet.e] at h₂
  simp only [h₂]
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.SimplicialObject.Splitting.IndexSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype (IndexSet Δ) :=
  Fintype.ofInjective
    (fun A =>
      ⟨⟨A.1.unop.len, Nat.lt_succ_iff.mpr (len_le_of_epi A.e)⟩,
        A.e.toOrderHom⟩ :
      IndexSet Δ → Sigma fun k : Fin (Δ.unop.len + 1) => Fin (Δ.unop.len + 1) → Fin (k + 1))
    (by
      rintro ⟨⟨Δ₁⟩, α₁⟩ ⟨⟨Δ₂⟩, α₂⟩ h₁
      simp only [unop_op, Sigma.mk.inj_iff, Fin.mk.injEq] at h₁
      have h₂ : Δ₁ = Δ₂ := by
        ext1
        simpa only [Fin.mk_eq_mk] using h₁.1
      subst h₂
      refine ext _ _ rfl ?_
      ext : 2
      exact eq_of_heq h₁.2)

variable (Δ)

/-- The distinguished element in `Splitting.IndexSet Δ` which corresponds to the
identity of `Δ`. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.id** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：id : IndexSet Δ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distinguished element in `Splitting.IndexSet Δ` which corresponds to the
identity of `Δ`.
-/
def id : IndexSet Δ :=
  ⟨Δ, ⟨𝟙 _, by infer_instance⟩⟩
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.SimplicialObject.Splitting.IndexSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (IndexSet Δ) :=
  ⟨id Δ⟩

variable {Δ}

/-- The condition that an element `Splitting.IndexSet Δ` is the distinguished
element `Splitting.IndexSet.Id Δ`. -/
@[simp]
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.EqId** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：EqId : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that an element `Splitting.IndexSet Δ` is the distinguished
element `Splitting.IndexSet.Id Δ`.
-/
def EqId : Prop :=
  A = id _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.eqId_iff_eq** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：eqId_iff_eq : A.EqId ↔ A.1 = Δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.IndexSet.ext`：ext (A₁ A₂ : Ind
exSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e) : A₁ = A₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `SimplexCategory.eq_id_of_epi`：eq_id_of_epi {x : SimplexCategory} (i : x 
⟶ x) [Epi i] : i = 𝟙 _
-/
theorem eqId_iff_eq : A.EqId ↔ A.1 = Δ := by
  constructor
  · intro h
    dsimp at h
    rw [h]
    rfl
  · intro h
    rcases A with ⟨_, ⟨f, hf⟩⟩
    simp only at h
    subst h
    refine ext _ _ rfl ?_
    simp only [eqToHom_refl, comp_id]
    exact eq_id_of_epi f
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.eqId_iff_len_eq** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：eqId_iff_len_eq : A.EqId ↔ A.1.unop.len = Δ.unop.len
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.IndexSet.eqId_iff_eq`：eqId_iff
_eq : A.EqId ↔ A.1 = Δ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Opposite.unop_inj_iff`：unop_inj_iff (x y : αᵒᵖ) : unop x = unop y ↔ x = 
y
· 使用定理 `SimplexCategory.ext`：∀ {x y : SimplexCategory}, x.len = y.len → x = y
-/
theorem eqId_iff_len_eq : A.EqId ↔ A.1.unop.len = Δ.unop.len := by
  rw [eqId_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← unop_inj_iff]
    ext
    exact h
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.eqId_iff_len_le** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：eqId_iff_len_le : A.EqId ↔ Δ.unop.len <= A.1.unop.len
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.IndexSet.eqId_iff_len_eq`：eqId
_iff_len_eq : A.EqId ↔ A.1.unop.len = Δ.unop.len
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimplexCategory.len_le_of_epi`：len_le_of_epi {x y : SimplexCategory} (f 
: x ⟶ y) [Epi f] : y.len <= x.len
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.IndexSet.instEpiSimplexCategor
yE`：∀ {Δ : SimplexCategoryᵒᵖ} (A : CategoryTheory.SimplicialObject.Splitting.Ind
exSet Δ), CategoryTheory.Epi A.e
-/
theorem eqId_iff_len_le : A.EqId ↔ Δ.unop.len ≤ A.1.unop.len := by
  rw [eqId_iff_len_eq]
  constructor
  · intro h
    rw [h]
  · exact le_antisymm (len_le_of_epi A.e)
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.eqId_iff_mono** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：eqId_iff_mono : A.EqId ↔ Mono A.e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.IndexSet.eqId_iff_len_le`：eqId
_iff_len_le : A.EqId ↔ Δ.unop.len <= A.1.unop.len
· 使用定理 `SimplexCategory.len_le_of_mono`：len_le_of_mono {x y : SimplexCategory} (
f : x ⟶ y) [Mono f] : x.len <= y.len
-/
theorem eqId_iff_mono : A.EqId ↔ Mono A.e := by
  constructor
  · intro h
    dsimp at h
    subst h
    dsimp only [id, e]
    infer_instance
  · intro
    rw [eqId_iff_len_le]
    exact len_le_of_mono A.e

/-- Given `A : IndexSet Δ₁`, if `p.unop : unop Δ₂ ⟶ unop Δ₁` is an epi, this
is the obvious element in `A : IndexSet Δ₂` associated to the composition
of epimorphisms `p.unop ≫ A.e`. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.epiComp** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：epiComp {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂) [Epi p
.unop] : IndexSet Δ₂
参数：A : IndexSet Δ₁；p : Δ₁ ⟶ Δ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `A : IndexSet Δ₁`, if `p.unop : unop Δ₂ ⟶ unop Δ₁` is an epi, this
is the obvious element in `A : IndexSet Δ₂` associated to the composition
of epimorphisms `p.unop ≫ A.e`.
-/
def epiComp {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂) [Epi p.unop] :
    IndexSet Δ₂ :=
  ⟨A.1, ⟨p.unop ≫ A.e, epi_comp _ _⟩⟩


variable {Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')

/-- When `A : IndexSet Δ` and `θ : Δ → Δ'` is a morphism in `SimplexCategoryᵒᵖ`,
an element in `IndexSet Δ'` can be defined by using the epi-mono factorisation
of `θ.unop ≫ A.e`. -/
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.pull** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：pull : IndexSet Δ'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `A : IndexSet Δ` and `θ : Δ → Δ'` is a morphism in `SimplexCategoryᵒᵖ`,
an element in `IndexSet Δ'` can be defined by using the epi-mono factorisation
of `θ.unop ≫ A.e`.
-/
def pull : IndexSet Δ' :=
  mk (factorThruImage (θ.unop ≫ A.e))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.SimplicialObject.Splitting.IndexSet.fac_pull** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.SimplicialObject.Splitting.IndexSet`。
形式化陈述：fac_pull : (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem fac_pull : (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e :=
  image.fac _

end IndexSet

variable (N : ℕ → C) (Δ : SimplexCategoryᵒᵖ) (X : SimplicialObject C) (φ : ∀ n, N n ⟶ X _⦋n⦌)

/-- Given a sequences of objects `N : ℕ → C` in a category `C`, this is
a family of objects indexed by the elements `A : Splitting.IndexSet Δ`.
The `Δ`-simplices of a split simplicial objects shall identify to the
coproduct of objects in such a family. -/
@[simp, nolint unusedArguments]
/-
**CategoryTheory.SimplicialObject.Splitting.summand** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.SimplicialObject.Splitting`。
形式化陈述：summand (A : IndexSet Δ) : C
参数：A : IndexSet Δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequences of objects `N : ℕ → C` in a category `C`, this is
a family of objects indexed by the elements `A : Splitting.IndexSet Δ`.
The `Δ`-simplices of a split simplicial objects shall identify to the
coproduct of objects in such a family.
-/
def summand (A : IndexSet Δ) : C :=
  N A.1.unop.len

/-- The cofan for `summand N Δ` induced by morphisms `N n ⟶ X _⦋n⦌` for all `n : ℕ`. -/
/-
**CategoryTheory.SimplicialObject.Splitting.cofan'** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：cofan' (Δ : SimplexCategoryᵒᵖ) : Cofan (summand N Δ)
参数：Δ : SimplexCategoryᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofan for `summand N Δ` induced by morphisms `N n ⟶ X _⦋n⦌` for all `n : ℕ`.
-/
abbrev cofan' (Δ : SimplexCategoryᵒᵖ) : Cofan (summand N Δ) :=
  Cofan.mk (X.obj Δ) (fun A => φ A.1.unop.len ≫ X.map A.e.op)

end Splitting

/-- A splitting of a simplicial object `X` consists of the datum of a sequence
of objects `N`, a sequence of morphisms `ι : N n ⟶ X _⦋n⦌` such that
for all `Δ : SimplexCategoryᵒᵖ`, the canonical map `Splitting.map X ι Δ`
is an isomorphism. -/
/-
**CategoryTheory.SimplicialObject.Splitting** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.SimplicialObject`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → CategoryT
heory.SimplicialObject C → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A splitting of a simplicial object `X` consists of the datum of a sequence
of objects `N`, a sequence of morphisms `ι : N n ⟶ X _⦋n⦌` such that
for all `Δ : SimplexCategoryᵒᵖ`, the canonical map `Splitting.map X ι Δ`
is an isomorphism.
-/
structure Splitting (X : SimplicialObject C) where
  /-- The "nondegenerate simplices" `N n` for all `n : ℕ`. -/
  N : ℕ → C
  /-- The "inclusion" `N n ⟶ X _⦋n⦌` for all `n : ℕ`. -/
  ι : ∀ n, N n ⟶ X _⦋n⦌
  /-- For each `Δ`, `X.obj Δ` identifies to the coproduct of the objects `N A.1.unop.len`
  for all `A : IndexSet Δ`. -/
  isColimit' : ∀ Δ : SimplexCategoryᵒᵖ, IsColimit (Splitting.cofan' N X ι Δ)

initialize_simps_projections Splitting (-isColimit')

namespace Splitting

variable {X Y : SimplicialObject C} (s : Splitting X)

/-- The cofan for `summand s.N Δ` induced by a splitting of a simplicial object. -/
@[implicit_reducible]
/-
**CategoryTheory.SimplicialObject.Splitting.cofan** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SimplicialObject.Splitting`。
形式化陈述：cofan (Δ : SimplexCategoryᵒᵖ) : Cofan (summand s.N Δ)
参数：Δ : SimplexCategoryᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofan for `summand s.N Δ` induced by a splitting of a simplicial object.
-/
def cofan (Δ : SimplexCategoryᵒᵖ) : Cofan (summand s.N Δ) :=
  Cofan.mk (X.obj Δ) (fun A => s.ι A.1.unop.len ≫ X.map A.e.op)

/-- The cofan `s.cofan Δ` is colimit. -/
/-
**CategoryTheory.SimplicialObject.Splitting.isColimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：isColimit (Δ : SimplexCategoryᵒᵖ) : IsColimit (s.cofan Δ)
参数：Δ : SimplexCategoryᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofan `s.cofan Δ` is colimit.
-/
def isColimit (Δ : SimplexCategoryᵒᵖ) : IsColimit (s.cofan Δ) := s.isColimit' Δ

@[reassoc]
/-
**CategoryTheory.SimplicialObject.Splitting.cofan_inj_eq** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：cofan_inj_eq {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) : (s.cofan Δ).inj A 
= s.ι A.1.unop.len ≫ X.map A.e.op
参数：A : IndexSet Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cofan_inj_eq {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A = s.ι A.1.unop.len ≫ X.map A.e.op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.SimplicialObject.Splitting.cofan_inj_id** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：cofan_inj_id (n : Nat) : (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) = s.ι n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cofan_inj_id (n : ℕ) : (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) = s.ι n := by
  simp [IndexSet.id, IndexSet.e, cofan_inj_eq]

/-- As it is stated in `Splitting.hom_ext`, a morphism `f : X ⟶ Y` from a split
simplicial object to any simplicial object is determined by its restrictions
`s.φ f n : s.N n ⟶ Y _⦋n⦌` to the distinguished summands in each degree `n`. -/
@[simp]
/-
**CategoryTheory.SimplicialObject.Splitting.** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As it is stated in `Splitting.hom_ext`, a morphism `f : X ⟶ Y` from a split
simplicial object to any simplicial object is determined by its restrictions
`s.φ f n : s.N n ⟶ Y _⦋n⦌` to the distinguished summands in each degree `n`.
-/
def φ (f : X ⟶ Y) (n : ℕ) : s.N n ⟶ Y _⦋n⦌ :=
  s.ι n ≫ f.app (op ⦋n⦌)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.cofan_inj_comp_app** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：cofan_inj_comp_app (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) : 
(s.cofan Δ).inj A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op
参数：f : X ⟶ Y；A : IndexSet Δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.cofan_inj_eq_assoc`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : CategoryTheory.Simplic
ialObject C} (s : X.Splitting)   {Δ : SimplexCateg…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem cofan_inj_comp_app (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op := by
  simp only [cofan_inj_eq_assoc, φ, assoc]
  rw [NatTrans.naturality]
/-
**CategoryTheory.SimplicialObject.Splitting.hom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：hom_ext' {Z : C} {Δ : SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z) (h : forall A
 : IndexSet Δ, (s.cofan Δ).inj A ≫ f = (s.cofan Δ).inj A ≫ g) : f = g
参数：f g : X.obj Δ ⟶ Z；h : forall A : IndexSet Δ, (s.cofan Δ).inj A ≫ f = (s.cofan
 Δ).inj A ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
-/
theorem hom_ext' {Z : C} {Δ : SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
    (h : ∀ A : IndexSet Δ, (s.cofan Δ).inj A ≫ f = (s.cofan Δ).inj A ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (s.isColimit Δ) _ _ h

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SimplicialObject.Splitting.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.SimplicialObject.Splitting`。
形式化陈述：hom_ext (f g : X ⟶ Y) (h : forall n : Nat, s.φ f n = s.φ g n) : f = g
参数：f g : X ⟶ Y；h : forall n : Nat, s.φ f n = s.φ g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SimplicialObject.hom_ext`：hom_ext {X Y : SimplicialObject
 C} (f g : X ⟶ Y) (h : forall (n : SimplexCategoryᵒᵖ), f.app n = g.app n) : f = 
g
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.hom_ext'`：hom_ext' {Z : C} {Δ 
: SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z) (h : forall A : IndexSet Δ, (s.cofan Δ)
.inj A ≫ f = (s.cofan Δ).inj A ≫ g) : f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.cofan_inj_comp_app`：cofan_inj_
comp_app (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) : (s.cofan Δ).inj 
A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_ext (f g : X ⟶ Y) (h : ∀ n : ℕ, s.φ f n = s.φ g n) : f = g := by
  ext ⟨Δ⟩
  apply s.hom_ext'
  intro A
  induction Δ using SimplexCategory.rec with | _ n
  dsimp
  simp only [s.cofan_inj_comp_app, h]

/-- The map `X.obj Δ ⟶ Z` obtained by providing a family of morphisms on all the
terms of decomposition given by a splitting `s : Splitting X` -/
/-
**CategoryTheory.SimplicialObject.Splitting.desc** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SimplicialObject.Splitting`。
形式化陈述：desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : forall A : IndexSet Δ, s.N A.1.u
nop.len ⟶ Z) : X.obj Δ ⟶ Z
参数：Δ : SimplexCategoryᵒᵖ；F : forall A : IndexSet Δ, s.N A.1.unop.len ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `X.obj Δ ⟶ Z` obtained by providing a family of morphisms on all the
terms of decomposition given by a splitting `s : Splitting X`
-/
def desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : ∀ A : IndexSet Δ, s.N A.1.unop.len ⟶ Z) :
    X.obj Δ ⟶ Z :=
  Cofan.IsColimit.desc (s.isColimit Δ) F

@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.Splitting.** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.SimplicialObject.Splitting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : ∀ A : IndexSet Δ, s.N A.1.unop.len ⟶ Z)
    (A : IndexSet Δ) : (s.cofan Δ).inj A ≫ s.desc Δ F = F A := by
  apply Cofan.IsColimit.fac

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A simplicial object that is isomorphic to a split simplicial object is split. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Splitting.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SimplicialObject.Splitting`。
形式化陈述：ofIso (e : X ≅ Y) : Splitting Y where N
参数：e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial object that is isomorphic to a split simplicial object is split.
-/
def ofIso (e : X ≅ Y) : Splitting Y where
  N := s.N
  ι n := s.ι n ≫ e.hom.app (op ⦋n⦌)
  isColimit' Δ := IsColimit.ofIsoColimit (s.isColimit Δ) (Cofan.ext (e.app Δ)
    (fun A => by simp [cofan, cofan']))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.SimplicialObject.Splitting.cofan_inj_epi_naturality** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.SimplicialObject.Splitting`。
形式化陈述：cofan_inj_epi_naturality {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p 
: Δ₁ ⟶ Δ₂) [Epi p.unop] : (s.cofan Δ₁).inj A ≫ X.map p = (s.cofan Δ₂).inj (A.epi
Comp p)
参数：A : IndexSet Δ₁；p : Δ₁ ⟶ Δ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem cofan_inj_epi_naturality {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂)
    [Epi p.unop] : (s.cofan Δ₁).inj A ≫ X.map p = (s.cofan Δ₂).inj (A.epiComp p) := by
  dsimp [cofan]
  rw [assoc, ← X.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The image of a splitting of simplicial object by a functor which preserves
finite coproducts -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Splitting.map** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.SimplicialObject.Splitting`。
形式化陈述：map (F : C ⥤ D) [PreservesFiniteCoproducts F] : Splitting (X ⋙ F) where N 
n
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a splitting of simplicial object by a functor which preserves
finite coproducts
-/
def map (F : C ⥤ D) [PreservesFiniteCoproducts F] :
    Splitting (X ⋙ F) where
  N n := F.obj (s.N n)
  ι n := F.map (s.ι n)
  isColimit' n :=
    IsColimit.ofIsoColimit (isColimitCofanMkObjOfIsColimit F _ _ (s.isColimit n))
      (Cofan.ext (Iso.refl _))

end Splitting

variable (C)

/-- The category `SimplicialObject.Split C` is the category of simplicial objects
in `C` equipped with a splitting, and morphisms are morphisms of simplicial objects
which are compatible with the splittings. -/
@[ext]
/-
**CategoryTheory.SimplicialObject.Split** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.SimplicialObject`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → Type (max u_1 v_
1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `SimplicialObject.Split C` is the category of simplicial objects
in `C` equipped with a splitting, and morphisms are morphisms of simplicial obje
cts
which are compatible with the splittings.
-/
structure Split where
  /-- the underlying simplicial object -/
  X : SimplicialObject C
  /-- a splitting of the simplicial object -/
  s : Splitting X

namespace Split

variable {C}

/-- The object in `SimplicialObject.Split C` attached to a splitting `s : Splitting X`
of a simplicial object `X`. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Split.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.SimplicialObject.Split`。
形式化陈述：mk' {X : SimplicialObject C} (s : Splitting X) : Split C
参数：s : Splitting X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in `SimplicialObject.Split C` attached to a splitting `s : Splitting 
X`
of a simplicial object `X`.
-/
def mk' {X : SimplicialObject C} (s : Splitting X) : Split C :=
  ⟨X, s⟩

/-- Morphisms in `SimplicialObject.Split C` are morphisms of simplicial objects that
are compatible with the splittings. -/
/-
**CategoryTheory.SimplicialObject.Split.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryT
heory.SimplicialObject.Split`。
形式化陈述：Hom (S₁ S₂ : Split C) where /-- the morphism between the underlying simpli
cial objects -/ F : S₁.X ⟶ S₂.X /-- the morphism between the "nondegenerate" `n`
-simplices for all `n : ℕ` -/ f : forall n : Nat, S₁.s.N n ⟶ S₂.s.N n comm : for
all n : Nat, S₁.s.ι n ≫ F.app (op ⦋n⦌) = f n ≫ S₂.s.ι n
参数：S₁ S₂ : Split C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms in `SimplicialObject.Split C` are morphisms of simplicial objects that
are compatible with the splittings.
-/
structure Hom (S₁ S₂ : Split C) where
  /-- the morphism between the underlying simplicial objects -/
  F : S₁.X ⟶ S₂.X
  /-- the morphism between the "nondegenerate" `n`-simplices for all `n : ℕ` -/
  f : ∀ n : ℕ, S₁.s.N n ⟶ S₂.s.N n
  comm : ∀ n : ℕ, S₁.s.ι n ≫ F.app (op ⦋n⦌) = f n ≫ S₂.s.ι n := by cat_disch

@[ext]
/-
**CategoryTheory.SimplicialObject.Split.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.SimplicialObject.Split.Hom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {S₁ S₂ : Ca
tegoryTheory.SimplicialObject.Split C}   (Φ₁ Φ₂ : S₁.Hom S₂), (∀ (n : ℕ), Φ₁.f n
 = Φ₂.f n) → Φ₁ = Φ₂
参数：Φ₁ Φ₂ : S₁.Hom S₂；∀ (n : ℕ), Φ₁.f n = Φ₂.f n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.SimplicialObject.Split.Hom.mk.injEq`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] {S₁ S₂ : CategoryTheory.SimplicialObj
ect.Split C}   (F : S₁.X ⟶ S₂.X) (f : (n…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.hom_ext`：hom_ext (f g : X ⟶ Y)
 (h : forall n : Nat, s.φ f n = s.φ g n) : f = g
-/
theorem Hom.ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : Hom S₁ S₂) (h : ∀ n : ℕ, Φ₁.f n = Φ₂.f n) : Φ₁ = Φ₂ := by
  rcases Φ₁ with ⟨F₁, f₁, c₁⟩
  rcases Φ₂ with ⟨F₂, f₂, c₂⟩
  have h' : f₁ = f₂ := by
    ext
    apply h
  subst h'
  simp only [mk.injEq, and_true]
  apply S₁.s.hom_ext
  intro n
  dsimp
  rw [c₁, c₂]

attribute [simp, reassoc] Hom.comm

end Split

/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Split C) where
  Hom := Split.Hom
  id S :=
    { F := 𝟙 _
      f := fun _ => 𝟙 _ }
  comp Φ₁₂ Φ₂₃ :=
    { F := Φ₁₂.F ≫ Φ₂₃.F
      f := fun n => Φ₁₂.f n ≫ Φ₂₃.f n
      comm := fun n => by
        dsimp
        simp only [assoc, Split.Hom.comm_assoc, Split.Hom.comm] }

variable {C}

namespace Split

@[ext]
/-
**CategoryTheory.SimplicialObject.Split.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.SimplicialObject.Split`。
形式化陈述：hom_ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : S₁ ⟶ S₂) (h : forall n : Nat, Φ₁.f n = 
Φ₂.f n) : Φ₁ = Φ₂
参数：Φ₁ Φ₂ : S₁ ⟶ S₂；h : forall n : Nat, Φ₁.f n = Φ₂.f n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.Split.Hom.ext`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {S₁ S₂ : CategoryTheory.SimplicialObject.S
plit C}   (Φ₁ Φ₂ : S₁.Hom S₂), (∀ (…
-/
theorem hom_ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : S₁ ⟶ S₂) (h : ∀ n : ℕ, Φ₁.f n = Φ₂.f n) : Φ₁ = Φ₂ :=
  Hom.ext _ _ h
/-
**CategoryTheory.SimplicialObject.Split.congr_F** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.SimplicialObject.Split`。
形式化陈述：congr_F {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) : Φ₁.f = Φ₂.f
参数：h : Φ₁ = Φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem congr_F {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) : Φ₁.f = Φ₂.f := by rw [h]
/-
**CategoryTheory.SimplicialObject.Split.congr_f** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.SimplicialObject.Split`。
形式化陈述：congr_f {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) (n : Nat) : Φ₁.f
 n = Φ₂.f n
参数：h : Φ₁ = Φ₂；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem congr_f {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) (n : ℕ) : Φ₁.f n = Φ₂.f n := by
  rw [h]

@[simp]
/-
**CategoryTheory.SimplicialObject.Split.id_F** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.SimplicialObject.Split`。
形式化陈述：id_F (S : Split C) : (𝟙 S : S ⟶ S).F = 𝟙 S.X
参数：S : Split C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_F (S : Split C) : (𝟙 S : S ⟶ S).F = 𝟙 S.X :=
  rfl

@[simp]
/-
**CategoryTheory.SimplicialObject.Split.id_f** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.SimplicialObject.Split`。
形式化陈述：id_f (S : Split C) (n : Nat) : (𝟙 S : S ⟶ S).f n = 𝟙 (S.s.N n)
参数：S : Split C；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f (S : Split C) (n : ℕ) : (𝟙 S : S ⟶ S).f n = 𝟙 (S.s.N n) :=
  rfl

@[simp]
/-
**CategoryTheory.SimplicialObject.Split.comp_F** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.SimplicialObject.Split`。
形式化陈述：comp_F {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) : (Φ₁₂ ≫ Φ₂₃).
F = Φ₁₂.F ≫ Φ₂₃.F
参数：Φ₁₂ : S₁ ⟶ S₂；Φ₂₃ : S₂ ⟶ S₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_F {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) :
    (Φ₁₂ ≫ Φ₂₃).F = Φ₁₂.F ≫ Φ₂₃.F :=
  rfl

@[simp]
/-
**CategoryTheory.SimplicialObject.Split.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.SimplicialObject.Split`。
形式化陈述：comp_f {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) (n : Nat) : (Φ
₁₂ ≫ Φ₂₃).f n = Φ₁₂.f n ≫ Φ₂₃.f n
参数：Φ₁₂ : S₁ ⟶ S₂；Φ₂₃ : S₂ ⟶ S₃；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) (n : ℕ) :
    (Φ₁₂ ≫ Φ₂₃).f n = Φ₁₂.f n ≫ Φ₂₃.f n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
-- This is not a `@[simp]` lemma as it can later be proved by `simp`.
@[reassoc]
/-
**CategoryTheory.SimplicialObject.Split.cofan_inj_naturality_symm** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.SimplicialObject.Split`。
形式化陈述：cofan_inj_naturality_symm {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) {Δ : SimplexCate
goryᵒᵖ} (A : Splitting.IndexSet Δ) : (S₁.s.cofan Δ).inj A ≫ Φ.F.app Δ = Φ.f A.1.
unop.len ≫ (S₂.s.cofan Δ).inj A
参数：Φ : S₁ ⟶ S₂；A : Splitting.IndexSet Δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.Splitting.cofan_inj_eq`：cofan_inj_eq {Δ 
: SimplexCategoryᵒᵖ} (A : IndexSet Δ) : (s.cofan Δ).inj A = s.ι A.1.unop.len ≫ X
.map A.e.op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.SimplicialObject.Split.Hom.comm_assoc`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {S₁ S₂ : CategoryTheory.SimplicialO
bject.Split C}   (self : S₁.Hom S₂) (n : ℕ…
-/
theorem cofan_inj_naturality_symm {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) {Δ : SimplexCategoryᵒᵖ}
    (A : Splitting.IndexSet Δ) :
    (S₁.s.cofan Δ).inj A ≫ Φ.F.app Δ = Φ.f A.1.unop.len ≫ (S₂.s.cofan Δ).inj A := by
  rw [S₁.s.cofan_inj_eq, S₂.s.cofan_inj_eq, assoc, Φ.F.naturality, ← Φ.comm_assoc]

variable (C)

/-- The functor `SimplicialObject.Split C ⥤ SimplicialObject C` which forgets
the splitting. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Split.forget** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.SimplicialObject.Split`。
形式化陈述：forget : Split C ⥤ SimplicialObject C where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplicialObject.Split C ⥤ SimplicialObject C` which forgets
the splitting.
-/
def forget : Split C ⥤ SimplicialObject C where
  obj S := S.X
  map Φ := Φ.F

/-- The functor `SimplicialObject.Split C ⥤ C` which sends a simplicial object equipped
with a splitting to its nondegenerate `n`-simplices. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Split.evalN** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SimplicialObject.Split`。
形式化陈述：evalN (n : Nat) : Split C ⥤ C where obj S
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplicialObject.Split C ⥤ C` which sends a simplicial object equip
ped
with a splitting to its nondegenerate `n`-simplices.
-/
def evalN (n : ℕ) : Split C ⥤ C where
  obj S := S.s.N n
  map Φ := Φ.f n

/-- The inclusion of each summand in the coproduct decomposition of simplices
in split simplicial objects is a natural transformation of functors
`SimplicialObject.Split C ⥤ C` -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Split.natTransCofanInj** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SimplicialObject.Split`。
形式化陈述：natTransCofanInj {Δ : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) : eval
N C A.1.unop.len ⟶ forget C ⋙ (evaluation SimplexCategoryᵒᵖ C).obj Δ where app S
参数：A : Splitting.IndexSet Δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of each summand in the coproduct decomposition of simplices
in split simplicial objects is a natural transformation of functors
`SimplicialObject.Split C ⥤ C`
-/
def natTransCofanInj {Δ : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) :
    evalN C A.1.unop.len ⟶ forget C ⋙ (evaluation SimplexCategoryᵒᵖ C).obj Δ where
  app S := (S.s.cofan Δ).inj A
  naturality _ _ Φ := (cofan_inj_naturality_symm Φ A).symm

end Split

end CategoryTheory.SimplicialObject

