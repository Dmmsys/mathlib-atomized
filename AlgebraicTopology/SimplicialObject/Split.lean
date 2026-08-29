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

/--
Definition of `IndexSet` / `IndexSet` 的定义

English:
definition IndexSet
  signature: (Δ : SimplexCategoryᵒᵖ)
  body: Σ Δ' : SimplexCategoryᵒᵖ, { α : Δ.unop ⟶ Δ'.unop // Epi α }

中文:
定义 IndexSet
  签名: (Δ : SimplexCategoryᵒᵖ)
  定义体: Σ Δ' : SimplexCategoryᵒᵖ, { α : Δ.unop ⟶ Δ'.unop // Epi α }
-/
def IndexSet (Δ : SimplexCategoryᵒᵖ) :=
  Σ Δ' : SimplexCategoryᵒᵖ, { α : Δ.unop ⟶ Δ'.unop // Epi α }

namespace IndexSet

/-- The element in `Splitting.IndexSet Δ` attached to an epimorphism `f : Δ ⟶ Δ'`. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') [Epi f]
  body: ⟨op Δ', f, inferInstance⟩

中文:
定义 mk
  签名: {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') [Epi f]
  定义体: ⟨op Δ', f, inferInstance⟩
-/
def mk {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') [Epi f] : IndexSet (op Δ) :=
  ⟨op Δ', f, inferInstance⟩

variable {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)

/--
Definition of `e` / `e` 的定义

English:
definition e
  body: A.2.1

中文:
定义 e
  定义体: A.2.1
-/
def e :=
  A.2.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi A.e
  body: A.2.2

中文:
实例 :
  签名: Epi A.e
  定义体: A.2.2
-/
instance : Epi A.e :=
  A.2.2

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  statement: A = ⟨A.1, ⟨A.e, A.2.2⟩⟩
  proof: rfl

中文:
定理 ext'
  结论: A = ⟨A.1, ⟨A.e, A.2.2⟩⟩
  证明: rfl
-/
theorem ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e)
  proof: by
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩
  simp only at h₁
  subst h₁
  simp only [eqToHom_refl, comp_id, IndexSet.e] at h₂
  simp only [h₂]

中文:
定理 ext
  条件: (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e)
  证明: by
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩
  simp only at h₁
  subst h₁
  simp only [eqToHom_refl, comp_id, IndexSet.e] at h₂
  simp only [h₂]

Depends on / 依赖: IndexSet, IndexSet.e, comp_id, eqToHom_refl
-/
theorem ext (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e) :
    A₁ = A₂ := by
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩
  simp only at h₁
  subst h₁
  simp only [eqToHom_refl, comp_id, IndexSet.e] at h₂
  simp only [h₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (IndexSet Δ)
  body: Fintype.ofInjective
    (fun A =>
      ⟨⟨A.1.unop.len, Nat.lt_succ_iff.mpr (len_le_of_epi A.e)⟩,
        A.e.toOrderHom⟩ :
      IndexSet Δ -> Sigma fun k : Fin (Δ.unop.len + 1) => Fin (Δ.unop.len + 1) -> Fin (k + 1))
    (by
      rintro ⟨⟨Δ₁⟩, α₁⟩ ⟨⟨Δ₂⟩, α₂⟩ h₁
      simp only [unop_op, Sigma.mk.

中文:
实例 :
  签名: Fintype (IndexSet Δ)
  定义体: Fintype.ofInjective
    (fun A =>
      ⟨⟨A.1.unop.len, Nat.lt_succ_iff.mpr (len_le_of_epi A.e)⟩,
        A.e.toOrderHom⟩ :
      IndexSet Δ -> Sigma fun k : Fin (Δ.unop.len + 1) => Fin (Δ.unop.len + 1) -> Fin (k + 1))
    (by
      rintro ⟨⟨Δ₁⟩, α₁⟩ ⟨⟨Δ₂⟩, α₂⟩ h₁
      simp only [unop_op, Sigma.mk.

Depends on / 依赖: A.e.toOrderHom, Fin.mk.injEq, Fin.mk_eq_mk, Fintype, Fintype.ofInjective, IndexSet, Nat.lt_succ_iff.mpr, Sigma.mk.inj_iff, eq_of_heq, inj_iff, len_le_of_epi, lt_succ_iff, mk_eq_mk, ofInjective, toOrderHom, unop.len, unop_op
-/
instance : Fintype (IndexSet Δ) :=
  Fintype.ofInjective
    (fun A =>
      ⟨⟨A.1.unop.len, Nat.lt_succ_iff.mpr (len_le_of_epi A.e)⟩,
        A.e.toOrderHom⟩ :
      IndexSet Δ -> Sigma fun k : Fin (Δ.unop.len + 1) => Fin (Δ.unop.len + 1) -> Fin (k + 1))
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
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : IndexSet Δ
  body: ⟨Δ, ⟨𝟙 _, by infer_instance⟩⟩

中文:
定义 id
  签名: : IndexSet Δ
  定义体: ⟨Δ, ⟨𝟙 _, by infer_instance⟩⟩

Depends on / 依赖: infer_instance
-/
def id : IndexSet Δ :=
  ⟨Δ, ⟨𝟙 _, by infer_instance⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (IndexSet Δ)
  body: ⟨id Δ⟩

中文:
实例 :
  签名: Inhabited (IndexSet Δ)
  定义体: ⟨id Δ⟩
-/
instance : Inhabited (IndexSet Δ) :=
  ⟨id Δ⟩

variable {Δ}

/-- The condition that an element `Splitting.IndexSet Δ` is the distinguished
element `Splitting.IndexSet.Id Δ`. -/
@[simp]
/--
Definition of `EqId` / `EqId` 的定义

English:
definition EqId
  signature: : Prop
  body: A = id _

中文:
定义 EqId
  签名: : 命题
  定义体: A = id _
-/
def EqId : Prop :=
  A = id _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eqId_iff_eq` / 定理 `eqId_iff_eq`

English:
theorem eqId_iff_eq
  statement: A.EqId ↔ A.1 = Δ
  proof: by
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

中文:
定理 eqId_iff_eq
  结论: A.EqId ↔ A.1 = Δ
  证明: by
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

Depends on / 依赖: comp_id, eqToHom_refl, eq_id_of_epi
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

/--
theorem `eqId_iff_len_eq` / 定理 `eqId_iff_len_eq`

English:
theorem eqId_iff_len_eq
  statement: A.EqId ↔ A.1.unop.len = Δ.unop.len
  proof: by
  rw [eqId_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← unop_inj_iff]
    ext
    exact h

中文:
定理 eqId_iff_len_eq
  结论: A.EqId ↔ A.1.unop.len = Δ.unop.len
  证明: by
  rw [eqId_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← unop_inj_iff]
    ext
    exact h

Depends on / 依赖: eqId_iff_eq, unop_inj_iff
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

/--
theorem `eqId_iff_len_le` / 定理 `eqId_iff_len_le`

English:
theorem eqId_iff_len_le
  statement: A.EqId ↔ Δ.unop.len <= A.1.unop.len
  proof: by
  rw [eqId_iff_len_eq]
  constructor
  · intro h
    rw [h]
  · exact le_antisymm (len_le_of_epi A.e)

中文:
定理 eqId_iff_len_le
  结论: A.EqId ↔ Δ.unop.len <= A.1.unop.len
  证明: by
  rw [eqId_iff_len_eq]
  constructor
  · intro h
    rw [h]
  · exact le_antisymm (len_le_of_epi A.e)

Depends on / 依赖: eqId_iff_len_eq, le_antisymm, len_le_of_epi
-/
theorem eqId_iff_len_le : A.EqId ↔ Δ.unop.len <= A.1.unop.len := by
  rw [eqId_iff_len_eq]
  constructor
  · intro h
    rw [h]
  · exact le_antisymm (len_le_of_epi A.e)

/--
theorem `eqId_iff_mono` / 定理 `eqId_iff_mono`

English:
theorem eqId_iff_mono
  statement: A.EqId ↔ Mono A.e
  proof: by
  constructor
  · intro h
    dsimp at h
    subst h
    dsimp only [id, e]
    infer_instance
  · intro
    rw [eqId_iff_len_le]
    exact len_le_of_mono A.e

中文:
定理 eqId_iff_mono
  结论: A.EqId ↔ Mono A.e
  证明: by
  constructor
  · intro h
    dsimp at h
    subst h
    dsimp only [id, e]
    infer_instance
  · intro
    rw [eqId_iff_len_le]
    exact len_le_of_mono A.e

Depends on / 依赖: eqId_iff_len_le, infer_instance, len_le_of_mono
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
/--
Definition of `epiComp` / `epiComp` 的定义

English:
definition epiComp
  signature: {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂) [Epi p.unop]
  body: ⟨A.1, ⟨p.unop ≫ A.e, epi_comp _ _⟩⟩

中文:
定义 epiComp
  签名: {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂) [Epi p.unop]
  定义体: ⟨A.1, ⟨p.unop ≫ A.e, epi_comp _ _⟩⟩

Depends on / 依赖: epi_comp, p.unop
-/
def epiComp {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂) [Epi p.unop] :
    IndexSet Δ₂ :=
  ⟨A.1, ⟨p.unop ≫ A.e, epi_comp _ _⟩⟩


variable {Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')

/--
Definition of `pull` / `pull` 的定义

English:
definition pull
  signature: : IndexSet Δ'
  body: mk (factorThruImage (θ.unop ≫ A.e))

#adaptation_note

中文:
定义 pull
  签名: : IndexSet Δ'
  定义体: mk (factorThruImage (θ.unop ≫ A.e))

#adaptation_note

Depends on / 依赖: factorThruImage
-/
def pull : IndexSet Δ' :=
  mk (factorThruImage (θ.unop ≫ A.e))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
theorem `fac_pull` / 定理 `fac_pull`

English:
theorem fac_pull
  statement: (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e
  proof: image.fac _

中文:
定理 fac_pull
  结论: (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e
  证明: image.fac _

Depends on / 依赖: image.fac
-/
theorem fac_pull : (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e :=
  image.fac _

end IndexSet

variable (N : Nat -> C) (Δ : SimplexCategoryᵒᵖ) (X : SimplicialObject C) (φ : forall n, N n ⟶ X _⦋n⦌)

/-- Given a sequences of objects `N : ℕ → C` in a category `C`, this is
a family of objects indexed by the elements `A : Splitting.IndexSet Δ`.
The `Δ`-simplices of a split simplicial objects shall identify to the
coproduct of objects in such a family. -/
@[simp, nolint unusedArguments]
/--
Definition of `summand` / `summand` 的定义

English:
definition summand
  signature: (A : IndexSet Δ)
  body: N A.1.unop.len

中文:
定义 summand
  签名: (A : IndexSet Δ)
  定义体: N A.1.unop.len

Depends on / 依赖: unop.len
-/
def summand (A : IndexSet Δ) : C :=
  N A.1.unop.len

/--
Definition of `cofan'` / `cofan'` 的定义

English:
abbreviation cofan'
  signature: (Δ : SimplexCategoryᵒᵖ)
  body: Cofan.mk (X.obj Δ) (fun A => φ A.1.unop.len ≫ X.map A.e.op)

中文:
缩写 cofan'
  签名: (Δ : SimplexCategoryᵒᵖ)
  定义体: Cofan.mk (X.obj Δ) (fun A => φ A.1.unop.len ≫ X.map A.e.op)

Depends on / 依赖: A.e.op, Cofan.mk, X.map, X.obj, unop.len
-/
abbrev cofan' (Δ : SimplexCategoryᵒᵖ) : Cofan (summand N Δ) :=
  Cofan.mk (X.obj Δ) (fun A => φ A.1.unop.len ≫ X.map A.e.op)

end Splitting

/--
Definition of `Splitting` / `Splitting` 的定义

English:
structure Splitting
  parameters: (X : SimplicialObject C)
  axioms and operations (3):
    - N : Nat -> C
    - ι : forall n, N n ⟶ X _⦋n⦌
    - isColimit' : forall Δ : SimplexCategoryᵒᵖ, IsColimit (Splitting.cofan' N X ι Δ)

中文:
结构 Splitting
  参数: (X : SimplicialObject C)
  公理与运算 (3 个):
    - N : 自然数 -> C
    - ι : 对任意 n, N n ⟶ X _⦋n⦌
    - isColimit' : 对任意 Δ : SimplexCategoryᵒᵖ, IsColimit (Splitting.cofan' N X ι Δ)
-/
structure Splitting (X : SimplicialObject C) where
  /-- The "nondegenerate simplices" `N n` for all `n : ℕ`. -/
  N : Nat -> C
  /-- The "inclusion" `N n ⟶ X _⦋n⦌` for all `n : ℕ`. -/
  ι : forall n, N n ⟶ X _⦋n⦌
  /-- For each `Δ`, `X.obj Δ` identifies to the coproduct of the objects `N A.1.unop.len`
  for all `A : IndexSet Δ`. -/
  isColimit' : forall Δ : SimplexCategoryᵒᵖ, IsColimit (Splitting.cofan' N X ι Δ)

initialize_simps_projections Splitting (-isColimit')

namespace Splitting

variable {X Y : SimplicialObject C} (s : Splitting X)

/-- The cofan for `summand s.N Δ` induced by a splitting of a simplicial object. -/
@[implicit_reducible]
/--
Definition of `cofan` / `cofan` 的定义

English:
definition cofan
  signature: (Δ : SimplexCategoryᵒᵖ)
  body: Cofan.mk (X.obj Δ) (fun A => s.ι A.1.unop.len ≫ X.map A.e.op)

中文:
定义 cofan
  签名: (Δ : SimplexCategoryᵒᵖ)
  定义体: Cofan.mk (X.obj Δ) (fun A => s.ι A.1.unop.len ≫ X.map A.e.op)

Depends on / 依赖: A.e.op, Cofan.mk, X.map, X.obj, unop.len
-/
def cofan (Δ : SimplexCategoryᵒᵖ) : Cofan (summand s.N Δ) :=
  Cofan.mk (X.obj Δ) (fun A => s.ι A.1.unop.len ≫ X.map A.e.op)

/--
Definition of `isColimit` / `isColimit` 的定义

English:
definition isColimit
  signature: (Δ : SimplexCategoryᵒᵖ)
  body: s.isColimit' Δ

@[reassoc]

中文:
定义 isColimit
  签名: (Δ : SimplexCategoryᵒᵖ)
  定义体: s.isColimit' Δ

@[reassoc]

Depends on / 依赖: isColimit, s.isColimit
-/
def isColimit (Δ : SimplexCategoryᵒᵖ) : IsColimit (s.cofan Δ) := s.isColimit' Δ

@[reassoc]
/--
theorem `cofan_inj_eq` / 定理 `cofan_inj_eq`

English:
theorem cofan_inj_eq
  given: {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
  proof: rfl

中文:
定理 cofan_inj_eq
  条件: {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
  证明: rfl
-/
theorem cofan_inj_eq {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A = s.ι A.1.unop.len ≫ X.map A.e.op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `cofan_inj_id` / 定理 `cofan_inj_id`

English:
theorem cofan_inj_id
  given: (n : Nat)
  statement: (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) = s.ι n
  proof: by
  simp [IndexSet.id, IndexSet.e, cofan_inj_eq]

中文:
定理 cofan_inj_id
  条件: (n : 自然数)
  结论: (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) = s.ι n
  证明: by
  simp [IndexSet.id, IndexSet.e, cofan_inj_eq]

Depends on / 依赖: IndexSet, IndexSet.e, IndexSet.id, cofan_inj_eq
-/
theorem cofan_inj_id (n : Nat) : (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) = s.ι n := by
  simp [IndexSet.id, IndexSet.e, cofan_inj_eq]

/-- As it is stated in `Splitting.hom_ext`, a morphism `f : X ⟶ Y` from a split
simplicial object to any simplicial object is determined by its restrictions
`s.φ f n : s.N n ⟶ Y _⦋n⦌` to the distinguished summands in each degree `n`. -/
@[simp]
/--
Definition of `φ` / `φ` 的定义

English:
definition φ
  signature: (f : X ⟶ Y) (n : Nat)
  body: s.ι n ≫ f.app (op ⦋n⦌)

中文:
定义 φ
  签名: (f : X ⟶ Y) (n : 自然数)
  定义体: s.ι n ≫ f.app (op ⦋n⦌)

Depends on / 依赖: f.app
-/
def φ (f : X ⟶ Y) (n : Nat) : s.N n ⟶ Y _⦋n⦌ :=
  s.ι n ≫ f.app (op ⦋n⦌)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `cofan_inj_comp_app` / 定理 `cofan_inj_comp_app`

English:
theorem cofan_inj_comp_app
  given: (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
  proof: by
  simp only [cofan_inj_eq_assoc, φ, assoc]
  rw [NatTrans.naturality]

中文:
定理 cofan_inj_comp_app
  条件: (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
  证明: by
  simp only [cofan_inj_eq_assoc, φ, assoc]
  rw [NatTrans.naturality]

Depends on / 依赖: NatTrans, NatTrans.naturality, cofan_inj_eq_assoc, naturality
-/
theorem cofan_inj_comp_app (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op := by
  simp only [cofan_inj_eq_assoc, φ, assoc]
  rw [NatTrans.naturality]

/--
theorem `hom_ext'` / 定理 `hom_ext'`

English:
theorem hom_ext'
  statement: {Z : C} {Δ : SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
  proof: Cofan.IsColimit.hom_ext (s.isColimit Δ) _ _ h

中文:
定理 hom_ext'
  结论: {Z : C} {Δ : SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
  证明: Cofan.IsColimit.hom_ext (s.isColimit Δ) _ _ h

Depends on / 依赖: Cofan.IsColimit.hom_ext, IsColimit, hom_ext, isColimit, s.isColimit
-/
theorem hom_ext' {Z : C} {Δ : SimplexCategoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
    (h : forall A : IndexSet Δ, (s.cofan Δ).inj A ≫ f = (s.cofan Δ).inj A ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (s.isColimit Δ) _ _ h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: (f g : X ⟶ Y) (h : forall n : Nat, s.φ f n = s.φ g n)
  statement: f = g
  proof: by
  ext ⟨Δ⟩
  apply s.hom_ext'
  intro A
  induction Δ using SimplexCategory.rec with | _ n
  dsimp
  simp only [s.cofan_inj_comp_app, h]

中文:
定理 hom_ext
  条件: (f g : X ⟶ Y) (h : 对任意 n : 自然数, s.φ f n = s.φ g n)
  结论: f = g
  证明: by
  ext ⟨Δ⟩
  apply s.hom_ext'
  intro A
  induction Δ using SimplexCategory.rec with | _ n
  dsimp
  simp only [s.cofan_inj_comp_app, h]

Depends on / 依赖: SimplexCategory, SimplexCategory.rec, cofan_inj_comp_app, hom_ext, s.cofan_inj_comp_app, s.hom_ext
-/
theorem hom_ext (f g : X ⟶ Y) (h : forall n : Nat, s.φ f n = s.φ g n) : f = g := by
  ext ⟨Δ⟩
  apply s.hom_ext'
  intro A
  induction Δ using SimplexCategory.rec with | _ n
  dsimp
  simp only [s.cofan_inj_comp_app, h]

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : forall A : IndexSet Δ, s.N A.1.unop.len ⟶ Z)
  body: Cofan.IsColimit.desc (s.isColimit Δ) F

@[reassoc (attr := simp)]

中文:
定义 desc
  签名: {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : 对任意 A : IndexSet Δ, s.N A.1.unop.len ⟶ Z)
  定义体: Cofan.IsColimit.desc (s.isColimit Δ) F

@[reassoc (attr := simp)]

Depends on / 依赖: Cofan.IsColimit.desc, IsColimit, isColimit, s.isColimit
-/
def desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : forall A : IndexSet Δ, s.N A.1.unop.len ⟶ Z) :
    X.obj Δ ⟶ Z :=
  Cofan.IsColimit.desc (s.isColimit Δ) F

@[reassoc (attr := simp)]
/--
theorem `ι_desc` / 定理 `ι_desc`

English:
theorem ι_desc
  statement: {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : forall A : IndexSet Δ, s.N A.1.unop.len ⟶ Z)
  proof: by
  apply Cofan.IsColimit.fac

中文:
定理 ι_desc
  结论: {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : 对任意 A : IndexSet Δ, s.N A.1.unop.len ⟶ Z)
  证明: by
  apply Cofan.IsColimit.fac

Depends on / 依赖: Cofan.IsColimit.fac, IsColimit
-/
theorem ι_desc {Z : C} (Δ : SimplexCategoryᵒᵖ) (F : forall A : IndexSet Δ, s.N A.1.unop.len ⟶ Z)
    (A : IndexSet Δ) : (s.cofan Δ).inj A ≫ s.desc Δ F = F A := by
  apply Cofan.IsColimit.fac

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A simplicial object that is isomorphic to a split simplicial object is split. -/
@[simps]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (e : X ≅ Y)
  body: s.N
  ι n := s.ι n ≫ e.hom.app (op ⦋n⦌)
  isColimit' Δ := IsColimit.ofIsoColimit (s.isColimit Δ) (Cofan.ext (e.app Δ)
    (fun A => by simp [cofan, cofan']))

中文:
定义 ofIso
  签名: (e : X ≅ Y)
  定义体: s.N
  ι n := s.ι n ≫ e.hom.app (op ⦋n⦌)
  isColimit' Δ := IsColimit.ofIsoColimit (s.isColimit Δ) (Cofan.ext (e.app Δ)
    (fun A => by simp [cofan, cofan']))
-/
def ofIso (e : X ≅ Y) : Splitting Y where
  N := s.N
  ι n := s.ι n ≫ e.hom.app (op ⦋n⦌)
  isColimit' Δ := IsColimit.ofIsoColimit (s.isColimit Δ) (Cofan.ext (e.app Δ)
    (fun A => by simp [cofan, cofan']))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
theorem `cofan_inj_epi_naturality` / 定理 `cofan_inj_epi_naturality`

English:
theorem cofan_inj_epi_naturality
  statement: {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂)
  proof: by
  dsimp [cofan]
  rw [assoc]; rw [← X.map_comp]
  rfl

中文:
定理 cofan_inj_epi_naturality
  结论: {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂)
  证明: by
  dsimp [cofan]
  rw [assoc]; rw [← X.map_comp]
  rfl

Depends on / 依赖: X.map_comp, map_comp
-/
theorem cofan_inj_epi_naturality {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (A : IndexSet Δ₁) (p : Δ₁ ⟶ Δ₂)
    [Epi p.unop] : (s.cofan Δ₁).inj A ≫ X.map p = (s.cofan Δ₂).inj (A.epiComp p) := by
  dsimp [cofan]
  rw [assoc]; rw [← X.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The image of a splitting of simplicial object by a functor which preserves
finite coproducts -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D) [PreservesFiniteCoproducts F]
  body: F.obj (s.N n)
  ι n := F.map (s.ι n)
  isColimit' n :=
    IsColimit.ofIsoColimit (isColimitCofanMkObjOfIsColimit F _ _ (s.isColimit n))
      (Cofan.ext (Iso.refl _))

中文:
定义 map
  签名: (F : C ⥤ D) [PreservesFiniteCoproducts F]
  定义体: F.obj (s.N n)
  ι n := F.map (s.ι n)
  isColimit' n :=
    IsColimit.ofIsoColimit (isColimitCofanMkObjOfIsColimit F _ _ (s.isColimit n))
      (Cofan.ext (Iso.refl _))

Depends on / 依赖: F.obj
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
/--
Definition of `Split` / `Split` 的定义

English:
structure Split
  parameters: where
  axioms and operations (2):
    - X : SimplicialObject C
    - s : Splitting X

中文:
结构 Split
  参数: where
  公理与运算 (2 个):
    - X : SimplicialObject C
    - s : Splitting X
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
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: {X : SimplicialObject C} (s : Splitting X)
  body: ⟨X, s⟩

中文:
定义 mk'
  签名: {X : SimplicialObject C} (s : Splitting X)
  定义体: ⟨X, s⟩
-/
def mk' {X : SimplicialObject C} (s : Splitting X) : Split C :=
  ⟨X, s⟩

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (S₁ S₂ : Split C)
  axioms and operations (3):
    - F : S₁.X ⟶ S₂.X
    - f : forall n : Nat, S₁.s.N n ⟶ S₂.s.N n
    - comm : forall n : Nat, S₁.s.ι n ≫ F.app (op ⦋n⦌) = f n ≫ S₂.s.ι n  [default: by cat_disch]

中文:
结构 Hom
  参数: (S₁ S₂ : Split C)
  公理与运算 (3 个):
    - F : S₁.X ⟶ S₂.X
    - f : 对任意 n : 自然数, S₁.s.N n ⟶ S₂.s.N n
    - comm : 对任意 n : 自然数, S₁.s.ι n ≫ F.app (op ⦋n⦌) = f n ≫ S₂.s.ι n  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (S₁ S₂ : Split C) where
  /-- the morphism between the underlying simplicial objects -/
  F : S₁.X ⟶ S₂.X
  /-- the morphism between the "nondegenerate" `n`-simplices for all `n : ℕ` -/
  f : forall n : Nat, S₁.s.N n ⟶ S₂.s.N n
  comm : forall n : Nat, S₁.s.ι n ≫ F.app (op ⦋n⦌) = f n ≫ S₂.s.ι n := by cat_disch

@[ext]
/--
theorem `Hom.ext` / 定理 `Hom.ext`

English:
theorem Hom.ext
  given: {S₁ S₂ : Split C} (Φ₁ Φ₂ : Hom S₁ S₂) (h : forall n : Nat, Φ₁.f n = Φ₂.f n)
  statement: Φ₁ = Φ₂
  proof: by
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
  rw [c₁]; rw [c₂]

中文:
定理 Hom.ext
  条件: {S₁ S₂ : Split C} (Φ₁ Φ₂ : Hom S₁ S₂) (h : 对任意 n : 自然数, Φ₁.f n = Φ₂.f n)
  结论: Φ₁ = Φ₂
  证明: by
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
  rw [c₁]; rw [c₂]
-/
theorem Hom.ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : Hom S₁ S₂) (h : forall n : Nat, Φ₁.f n = Φ₂.f n) : Φ₁ = Φ₂ := by
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
  rw [c₁]; rw [c₂]

attribute [simp, reassoc] Hom.comm

end Split

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Split C)
  body: Split.Hom
  id S :=
    { F := 𝟙 _
      f := fun _ => 𝟙 _ }
  comp Φ₁₂ Φ₂₃ :=
    { F := Φ₁₂.F ≫ Φ₂₃.F
      f := fun n => Φ₁₂.f n ≫ Φ₂₃.f n
      comm := fun n => by
        dsimp
        simp only [assoc, Split.Hom.comm_assoc, Split.Hom.comm] }

中文:
实例 :
  签名: Category (Split C)
  定义体: Split.Hom
  id S :=
    { F := 𝟙 _
      f := fun _ => 𝟙 _ }
  comp Φ₁₂ Φ₂₃ :=
    { F := Φ₁₂.F ≫ Φ₂₃.F
      f := fun n => Φ₁₂.f n ≫ Φ₂₃.f n
      comm := fun n => by
        dsimp
        simp only [assoc, Split.Hom.comm_assoc, Split.Hom.comm] }

Depends on / 依赖: Split.Hom
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
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {S₁ S₂ : Split C} (Φ₁ Φ₂ : S₁ ⟶ S₂) (h : forall n : Nat, Φ₁.f n = Φ₂.f n)
  statement: Φ₁ = Φ₂
  proof: Hom.ext _ _ h

中文:
定理 hom_ext
  条件: {S₁ S₂ : Split C} (Φ₁ Φ₂ : S₁ ⟶ S₂) (h : 对任意 n : 自然数, Φ₁.f n = Φ₂.f n)
  结论: Φ₁ = Φ₂
  证明: Hom.ext _ _ h

Depends on / 依赖: Hom.ext
-/
theorem hom_ext {S₁ S₂ : Split C} (Φ₁ Φ₂ : S₁ ⟶ S₂) (h : forall n : Nat, Φ₁.f n = Φ₂.f n) : Φ₁ = Φ₂ :=
  Hom.ext _ _ h

/--
theorem `congr_F` / 定理 `congr_F`

English:
theorem congr_F
  given: {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂)
  statement: Φ₁.f = Φ₂.f
  proof: by rw [h]

中文:
定理 congr_F
  条件: {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂)
  结论: Φ₁.f = Φ₂.f
  证明: by rw [h]
-/
theorem congr_F {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) : Φ₁.f = Φ₂.f := by rw [h]

/--
theorem `congr_f` / 定理 `congr_f`

English:
theorem congr_f
  given: {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) (n : Nat)
  statement: Φ₁.f n = Φ₂.f n
  proof: by
  rw [h]

@[simp]

中文:
定理 congr_f
  条件: {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) (n : 自然数)
  结论: Φ₁.f n = Φ₂.f n
  证明: by
  rw [h]

@[simp]
-/
theorem congr_f {S₁ S₂ : Split C} {Φ₁ Φ₂ : S₁ ⟶ S₂} (h : Φ₁ = Φ₂) (n : Nat) : Φ₁.f n = Φ₂.f n := by
  rw [h]

@[simp]
/--
theorem `id_F` / 定理 `id_F`

English:
theorem id_F
  given: (S : Split C)
  statement: (𝟙 S : S ⟶ S).F = 𝟙 S.X
  proof: rfl

@[simp]

中文:
定理 id_F
  条件: (S : Split C)
  结论: (𝟙 S : S ⟶ S).F = 𝟙 S.X
  证明: rfl

@[simp]
-/
theorem id_F (S : Split C) : (𝟙 S : S ⟶ S).F = 𝟙 S.X :=
  rfl

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  given: (S : Split C) (n : Nat)
  statement: (𝟙 S : S ⟶ S).f n = 𝟙 (S.s.N n)
  proof: rfl

@[simp]

中文:
定理 id_f
  条件: (S : Split C) (n : 自然数)
  结论: (𝟙 S : S ⟶ S).f n = 𝟙 (S.s.N n)
  证明: rfl

@[simp]
-/
theorem id_f (S : Split C) (n : Nat) : (𝟙 S : S ⟶ S).f n = 𝟙 (S.s.N n) :=
  rfl

@[simp]
/--
theorem `comp_F` / 定理 `comp_F`

English:
theorem comp_F
  given: {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃)
  proof: rfl

@[simp]

中文:
定理 comp_F
  条件: {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃)
  证明: rfl

@[simp]
-/
theorem comp_F {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) :
    (Φ₁₂ ≫ Φ₂₃).F = Φ₁₂.F ≫ Φ₂₃.F :=
  rfl

@[simp]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  given: {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) (n : Nat)
  proof: rfl

中文:
定理 comp_f
  条件: {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) (n : 自然数)
  证明: rfl
-/
theorem comp_f {S₁ S₂ S₃ : Split C} (Φ₁₂ : S₁ ⟶ S₂) (Φ₂₃ : S₂ ⟶ S₃) (n : Nat) :
    (Φ₁₂ ≫ Φ₂₃).f n = Φ₁₂.f n ≫ Φ₂₃.f n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
-- This is not a `@[simp]` lemma as it can later be proved by `simp`.
@[reassoc]
/--
theorem `cofan_inj_naturality_symm` / 定理 `cofan_inj_naturality_symm`

English:
theorem cofan_inj_naturality_symm
  statement: {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) {Δ : SimplexCategoryᵒᵖ}
  proof: by
  rw [S₁.s.cofan_inj_eq]; rw [S₂.s.cofan_inj_eq]; rw [assoc]; rw [Φ.F.naturality]; rw [← Φ.comm_assoc]

中文:
定理 cofan_inj_naturality_symm
  结论: {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) {Δ : SimplexCategoryᵒᵖ}
  证明: by
  rw [S₁.s.cofan_inj_eq]; rw [S₂.s.cofan_inj_eq]; rw [assoc]; rw [Φ.F.naturality]; rw [← Φ.comm_assoc]

Depends on / 依赖: F.naturality, cofan_inj_eq, comm_assoc, naturality, s.cofan_inj_eq
-/
theorem cofan_inj_naturality_symm {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) {Δ : SimplexCategoryᵒᵖ}
    (A : Splitting.IndexSet Δ) :
    (S₁.s.cofan Δ).inj A ≫ Φ.F.app Δ = Φ.f A.1.unop.len ≫ (S₂.s.cofan Δ).inj A := by
  rw [S₁.s.cofan_inj_eq]; rw [S₂.s.cofan_inj_eq]; rw [assoc]; rw [Φ.F.naturality]; rw [← Φ.comm_assoc]

variable (C)

/-- The functor `SimplicialObject.Split C ⥤ SimplicialObject C` which forgets
the splitting. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Split C ⥤ SimplicialObject C where
  body: S.X
  map Φ := Φ.F

中文:
定义 forget
  签名: : Split C ⥤ SimplicialObject C where
  定义体: S.X
  map Φ := Φ.F
-/
def forget : Split C ⥤ SimplicialObject C where
  obj S := S.X
  map Φ := Φ.F

/-- The functor `SimplicialObject.Split C ⥤ C` which sends a simplicial object equipped
with a splitting to its nondegenerate `n`-simplices. -/
@[simps]
/--
Definition of `evalN` / `evalN` 的定义

English:
definition evalN
  signature: (n : Nat)
  body: S.s.N n
  map Φ := Φ.f n

中文:
定义 evalN
  签名: (n : 自然数)
  定义体: S.s.N n
  map Φ := Φ.f n

Depends on / 依赖: S.s.N
-/
def evalN (n : Nat) : Split C ⥤ C where
  obj S := S.s.N n
  map Φ := Φ.f n

/-- The inclusion of each summand in the coproduct decomposition of simplices
in split simplicial objects is a natural transformation of functors
`SimplicialObject.Split C ⥤ C` -/
@[simps]
/--
Definition of `natTransCofanInj` / `natTransCofanInj` 的定义

English:
definition natTransCofanInj
  signature: {Δ : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ)
  body: (S.s.cofan Δ).inj A
  naturality _ _ Φ := (cofan_inj_naturality_symm Φ A).symm

中文:
定义 natTransCofanInj
  签名: {Δ : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ)
  定义体: (S.s.cofan Δ).inj A
  naturality _ _ Φ := (cofan_inj_naturality_symm Φ A).symm

Depends on / 依赖: S.s.cofan
-/
def natTransCofanInj {Δ : SimplexCategoryᵒᵖ} (A : Splitting.IndexSet Δ) :
    evalN C A.1.unop.len ⟶ forget C ⋙ (evaluation SimplexCategoryᵒᵖ C).obj Δ where
  app S := (S.s.cofan Δ).inj A
  naturality _ _ Φ := (cofan_inj_naturality_symm Φ A).symm

end Split

end CategoryTheory.SimplicialObject
