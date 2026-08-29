/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.PathCategory.Basic
/-! # Presentation of the simplex category by generators and relations.

We introduce `SimplexCategoryGenRel` as the category presented by generating
morphisms `δ i : [n] ⟶ [n + 1]` and `σ i : [n + 1] ⟶ [n]` and subject to the
simplicial identities, and we provide induction principles for reasoning about
objects and morphisms in this category.

This category admits a canonical functor `toSimplexCategory` to the usual simplex category.
The fact that this functor is an equivalence will be recorded in a separate file.
-/

@[expose] public section
open CategoryTheory

/--
Definition of `FreeSimplexQuiver` / `FreeSimplexQuiver` 的定义

English:
definition FreeSimplexQuiver
  body: Nat

中文:
定义 FreeSimplexQuiver
  定义体: Nat
-/
def FreeSimplexQuiver := Nat

/--
Definition of `FreeSimplexQuiver.mk` / `FreeSimplexQuiver.mk` 的定义

English:
definition FreeSimplexQuiver.mk
  signature: (n : Nat)
  body: n

中文:
定义 FreeSimplexQuiver.mk
  签名: (n : 自然数)
  定义体: n
-/
def FreeSimplexQuiver.mk (n : Nat) : FreeSimplexQuiver := n

/--
Definition of `FreeSimplexQuiver.len` / `FreeSimplexQuiver.len` 的定义

English:
definition FreeSimplexQuiver.len
  signature: (x : FreeSimplexQuiver)
  body: x

中文:
定义 FreeSimplexQuiver.len
  签名: (x : FreeSimplexQuiver)
  定义体: x
-/
def FreeSimplexQuiver.len (x : FreeSimplexQuiver) : Nat := x

namespace FreeSimplexQuiver

/--
Inductive type `Hom` / 归纳类型 `Hom`

English:
inductive Hom
  parameters: : FreeSimplexQuiver -> FreeSimplexQuiver -> Type
  constructors (2):
    - δ: {n : Nat} (i : Fin (n + 2)) : Hom (.mk n) (.mk (n + 1))
    - σ: {n : Nat} (i : Fin (n + 1)) : Hom (.mk (n + 1)) (.mk n)

中文:
归纳类型 Hom
  参数: : FreeSimplexQuiver -> FreeSimplexQuiver -> Type
  构造子 (2 个):
    - δ: {n : 自然数} (i : Fin (n + 2)) : Hom (.mk n) (.mk (n + 1))
    - σ: {n : 自然数} (i : Fin (n + 1)) : Hom (.mk (n + 1)) (.mk n)
-/
inductive Hom : FreeSimplexQuiver -> FreeSimplexQuiver -> Type
  | δ {n : Nat} (i : Fin (n + 2)) : Hom (.mk n) (.mk (n + 1))
  | σ {n : Nat} (i : Fin (n + 1)) : Hom (.mk (n + 1)) (.mk n)

/--
Instance `quiv` / 实例 `quiv`

English:
instance quiv
  signature: : Quiver FreeSimplexQuiver where
  body: FreeSimplexQuiver.Hom

中文:
实例 quiv
  签名: : Quiver FreeSimplexQuiver where
  定义体: FreeSimplexQuiver.Hom

Depends on / 依赖: FreeSimplexQuiver, FreeSimplexQuiver.Hom
-/
instance quiv : Quiver FreeSimplexQuiver where
  Hom := FreeSimplexQuiver.Hom

/--
Definition of `δ` / `δ` 的定义

English:
abbreviation δ
  signature: {n : Nat} (i : Fin (n + 2))
  body: FreeSimplexQuiver.Hom.δ i

中文:
缩写 δ
  签名: {n : 自然数} (i : Fin (n + 2))
  定义体: FreeSimplexQuiver.Hom.δ i

Depends on / 依赖: FreeSimplexQuiver, FreeSimplexQuiver.Hom
-/
abbrev δ {n : Nat} (i : Fin (n + 2)) : FreeSimplexQuiver.mk n ⟶ .mk (n + 1) :=
  FreeSimplexQuiver.Hom.δ i

/--
Definition of `σ` / `σ` 的定义

English:
abbreviation σ
  signature: {n : Nat} (i : Fin (n + 1))
  body: FreeSimplexQuiver.Hom.σ i

中文:
缩写 σ
  签名: {n : 自然数} (i : Fin (n + 1))
  定义体: FreeSimplexQuiver.Hom.σ i

Depends on / 依赖: FreeSimplexQuiver, FreeSimplexQuiver.Hom
-/
abbrev σ {n : Nat} (i : Fin (n + 1)) : FreeSimplexQuiver.mk (n + 1) ⟶ .mk n :=
  FreeSimplexQuiver.Hom.σ i

/--
Inductive type `homRel` / 归纳类型 `homRel`

English:
inductive homRel
  parameters: : HomRel (Paths FreeSimplexQuiver)
  constructors (6):
    - δ_comp_δ: {n : Nat} {i j : Fin (n + 2)} (H : i <= j) : homRel ((Paths.of FreeSimplexQuiver).map (δ i) ≫ (Paths.of FreeSimplexQuiver).map (δ j.succ)) ((Paths.of FreeSimplexQuiver).map (δ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i.castSucc))
    - δ_comp_σ_of_le: {n : Nat} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc) : homRel ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j.succ)) ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
    - δ_comp_σ_self: {n : Nat} {i : Fin (n + 1)} : homRel ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
    - δ_comp_σ_succ: {n : Nat} {i : Fin (n + 1)} : homRel ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
    - δ_comp_σ_of_gt: {n : Nat} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) : homRel ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ j.castSucc)) ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
    - σ_comp_σ: {n : Nat} {i j : Fin (n + 1)} (H : i <= j) : homRel ((Paths.of FreeSimplexQuiver).map (σ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j)) ((Paths.of FreeSimplexQuiver).map (σ j.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i))

中文:
归纳类型 homRel
  参数: : HomRel (Paths FreeSimplexQuiver)
  构造子 (6 个):
    - δ_comp_δ: {n : 自然数} {i j : Fin (n + 2)} (H : i <= j) : homRel ((Paths.of FreeSimplexQuiver).map (δ i) ≫ (Paths.of FreeSimplexQuiver).map (δ j.succ)) ((Paths.of FreeSimplexQuiver).map (δ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i.castSucc))
    - δ_comp_σ_of_le: {n : 自然数} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc) : homRel ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j.succ)) ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
    - δ_comp_σ_self: {n : 自然数} {i : Fin (n + 1)} : homRel ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
    - δ_comp_σ_succ: {n : 自然数} {i : Fin (n + 1)} : homRel ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
    - δ_comp_σ_of_gt: {n : 自然数} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) : homRel ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ j.castSucc)) ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
    - σ_comp_σ: {n : 自然数} {i j : Fin (n + 1)} (H : i <= j) : homRel ((Paths.of FreeSimplexQuiver).map (σ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j)) ((Paths.of FreeSimplexQuiver).map (σ j.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i))
-/
inductive homRel : HomRel (Paths FreeSimplexQuiver)
  | δ_comp_δ {n : Nat} {i j : Fin (n + 2)} (H : i <= j) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i) ≫ (Paths.of FreeSimplexQuiver).map (δ j.succ))
    ((Paths.of FreeSimplexQuiver).map (δ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i.castSucc))
  | δ_comp_σ_of_le {n : Nat} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j.succ))
    ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
  | δ_comp_σ_self {n : Nat} {i : Fin (n + 1)} : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
  | δ_comp_σ_succ {n : Nat} {i : Fin (n + 1)} : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
  | δ_comp_σ_of_gt {n : Nat} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ j.castSucc))
    ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
  | σ_comp_σ {n : Nat} {i j : Fin (n + 1)} (H : i <= j) : homRel
    ((Paths.of FreeSimplexQuiver).map (σ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j))
    ((Paths.of FreeSimplexQuiver).map (σ j.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i))

end FreeSimplexQuiver

/--
Definition of `SimplexCategoryGenRel` / `SimplexCategoryGenRel` 的定义

English:
definition SimplexCategoryGenRel
  body: Quotient FreeSimplexQuiver.homRel
  deriving Category

中文:
定义 SimplexCategoryGenRel
  定义体: Quotient FreeSimplexQuiver.homRel
  deriving Category

Depends on / 依赖: FreeSimplexQuiver, FreeSimplexQuiver.homRel, Quotient, homRel
-/
def SimplexCategoryGenRel := Quotient FreeSimplexQuiver.homRel
  deriving Category

/--
Definition of `SimplexCategoryGenRel.mk` / `SimplexCategoryGenRel.mk` 的定义

English:
definition SimplexCategoryGenRel.mk
  signature: (n : Nat)
  body: (Paths.of FreeSimplexQuiver).obj n

中文:
定义 SimplexCategoryGenRel.mk
  签名: (n : 自然数)
  定义体: (Paths.of FreeSimplexQuiver).obj n

Depends on / 依赖: FreeSimplexQuiver, Paths.of
-/
def SimplexCategoryGenRel.mk (n : Nat) : SimplexCategoryGenRel where
  as := (Paths.of FreeSimplexQuiver).obj n

namespace SimplexCategoryGenRel

/--
Definition of `δ` / `δ` 的定义

English:
abbreviation δ
  signature: {n : Nat} (i : Fin (n + 2))
  body: (Quotient.functor FreeSimplexQuiver.homRel).map (Paths.of FreeSimplexQuiver).map (.δ i)

中文:
缩写 δ
  签名: {n : 自然数} (i : Fin (n + 2))
  定义体: (Quotient.functor FreeSimplexQuiver.homRel).map (Paths.of FreeSimplexQuiver).map (.δ i)

Depends on / 依赖: FreeSimplexQuiver, FreeSimplexQuiver.homRel, Paths.of, Quotient, Quotient.functor, functor, homRel
-/
abbrev δ {n : Nat} (i : Fin (n + 2)) : mk n ⟶ mk (n + 1) :=
(Quotient.functor FreeSimplexQuiver.homRel).map (Paths.of FreeSimplexQuiver).map (.δ i)

/--
Definition of `σ` / `σ` 的定义

English:
abbreviation σ
  signature: {n : Nat} (i : Fin (n + 1))
  body: (Quotient.functor FreeSimplexQuiver.homRel).map (Paths.of FreeSimplexQuiver).map (.σ i)

中文:
缩写 σ
  签名: {n : 自然数} (i : Fin (n + 1))
  定义体: (Quotient.functor FreeSimplexQuiver.homRel).map (Paths.of FreeSimplexQuiver).map (.σ i)

Depends on / 依赖: FreeSimplexQuiver, FreeSimplexQuiver.homRel, Paths.of, Quotient, Quotient.functor, functor, homRel
-/
abbrev σ {n : Nat} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk n :=
(Quotient.functor FreeSimplexQuiver.homRel).map (Paths.of FreeSimplexQuiver).map (.σ i)

/--
Definition of `len` / `len` 的定义

English:
definition len
  signature: (x : SimplexCategoryGenRel)
  body: by rcases x with ⟨n⟩; exact n

@[simp]

中文:
定义 len
  签名: (x : SimplexCategoryGenRel)
  定义体: by rcases x with ⟨n⟩; exact n

@[simp]
-/
def len (x : SimplexCategoryGenRel) : Nat := by rcases x with ⟨n⟩; exact n

@[simp]
/--
lemma `mk_len` / 引理 `mk_len`

English:
lemma mk_len
  given: (n : Nat)
  statement: len (mk n) = n
  proof: rfl

中文:
引理 mk_len
  条件: (n : 自然数)
  结论: len (mk n) = n
  证明: rfl
-/
lemma mk_len (n : Nat) : len (mk n) = n := rfl

section InductionPrinciples

/--
Inductive type `faces` / 归纳类型 `faces`

English:
inductive faces
  parameters: : MorphismProperty SimplexCategoryGenRel
  constructors (1):
    - δ: {n : Nat} (i : Fin (n + 2)) : faces (δ i)

中文:
归纳类型 faces
  参数: : Morphism命题erty SimplexCategoryGenRel
  构造子 (1 个):
    - δ: {n : 自然数} (i : Fin (n + 2)) : faces (δ i)
-/
inductive faces : MorphismProperty SimplexCategoryGenRel
  | δ {n : Nat} (i : Fin (n + 2)) : faces (δ i)

/--
Inductive type `degeneracies` / 归纳类型 `degeneracies`

English:
inductive degeneracies
  parameters: : MorphismProperty SimplexCategoryGenRel
  constructors (1):
    - σ: {n : Nat} (i : Fin (n + 1)) : degeneracies (σ i)

中文:
归纳类型 degeneracies
  参数: : Morphism命题erty SimplexCategoryGenRel
  构造子 (1 个):
    - σ: {n : 自然数} (i : Fin (n + 1)) : degeneracies (σ i)
-/
inductive degeneracies : MorphismProperty SimplexCategoryGenRel
  | σ {n : Nat} (i : Fin (n + 1)) : degeneracies (σ i)

/--
Definition of `generators` / `generators` 的定义

English:
abbreviation generators
  body: faces ⊔ degeneracies

中文:
缩写 generators
  定义体: faces ⊔ degeneracies

Depends on / 依赖: degeneracies
-/
abbrev generators := faces ⊔ degeneracies

namespace generators

/--
lemma `δ` / 引理 `δ`

English:
lemma δ
  given: {n : Nat} (i : Fin (n + 2))
  statement: generators (δ i)
  proof: le_sup_left (a := faces) _ (.δ i)

中文:
引理 δ
  条件: {n : 自然数} (i : Fin (n + 2))
  结论: generators (δ i)
  证明: le_sup_left (a := faces) _ (.δ i)

Depends on / 依赖: le_sup_left
-/
lemma δ {n : Nat} (i : Fin (n + 2)) : generators (δ i) := le_sup_left (a := faces) _ (.δ i)

/--
lemma `σ` / 引理 `σ`

English:
lemma σ
  given: {n : Nat} (i : Fin (n + 1))
  statement: generators (σ i)
  proof: le_sup_right (a := faces) _ (.σ i)

中文:
引理 σ
  条件: {n : 自然数} (i : Fin (n + 1))
  结论: generators (σ i)
  证明: le_sup_right (a := faces) _ (.σ i)

Depends on / 依赖: le_sup_right
-/
lemma σ {n : Nat} (i : Fin (n + 1)) : generators (σ i) := le_sup_right (a := faces) _ (.σ i)

end generators

/--
lemma `multiplicativeClosure_isGenerator_eq_top` / 引理 `multiplicativeClosure_isGenerator_eq_top`

English:
lemma multiplicativeClosure_isGenerator_eq_top
  statement: generators.multiplicativeClosure = ⊤
  proof: by
  apply le_antisymm (by simp)
  rintro x y f -
  induction f using CategoryTheory.Quotient.induction with | _ f
  induction f using Paths.induction with
  | id => exact generators.multiplicativeClosure.id_mem _
  | comp _ k h =>
    cases k
· exact generators.multiplicativeClosure.comp_mem _ _ h 

中文:
引理 multiplicativeClosure_isGenerator_eq_top
  结论: generators.multiplicativeClosure = ⊤
  证明: by
  apply le_antisymm (by simp)
  rintro x y f -
  induction f using CategoryTheory.Quotient.induction with | _ f
  induction f using Paths.induction with
  | id => exact generators.multiplicativeClosure.id_mem _
  | comp _ k h =>
    cases k
· exact generators.multiplicativeClosure.comp_mem _ _ h 

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.induction, Paths.induction, Quotient, comp_mem, generators, generators.multiplicativeClosure.comp_mem, generators.multiplicativeClosure.id_mem, id_mem, le_antisymm, multiplicativeClosure
-/
lemma multiplicativeClosure_isGenerator_eq_top : generators.multiplicativeClosure = ⊤ := by
  apply le_antisymm (by simp)
  rintro x y f -
  induction f using CategoryTheory.Quotient.induction with | _ f
  induction f using Paths.induction with
  | id => exact generators.multiplicativeClosure.id_mem _
  | comp _ k h =>
    cases k
· exact generators.multiplicativeClosure.comp_mem _ _ h .of _ .δ _
· exact generators.multiplicativeClosure.comp_mem _ _ h .of _ .σ _

/-- An unrolled version of the induction principle obtained in the previous lemma. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
lemma `hom_induction` / 引理 `hom_induction`

English:
lemma hom_induction
  statement: (P : MorphismProperty SimplexCategoryGenRel)
  proof: by
  suffices generators.multiplicativeClosure <= P by
    rw [multiplicativeClosure_isGenerator_eq_top]; rw [top_le_iff] at this
    rw [this]
    apply MorphismProperty.top_apply
  intro _ _ f hf
  induction hf with
  | of f h =>
    rcases h with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using! (comp_δ (𝟙 _) i i

中文:
引理 hom_induction
  结论: (P : Morphism命题erty SimplexCategoryGenRel)
  证明: by
  suffices generators.multiplicativeClosure <= P by
    rw [multiplicativeClosure_isGenerator_eq_top]; rw [top_le_iff] at this
    rw [this]
    apply MorphismProperty.top_apply
  intro _ _ f hf
  induction hf with
  | of f h =>
    rcases h with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using! (comp_δ (𝟙 _) i i

Depends on / 依赖: MorphismProperty, MorphismProperty.top_apply, comp_of, generators, generators.multiplicativeClosure, multiplicativeClosure, multiplicativeClosure_isGenerator_eq_top, top_apply, top_le_iff
-/
lemma hom_induction (P : MorphismProperty SimplexCategoryGenRel)
    (id : forall {n : Nat}, P (𝟙 (mk n)))
    (comp_δ : forall {n m : Nat} (u : mk n ⟶ mk m) (i : Fin (m + 2)), P u -> P (u ≫ δ i))
    (comp_σ : forall {n m : Nat} (u : mk n ⟶ mk (m + 1)) (i : Fin (m + 1)), P u -> P (u ≫ σ i))
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) : P f := by
  suffices generators.multiplicativeClosure <= P by
    rw [multiplicativeClosure_isGenerator_eq_top]; rw [top_le_iff] at this
    rw [this]
    apply MorphismProperty.top_apply
  intro _ _ f hf
  induction hf with
  | of f h =>
    rcases h with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using! (comp_δ (𝟙 _) i id)
    · simpa using! (comp_σ (𝟙 _) i id)
  | id n => exact id
  | comp_of f g hf hg hrec =>
    rcases hg with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using! (comp_δ f i hrec)
    · simpa using! (comp_σ f i hrec)

/--
lemma `hom_induction'` / 引理 `hom_induction'`

English:
lemma hom_induction'
  statement: (P : MorphismProperty SimplexCategoryGenRel)
  proof: by
  suffices generators.multiplicativeClosure' <= P by
    rw [← MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure']; rw [multiplicativeClosure_isGenerator_eq_top]; rw [top_le_iff] at this
    rw [this]
    apply MorphismProperty.top_apply
  intro _ _ f hf
  induction hf with
  | of f

中文:
引理 hom_induction'
  结论: (P : Morphism命题erty SimplexCategoryGenRel)
  证明: by
  suffices generators.multiplicativeClosure' <= P by
    rw [← MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure']; rw [multiplicativeClosure_isGenerator_eq_top]; rw [top_le_iff] at this
    rw [this]
    apply MorphismProperty.top_apply
  intro _ _ f hf
  induction hf with
  | of f

Depends on / 依赖: MorphismProperty, MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure, MorphismProperty.top_apply, generators, generators.multiplicativeClosure, multiplicativeClosure, multiplicativeClosure_eq_multiplicativeClosure, multiplicativeClosure_isGenerator_eq_top, of_comp, top_apply, top_le_iff
-/
lemma hom_induction' (P : MorphismProperty SimplexCategoryGenRel)
    (id : forall {n : Nat}, P (𝟙 (mk n)))
    (δ_comp : forall {n m : Nat} (u : mk (m + 1) ⟶ mk n)
      (i : Fin (m + 2)), P u -> P (δ i ≫ u))
    (σ_comp : forall {n m : Nat} (u : mk m ⟶ mk n)
      (i : Fin (m + 1)), P u -> P (σ i ≫ u)) {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    P f := by
  suffices generators.multiplicativeClosure' <= P by
    rw [← MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure']; rw [multiplicativeClosure_isGenerator_eq_top]; rw [top_le_iff] at this
    rw [this]
    apply MorphismProperty.top_apply
  intro _ _ f hf
  induction hf with
  | of f h =>
    rcases h with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using! (δ_comp (𝟙 _) i id)
    · simpa using! (σ_comp (𝟙 _) i id)
  | id n => exact id
  | of_comp f g hf hg hrec =>
    rcases hf with ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩
    · simpa using! (δ_comp g i hrec)
    · simpa using! (σ_comp g i hrec)

/-- An induction principle for reasoning about objects in `SimplexCategoryGenRel`. This should be
used instead of identifying an object with `mk` of its `len`. -/
@[elab_as_elim, cases_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {P : SimplexCategoryGenRel -> Sort*}
  body: by
  intro x
  exact H x.len

中文:
定义 rec
  签名: {P : SimplexCategoryGenRel -> Sort*}
  定义体: by
  intro x
  exact H x.len
-/
protected def rec {P : SimplexCategoryGenRel -> Sort*}
    (H : forall n : Nat, P (.mk n)) :
    forall x : SimplexCategoryGenRel, P x := by
  intro x
  exact H x.len

/-- A basic `ext` lemma for objects of `SimplexCategoryGenRel`. -/
@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {x y : SimplexCategoryGenRel} (h : x.len = y.len)
  statement: x = y
  proof: by
  cases x
  cases y
  simp only [mk_len] at h
  congr

中文:
引理 ext
  条件: {x y : SimplexCategoryGenRel} (h : x.len = y.len)
  结论: x = y
  证明: by
  cases x
  cases y
  simp only [mk_len] at h
  congr

Depends on / 依赖: mk_len
-/
lemma ext {x y : SimplexCategoryGenRel} (h : x.len = y.len) : x = y := by
  cases x
  cases y
  simp only [mk_len] at h
  congr

end InductionPrinciples

section SimplicialIdentities

@[reassoc]
/--
theorem `δ_comp_δ` / 定理 `δ_comp_δ`

English:
theorem δ_comp_δ
  given: {n} {i j : Fin (n + 2)} (H : i <= j)
  proof: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_δ H

@[reassoc]

中文:
定理 δ_comp_δ
  条件: {n} {i j : Fin (n + 2)} (H : i <= j)
  证明: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_δ H

@[reassoc]

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, FreeSimplexQuiver, FreeSimplexQuiver.homRel, Quotient, homRel
-/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i <= j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_δ H

@[reassoc]
/--
theorem `δ_comp_σ_of_le` / 定理 `δ_comp_σ_of_le`

English:
theorem δ_comp_σ_of_le
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc)
  proof: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_le H

@[reassoc]

中文:
定理 δ_comp_σ_of_le
  条件: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc)
  证明: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_le H

@[reassoc]

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, FreeSimplexQuiver, FreeSimplexQuiver.homRel, Quotient, homRel
-/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc) :
    δ i.castSucc ≫ σ j.succ = σ j ≫ δ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_le H

@[reassoc]
/--
theorem `δ_comp_σ_self` / 定理 `δ_comp_σ_self`

English:
theorem δ_comp_σ_self
  given: {n} {i : Fin (n + 1)}
  proof: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_self

@[reassoc]

中文:
定理 δ_comp_σ_self
  条件: {n} {i : Fin (n + 1)}
  证明: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_self

@[reassoc]

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, FreeSimplexQuiver, FreeSimplexQuiver.homRel, Quotient, homRel
-/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ i.castSucc ≫ σ i = 𝟙 (mk n) := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_self

@[reassoc]
/--
theorem `δ_comp_σ_succ` / 定理 `δ_comp_σ_succ`

English:
theorem δ_comp_σ_succ
  given: {n} {i : Fin (n + 1)}
  statement: δ i.succ ≫ σ i = 𝟙 (mk n)
  proof: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_succ

@[reassoc]

中文:
定理 δ_comp_σ_succ
  条件: {n} {i : Fin (n + 1)}
  结论: δ i.succ ≫ σ i = 𝟙 (mk n)
  证明: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_succ

@[reassoc]

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, FreeSimplexQuiver, FreeSimplexQuiver.homRel, Quotient, homRel
-/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 (mk n) := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_succ

@[reassoc]
/--
theorem `δ_comp_σ_of_gt` / 定理 `δ_comp_σ_of_gt`

English:
theorem δ_comp_σ_of_gt
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i)
  proof: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_gt H

@[reassoc]

中文:
定理 δ_comp_σ_of_gt
  条件: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i)
  证明: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_gt H

@[reassoc]

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, FreeSimplexQuiver, FreeSimplexQuiver.homRel, Quotient, homRel
-/
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) :
    δ i.succ ≫ σ j.castSucc = σ j ≫ δ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_gt H

@[reassoc]
/--
theorem `σ_comp_σ` / 定理 `σ_comp_σ`

English:
theorem σ_comp_σ
  given: {n} {i j : Fin (n + 1)} (H : i <= j)
  proof: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.σ_comp_σ H

中文:
定理 σ_comp_σ
  条件: {n} {i j : Fin (n + 1)} (H : i <= j)
  证明: by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.σ_comp_σ H

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, FreeSimplexQuiver, FreeSimplexQuiver.homRel, Quotient, homRel
-/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i <= j) :
    σ i.castSucc ≫ σ j = σ j.succ ≫ σ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.σ_comp_σ H

/--
lemma `δ_comp_δ_nat` / 引理 `δ_comp_δ_nat`

English:
lemma δ_comp_δ_nat
  given: {n} (i j : Nat) (hi : i < n + 2) (hj : j < n + 2) (H : i <= j)
  proof: δ_comp_δ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)

中文:
引理 δ_comp_δ_nat
  条件: {n} (i j : 自然数) (hi : i < n + 2) (hj : j < n + 2) (H : i <= j)
  证明: δ_comp_δ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)
-/
lemma δ_comp_δ_nat {n} (i j : Nat) (hi : i < n + 2) (hj : j < n + 2) (H : i <= j) :
    δ ⟨i, hi⟩ ≫ δ ⟨j + 1, by lia⟩ = δ ⟨j, hj⟩ ≫ δ ⟨i, by lia⟩ :=
  δ_comp_δ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)

/--
lemma `σ_comp_σ_nat` / 引理 `σ_comp_σ_nat`

English:
lemma σ_comp_σ_nat
  given: {n} (i j : Nat) (hi : i < n + 1) (hj : j < n + 1) (H : i <= j)
  proof: σ_comp_σ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)

中文:
引理 σ_comp_σ_nat
  条件: {n} (i j : 自然数) (hi : i < n + 1) (hj : j < n + 1) (H : i <= j)
  证明: σ_comp_σ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)
-/
lemma σ_comp_σ_nat {n} (i j : Nat) (hi : i < n + 1) (hj : j < n + 1) (H : i <= j) :
    σ ⟨i, by lia⟩ ≫ σ ⟨j, hj⟩ = σ ⟨j + 1, by lia⟩ ≫ σ ⟨i, hi⟩ :=
  σ_comp_σ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)

end SimplicialIdentities

/--
Definition of `toSimplexCategory` / `toSimplexCategory` 的定义

English:
definition toSimplexCategory
  signature: : SimplexCategoryGenRel ⥤ SimplexCategory
  body: CategoryTheory.Quotient.lift _
    (Paths.lift
      { obj := .mk
        map f := match f with
          | FreeSimplexQuiver.Hom.δ i => SimplexCategory.δ i
          | FreeSimplexQuiver.Hom.σ i => SimplexCategory.σ i })
    (fun _ _ _ _ h => match h with
      | .δ_comp_δ H => SimplexCategory.δ_com

中文:
定义 toSimplexCategory
  签名: : SimplexCategoryGenRel ⥤ SimplexCategory
  定义体: CategoryTheory.Quotient.lift _
    (Paths.lift
      { obj := .mk
        map f := match f with
          | FreeSimplexQuiver.Hom.δ i => SimplexCategory.δ i
          | FreeSimplexQuiver.Hom.σ i => SimplexCategory.σ i })
    (fun _ _ _ _ h => match h with
      | .δ_comp_δ H => SimplexCategory.δ_com

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, FreeSimplexQuiver, FreeSimplexQuiver.Hom, Paths.lift, Quotient, SimplexCatego, SimplexCategory
-/
def toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory :=
  CategoryTheory.Quotient.lift _
    (Paths.lift
      { obj := .mk
        map f := match f with
          | FreeSimplexQuiver.Hom.δ i => SimplexCategory.δ i
          | FreeSimplexQuiver.Hom.σ i => SimplexCategory.σ i })
    (fun _ _ _ _ h => match h with
      | .δ_comp_δ H => SimplexCategory.δ_comp_δ H
      | .δ_comp_σ_of_le H => SimplexCategory.δ_comp_σ_of_le H
      | .δ_comp_σ_self => SimplexCategory.δ_comp_σ_self
      | .δ_comp_σ_succ => SimplexCategory.δ_comp_σ_succ
      | .δ_comp_σ_of_gt H => SimplexCategory.δ_comp_σ_of_gt H
      | .σ_comp_σ H => SimplexCategory.σ_comp_σ H)

@[simp]
/--
lemma `toSimplexCategory_obj_mk` / 引理 `toSimplexCategory_obj_mk`

English:
lemma toSimplexCategory_obj_mk
  given: (n : Nat)
  statement: toSimplexCategory.obj (mk n) = .mk n
  proof: rfl

@[simp]

中文:
引理 toSimplexCategory_obj_mk
  条件: (n : 自然数)
  结论: toSimplexCategory.obj (mk n) = .mk n
  证明: rfl

@[simp]
-/
lemma toSimplexCategory_obj_mk (n : Nat) : toSimplexCategory.obj (mk n) = .mk n := rfl

@[simp]
/--
lemma `toSimplexCategory_map_δ` / 引理 `toSimplexCategory_map_δ`

English:
lemma toSimplexCategory_map_δ
  given: {n : Nat} (i : Fin (n + 2))
  proof: rfl

@[simp]

中文:
引理 toSimplexCategory_map_δ
  条件: {n : 自然数} (i : Fin (n + 2))
  证明: rfl

@[simp]
-/
lemma toSimplexCategory_map_δ {n : Nat} (i : Fin (n + 2)) :
    toSimplexCategory.map (δ i) = SimplexCategory.δ i := rfl

@[simp]
/--
lemma `toSimplexCategory_map_σ` / 引理 `toSimplexCategory_map_σ`

English:
lemma toSimplexCategory_map_σ
  given: {n : Nat} (i : Fin (n + 1))
  proof: rfl

@[simp]

中文:
引理 toSimplexCategory_map_σ
  条件: {n : 自然数} (i : Fin (n + 1))
  证明: rfl

@[simp]
-/
lemma toSimplexCategory_map_σ {n : Nat} (i : Fin (n + 1)) :
    toSimplexCategory.map (σ i) = SimplexCategory.σ i := rfl

@[simp]
/--
lemma `toSimplexCategory_len` / 引理 `toSimplexCategory_len`

English:
lemma toSimplexCategory_len
  given: {x : SimplexCategoryGenRel}
  statement: (toSimplexCategory.obj x).len = x.len
  proof: rfl

中文:
引理 toSimplexCategory_len
  条件: {x : SimplexCategoryGenRel}
  结论: (toSimplexCategory.obj x).len = x.len
  证明: rfl
-/
lemma toSimplexCategory_len {x : SimplexCategoryGenRel} : (toSimplexCategory.obj x).len = x.len :=
  rfl

end SimplexCategoryGenRel
