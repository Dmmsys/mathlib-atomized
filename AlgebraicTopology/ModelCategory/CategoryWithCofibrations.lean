/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Categories with classes of fibrations, cofibrations, weak equivalences

We introduce typeclasses `CategoryWithFibrations`, `CategoryWithCofibrations` and
`CategoryWithWeakEquivalences` to express that a category `C` is equipped with
classes of morphisms named "fibrations", "cofibrations" or "weak equivalences".

-/

@[expose] public section

universe v u

namespace HomotopicalAlgebra

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/--
Definition of `CategoryWithFibrations` / `CategoryWithFibrations` 的定义

English:
class CategoryWithFibrations
  parameters: where
  axioms and operations (1):
    - fibrations : MorphismProperty C

中文:
类 CategoryWithFibrations
  参数: where
  公理与运算 (1 个):
    - fibrations : Morphism命题erty C
-/
class CategoryWithFibrations where
  /-- the class of fibrations -/
  fibrations : MorphismProperty C

/--
Definition of `CategoryWithCofibrations` / `CategoryWithCofibrations` 的定义

English:
class CategoryWithCofibrations
  parameters: where
  axioms and operations (1):
    - cofibrations : MorphismProperty C

中文:
类 CategoryWithCofibrations
  参数: where
  公理与运算 (1 个):
    - cofibrations : Morphism命题erty C
-/
class CategoryWithCofibrations where
  /-- the class of cofibrations -/
  cofibrations : MorphismProperty C

/--
Definition of `CategoryWithWeakEquivalences` / `CategoryWithWeakEquivalences` 的定义

English:
class CategoryWithWeakEquivalences
  parameters: where
  axioms and operations (1):
    - weakEquivalences : MorphismProperty C

中文:
类 CategoryWithWeakEquivalences
  参数: where
  公理与运算 (1 个):
    - weakEquivalences : Morphism命题erty C
-/
class CategoryWithWeakEquivalences where
  /-- the class of weak equivalences -/
  weakEquivalences : MorphismProperty C

variable {X Y : C} (f : X ⟶ Y)

section Fib

variable [CategoryWithFibrations C]

/--
Definition of `fibrations` / `fibrations` 的定义

English:
definition fibrations
  signature: : MorphismProperty C
  body: CategoryWithFibrations.fibrations

中文:
定义 fibrations
  签名: : Morphism命题erty C
  定义体: CategoryWithFibrations.fibrations

Depends on / 依赖: CategoryWithFibrations, CategoryWithFibrations.fibrations, fibrations
-/
def fibrations : MorphismProperty C := CategoryWithFibrations.fibrations

variable {C}

/-- A morphism `f` satisfies `[Fibration f]` if it belongs to `fibrations C`. -/
@[mk_iff]
/--
Definition of `Fibration` / `Fibration` 的定义

English:
class Fibration
  parameters: : Prop where
  axioms and operations (1):
    - mem : fibrations C f

中文:
类 Fibration
  参数: : 命题 where
  公理与运算 (1 个):
    - mem : fibrations C f
-/
class Fibration : Prop where
  mem : fibrations C f

/--
lemma `mem_fibrations` / 引理 `mem_fibrations`

English:
lemma mem_fibrations
  given: [Fibration f]
  statement: fibrations C f
  proof: Fibration.mem

中文:
引理 mem_fibrations
  条件: [Fibration f]
  结论: fibrations C f
  证明: Fibration.mem

Depends on / 依赖: Fibration, Fibration.mem
-/
lemma mem_fibrations [Fibration f] : fibrations C f := Fibration.mem

end Fib

section Cof

variable [CategoryWithCofibrations C]

/--
Definition of `cofibrations` / `cofibrations` 的定义

English:
definition cofibrations
  signature: : MorphismProperty C
  body: CategoryWithCofibrations.cofibrations

中文:
定义 cofibrations
  签名: : Morphism命题erty C
  定义体: CategoryWithCofibrations.cofibrations

Depends on / 依赖: CategoryWithCofibrations, CategoryWithCofibrations.cofibrations, cofibrations
-/
def cofibrations : MorphismProperty C := CategoryWithCofibrations.cofibrations

variable {C}

/-- A morphism `f` satisfies `[Cofibration f]` if it belongs to `cofibrations C`. -/
@[mk_iff]
/--
Definition of `Cofibration` / `Cofibration` 的定义

English:
class Cofibration
  parameters: : Prop where
  axioms and operations (1):
    - mem : cofibrations C f

中文:
类 Cofibration
  参数: : 命题 where
  公理与运算 (1 个):
    - mem : cofibrations C f
-/
class Cofibration : Prop where
  mem : cofibrations C f

/--
lemma `mem_cofibrations` / 引理 `mem_cofibrations`

English:
lemma mem_cofibrations
  given: [Cofibration f]
  statement: cofibrations C f
  proof: Cofibration.mem

中文:
引理 mem_cofibrations
  条件: [Cofibration f]
  结论: cofibrations C f
  证明: Cofibration.mem

Depends on / 依赖: Cofibration, Cofibration.mem
-/
lemma mem_cofibrations [Cofibration f] : cofibrations C f := Cofibration.mem

end Cof

section W

variable [CategoryWithWeakEquivalences C]

/--
Definition of `weakEquivalences` / `weakEquivalences` 的定义

English:
definition weakEquivalences
  signature: : MorphismProperty C
  body: CategoryWithWeakEquivalences.weakEquivalences

中文:
定义 weakEquivalences
  签名: : Morphism命题erty C
  定义体: CategoryWithWeakEquivalences.weakEquivalences

Depends on / 依赖: CategoryWithWeakEquivalences, CategoryWithWeakEquivalences.weakEquivalences, weakEquivalences
-/
def weakEquivalences : MorphismProperty C := CategoryWithWeakEquivalences.weakEquivalences

variable {C}

/-- A morphism `f` satisfies `[WeakEquivalence f]` if it belongs to `weakEquivalences C`. -/
@[mk_iff]
/--
Definition of `WeakEquivalence` / `WeakEquivalence` 的定义

English:
class WeakEquivalence
  parameters: : Prop where
  axioms and operations (1):
    - mem : weakEquivalences C f

中文:
类 WeakEquivalence
  参数: : 命题 where
  公理与运算 (1 个):
    - mem : weakEquivalences C f
-/
class WeakEquivalence : Prop where
  mem : weakEquivalences C f

/--
lemma `mem_weakEquivalences` / 引理 `mem_weakEquivalences`

English:
lemma mem_weakEquivalences
  given: [WeakEquivalence f]
  statement: weakEquivalences C f
  proof: WeakEquivalence.mem

中文:
引理 mem_weakEquivalences
  条件: [WeakEquivalence f]
  结论: weakEquivalences C f
  证明: WeakEquivalence.mem

Depends on / 依赖: WeakEquivalence, WeakEquivalence.mem
-/
lemma mem_weakEquivalences [WeakEquivalence f] : weakEquivalences C f := WeakEquivalence.mem

end W

section TrivFib

variable [CategoryWithFibrations C] [CategoryWithWeakEquivalences C]

/--
Definition of `trivialFibrations` / `trivialFibrations` 的定义

English:
definition trivialFibrations
  signature: : MorphismProperty C
  body: fibrations C ⊓ weakEquivalences C

中文:
定义 trivialFibrations
  签名: : Morphism命题erty C
  定义体: fibrations C ⊓ weakEquivalences C

Depends on / 依赖: fibrations, weakEquivalences
-/
def trivialFibrations : MorphismProperty C := fibrations C ⊓ weakEquivalences C

/--
lemma `trivialFibrations_sub_fibrations` / 引理 `trivialFibrations_sub_fibrations`

English:
lemma trivialFibrations_sub_fibrations
  statement: trivialFibrations C <= fibrations C
  proof: fun _ _ _ hf => hf.1

中文:
引理 trivialFibrations_sub_fibrations
  结论: trivialFibrations C <= fibrations C
  证明: fun _ _ _ hf => hf.1
-/
lemma trivialFibrations_sub_fibrations : trivialFibrations C <= fibrations C :=
  fun _ _ _ hf => hf.1

/--
lemma `trivialFibrations_sub_weakEquivalences` / 引理 `trivialFibrations_sub_weakEquivalences`

English:
lemma trivialFibrations_sub_weakEquivalences
  statement: trivialFibrations C <= weakEquivalences C
  proof: fun _ _ _ hf => hf.2

中文:
引理 trivialFibrations_sub_weakEquivalences
  结论: trivialFibrations C <= weakEquivalences C
  证明: fun _ _ _ hf => hf.2
-/
lemma trivialFibrations_sub_weakEquivalences : trivialFibrations C <= weakEquivalences C :=
  fun _ _ _ hf => hf.2

variable {C}

/--
lemma `mem_trivialFibrations` / 引理 `mem_trivialFibrations`

English:
lemma mem_trivialFibrations
  given: [Fibration f] [WeakEquivalence f]
  proof: ⟨mem_fibrations f, mem_weakEquivalences f⟩

中文:
引理 mem_trivialFibrations
  条件: [Fibration f] [WeakEquivalence f]
  证明: ⟨mem_fibrations f, mem_weakEquivalences f⟩

Depends on / 依赖: mem_fibrations, mem_weakEquivalences
-/
lemma mem_trivialFibrations [Fibration f] [WeakEquivalence f] :
    trivialFibrations C f :=
  ⟨mem_fibrations f, mem_weakEquivalences f⟩

/--
lemma `mem_trivialFibrations_iff` / 引理 `mem_trivialFibrations_iff`

English:
lemma mem_trivialFibrations_iff
  proof: by
  rw [fibration_iff]; rw [weakEquivalence_iff]
  rfl

中文:
引理 mem_trivialFibrations_iff
  证明: by
  rw [fibration_iff]; rw [weakEquivalence_iff]
  rfl

Depends on / 依赖: fibration_iff, weakEquivalence_iff
-/
lemma mem_trivialFibrations_iff :
    trivialFibrations C f ↔ Fibration f ∧ WeakEquivalence f := by
  rw [fibration_iff]; rw [weakEquivalence_iff]
  rfl

end TrivFib

section TrivCof

variable [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/--
Definition of `trivialCofibrations` / `trivialCofibrations` 的定义

English:
definition trivialCofibrations
  signature: : MorphismProperty C
  body: cofibrations C ⊓ weakEquivalences C

中文:
定义 trivialCofibrations
  签名: : Morphism命题erty C
  定义体: cofibrations C ⊓ weakEquivalences C

Depends on / 依赖: cofibrations, weakEquivalences
-/
def trivialCofibrations : MorphismProperty C := cofibrations C ⊓ weakEquivalences C

/--
lemma `trivialCofibrations_sub_cofibrations` / 引理 `trivialCofibrations_sub_cofibrations`

English:
lemma trivialCofibrations_sub_cofibrations
  statement: trivialCofibrations C <= cofibrations C
  proof: fun _ _ _ hf => hf.1

中文:
引理 trivialCofibrations_sub_cofibrations
  结论: trivialCofibrations C <= cofibrations C
  证明: fun _ _ _ hf => hf.1
-/
lemma trivialCofibrations_sub_cofibrations : trivialCofibrations C <= cofibrations C :=
  fun _ _ _ hf => hf.1

/--
lemma `trivialCofibrations_sub_weakEquivalences` / 引理 `trivialCofibrations_sub_weakEquivalences`

English:
lemma trivialCofibrations_sub_weakEquivalences
  statement: trivialCofibrations C <= weakEquivalences C
  proof: fun _ _ _ hf => hf.2

中文:
引理 trivialCofibrations_sub_weakEquivalences
  结论: trivialCofibrations C <= weakEquivalences C
  证明: fun _ _ _ hf => hf.2
-/
lemma trivialCofibrations_sub_weakEquivalences : trivialCofibrations C <= weakEquivalences C :=
  fun _ _ _ hf => hf.2


variable {C}

/--
lemma `mem_trivialCofibrations` / 引理 `mem_trivialCofibrations`

English:
lemma mem_trivialCofibrations
  given: [Cofibration f] [WeakEquivalence f]
  proof: ⟨mem_cofibrations f, mem_weakEquivalences f⟩

中文:
引理 mem_trivialCofibrations
  条件: [Cofibration f] [WeakEquivalence f]
  证明: ⟨mem_cofibrations f, mem_weakEquivalences f⟩

Depends on / 依赖: mem_cofibrations, mem_weakEquivalences
-/
lemma mem_trivialCofibrations [Cofibration f] [WeakEquivalence f] :
    trivialCofibrations C f :=
  ⟨mem_cofibrations f, mem_weakEquivalences f⟩

/--
lemma `mem_trivialCofibrations_iff` / 引理 `mem_trivialCofibrations_iff`

English:
lemma mem_trivialCofibrations_iff
  proof: by
  rw [cofibration_iff]; rw [weakEquivalence_iff]
  rfl

中文:
引理 mem_trivialCofibrations_iff
  证明: by
  rw [cofibration_iff]; rw [weakEquivalence_iff]
  rfl

Depends on / 依赖: cofibration_iff, weakEquivalence_iff
-/
lemma mem_trivialCofibrations_iff :
    trivialCofibrations C f ↔ Cofibration f ∧ WeakEquivalence f := by
  rw [cofibration_iff]; rw [weakEquivalence_iff]
  rfl

end TrivCof

section

variable [CategoryWithCofibrations C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithFibrations Cᵒᵖ
  body: (cofibrations C).op

中文:
实例 :
  签名: CategoryWithFibrations Cᵒᵖ
  定义体: (cofibrations C).op

Depends on / 依赖: cofibrations
-/
instance : CategoryWithFibrations Cᵒᵖ where
  fibrations := (cofibrations C).op

/--
lemma `fibrations_op` / 引理 `fibrations_op`

English:
lemma fibrations_op
  statement: fibrations Cᵒᵖ = (cofibrations C).op
  proof: rfl

中文:
引理 fibrations_op
  结论: fibrations Cᵒᵖ = (cofibrations C).op
  证明: rfl
-/
lemma fibrations_op : fibrations Cᵒᵖ = (cofibrations C).op := rfl
/--
lemma `cofibrations_eq_unop` / 引理 `cofibrations_eq_unop`

English:
lemma cofibrations_eq_unop
  statement: cofibrations C = (fibrations Cᵒᵖ).unop
  proof: rfl

中文:
引理 cofibrations_eq_unop
  结论: cofibrations C = (fibrations Cᵒᵖ).unop
  证明: rfl
-/
lemma cofibrations_eq_unop : cofibrations C = (fibrations Cᵒᵖ).unop := rfl

variable {C}

/--
lemma `fibration_op_iff` / 引理 `fibration_op_iff`

English:
lemma fibration_op_iff
  statement: Fibration f.op ↔ Cofibration f
  proof: by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]

中文:
引理 fibration_op_iff
  结论: Fibration f.op ↔ Cofibration f
  证明: by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]

Depends on / 依赖: cofibration_iff, cofibrations_eq_unop, fibration_iff
-/
lemma fibration_op_iff : Fibration f.op ↔ Cofibration f := by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]

/--
lemma `cofibration_unop_iff` / 引理 `cofibration_unop_iff`

English:
lemma cofibration_unop_iff
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]

中文:
引理 cofibration_unop_iff
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]

Depends on / 依赖: cofibration_iff, cofibrations_eq_unop, fibration_iff
-/
lemma cofibration_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Cofibration f.unop ↔ Fibration f := by
  simp [cofibration_iff, fibration_iff, cofibrations_eq_unop]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Cofibration
  signature: f] : Fibration f.op
  body: by
  rwa [fibration_op_iff]

中文:
实例 [Cofibration
  签名: f] : Fibration f.op
  定义体: by
  rwa [fibration_op_iff]

Depends on / 依赖: fibration_op_iff
-/
instance [Cofibration f] : Fibration f.op := by
  rwa [fibration_op_iff]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [Fibration f] : Cofibration f.unop := by
  rwa [cofibration_unop_iff]

end

section

variable [CategoryWithFibrations C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithCofibrations Cᵒᵖ
  body: (fibrations C).op

中文:
实例 :
  签名: CategoryWithCofibrations Cᵒᵖ
  定义体: (fibrations C).op

Depends on / 依赖: fibrations
-/
instance : CategoryWithCofibrations Cᵒᵖ where
  cofibrations := (fibrations C).op

/--
lemma `cofibrations_op` / 引理 `cofibrations_op`

English:
lemma cofibrations_op
  statement: cofibrations Cᵒᵖ = (fibrations C).op
  proof: rfl

中文:
引理 cofibrations_op
  结论: cofibrations Cᵒᵖ = (fibrations C).op
  证明: rfl
-/
lemma cofibrations_op : cofibrations Cᵒᵖ = (fibrations C).op := rfl
/--
lemma `fibrations_eq_unop` / 引理 `fibrations_eq_unop`

English:
lemma fibrations_eq_unop
  statement: fibrations C = (cofibrations Cᵒᵖ).unop
  proof: rfl

中文:
引理 fibrations_eq_unop
  结论: fibrations C = (cofibrations Cᵒᵖ).unop
  证明: rfl
-/
lemma fibrations_eq_unop : fibrations C = (cofibrations Cᵒᵖ).unop := rfl

variable {C}

/--
lemma `cofibration_op_iff` / 引理 `cofibration_op_iff`

English:
lemma cofibration_op_iff
  statement: Cofibration f.op ↔ Fibration f
  proof: by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]

中文:
引理 cofibration_op_iff
  结论: Cofibration f.op ↔ Fibration f
  证明: by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]

Depends on / 依赖: cofibration_iff, fibration_iff, fibrations_eq_unop
-/
lemma cofibration_op_iff : Cofibration f.op ↔ Fibration f := by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]

/--
lemma `fibration_unop_iff` / 引理 `fibration_unop_iff`

English:
lemma fibration_unop_iff
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]

中文:
引理 fibration_unop_iff
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]

Depends on / 依赖: cofibration_iff, fibration_iff, fibrations_eq_unop
-/
lemma fibration_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Fibration f.unop ↔ Cofibration f := by
  simp [cofibration_iff, fibration_iff, fibrations_eq_unop]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fibration
  signature: f] : Cofibration f.op
  body: by
  rwa [cofibration_op_iff]

中文:
实例 [Fibration
  签名: f] : Cofibration f.op
  定义体: by
  rwa [cofibration_op_iff]

Depends on / 依赖: cofibration_op_iff
-/
instance [Fibration f] : Cofibration f.op := by
  rwa [cofibration_op_iff]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [Cofibration f] : Fibration f.unop := by
  rwa [fibration_unop_iff]

end

section

variable [CategoryWithWeakEquivalences C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithWeakEquivalences Cᵒᵖ
  body: (weakEquivalences C).op

中文:
实例 :
  签名: CategoryWithWeakEquivalences Cᵒᵖ
  定义体: (weakEquivalences C).op

Depends on / 依赖: weakEquivalences
-/
instance : CategoryWithWeakEquivalences Cᵒᵖ where
  weakEquivalences := (weakEquivalences C).op

/--
lemma `weakEquivalences_op` / 引理 `weakEquivalences_op`

English:
lemma weakEquivalences_op
  statement: weakEquivalences Cᵒᵖ = (weakEquivalences C).op
  proof: rfl

中文:
引理 weakEquivalences_op
  结论: weakEquivalences Cᵒᵖ = (weakEquivalences C).op
  证明: rfl
-/
lemma weakEquivalences_op : weakEquivalences Cᵒᵖ = (weakEquivalences C).op := rfl
/--
lemma `weakEquivalences_eq_unop` / 引理 `weakEquivalences_eq_unop`

English:
lemma weakEquivalences_eq_unop
  statement: weakEquivalences C = (weakEquivalences Cᵒᵖ).unop
  proof: rfl

中文:
引理 weakEquivalences_eq_unop
  结论: weakEquivalences C = (weakEquivalences Cᵒᵖ).unop
  证明: rfl
-/
lemma weakEquivalences_eq_unop : weakEquivalences C = (weakEquivalences Cᵒᵖ).unop := rfl

variable {C}

/--
lemma `weakEquivalences_op_iff` / 引理 `weakEquivalences_op_iff`

English:
lemma weakEquivalences_op_iff
  statement: WeakEquivalence f.op ↔ WeakEquivalence f
  proof: by
  simp [weakEquivalence_iff, weakEquivalences_op]

中文:
引理 weakEquivalences_op_iff
  结论: WeakEquivalence f.op ↔ WeakEquivalence f
  证明: by
  simp [weakEquivalence_iff, weakEquivalences_op]

Depends on / 依赖: weakEquivalence_iff, weakEquivalences_op
-/
lemma weakEquivalences_op_iff : WeakEquivalence f.op ↔ WeakEquivalence f := by
  simp [weakEquivalence_iff, weakEquivalences_op]

/--
lemma `weakEquivalences_unop_iff` / 引理 `weakEquivalences_unop_iff`

English:
lemma weakEquivalences_unop_iff
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: (weakEquivalences_op_iff f.unop).symm

中文:
引理 weakEquivalences_unop_iff
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: (weakEquivalences_op_iff f.unop).symm

Depends on / 依赖: f.unop, weakEquivalences_op_iff
-/
lemma weakEquivalences_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    WeakEquivalence f.unop ↔ WeakEquivalence f :=
  (weakEquivalences_op_iff f.unop).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WeakEquivalence
  signature: f] : WeakEquivalence f.op
  body: by
  rwa [weakEquivalences_op_iff]

中文:
实例 [WeakEquivalence
  签名: f] : WeakEquivalence f.op
  定义体: by
  rwa [weakEquivalences_op_iff]

Depends on / 依赖: weakEquivalences_op_iff
-/
instance [WeakEquivalence f] : WeakEquivalence f.op := by
  rwa [weakEquivalences_op_iff]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.unop := by
  rwa [weakEquivalences_unop_iff]

end

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]

/--
lemma `trivialFibrations_op` / 引理 `trivialFibrations_op`

English:
lemma trivialFibrations_op
  statement: trivialFibrations Cᵒᵖ = (trivialCofibrations C).op
  proof: rfl

中文:
引理 trivialFibrations_op
  结论: trivialFibrations Cᵒᵖ = (trivialCofibrations C).op
  证明: rfl
-/
lemma trivialFibrations_op : trivialFibrations Cᵒᵖ = (trivialCofibrations C).op := rfl
/--
lemma `trivialCofibrations_eq_unop` / 引理 `trivialCofibrations_eq_unop`

English:
lemma trivialCofibrations_eq_unop
  statement: trivialCofibrations C = (trivialFibrations Cᵒᵖ).unop
  proof: rfl

中文:
引理 trivialCofibrations_eq_unop
  结论: trivialCofibrations C = (trivialFibrations Cᵒᵖ).unop
  证明: rfl
-/
lemma trivialCofibrations_eq_unop : trivialCofibrations C = (trivialFibrations Cᵒᵖ).unop := rfl

end

section

variable [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]

/--
lemma `trivialCofibrations_op` / 引理 `trivialCofibrations_op`

English:
lemma trivialCofibrations_op
  statement: trivialCofibrations Cᵒᵖ = (trivialFibrations C).op
  proof: rfl

中文:
引理 trivialCofibrations_op
  结论: trivialCofibrations Cᵒᵖ = (trivialFibrations C).op
  证明: rfl
-/
lemma trivialCofibrations_op : trivialCofibrations Cᵒᵖ = (trivialFibrations C).op := rfl
/--
lemma `trivialFibrations_eq_unop` / 引理 `trivialFibrations_eq_unop`

English:
lemma trivialFibrations_eq_unop
  statement: trivialFibrations C = (trivialCofibrations Cᵒᵖ).unop
  proof: rfl

中文:
引理 trivialFibrations_eq_unop
  结论: trivialFibrations C = (trivialCofibrations Cᵒᵖ).unop
  证明: rfl
-/
lemma trivialFibrations_eq_unop : trivialFibrations C = (trivialCofibrations Cᵒᵖ).unop := rfl

end

section ObjectProperty

variable [CategoryWithWeakEquivalences C] {P : ObjectProperty C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithWeakEquivalences P.FullSubcategory
  body: (weakEquivalences C).inverseImage P.ι

中文:
实例 :
  签名: CategoryWithWeakEquivalences P.FullSubcategory
  定义体: (weakEquivalences C).inverseImage P.ι

Depends on / 依赖: inverseImage, weakEquivalences
-/
instance : CategoryWithWeakEquivalences P.FullSubcategory where
  weakEquivalences := (weakEquivalences C).inverseImage P.ι

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(weakEquivalences
  signature: C).HasTwoOutOfThreeProperty] :
  body: inferInstanceAs ((weakEquivalences C).inverseImage P.ι).HasTwoOutOfThreeProperty

中文:
实例 [(weakEquivalences
  签名: C).HasTwoOutOfThree命题erty] :
  定义体: inferInstanceAs ((weakEquivalences C).inverseImage P.ι).HasTwoOutOfThreeProperty

Depends on / 依赖: HasTwoOutOfThreeProperty, inverseImage, weakEquivalences
-/
instance [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences P.FullSubcategory).HasTwoOutOfThreeProperty :=
  inferInstanceAs ((weakEquivalences C).inverseImage P.ι).HasTwoOutOfThreeProperty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(weakEquivalences
  signature: C).IsMultiplicative] :
  body: inferInstanceAs ((weakEquivalences C).inverseImage P.ι).IsMultiplicative

中文:
实例 [(weakEquivalences
  签名: C).IsMultiplicative] :
  定义体: inferInstanceAs ((weakEquivalences C).inverseImage P.ι).IsMultiplicative

Depends on / 依赖: IsMultiplicative, inverseImage, weakEquivalences
-/
instance [(weakEquivalences C).IsMultiplicative] :
    (weakEquivalences P.FullSubcategory).IsMultiplicative :=
  inferInstanceAs ((weakEquivalences C).inverseImage P.ι).IsMultiplicative

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(weakEquivalences
  signature: C).RespectsIso] :
  body: inferInstanceAs ((weakEquivalences C).inverseImage P.ι).RespectsIso

中文:
实例 [(weakEquivalences
  签名: C).RespectsIso] :
  定义体: inferInstanceAs ((weakEquivalences C).inverseImage P.ι).RespectsIso

Depends on / 依赖: RespectsIso, inverseImage, weakEquivalences
-/
instance [(weakEquivalences C).RespectsIso] :
    (weakEquivalences P.FullSubcategory).RespectsIso :=
  inferInstanceAs ((weakEquivalences C).inverseImage P.ι).RespectsIso

/--
lemma `weakEquivalence_iff_of_objectProperty` / 引理 `weakEquivalence_iff_of_objectProperty`

English:
lemma weakEquivalence_iff_of_objectProperty
  proof: by
  simp only [weakEquivalence_iff]
  rfl

中文:
引理 weakEquivalence_iff_of_objectProperty
  证明: by
  simp only [weakEquivalence_iff]
  rfl

Depends on / 依赖: weakEquivalence_iff
-/
lemma weakEquivalence_iff_of_objectProperty
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.hom := by
  simp only [weakEquivalence_iff]
  rfl

instance {X Y : P.FullSubcategory} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence f.hom := by
  rwa [← weakEquivalence_iff_of_objectProperty]

instance {X Y : P.FullSubcategory} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (P.ι.map f) := by
  dsimp
  infer_instance

end ObjectProperty

end HomotopicalAlgebra
