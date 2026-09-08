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

/-- The objects of the free simplex quiver are the natural numbers. -/
/-
**FreeSimplexQuiver** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FreeSimplexQuiver
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The objects of the free simplex quiver are the natural numbers.
-/
def FreeSimplexQuiver := ℕ

/-- Making an object of `FreeSimplexQuiver` out of a natural number. -/
/-
**FreeSimplexQuiver.mk** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FreeSimplexQuiver.mk (n : Nat) : FreeSimplexQuiver
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Making an object of `FreeSimplexQuiver` out of a natural number.
-/
def FreeSimplexQuiver.mk (n : ℕ) : FreeSimplexQuiver := n

/-- Getting back the natural number from the objects. -/
/-
**FreeSimplexQuiver.len** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FreeSimplexQuiver.len (x : FreeSimplexQuiver) : Nat
参数：x : FreeSimplexQuiver。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Getting back the natural number from the objects.
-/
def FreeSimplexQuiver.len (x : FreeSimplexQuiver) : ℕ := x

namespace FreeSimplexQuiver

/-- A morphism in `FreeSimplexQuiver` is either a face map (`δ`) or a degeneracy map (`σ`). -/
/-
**FreeSimplexQuiver.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `FreeSimplexQuiver`。
形式化陈述：FreeSimplexQuiver → FreeSimplexQuiver → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `FreeSimplexQuiver` is either a face map (`δ`) or a degeneracy map
 (`σ`).
-/
inductive Hom : FreeSimplexQuiver → FreeSimplexQuiver → Type
  | δ {n : ℕ} (i : Fin (n + 2)) : Hom (.mk n) (.mk (n + 1))
  | σ {n : ℕ} (i : Fin (n + 1)) : Hom (.mk (n + 1)) (.mk n)
/-
**FreeSimplexQuiver.quiv** 是 Mathlib 中的一个实例，位于命名空间 `FreeSimplexQuiver`。
形式化陈述：quiv : Quiver FreeSimplexQuiver where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance quiv : Quiver FreeSimplexQuiver where
  Hom := FreeSimplexQuiver.Hom

/-- `FreeSimplexQuiver.δ i` represents the `i`-th face map `.mk n ⟶ .mk (n + 1)`. -/
/-
**FreeSimplexQuiver.** 是 Mathlib 中的一个缩写定义，位于命名空间 `FreeSimplexQuiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FreeSimplexQuiver.δ i` represents the `i`-th face map `.mk n ⟶ .mk (n + 1)`.
-/
abbrev δ {n : ℕ} (i : Fin (n + 2)) : FreeSimplexQuiver.mk n ⟶ .mk (n + 1) :=
  FreeSimplexQuiver.Hom.δ i

/-- `FreeSimplexQuiver.σ i` represents `i`-th degeneracy map `.mk (n + 1) ⟶ .mk n`. -/
/-
**FreeSimplexQuiver.** 是 Mathlib 中的一个缩写定义，位于命名空间 `FreeSimplexQuiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FreeSimplexQuiver.σ i` represents `i`-th degeneracy map `.mk (n + 1) ⟶ .mk n`.
-/
abbrev σ {n : ℕ} (i : Fin (n + 1)) : FreeSimplexQuiver.mk (n + 1) ⟶ .mk n :=
  FreeSimplexQuiver.Hom.σ i

/-- `FreeSimplexQuiver.homRel` is the relation on morphisms freely generated on the
five simplicial identities. -/
/-
**FreeSimplexQuiver.homRel** 是 Mathlib 中的一个归纳类型，位于命名空间 `FreeSimplexQuiver`。
形式化陈述：HomRel (CategoryTheory.Paths FreeSimplexQuiver)
参数：CategoryTheory.Paths FreeSimplexQuiver。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FreeSimplexQuiver.homRel` is the relation on morphisms freely generated on the
five simplicial identities.
-/
inductive homRel : HomRel (Paths FreeSimplexQuiver)
  | δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i) ≫ (Paths.of FreeSimplexQuiver).map (δ j.succ))
    ((Paths.of FreeSimplexQuiver).map (δ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i.castSucc))
  | δ_comp_σ_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j.succ))
    ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
  | δ_comp_σ_self {n : ℕ} {i : Fin (n + 1)} : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
  | δ_comp_σ_succ {n : ℕ} {i : Fin (n + 1)} : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
  | δ_comp_σ_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ j.castSucc))
    ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
  | σ_comp_σ {n : ℕ} {i j : Fin (n + 1)} (H : i ≤ j) : homRel
    ((Paths.of FreeSimplexQuiver).map (σ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j))
    ((Paths.of FreeSimplexQuiver).map (σ j.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i))

end FreeSimplexQuiver

/-- SimplexCategory is the category presented by generators and relation by the simplicial
identities. -/
/-
**SimplexCategoryGenRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SimplexCategoryGenRel
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
SimplexCategory is the category presented by generators and relation by the simp
licial
identities.
-/
def SimplexCategoryGenRel := Quotient FreeSimplexQuiver.homRel
  deriving Category

/-- `SimplexCategoryGenRel.mk` is the main constructor for objects of `SimplexCategoryGenRel`. -/
/-
**SimplexCategoryGenRel.mk** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SimplexCategoryGenRel.mk (n : Nat) : SimplexCategoryGenRel where as
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SimplexCategoryGenRel.mk` is the main constructor for objects of `SimplexCatego
ryGenRel`.
-/
def SimplexCategoryGenRel.mk (n : ℕ) : SimplexCategoryGenRel where
  as := (Paths.of FreeSimplexQuiver).obj n

namespace SimplexCategoryGenRel

/-- `SimplexCategoryGenRel.δ i` is the `i`-th face map `.mk n ⟶ .mk (n + 1)`. -/
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SimplexCategoryGenRel.δ i` is the `i`-th face map `.mk n ⟶ .mk (n + 1)`.
-/
abbrev δ {n : ℕ} (i : Fin (n + 2)) : mk n ⟶ mk (n + 1) :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| (Paths.of FreeSimplexQuiver).map (.δ i)

/-- `SimplexCategoryGenRel.σ i` is the `i`-th degeneracy map `.mk (n + 1) ⟶ .mk n`. -/
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SimplexCategoryGenRel.σ i` is the `i`-th degeneracy map `.mk (n + 1) ⟶ .mk n`.
-/
abbrev σ {n : ℕ} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk n :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| (Paths.of FreeSimplexQuiver).map (.σ i)

/-- The length of an object of `SimplexCategoryGenRel`. -/
/-
**SimplexCategoryGenRel.len** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategoryGenRel`。
形式化陈述：len (x : SimplexCategoryGenRel) : Nat
参数：x : SimplexCategoryGenRel。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of an object of `SimplexCategoryGenRel`.
-/
def len (x : SimplexCategoryGenRel) : ℕ := by rcases x with ⟨n⟩; exact n

@[simp]
/-
**SimplexCategoryGenRel.mk_len** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGenRel`
。
形式化陈述：mk_len (n : Nat) : len (mk n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_len (n : ℕ) : len (mk n) = n := rfl

section InductionPrinciples

/-- A morphism is called a face if it is a `δ i` for some `i : Fin (n + 2)`. -/
/-
**SimplexCategoryGenRel.faces** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimplexCategoryGenRel
`。
形式化陈述：CategoryTheory.MorphismProperty SimplexCategoryGenRel
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is called a face if it is a `δ i` for some `i : Fin (n + 2)`.
-/
inductive faces : MorphismProperty SimplexCategoryGenRel
  | δ {n : ℕ} (i : Fin (n + 2)) : faces (δ i)

/-- A morphism is called a degeneracy if it is a `σ i` for some `i : Fin (n + 1)`. -/
/-
**SimplexCategoryGenRel.degeneracies** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimplexCategor
yGenRel`。
形式化陈述：CategoryTheory.MorphismProperty SimplexCategoryGenRel
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is called a degeneracy if it is a `σ i` for some `i : Fin (n + 1)`.
-/
inductive degeneracies : MorphismProperty SimplexCategoryGenRel
  | σ {n : ℕ} (i : Fin (n + 1)) : degeneracies (σ i)

/-- A morphism is a generator if it is either a face or a degeneracy. -/
/-
**SimplexCategoryGenRel.generators** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategoryG
enRel`。
形式化陈述：generators
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is a generator if it is either a face or a degeneracy.
-/
abbrev generators := faces ⊔ degeneracies

namespace generators

/-
**SimplexCategoryGenRel.generators.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGe
nRel.generators`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ {n : ℕ} (i : Fin (n + 2)) : generators (δ i) := le_sup_left (a := faces) _ (.δ i)
/-
**SimplexCategoryGenRel.generators.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGe
nRel.generators`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ {n : ℕ} (i : Fin (n + 1)) : generators (σ i) := le_sup_right (a := faces) _ (.σ i)

end generators

/-- A property is true for every morphism iff it holds for generators and is multiplicative. -/
/-
**SimplexCategoryGenRel.multiplicativeClosure_isGenerator_eq_top** 是 Mathlib 中的一
个引理，位于命名空间 `SimplexCategoryGenRel`。
形式化陈述：multiplicativeClosure_isGenerator_eq_top : generators.multiplicativeClosur
e = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Quotient.induction`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] (r : HomRel C)   {P : {a b : CategoryTheory.Quotient r
} → (a ⟶ b) → Prop},   …
· 使用引理 `CategoryTheory.Paths.induction`：induction (P : forall {a b : Paths V}, (
a ⟶ b) -> Prop) (id : forall {v : V}, P (𝟙 ((of V).obj v))) (comp : forall {u v 
w : V} (p : (of V).o…
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.instIsMultiplicativeMultiplicativeClosur
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.
MorphismProperty C),   W.multiplicativeClosure.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用引理 `SimplexCategoryGenRel.generators.δ`：δ {n : Nat} (i : Fin (n + 2)) : gene
rators (δ i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `SimplexCategoryGenRel.generators.σ`：σ {n : Nat} (i : Fin (n + 1)) : gene
rators (σ i)

--- 原说明 ---
A property is true for every morphism iff it holds for generators and is multipl
icative.
-/
lemma multiplicativeClosure_isGenerator_eq_top : generators.multiplicativeClosure = ⊤ := by
  apply le_antisymm (by simp)
  rintro x y f -
  induction f using CategoryTheory.Quotient.induction with | _ f
  induction f using Paths.induction with
  | id => exact generators.multiplicativeClosure.id_mem _
  | comp _ k h =>
    cases k
    · exact generators.multiplicativeClosure.comp_mem _ _ h <| .of _ <| .δ _
    · exact generators.multiplicativeClosure.comp_mem _ _ h <| .of _ <| .σ _

/-- An unrolled version of the induction principle obtained in the previous lemma. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**SimplexCategoryGenRel.hom_induction** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory
GenRel`。
形式化陈述：hom_induction (P : MorphismProperty SimplexCategoryGenRel) (id : forall {n
 : Nat}, P (𝟙 (mk n))) (comp_δ : forall {n m : Nat} (u : mk n ⟶ mk m) (i : Fin (
m + 2)), P u -> P (u ≫ δ i)) (comp_σ : forall {n m : Nat} (u : mk n ⟶ mk (m + 1)
) (i : Fin (m + 1)), P u -> P (u ≫ σ i)) {a b : SimplexCategoryGenRel} (f : a ⟶ 
b) : P f
参数：P : MorphismProperty SimplexCategoryGenRel；id : forall {n : Nat}, P (𝟙 (mk n)
)；comp_δ : forall {n m : Nat} (u : mk n ⟶ mk m) (i : Fin (m + 2)), P u -> P (u ≫
 δ i)；comp_σ : forall {n m : Nat} (u : mk n ⟶ mk (m + 1)) (i : Fin (m + 1)), P u
 -> P (u ≫ σ i)；f : a ⟶ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `SimplexCategoryGenRel.multiplicativeClosure_isGenerator_eq_top`：multipli
cativeClosure_isGenerator_eq_top : generators.multiplicativeClosure = ⊤
· 使用引理 `CategoryTheory.MorphismProperty.top_apply`：top_apply {X Y : C} (f : X ⟶ 
Y) : (⊤ : MorphismProperty C) f

--- 原说明 ---
An unrolled version of the induction principle obtained in the previous lemma.
-/
lemma hom_induction (P : MorphismProperty SimplexCategoryGenRel)
    (id : ∀ {n : ℕ}, P (𝟙 (mk n)))
    (comp_δ : ∀ {n m : ℕ} (u : mk n ⟶ mk m) (i : Fin (m + 2)), P u → P (u ≫ δ i))
    (comp_σ : ∀ {n m : ℕ} (u : mk n ⟶ mk (m + 1)) (i : Fin (m + 1)), P u → P (u ≫ σ i))
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) : P f := by
  suffices generators.multiplicativeClosure ≤ P by
    rw [multiplicativeClosure_isGenerator_eq_top, top_le_iff] at this
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

/-- An induction principle for reasoning about morphisms in SimplexCategoryGenRel, where we compose
with generators on the right. -/
/-
**SimplexCategoryGenRel.hom_induction'** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategor
yGenRel`。
形式化陈述：hom_induction' (P : MorphismProperty SimplexCategoryGenRel) (id : forall {
n : Nat}, P (𝟙 (mk n))) (δ_comp : forall {n m : Nat} (u : mk (m + 1) ⟶ mk n) (i 
: Fin (m + 2)), P u -> P (δ i ≫ u)) (σ_comp : forall {n m : Nat} (u : mk m ⟶ mk 
n) (i : Fin (m + 1)), P u -> P (σ i ≫ u)) {a b : SimplexCategoryGenRel} (f : a ⟶
 b) : P f
参数：P : MorphismProperty SimplexCategoryGenRel；id : forall {n : Nat}, P (𝟙 (mk n)
)；δ_comp : forall {n m : Nat} (u : mk (m + 1) ⟶ mk n) (i : Fin (m + 2)), P u -> 
P (δ i ≫ u)；σ_comp : forall {n m : Nat} (u : mk m ⟶ mk n) (i : Fin (m + 1)), P u
 -> P (σ i ≫ u)；f : a ⟶ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `SimplexCategoryGenRel.multiplicativeClosure_isGenerator_eq_top`：multipli
cativeClosure_isGenerator_eq_top : generators.multiplicativeClosure = ⊤
· 使用引理 `CategoryTheory.MorphismProperty.multiplicativeClosure_eq_multiplicativeC
losure'`：multiplicativeClosure_eq_multiplicativeClosure' : W.multiplicativeClosu
re = W.multiplicativeClosure'
· 使用引理 `CategoryTheory.MorphismProperty.top_apply`：top_apply {X Y : C} (f : X ⟶ 
Y) : (⊤ : MorphismProperty C) f

--- 原说明 ---
An induction principle for reasoning about morphisms in SimplexCategoryGenRel, w
here we compose
with generators on the right.
-/
lemma hom_induction' (P : MorphismProperty SimplexCategoryGenRel)
    (id : ∀ {n : ℕ}, P (𝟙 (mk n)))
    (δ_comp : ∀ {n m : ℕ} (u : mk (m + 1) ⟶ mk n)
      (i : Fin (m + 2)), P u → P (δ i ≫ u))
    (σ_comp : ∀ {n m : ℕ} (u : mk m ⟶ mk n)
      (i : Fin (m + 1)), P u → P (σ i ≫ u)) {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    P f := by
  suffices generators.multiplicativeClosure' ≤ P by
    rw [← MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure',
      multiplicativeClosure_isGenerator_eq_top, top_le_iff] at this
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
/-
**SimplexCategoryGenRel.rec** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategoryGenRel`。
形式化陈述：{P : SimplexCategoryGenRel → Sort u_1} → ((n : ℕ) → P (SimplexCategoryGenR
el.mk n)) → (x : SimplexCategoryGenRel) → P x
参数：(n : ℕ) → P (SimplexCategoryGenRel.mk n)；x : SimplexCategoryGenRel。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An induction principle for reasoning about objects in `SimplexCategoryGenRel`. T
his should be
used instead of identifying an object with `mk` of its `len`.
-/
protected def rec {P : SimplexCategoryGenRel → Sort*}
    (H : ∀ n : ℕ, P (.mk n)) :
    ∀ x : SimplexCategoryGenRel, P x := by
  intro x
  exact H x.len

/-- A basic `ext` lemma for objects of `SimplexCategoryGenRel`. -/
@[ext]
/-
**SimplexCategoryGenRel.ext** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGenRel`。
形式化陈述：ext {x y : SimplexCategoryGenRel} (h : x.len = y.len) : x = y
参数：h : x.len = y.len。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A basic `ext` lemma for objects of `SimplexCategoryGenRel`.
-/
lemma ext {x y : SimplexCategoryGenRel} (h : x.len = y.len) : x = y := by
  cases x
  cases y
  simp only [mk_len] at h
  congr

end InductionPrinciples

section SimplicialIdentities

@[reassoc]
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_δ H

@[reassoc]
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) :
    δ i.castSucc ≫ σ j.succ = σ j ≫ δ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_le H

@[reassoc]
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ i.castSucc ≫ σ i = 𝟙 (mk n) := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_self

@[reassoc]
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 (mk n) := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_succ

@[reassoc]
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) :
    δ i.succ ≫ σ j.castSucc = σ j ≫ δ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.δ_comp_σ_of_gt H

@[reassoc]
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ i.castSucc ≫ σ j = σ j.succ ≫ σ i := by
  apply CategoryTheory.Quotient.sound
  exact FreeSimplexQuiver.homRel.σ_comp_σ H

/-- A version of δ_comp_δ with indices in ℕ satisfying relevant inequalities. -/
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of δ_comp_δ with indices in ℕ satisfying relevant inequalities.
-/
lemma δ_comp_δ_nat {n} (i j : ℕ) (hi : i < n + 2) (hj : j < n + 2) (H : i ≤ j) :
    δ ⟨i, hi⟩ ≫ δ ⟨j + 1, by lia⟩ = δ ⟨j, hj⟩ ≫ δ ⟨i, by lia⟩ :=
  δ_comp_δ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)

/-- A version of σ_comp_σ with indices in ℕ satisfying relevant inequalities. -/
/-
**SimplexCategoryGenRel.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of σ_comp_σ with indices in ℕ satisfying relevant inequalities.
-/
lemma σ_comp_σ_nat {n} (i j : ℕ) (hi : i < n + 1) (hj : j < n + 1) (H : i ≤ j) :
    σ ⟨i, by lia⟩ ≫ σ ⟨j, hj⟩ = σ ⟨j + 1, by lia⟩ ≫ σ ⟨i, hi⟩ :=
  σ_comp_σ (n := n) (i := ⟨i, by lia⟩) (j := ⟨j, by lia⟩) (by simpa)

end SimplicialIdentities

/-- The canonical functor from `SimplexCategoryGenRel` to SimplexCategory, which exists as the
simplicial identities hold in `SimplexCategory`. -/
/-
**SimplexCategoryGenRel.toSimplexCategory** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCate
goryGenRel`。
形式化陈述：toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor from `SimplexCategoryGenRel` to SimplexCategory, which exi
sts as the
simplicial identities hold in `SimplexCategory`.
-/
def toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory :=
  CategoryTheory.Quotient.lift _
    (Paths.lift
      { obj := .mk
        map f := match f with
          | FreeSimplexQuiver.Hom.δ i => SimplexCategory.δ i
          | FreeSimplexQuiver.Hom.σ i => SimplexCategory.σ i })
    (fun _ _ _ _ h ↦ match h with
      | .δ_comp_δ H => SimplexCategory.δ_comp_δ H
      | .δ_comp_σ_of_le H => SimplexCategory.δ_comp_σ_of_le H
      | .δ_comp_σ_self => SimplexCategory.δ_comp_σ_self
      | .δ_comp_σ_succ => SimplexCategory.δ_comp_σ_succ
      | .δ_comp_σ_of_gt H => SimplexCategory.δ_comp_σ_of_gt H
      | .σ_comp_σ H => SimplexCategory.σ_comp_σ H)

@[simp]
/-
**SimplexCategoryGenRel.toSimplexCategory_obj_mk** 是 Mathlib 中的一个引理，位于命名空间 `Simp
lexCategoryGenRel`。
形式化陈述：toSimplexCategory_obj_mk (n : Nat) : toSimplexCategory.obj (mk n) = .mk n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSimplexCategory_obj_mk (n : ℕ) : toSimplexCategory.obj (mk n) = .mk n := rfl

@[simp]
/-
**SimplexCategoryGenRel.toSimplexCategory_map_** 是 Mathlib 中的一个引理，位于命名空间 `Simple
xCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSimplexCategory_map_δ {n : ℕ} (i : Fin (n + 2)) :
    toSimplexCategory.map (δ i) = SimplexCategory.δ i := rfl

@[simp]
/-
**SimplexCategoryGenRel.toSimplexCategory_map_** 是 Mathlib 中的一个引理，位于命名空间 `Simple
xCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSimplexCategory_map_σ {n : ℕ} (i : Fin (n + 1)) :
    toSimplexCategory.map (σ i) = SimplexCategory.σ i := rfl

@[simp]
/-
**SimplexCategoryGenRel.toSimplexCategory_len** 是 Mathlib 中的一个引理，位于命名空间 `Simplex
CategoryGenRel`。
形式化陈述：toSimplexCategory_len {x : SimplexCategoryGenRel} : (toSimplexCategory.obj
 x).len = x.len
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSimplexCategory_len {x : SimplexCategoryGenRel} : (toSimplexCategory.obj x).len = x.len :=
  rfl

end SimplexCategoryGenRel

