/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Robin Carlier, Christian Merten
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# Nonsingular simplicial sets

In this file, we introduce a typeclass `SSet.Nonsingular` for a
simplicial set `X : SSet`: it says that for any non-degenerate simplex
`x : X _⦋n⦌`, the corresponding morphism `Δ[n] ⟶ X` is a monomorphism.
This notion is useful in the context of the study of the subdivision
functor (TODO @joelriou).

The condition `SSet.Nonsingular` is a weaker condition compared
to the notion of "polyhedral complex" which appears in the article
*Simplicial approximation* by Jardine, and which says that there
exists a monomorphism `X ⟶ nerve T` where `T` is a partially ordered type.

## References
* [Vegard Fjellbo and John Rognes,
  *Exponentials of non-singular simplicial sets*][fjellbo-rognes-2022]
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SSet

variable {X Y : SSet.{u}}

variable (X) in
/-- A simplicial set `X` is nonsingular if for any
nondegenerate simplex `x` (of dimension `n`), the corresponding
morphism `Δ[n] ⟶ X` is a monomorphism. -/
@[kerodon 02MG]
/-
**SSet.Nonsingular** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set `X` is nonsingular if for any
nondegenerate simplex `x` (of dimension `n`), the corresponding
morphism `Δ[n] ⟶ X` is a monomorphism.
-/
class Nonsingular where
  mono {n : ℕ} (x : X.nonDegenerate n) : Mono (yonedaEquiv.symm x.val)

attribute [instance] Nonsingular.mono
/-
**SSet.Nonsingular.mono'** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Nonsingular`。
形式化陈述：∀ {X : _root_.SSet} [X.Nonsingular] {n : ℕ}, ∀ x ∈ X.nonDegenerate n, Cate
goryTheory.Mono (SSet.yonedaEquiv.symm x)
参数：SSet.yonedaEquiv.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Nonsingular.mono`：∀ {X : _root_.SSet} [self : X.Nonsingular] {n : ℕ
} (x : ↑(X.nonDegenerate n)),   CategoryTheory.Mono (SSet.yonedaEquiv.symm ↑x)
-/
lemma Nonsingular.mono' [X.Nonsingular]
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    Mono (yonedaEquiv.symm x) := mono ⟨x, hx⟩

@[kerodon 02MK]
/-
**SSet.Nonsingular.of_mono** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Nonsingular`。
形式化陈述：∀ {X Y : _root_.SSet} (f : X ⟶ Y) [CategoryTheory.Mono f] [Y.Nonsingular],
 X.Nonsingular
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `SSet.Nonsingular.mono'`：∀ {X : _root_.SSet} [X.Nonsingular] {n : ℕ}, ∀ x
 ∈ X.nonDegenerate n, CategoryTheory.Mono (SSet.yonedaEquiv.symm x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.nonDegenerate_iff_of_mono`：nonDegenerate_iff_of_mono {Y : SSet.{u}}
 (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) : f.app _ x in Y.nonDegenerate n ↔ x in X.non
Degenerate n
· 使用定理 `CategoryTheory.mono_of_mono`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)   [CategoryTheory.Mono (Catego
ryTheory.Category…
· 使用定理 `SSet.yonedaEquiv_symm_comp`：∀ {X Y : _root_.SSet} {n : SimplexCategory} 
(x : X.obj (Opposite.op n)) (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (S
Set.yonedaEquiv.…
-/
lemma Nonsingular.of_mono (f : X ⟶ Y) [Mono f] [Y.Nonsingular] :
    X.Nonsingular where
  mono := by
    intro n ⟨x, hx⟩
    rw [← nonDegenerate_iff_of_mono f] at hx
    have := mono' _ hx
    rw [← SSet.yonedaEquiv_symm_comp] at this
    exact mono_of_mono _ f
/-
**SSet.Nonsingular.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Nonsingular`。
形式化陈述：∀ {X Y : _root_.SSet} (e : X ≅ Y) [X.Nonsingular], Y.Nonsingular
参数：e : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Nonsingular.of_mono`：∀ {X Y : _root_.SSet} (f : X ⟶ Y) [CategoryThe
ory.Mono f] [Y.Nonsingular], X.Nonsingular
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma Nonsingular.of_iso (e : X ≅ Y) [X.Nonsingular] : Y.Nonsingular :=
  .of_mono e.inv
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : X.Subcomplex) [X.Nonsingular] : (A : SSet).Nonsingular :=
  .of_mono A.ι

@[kerodon 02MT]
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (T : Type*) [PartialOrder T] : (nerve T).Nonsingular where
  mono := by
    intro n ⟨x, hx⟩
    rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective] at hx
    simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
    intro ⟨⟨k⟩⟩ i j hij
    ext l : 1
    exact hx (Functor.congr_obj hij l)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).Nonsingular :=
  Nonsingular.of_iso (stdSimplex.isoNerve _).symm
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n m : SimplexCategory) :
    (stdSimplex.{u}.obj n ⊗ stdSimplex.obj m).Nonsingular :=
  Nonsingular.of_iso (prodStdSimplex.isoNerve _ _).symm

@[kerodon 02MH]
/-
**SSet.nonDegenerate_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonDegenerate_δ [X.Nonsingular]
    {n : ℕ} {x : X _⦋n + 1⦌} (hx : x ∈ X.nonDegenerate _) (i : Fin (n + 2)) :
    X.δ i x ∈ X.nonDegenerate _ := by
  have := Nonsingular.mono' x hx
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this, nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
    Equiv.apply_symm_apply]
  infer_instance
/-
**SSet.Nonsingular.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nonsingular.δ_injective [X.Nonsingular]
    {n : ℕ} (x : X _⦋n + 1⦌) (hx : x ∈ X.nonDegenerate _)
    (i j : Fin (n + 2)) (hij : X.δ i x = X.δ j x) : i = j := by
  apply SimplexCategory.δ_injective
  apply stdSimplex.objEquiv.symm.injective
  have := mono' x hx
  exact injective_of_mono ((yonedaEquiv.symm x).app _) hij
/-
**SSet.Nonsingular.injective_map** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Nonsingular`。
形式化陈述：∀ {X : _root_.SSet} [X.Nonsingular] {n : ℕ},   ∀ x ∈ X.nonDegenerate n,   
  ∀ {m : SimplexCategory} {f g : m ⟶ { len := n }},       (CategoryTheory.Concre
teCategory.hom (X.map f.op)) x = (CategoryTheory.ConcreteCategory.hom (X.map g.o
p)) x →         f = g
参数：CategoryTheory.ConcreteCategory.hom (X.map f.op)；CategoryTheory.ConcreteCateg
ory.hom (X.map g.op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `SSet.Nonsingular.mono'`：∀ {X : _root_.SSet} [X.Nonsingular] {n : ℕ}, ∀ x
 ∈ X.nonDegenerate n, CategoryTheory.Mono (SSet.yonedaEquiv.symm x)
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `SSet.stdSimplex.instFaithfulSimplexCategory`：CategoryTheory.Functor.Fait
hful SSet.stdSimplex
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SSet.yonedaEquiv_map`：yonedaEquiv_map {n m : SimplexCategory} (f : n ⟶ m
) : yonedaEquiv.{u} (stdSimplex.map f) = stdSimplex.objEquiv.symm f
-/
lemma Nonsingular.injective_map
    [X.Nonsingular] {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
    {m : SimplexCategory} {f g : m ⟶ ⦋n⦌}
    (h : X.map f.op x = X.map g.op x) :
    f = g := by
  have := Nonsingular.mono' x hx
  apply stdSimplex.{u}.map_injective
  rw [← cancel_mono (yonedaEquiv.symm x)]
  apply yonedaEquiv.injective
  simpa [yonedaEquiv_comp, yonedaEquiv_map]
/-
**SSet.Nonsingular.isIso_toOfSimplex** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Nonsingular
`。
形式化陈述：∀ {X : _root_.SSet} [X.Nonsingular] {n : ℕ},   ∀ x ∈ X.nonDegenerate n, Ca
tegoryTheory.IsIso (SSet.Subcomplex.toOfSimplex x)
参数：SSet.Subcomplex.toOfSimplex x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.isIso_toOfSimplex_iff`：isIso_toOfSimplex_iff : IsIso (to
OfSimplex x) ↔ Mono (yonedaEquiv.symm x)
· 使用定理 `SSet.Nonsingular.mono'`：∀ {X : _root_.SSet} [X.Nonsingular] {n : ℕ}, ∀ x
 ∈ X.nonDegenerate n, CategoryTheory.Mono (SSet.yonedaEquiv.symm x)
-/
lemma Nonsingular.isIso_toOfSimplex [X.Nonsingular]
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    IsIso (Subcomplex.toOfSimplex x) := by
  rw [Subcomplex.isIso_toOfSimplex_iff]
  exact Nonsingular.mono' x hx

/-- If `x : X _⦋n⦌` is a nondegenerate simplex of a nonsingular simplicial set,
this is the isomorphism `Δ[n] ≅ Subcomplex.ofSimplex x` induced by `x`. -/
@[expose, simps! hom]
/-
**SSet.Nonsingular.iso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Nonsingular`。
形式化陈述：{X : _root_.SSet} →   [X.Nonsingular] →     {n : ℕ} →       (x : X.obj (Op
posite.op { len := n })) →         x ∈ X.nonDegenerate n → (SSet.stdSimplex.obj 
{ len := n } ≅ (SSet.Subcomplex.ofSimplex x).toSSet)
参数：x : X.obj (Opposite.op { len := n })；SSet.stdSimplex.obj { len := n } ≅ (SSet
.Subcomplex.ofSimplex x).toSSet。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Nonsingular.isIso_toOfSimplex`：∀ {X : _root_.SSet} [X.Nonsingular] 
{n : ℕ},   ∀ x ∈ X.nonDegenerate n, CategoryTheory.IsIso (SSet.Subcomplex.toOfSi
mplex x)

--- 原说明 ---
If `x : X _⦋n⦌` is a nondegenerate simplex of a nonsingular simplicial set,
this is the isomorphism `Δ[n] ≅ Subcomplex.ofSimplex x` induced by `x`.
-/
noncomputable def Nonsingular.iso
    [X.Nonsingular] {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    Δ[n] ≅ Subcomplex.ofSimplex x :=
  letI := Nonsingular.isIso_toOfSimplex x hx
  asIso (Subcomplex.toOfSimplex x)

namespace N

variable [X.Nonsingular] {x y z : X.N} (h : x ≤ y)

include h in
/-
**SSet.N.existsUnique_of_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：existsUnique_of_le : exists! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op 
y.1.2 = x.1.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SSet.N.le_iff_exists_mono`：le_iff_exists_mono {x y : X.N} : x <= y ↔ exi
sts (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (_ : Mono f), X.map f.op y.simplex = x.simplex
· 使用定理 `SSet.Nonsingular.injective_map`：∀ {X : _root_.SSet} [X.Nonsingular] {n :
 ℕ},   ∀ x ∈ X.nonDegenerate n,     ∀ {m : SimplexCategory} {f g : m ⟶ { len := 
n }},       (Categor…
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma existsUnique_of_le :
    ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.1.2 = x.1.2 :=
  existsUnique_of_exists_of_unique (by
    obtain ⟨f, _, hf⟩ := le_iff_exists_mono.1 h
    exact ⟨f, inferInstance, hf⟩) (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ ↦ by
    exact Nonsingular.injective_map _ y.nonDegenerate (by rw [hf₁, hf₂]))

/-- Given an inequality `x ≤ y` between nondegenerate simplices of a
nonsingular simplicial set `X`, this is the corresponding morphism
`⦋x.dim⦌ ⟶ ⦋y.dim⦌` in the simplex category. -/
/-
**SSet.N.monoOfLE** 是 Mathlib 中的一个定义，位于命名空间 `SSet.N`。
形式化陈述：monoOfLE : ⦋x.dim⦌ ⟶ ⦋y.dim⦌
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an inequality `x ≤ y` between nondegenerate simplices of a
nonsingular simplicial set `X`, this is the corresponding morphism
`⦋x.dim⦌ ⟶ ⦋y.dim⦌` in the simplex category.
-/
noncomputable def monoOfLE : ⦋x.dim⦌ ⟶ ⦋y.dim⦌ :=
  (existsUnique_of_le h).exists.choose
/-
**SSet.N.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.N`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (monoOfLE h) :=
  (existsUnique_of_le h).exists.choose_spec.1

@[simp]
/-
**SSet.N.map_monoOfLE** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：map_monoOfLE : X.map (monoOfLE h).op y.simplex = x.simplex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用引理 `SSet.N.existsUnique_of_le`：existsUnique_of_le : exists! (f : ⦋x.dim⦌ ⟶ ⦋
y.dim⦌), Mono f ∧ X.map f.op y.1.2 = x.1.2
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma map_monoOfLE : X.map (monoOfLE h).op y.simplex = x.simplex :=
  (existsUnique_of_le h).exists.choose_spec.2

@[reassoc, simp]
/-
**SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex** 是 Mathlib 中的一个引理，位于命
名空间 `SSet.N`。
形式化陈述：stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex : stdSimplex.map (monoOfL
E h) ≫ yonedaEquiv.symm y.simplex = yonedaEquiv.symm x.simplex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.yonedaEquiv_symm_naturality_left`：yonedaEquiv_symm_naturality_left 
{X : SSet} {m n : SimplexCategory} (f : m ⟶ n) (g : X.obj (Opposite.op n)) : std
Simplex.map f ≫ yonedaEquiv…
· 使用引理 `SSet.N.map_monoOfLE`：map_monoOfLE : X.map (monoOfLE h).op y.simplex = x.
simplex
-/
lemma stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex :
    stdSimplex.map (monoOfLE h) ≫ yonedaEquiv.symm y.simplex =
      yonedaEquiv.symm x.simplex := by
  rw [yonedaEquiv_symm_naturality_left, map_monoOfLE]
/-
**SSet.N.monoOfLE_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：monoOfLE_eq_iff (h : x <= y) (g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Mono g] : monoOfLE h
 = g ↔ X.map g.op y.simplex = x.simplex
参数：h : x <= y；g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.N.map_monoOfLE`：map_monoOfLE : X.map (monoOfLE h).op y.simplex = x.
simplex
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用引理 `SSet.N.existsUnique_of_le`：existsUnique_of_le : exists! (f : ⦋x.dim⦌ ⟶ ⦋
y.dim⦌), Mono f ∧ X.map f.op y.1.2 = x.1.2
· 使用定理 `SSet.N.instMonoSimplexCategoryMonoOfLE`：∀ {X : _root_.SSet} [inst : X.No
nsingular] {x y : X.N} (h : x ≤ y), CategoryTheory.Mono (SSet.N.monoOfLE h)
-/
lemma monoOfLE_eq_iff (h : x ≤ y) (g : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Mono g] :
    monoOfLE h = g ↔ X.map g.op y.simplex = x.simplex :=
  ⟨by rintro rfl; simp,
    fun h' ↦ (existsUnique_of_le h).unique ⟨inferInstance, by simp⟩ ⟨inferInstance, h'⟩⟩

variable (x) in
@[simp]
/-
**SSet.N.monoOfLE_refl** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：monoOfLE_refl : monoOfLE (le_refl x) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monoOfLE_refl : monoOfLE (le_refl x) = 𝟙 _ := by
  simp [monoOfLE_eq_iff]

@[reassoc (attr := simp)]
/-
**SSet.N.monoOfLE_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet.N`。
形式化陈述：monoOfLE_comp (h' : y <= z) : monoOfLE h ≫ monoOfLE h' = monoOfLE (h.trans
 h')
参数：h' : y <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `SSet.N.instMonoSimplexCategoryMonoOfLE`：∀ {X : _root_.SSet} [inst : X.No
nsingular] {x y : X.N} (h : x ≤ y), CategoryTheory.Mono (SSet.N.monoOfLE h)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用引理 `SSet.N.map_monoOfLE`：map_monoOfLE : X.map (monoOfLE h).op y.simplex = x.
simplex
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monoOfLE_comp (h' : y ≤ z) :
    monoOfLE h ≫ monoOfLE h' = monoOfLE (h.trans h') := by
  symm
  simp [monoOfLE_eq_iff]

end N

end SSet

