/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Kan complexes

In this file, the abbreviation `KanComplex` is introduced for
fibrant objects in the category `SSet` which is equipped with
Kan fibrations.

In `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean`
we show that every Kan complex is a quasicategory.

## TODO

- Show that the singular simplicial set of a topological space is a Kan complex.

-/

public section

universe u

namespace SSet

open CategoryTheory Simplicial Limits HomotopicalAlgebra

open modelCategoryQuillen in
/-- A simplicial set `S` is a Kan complex if it is fibrant, which means that
the projection `S ⟶ ⊤_ _` has the right lifting property with respect to horn inclusions. -/
/-
**SSet.KanComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：KanComplex (S : SSet.{u}) : Prop
参数：S : SSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set `S` is a Kan complex if it is fibrant, which means that
the projection `S ⟶ ⊤_ _` has the right lifting property with respect to horn in
clusions.
-/
abbrev KanComplex (S : SSet.{u}) : Prop := HomotopicalAlgebra.IsFibrant S

/-- A Kan complex `S` satisfies the following horn-filling condition:
for every nonzero `n : ℕ` and `0 ≤ i ≤ n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`. -/
/-
**SSet.KanComplex.hornFilling** 是 Mathlib 中的一个定理，位于命名空间 `SSet.KanComplex`。
形式化陈述：∀ {S : _root_.SSet} [S.KanComplex] {n : ℕ} {i : Fin (n + 2)} (σ₀ : (SSet.h
orn (n + 1) i).toSSet ⟶ S),   ∃ σ, σ₀ = CategoryTheory.CategoryStruct.comp (SSet
.horn (n + 1) i).ι σ
参数：n + 2；σ₀ : (SSet.horn (n + 1) i).toSSet ⟶ S；SSet.horn (n + 1) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `SSet.modelCategoryQuillen.instHasLiftingPropertyιHornHAddNatOfNatOfFibra
tion`：∀ {X Y : _root_.SSet} (f : X ⟶ Y) [hf : HomotopicalAlgebra.Fibration f] {n
 : ℕ} (i : Fin (n + 2)),   CategoryTheory.HasLiftingProperty (SSet…
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f

--- 原说明 ---
A Kan complex `S` satisfies the following horn-filling condition:
for every nonzero `n : ℕ` and `0 ≤ i ≤ n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[
n] → S`.
-/
lemma KanComplex.hornFilling {S : SSet.{u}} [KanComplex S]
    {n : ℕ} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ S) :
    ∃ σ : Δ[n + 1] ⟶ S, σ₀ = Λ[n + 1, i].ι ≫ σ := by
  have sq' : CommSq σ₀ Λ[n + 1, i].ι (terminal.from S) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq'.lift, by simp⟩

namespace horn.IsCompatible

variable {X : SSet.{u}} {n : ℕ}
  {i : Fin (n + 2)} {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X}

/-
**SSet.horn.IsCompatible.exists_lift_of_kanComplex** 是 Mathlib 中的一个引理，位于命名空间 `SS
et.horn.IsCompatible`。
形式化陈述：exists_lift_of_kanComplex [KanComplex X] (hf : horn.IsCompatible f) : exis
ts (φ : Δ[n + 1] ⟶ X), forall (j : Fin (n + 2)) (hj : j != i), stdSimplex.δ j ≫ 
φ = f j hj
参数：hf : horn.IsCompatible f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `SSet.horn.IsCompatible.exists_lift`：exists_lift : exists (φ : Δ[n + 1] ⟶
 X), (forall (j : Fin (n + 2)) (hj : j != i), stdSimplex.δ j ≫ φ = f j hj) ∧ φ ≫
 p = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma exists_lift_of_kanComplex [KanComplex X]
    (hf : horn.IsCompatible f) :
    ∃ (φ : Δ[n + 1] ⟶ X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  obtain ⟨φ, hφ, _⟩ := hf.exists_lift (terminal.from _) (terminal.from _) (by simp)
  exact ⟨φ, hφ⟩

/-- If `X` is a Kan complex and `f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X`
is a compatible family of morphisms (which defines a morphism `Λ[n + 1, i] ⟶ X`),
then this is a lifting `Δ[n + 1] ⟶ X`. -/
/-
**SSet.horn.IsCompatible.liftOfKanComplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn.I
sCompatible`。
形式化陈述：liftOfKanComplex [KanComplex X] (hf : horn.IsCompatible f) : Δ[n + 1] ⟶ X
参数：hf : horn.IsCompatible f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.horn.IsCompatible.exists_lift_of_kanComplex`：exists_lift_of_kanComp
lex [KanComplex X] (hf : horn.IsCompatible f) : exists (φ : Δ[n + 1] ⟶ X), foral
l (j : Fin (n + 2)) (hj : j != i), std…

--- 原说明 ---
If `X` is a Kan complex and `f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X`
is a compatible family of morphisms (which defines a morphism `Λ[n + 1, i] ⟶ X`)
,
then this is a lifting `Δ[n + 1] ⟶ X`.
-/
noncomputable def liftOfKanComplex [KanComplex X] (hf : horn.IsCompatible f) :
    Δ[n + 1] ⟶ X :=
  hf.exists_lift_of_kanComplex.choose

@[reassoc]
/-
**SSet.horn.IsCompatible.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn.IsCompatible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_liftOfKanComplex [KanComplex X] (hf : horn.IsCompatible f)
    (j : Fin (n + 2)) (hj : j ≠ i := by grind) :
    stdSimplex.δ j ≫ hf.liftOfKanComplex = f j hj :=
  hf.exists_lift_of_kanComplex.choose_spec j hj

end horn.IsCompatible

open modelCategoryQuillen in
/-- A simplicial set `X` is a Kan complex iff for any `n : ℕ`, `i : Fin (n + 2)`,
and any family of morphisms `Δ[n] ⟶ Z` for all `j ≠ i` that is compatible
(in the sense that it extends to a morphism `Λ[n + 1, i] ⟶ X`), there
exists a morphism `Δ[n + 1] ⟶ Z` which induces the given family of morphisms
on the faces `j ≠ i`. -/
/-
**SSet.KanComplex.iff** 是 Mathlib 中的一个定理，位于命名空间 `SSet.KanComplex`。
形式化陈述：∀ {Z : _root_.SSet},   Z.KanComplex ↔     ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 2)⦄ (f :
 (j : Fin (n + 2)) → j ≠ i → (SSet.stdSimplex.obj { len := n } ⟶ Z)),       SSet
.horn.IsCompatible f →         ∃ φ, ∀ (j : Fin (n + 2)) (hj : j ≠ i), CategoryTh
eory.CategoryStruct.comp (SSet.stdSimplex.δ j) φ = f j hj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.horn.IsCompatible.exists_lift_of_kanComplex`：exists_lift_of_kanComp
lex [KanComplex X] (hf : horn.IsCompatible f) : exists (φ : Δ[n + 1] ⟶ X), foral
l (j : Fin (n + 2)) (hj : j != i), std…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HomotopicalAlgebra.isFibrant_iff`：isFibrant_iff (X : C) : IsFibrant X ↔ 
Fibration (terminal.from X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.modelCategoryQuillen.fibrations_eq`：fibrations_eq : fibrations SSet
.{u} = J.rlp
· 使用引理 `SSet.horn.IsCompatible.of_hom`：of_hom {i : Fin (n + 2)} (g : (Λ[n + 1, i
] : SSet) ⟶ X) : horn.IsCompatible (fun j hj => horn.ι i j hj ≫ g)
· 使用引理 `SSet.horn.hom_ext'`：hom_ext' {i : Fin (n + 2)} {f g : (Λ[n + 1, i] : SSe
t) ⟶ X} (h : forall (j : Fin (n + 2)) (hj : j != i), horn.ι i j hj ≫ f = horn.ι 
i j hj ≫…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.horn.ι_ι_assoc`：∀ {n : ℕ} (i j : Fin (n + 2)) (hij : j ≠ i) {Z : _r
oot_.SSet} (h : SSet.stdSimplex.obj { len := n + 1 } ⟶ Z),   CategoryTheory.Cate
goryStruc…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A simplicial set `X` is a Kan complex iff for any `n : ℕ`, `i : Fin (n + 2)`,
and any family of morphisms `Δ[n] ⟶ Z` for all `j ≠ i` that is compatible
(in the sense that it extends to a morphism `Λ[n + 1, i] ⟶ X`), there
exists a morphism `Δ[n + 1] ⟶ Z` which induces the given family of morphisms
on the faces `j ≠ i`.
-/
lemma KanComplex.iff {Z : SSet.{u}} :
    KanComplex Z ↔
      ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 2)⦄ (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ Z)
        (_ : horn.IsCompatible f),
        ∃ (φ : Δ[n + 1] ⟶ Z),
          ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  refine ⟨fun _ n i f hf ↦ hf.exists_lift_of_kanComplex,
    fun h ↦ (isFibrant_iff _).2 ⟨?_⟩⟩
  rw [fibrations_eq]
  intro _ _ _ hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  refine ⟨fun {t _} _ ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := h _ (horn.IsCompatible.of_hom t)
  exact ⟨⟨{
    l := φ
    fac_left := horn.hom_ext' (by simpa using hφ)
    fac_right := by subsingleton }⟩⟩

end SSet

