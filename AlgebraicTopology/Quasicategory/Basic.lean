/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Quasicategories

In this file we define quasicategories,
a common model of infinity categories.
We show that every Kan complex is a quasicategory.

In `Mathlib/AlgebraicTopology/Quasicategory/Nerve.lean`,
we show that the nerve of a category is a quasicategory.

## TODO

- Generalize the definition to higher universes.
  See the corresponding TODO in
  `Mathlib/AlgebraicTopology/SimplicialSet/KanComplex.lean`.

-/

public section

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *quasicategory* if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.
-/
@[kerodon 003A]
/-
**SSet.Quasicategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set `S` is a *quasicategory* if it satisfies the following horn-fil
ling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[
n] → S`.
-/
class Quasicategory (S : SSet) : Prop where
  hornFilling' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)),
      ∃ σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ
/-
**SSet.Quasicategory.hornFilling** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Quasicategory`。
形式化陈述：∀ {S : _root_.SSet} [S.Quasicategory] ⦃n : ℕ⦄ ⦃i : Fin (n + 1)⦄,   0 < i →
     i < Fin.last n →       ∀ (σ₀ : (SSet.horn n i).toSSet ⟶ S), ∃ σ, σ₀ = Categ
oryTheory.CategoryStruct.comp (SSet.horn n i).ι σ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SSet.Quasicategory.hornFilling'`：∀ {S : _root_.SSet} [self : S.Quasicate
gory] ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (SSet.horn (n + 2) i).toSSet ⟶ S),   0 < i
 → i < Fin.last (n + …
-/
lemma Quasicategory.hornFilling {S : SSet} [Quasicategory S] ⦃n : ℕ⦄ ⦃i : Fin (n + 1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : (Λ[n, i] : SSet) ⟶ S) : ∃ σ : Δ[n] ⟶ S, σ₀ = Λ[n, i].ι ≫ σ := by
  match n with
  | 0
  | 1 => lia
  | n + 2 => exact Quasicategory.hornFilling' σ₀ h0 hn

/-- Every Kan complex is a quasicategory. -/
@[kerodon 003C]
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Kan complex is a quasicategory.
-/
instance (S : SSet) [KanComplex S] : Quasicategory S where
  hornFilling' _ _ σ₀ _ _ := KanComplex.hornFilling σ₀
/-
**SSet.quasicategory_of_filler** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：quasicategory_of_filler (S : SSet) (filler : forall ⦃n : Nat⦄ ⦃i : Fin (n 
+ 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S) (_h0 : 0 < i) (_hn : i < Fin.last (n + 2))
, exists σ : S _⦋n + 2⦌, forall (j) (h : j != i), S.δ j σ = σ₀.app _ (horn.face 
i j h)) : Quasicategory S where hornFilling' n i σ₀ h₀ hₙ
参数：S : SSet；filler : forall ⦃n : Nat⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSe
t) ⟶ S) (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)), exists σ : S _⦋n + 2⦌, foral
l (j) (h : j != i), S.δ j σ = σ₀.app _ (horn.face i j h)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `SSet.horn.hom_ext`：hom_ext {n : Nat} {i : Fin (n + 2)} {S : SSet} (σ₁ σ₂
 : (Λ[n + 1, i] : SSet.{u}) ⟶ S) (h : forall (j) (h : j != i), σ₁.app _ (face i 
j h) = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
-/
lemma quasicategory_of_filler (S : SSet)
    (filler : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S)
      (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)),
      ∃ σ : S _⦋n + 2⦌, ∀ (j) (h : j ≠ i), S.δ j σ = σ₀.app _ (horn.face i j h)) :
    Quasicategory S where
  hornFilling' n i σ₀ h₀ hₙ := by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨yonedaEquiv.symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj, NatTrans.comp_app]
    rfl
/-
**SSet.quasicategory_of_hasLiftingProperty** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：quasicategory_of_hasLiftingProperty (S : SSet) {X : SSet} (t : Limits.IsTe
rminal X) (h : forall {n : Nat} {i : Fin (n + 1)} (_ : 0 < i) (_ : i < Fin.last 
n), HasLiftingProperty Λ[n, i].ι (t.from S)) : Quasicategory S where hornFilling
' n i σ₀ h0 hn
参数：S : SSet；t : Limits.IsTerminal X；h : forall {n : Nat} {i : Fin (n + 1)} (_ : 
0 < i) (_ : i < Fin.last n), HasLiftingProperty Λ[n, i].ι (t.from S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quasicategory_of_hasLiftingProperty (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
    (h : ∀ {n : ℕ} {i : Fin (n + 1)} (_ : 0 < i) (_ : i < Fin.last n),
      HasLiftingProperty Λ[n, i].ι (t.from S)) :
    Quasicategory S where
  hornFilling' n i σ₀ h0 hn :=
    let := h h0 hn
    ⟨(CommSq.mk (t.hom_ext (σ₀ ≫ t.from S) (Λ[n + 2, i].ι ≫ t.from Δ[n + 2]))).lift, by simp⟩
/-
**SSet.Quasicategory.hasLiftingProperty** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Quasicat
egory`。
形式化陈述：∀ (S : _root_.SSet) [S.Quasicategory] {X : _root_.SSet} (t : CategoryTheor
y.Limits.IsTerminal X) {n : ℕ}   {i : Fin (n + 1)}, 0 < i → i < Fin.last n → Cat
egoryTheory.HasLiftingProperty (SSet.horn n i).ι (t.from S)
参数：S : _root_.SSet；t : CategoryTheory.Limits.IsTerminal X；n + 1；SSet.horn n i；t.
from S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SSet.Quasicategory.hornFilling`：∀ {S : _root_.SSet} [S.Quasicategory] ⦃n
 : ℕ⦄ ⦃i : Fin (n + 1)⦄,   0 < i →     i < Fin.last n →       ∀ (σ₀ : (SSet.horn
 n i).toSSet ⟶ S), ∃…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
lemma Quasicategory.hasLiftingProperty (S : SSet) [Quasicategory S] {X : SSet}
    (t : Limits.IsTerminal X) {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n) :
    HasLiftingProperty Λ[n, i].ι (t.from S) where
  sq_hasLift _ :=
    ⟨(hornFilling h0 hn _).choose, (hornFilling h0 hn _).choose_spec.symm, t.hom_ext _ _⟩
/-
**SSet.quasicategory_iff_hasLiftingProperty** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：quasicategory_iff_hasLiftingProperty (S : SSet) {X : SSet} (t : Limits.IsT
erminal X) : Quasicategory S ↔ forall {n : Nat} {i : Fin (n + 1)} (_ : 0 < i) (_
 : i < Fin.last n), HasLiftingProperty Λ[n, i].ι (t.from S)
参数：S : SSet；t : Limits.IsTerminal X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SSet.Quasicategory.hasLiftingProperty`：∀ (S : _root_.SSet) [S.Quasicateg
ory] {X : _root_.SSet} (t : CategoryTheory.Limits.IsTerminal X) {n : ℕ}   {i : F
in (n + 1)}, 0 < i → i < Fi…
· 使用引理 `SSet.quasicategory_of_hasLiftingProperty`：quasicategory_of_hasLiftingPro
perty (S : SSet) {X : SSet} (t : Limits.IsTerminal X) (h : forall {n : Nat} {i :
 Fin (n + 1)} (_ : 0 < i) (_ :…
-/
lemma quasicategory_iff_hasLiftingProperty (S : SSet) {X : SSet} (t : Limits.IsTerminal X) :
    Quasicategory S ↔ ∀ {n : ℕ} {i : Fin (n + 1)} (_ : 0 < i) (_ : i < Fin.last n),
      HasLiftingProperty Λ[n, i].ι (t.from S) :=
  ⟨fun _ ↦ Quasicategory.hasLiftingProperty S t, quasicategory_of_hasLiftingProperty S t⟩

end SSet

