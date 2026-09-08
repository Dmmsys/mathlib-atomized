/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.PInfty

/-!

# Decomposition of the Q endomorphisms

In this file, we obtain a lemma `decomposition_Q` which expresses
explicitly the projection `(Q q).f (n+1) : X _⦋n+1⦌ ⟶ X _⦋n+1⦌`
(`X : SimplicialObject C` with `C` a preadditive category) as
a sum of terms which are postcompositions with degeneracies.

(TODO @joelriou: when `C` is abelian, define the degenerate
subcomplex of the alternating face map complex of `X` and show
that it is a complement to the normalized Moore complex.)

Then, we introduce an ad hoc structure `MorphComponents X n Z` which
can be used in order to define morphisms `X _⦋n+1⦌ ⟶ Z` using the
decomposition provided by `decomposition_Q`. This shall play a critical
role in the proof that the functor
`N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
  Opposite Simplicial

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X X' : SimplicialObject C}

set_option backward.isDefEq.respectTransparency false in
/-- In each positive degree, this lemma decomposes the idempotent endomorphism
`Q q` as a sum of morphisms which are postcompositions with suitable degeneracies.
As `Q q` is the complement projection to `P q`, this implies that in the case of
simplicial abelian groups, any $(n+1)$-simplex $x$ can be decomposed as
$x = x' + \sum (i=0}^{q-1} σ_{n-i}(y_i)$ where $x'$ is in the image of `P q` and
the $y_i$ are in degree $n$. -/
/-
**AlgebraicTopology.DoldKan.decomposition_Q** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Topology.DoldKan`。
形式化陈述：decomposition_Q (n q : Nat) : ((Q q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌) 
= ∑ i : Fin (n + 1) with i.val < q, (P i).f (n + 1) ≫ X.δ i.rev.succ ≫ X.σ (Fin.
rev i)
参数：n q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgebraicTopology.DoldKan.Q_zero`：Q_zero : (Q 0 : K[X] ⟶ _) = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicTopology.DoldKan.Q_is_eventually_constant`：Q_is_eventually_cons
tant {q n : Nat} (hqn : n <= q) : ((Q (q + 1)).f n : X _⦋n⦌ ⟶ _) = (Q q).f n
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Nat.le.dest`：∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
· 使用定理 `AlgebraicTopology.DoldKan.Q_succ`：Q_succ (q : Nat) : (Q (q + 1) : K[X] ⟶
 _) = Q q - P q ≫ Hσ q
· 使用定理 `HomologicalComplex.sub_f_apply`：sub_f_apply (f g : C ⟶ D) (i : ι) : (f -
 g).f i = f.f i - g.f i
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
In each positive degree, this lemma decomposes the idempotent endomorphism
`Q q` as a sum of morphisms which are postcompositions with suitable degeneracie
s.
As `Q q` is the complement projection to `P q`, this implies that in the case of
simplicial abelian groups, any $(n+1)$-simplex $x$ can be decomposed as
$x = x' + \sum (i=0}^{q-1} σ_{n-i}(y_i)$ where $x'$ is in the image of `P q` and
the $y_i$ are in degree $n$.
-/
theorem decomposition_Q (n q : ℕ) :
    ((Q q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌) =
      ∑ i : Fin (n + 1) with i.val < q, (P i).f (n + 1) ≫ X.δ i.rev.succ ≫ X.σ (Fin.rev i) := by
  induction q with
  | zero =>
    simp only [Q_zero, HomologicalComplex.zero_f_apply, Nat.not_lt_zero,
      Finset.filter_false, Finset.sum_empty]
  | succ q hq =>
    by_cases! hqn : n < q
    · rw [Q_is_eventually_constant (show n + 1 ≤ q by lia), hq]
      congr 1
      ext ⟨x, hx⟩
      simp_rw [Finset.mem_filter_univ]
      lia
    · obtain ⟨a, ha⟩ := Nat.le.dest hqn
      rw [Q_succ, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f, hq]
      symm
      conv_rhs => rw [sub_eq_add_neg, add_comm]
      let q' : Fin (n + 1) := ⟨q, Nat.lt_succ_of_le hqn⟩
      rw [← @Finset.add_sum_erase _ _ _ _ _ _ q' (by simp [q'])]
      congr
      · have hnaq' : n = a + q := by lia
        simp only [(HigherFacesVanish.of_P q n).comp_Hσ_eq hnaq', q'.rev_eq hnaq', neg_neg]
        rfl
      · ext ⟨i, hi⟩
        simp_rw [Finset.mem_erase, Finset.mem_filter_univ, q', ne_eq, Fin.mk.injEq]
        lia

variable (X)

/-- The structure `MorphComponents` is an ad hoc structure that is used in
the proof that `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms. The fields are the data that are needed in order to
construct a morphism `X _⦋n+1⦌ ⟶ Z` (see `φ`) using the decomposition of the
identity given by `decomposition_Q n (n+1)`. -/
@[ext]
/-
**AlgebraicTopology.DoldKan.MorphComponents** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra
icTopology.DoldKan`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → CategoryT
heory.SimplicialObject C → ℕ → C → Type v_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure `MorphComponents` is an ad hoc structure that is used in
the proof that `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms. The fields are the data that are needed in order to
construct a morphism `X _⦋n+1⦌ ⟶ Z` (see `φ`) using the decomposition of the
identity given by `decomposition_Q n (n+1)`.
-/
structure MorphComponents (n : ℕ) (Z : C) where
  a : X _⦋n + 1⦌ ⟶ Z
  b : Fin (n + 1) → (X _⦋n⦌ ⟶ Z)

namespace MorphComponents

variable {X} {n : ℕ} {Z Z' : C} (f : MorphComponents X n Z) (g : X' ⟶ X) (h : Z ⟶ Z')

/-- The morphism `X _⦋n+1⦌ ⟶ Z` associated to `f : MorphComponents X n Z`. -/
/-
**AlgebraicTopology.DoldKan.MorphComponents.** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cTopology.DoldKan.MorphComponents`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `X _⦋n+1⦌ ⟶ Z` associated to `f : MorphComponents X n Z`.
-/
def φ {Z : C} (f : MorphComponents X n Z) : X _⦋n + 1⦌ ⟶ Z :=
  PInfty.f (n + 1) ≫ f.a + ∑ i : Fin (n + 1), (P i).f (n + 1) ≫ X.δ i.rev.succ ≫
    f.b (Fin.rev i)

variable (X n)

/-- the canonical `MorphComponents` whose associated morphism is the identity
(see `F_id`) thanks to `decomposition_Q n (n+1)` -/
@[simps]
/-
**AlgebraicTopology.DoldKan.MorphComponents.id** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicTopology.DoldKan.MorphComponents`。
形式化陈述：id : MorphComponents X n (X _⦋n + 1⦌) where a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the canonical `MorphComponents` whose associated morphism is the identity
(see `F_id`) thanks to `decomposition_Q n (n+1)`
-/
def id : MorphComponents X n (X _⦋n + 1⦌) where
  a := PInfty.f (n + 1)
  b i := X.σ i

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicTopology.DoldKan.MorphComponents.id_** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicTopology.DoldKan.MorphComponents`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_φ : (id X n).φ = 𝟙 _ := by
  simp only [← P_add_Q_f (n + 1) (n + 1), φ]
  congr 1
  · simp only [id, PInfty_f, P_f_idem]
  · exact Eq.trans (by simp) (decomposition_Q n (n + 1)).symm

variable {X n}

/-- A `MorphComponents` can be postcomposed with a morphism. -/
@[simps]
/-
**AlgebraicTopology.DoldKan.MorphComponents.postComp** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicTopology.DoldKan.MorphComponents`。
形式化陈述：postComp : MorphComponents X n Z' where a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MorphComponents` can be postcomposed with a morphism.
-/
def postComp : MorphComponents X n Z' where
  a := f.a ≫ h
  b i := f.b i ≫ h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicTopology.DoldKan.MorphComponents.postComp_** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicTopology.DoldKan.MorphComponents`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem postComp_φ : (f.postComp h).φ = f.φ ≫ h := by
  unfold φ postComp
  simp only [add_comp, sum_comp, assoc]

/-- A `MorphComponents` can be precomposed with a morphism of simplicial objects. -/
@[simps]
/-
**AlgebraicTopology.DoldKan.MorphComponents.preComp** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicTopology.DoldKan.MorphComponents`。
形式化陈述：preComp : MorphComponents X' n Z where a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MorphComponents` can be precomposed with a morphism of simplicial objects.
-/
def preComp : MorphComponents X' n Z where
  a := g.app (op ⦋n + 1⦌) ≫ f.a
  b i := g.app (op ⦋n⦌) ≫ f.b i

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicTopology.DoldKan.MorphComponents.preComp_** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicTopology.DoldKan.MorphComponents`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preComp_φ : (f.preComp g).φ = g.app (op ⦋n + 1⦌) ≫ f.φ := by
  unfold φ preComp
  simp only [PInfty_f, comp_add]
  congr 1
  · simp
  · simp only [comp_sum, P_f_naturality_assoc, SimplicialObject.δ_naturality_assoc]

end MorphComponents

end DoldKan

end AlgebraicTopology

