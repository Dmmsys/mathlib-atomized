/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
public import Mathlib.CategoryTheory.Subfunctor.Equalizer

/-!
# Horns

This file introduces horns `Λ[n, i]`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex,
where `i : n`. It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
@[simps -isSimp obj]
/-
**SSet.horn** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：horn (n : Nat) (i : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex where obj 
_
参数：n : Nat；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex,
where `i : n`. It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`).
-/
def horn (n : ℕ) (i : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ := Set.ofPred (fun s ↦ Set.range (stdSimplex.asOrderHom s) ∪ {i} ≠ Set.univ)
  map φ s hs h := hs (by
    rw [Set.eq_univ_iff_forall] at h ⊢; intro j
    apply Or.imp _ id (h j)
    intro hj
    exact Set.range_comp_subset_range _ _ hj)

/-- The `i`-th horn `Λ[n, i]` of the standard `n`-simplex -/
scoped[Simplicial] notation3 "Λ[" n ", " i "]" => SSet.horn (n : ℕ) i

/-
**SSet.mem_horn_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：mem_horn_iff {n : Nat} (i : Fin (n + 1)) {m : SimplexCategoryᵒᵖ} (x : Δ[n]
.obj m) : x in (horn n i).obj m ↔ Set.range (stdSimplex.asOrderHom x) union {i} 
!= Set.univ
参数：i : Fin (n + 1)；x : Δ[n].obj m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_horn_iff {n : ℕ} (i : Fin (n + 1)) {m : SimplexCategoryᵒᵖ} (x : Δ[n].obj m) :
    x ∈ (horn n i).obj m ↔ Set.range (stdSimplex.asOrderHom x) ∪ {i} ≠ Set.univ := Iff.rfl
/-
**SSet.horn_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n i = ⨆ (j : ({i}ᶜ : S
et (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
参数：n : Nat；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Subfunctor.mk.congr_simp`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (obj obj_1 :
 (U : C) → Set (F.obj U)) (e_…
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `SSet.stdSimplex.face_obj`：∀ {n : ℕ} (S : Finset (Fin (n + 1))) (U : Simp
lexCategoryᵒᵖ),   (SSet.stdSimplex.face S).obj U =     {f | Finset.image ⇑(Simpl
exCategory.Hom…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma horn_eq_iSup (n : ℕ) (i : Fin (n + 1)) :
    horn.{u} n i =
      ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ := by
  ext m j
  simp [stdSimplex.face_obj, horn, Set.eq_univ_iff_forall]
  rfl
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} (i : Fin (n + 1)) : HasDimensionLT (horn.{u} n i) n := by
  rw [horn_eq_iSup, hasDimensionLT_iSup_iff]
  intro i
  exact stdSimplex.hasDimensionLT_face _ _ (by simp [Finset.card_compl])
/-
**SSet.mem_horn_iff_notMem_range** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：mem_horn_iff_notMem_range {n d : Nat} (s : Δ[n] _⦋d⦌) (i : Fin (n + 1)) : 
s in (horn.{u} n i).obj _ ↔ exists (j : Fin (n + 1)) (_ : j != i), j ∉ Set.range
 s
参数：s : Δ[n] _⦋d⦌；i : Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SSet.horn_eq_iSup`：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n
 i = ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_horn_iff_notMem_range {n d : ℕ} (s : Δ[n] _⦋d⦌) (i : Fin (n + 1)) :
    s ∈ (horn.{u} n i).obj _ ↔ ∃ (j : Fin (n + 1)) (_ : j ≠ i), j ∉ Set.range s := by
  simp [horn_eq_iSup]
/-
**SSet.face_le_horn** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：face_le_horn {n : Nat} (i j : Fin (n + 1)) (h : i != j) : stdSimplex.face.
{u} {i}ᶜ <= horn n j
参数：i j : Fin (n + 1)；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.horn_eq_iSup`：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n
 i = ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma face_le_horn {n : ℕ} (i j : Fin (n + 1)) (h : i ≠ j) :
    stdSimplex.face.{u} {i}ᶜ ≤ horn n j := by
  rw [horn_eq_iSup]
  exact le_iSup (fun (k : ({j}ᶜ : Set (Fin (n + 1)))) ↦ stdSimplex.face.{u} {k.1}ᶜ) ⟨i, h⟩

@[simp]
/-
**SSet.horn_obj_zero** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：horn_obj_zero (n : Nat) (i : Fin (n + 3)) : (horn.{u} (n + 2) i).obj (op (
.mk 0)) = ⊤
参数：n : Nat；i : Fin (n + 3)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SSet.horn_eq_iSup`：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n
 i = ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_le_two`：card_le_two : #{a, b} <= 2
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 32 条，此处仅展示前 30 条）
-/
lemma horn_obj_zero (n : ℕ) (i : Fin (n + 3)) :
    (horn.{u} (n + 2) i).obj (op (.mk 0)) = ⊤ := by
  ext j
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, Finset.mem_compl, Finset.mem_singleton, exists_prop, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  let S : Finset (Fin (n + 3)) := {i, j 0}
  have hS : ¬ (S = Finset.univ) := fun hS ↦ by
    have := Finset.card_le_card hS.symm.le
    simp only [Finset.card_univ, Fintype.card_fin, S] at this
    have := this.trans Finset.card_le_two
    lia
  rw [Finset.eq_univ_iff_forall, not_forall] at hS
  obtain ⟨k, hk⟩ := hS
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, S] at hk
  refine ⟨k, hk.1, fun a ↦ ?_⟩
  fin_cases a
  exact Ne.symm hk.2
/-
**SSet.horn_obj_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：horn_obj_eq_univ {n : Nat} (i : Fin (n + 1)) (m : Nat) (h : m + 1 < n
参数：i : Fin (n + 1)；m : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
（共 48 条，此处仅展示前 30 条）
-/
lemma horn_obj_eq_univ {n : ℕ} (i : Fin (n + 1)) (m : ℕ) (h : m + 1 < n := by lia) :
    (horn.{u} n i).obj (op ⦋m⦌) = .univ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  obtain ⟨j, hij, hj⟩ : ∃ (j : Fin (n + 1)), j ≠ i ∧ j ∉ Set.range f.toOrderHom := by
    by_contra!
    have : Finset.image f.toOrderHom ⊤ ∪ {i} = ⊤ := by ext k; by_cases k = i <;> aesop
    have := (congr_arg Finset.card this).symm.le.trans (Finset.card_union_le _ _)
    simp only [SimplexCategory.len_mk, Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, add_le_add_iff_right] at this
    have : n ≤ m + 1 := by simpa using this.trans Finset.card_image_le
    lia
  have : ∃ j, ¬j = i ∧ ∀ (i : Fin (m + 1)), ¬(stdSimplex.objEquiv.{u}.symm f) i = j :=
    ⟨j, hij, fun k hk ↦ hj ⟨k, hk⟩⟩
  simpa [horn_eq_iSup] using this
/-
**SSet.subcomplex_le_horn_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：subcomplex_le_horn_iff {n : Nat} (A : Δ[n + 1].Subcomplex) (i : Fin (n + 2
)) : A <= horn.{u} (n + 1) i ↔ ¬ stdSimplex.face {i}ᶜ <= A
参数：A : Δ[n + 1].Subcomplex；i : Fin (n + 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.mem_horn_iff`：mem_horn_iff {n : Nat} (i : Fin (n + 1)) {m : Simplex
Categoryᵒᵖ} (x : Δ[n].obj m) : x in (horn n i).obj m ↔ Set.range (stdSimplex.asO
rderHom…
· 使用引理 `SSet.Subcomplex.ofSimplex_le_iff`：ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌
) (A : X.Subcomplex) : ofSimplex x <= A ↔ x in A.obj _
· 使用引理 `SSet.stdSimplex.face_singleton_compl`：face_singleton_compl {n : Nat} (i 
: Fin (n + 2)) : face.{u} {i}ᶜ = Subcomplex.ofSimplex (objEquiv.symm (SimplexCat
egory.δ i))
· 使用引理 `SSet.stdSimplex.coe_asOrderHom_objEquiv_symm`：coe_asOrderHom_objEquiv_sy
mm {n m : Nat} (α : ⦋n⦌ ⟶ ⦋m⦌) : ⇑(asOrderHom (objEquiv.{u}.symm α)) = α
· 使用引理 `SimplexCategory.coe_δ`：coe_δ {n : Nat} (i : Fin (n + 2)) : dsimp% ⇑(δ i)
 = Fin.succAbove i
· 使用定理 `Fin.range_succAbove`：∀ {n : ℕ} (p : Fin (n + 1)), Set.range p.succAbove 
= {p}ᶜ
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用引理 `SSet.Subcomplex.le_iff_contains_nonDegenerate`：le_iff_contains_nonDegene
rate (B : X.Subcomplex) : A <= B ↔ forall (n : Nat) (x : X.nonDegenerate n), x.v
al in A.obj _ -> x.val in B.obj _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.horn_obj_eq_univ`：horn_obj_eq_univ {n : Nat} (i : Fin (n + 1)) (m :
 Nat) (h : m + 1 < n
· 使用引理 `SSet.stdSimplex.nonDegenerateEquiv'`：nonDegenerateEquiv'_iff {n d : Nat}
 (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) : j in (nonDegenerate
Equiv' x).val ↔ exists (i…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `SSet.stdSimplex.face_univ`：face_univ (n : Nat) : face.{u} (.univ : Finse
t (Fin (n + 1))) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_eq_iff_eq_univ`：Finset.card_eq_iff_eq_univ [Fintype α] (s : 
Finset α) : #s = Fintype.card α ↔ s = univ
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `card_finset_fin_le`：card_finset_fin_le {n : Nat} (s : Finset (Fin n)) : 
#s <= n
· 使用定理 `Finset.card_compl_add_card`：Finset.card_compl_add_card [DecidableEq α] [
Fintype α] (s : Finset α) : #sᶜ + #s = Fintype.card α
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SSet.face_le_horn`：face_le_horn {n : Nat} (i j : Fin (n + 1)) (h : i != 
j) : stdSimplex.face.{u} {i}ᶜ <= horn n j
-/
lemma subcomplex_le_horn_iff {n : ℕ}
    (A : Δ[n + 1].Subcomplex) (i : Fin (n + 2)) :
    A ≤ horn.{u} (n + 1) i ↔ ¬ stdSimplex.face {i}ᶜ ≤ A := by
  refine ⟨fun hA h ↦ ?_, fun h ↦ ?_⟩
  · replace h := h.trans hA
    rw [stdSimplex.face_singleton_compl, Subcomplex.ofSimplex_le_iff, mem_horn_iff] at h
    apply h
    rw [stdSimplex.coe_asOrderHom_objEquiv_symm, SimplexCategory.coe_δ,
      Fin.range_succAbove, Set.compl_union_self]
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    by_cases! hd : d < n
    · simp [horn_obj_eq_univ i d]
    · obtain ⟨⟨S, hS⟩, rfl⟩ := stdSimplex.nonDegenerateEquiv'.symm.surjective x
      dsimp at hS
      simp only [stdSimplex.nonDegenerateEquiv'_symm_mem_iff_face_le] at hx ⊢
      obtain hd | rfl := hd.lt_or_eq
      · obtain rfl : S = .univ := by
          rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
          exact le_antisymm (card_finset_fin_le S) (by lia)
        exact (h (le_trans (by simp) hx)).elim
      · replace hS : Sᶜ.card = 1 := by
          have := S.card_compl_add_card
          rw [Fintype.card_fin] at this
          lia
        obtain ⟨j, rfl⟩ : ∃ j, S = {j}ᶜ := by
          rw [Finset.card_eq_one] at hS
          obtain ⟨j, hS⟩ := hS
          exact ⟨j, by simp [← hS]⟩
        exact face_le_horn _ _ (by rintro rfl; tauto)
/-
**SSet.face_le_horn_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：face_le_horn_iff {n : Nat} (S : Finset (Fin (n + 2))) (j : Fin (n + 2)) : 
stdSimplex.face.{u} S <= Λ[n + 1, j] ↔ S != .univ ∧ S != {j}ᶜ
参数：S : Finset (Fin (n + 2))；j : Fin (n + 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.subcomplex_le_horn_iff`：subcomplex_le_horn_iff {n : Nat} (A : Δ[n +
 1].Subcomplex) (i : Fin (n + 2)) : A <= horn.{u} (n + 1) i ↔ ¬ stdSimplex.face 
{i}ᶜ <= A
· 使用引理 `SSet.stdSimplex.face_le_face_iff`：face_le_face_iff {n : Nat} (S₁ S₂ : Fi
nset (Fin (n + 1))) : face.{u} S₁ <= face S₂ ↔ S₁ <= S₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.compl_eq_empty_iff`：compl_eq_empty_iff (s : Finset α) : sᶜ = ∅ ↔ 
s = univ
· 使用定理 `Finset.subset_singleton_iff`：subset_singleton_iff {s : Finset α} {a : α}
 : s subseteq {a} ↔ s = ∅ ∨ s = {a}
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `Finset.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subse
teq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma face_le_horn_iff {n : ℕ} (S : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    stdSimplex.face.{u} S ≤ Λ[n + 1, j] ↔ S ≠ .univ ∧ S ≠ {j}ᶜ := by
  rw [subcomplex_le_horn_iff, stdSimplex.face_le_face_iff, ← not_iff_not]
  simp only [Decidable.not_not, ne_eq, not_and_or]
  refine ⟨fun h ↦ ?_, by aesop⟩
  rw [← Finset.compl_subset_compl, compl_compl,
    Finset.subset_singleton_iff, Finset.compl_eq_empty_iff] at h
  grind [eq_compl_comm]
/-
**SSet.objEquiv_symm_notMem_horn_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：objEquiv_symm_notMem_horn_of_isIso {n : Nat} (i : Fin (n + 1)) {d : Simple
xCategory} (f : d ⟶ ⦋n⦌) [IsIso f] : stdSimplex.objEquiv.{u}.symm f ∉ Λ[n, i].ob
j (op d)
参数：i : Fin (n + 1)；f : d ⟶ ⦋n⦌。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.mem_horn_iff`：mem_horn_iff {n : Nat} (i : Fin (n + 1)) {m : Simplex
Categoryᵒᵖ} (x : Δ[n].obj m) : x in (horn n i).obj m ↔ Set.range (stdSimplex.asO
rderHom…
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SSet.stdSimplex.coe_asOrderHom_objEquiv_symm`：coe_asOrderHom_objEquiv_sy
mm {n m : Nat} (α : ⦋n⦌ ⟶ ⦋m⦌) : ⇑(asOrderHom (objEquiv.{u}.symm α)) = α
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f]   {F 
: C → C → Type uF} {carrier…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma objEquiv_symm_notMem_horn_of_isIso {n : ℕ} (i : Fin (n + 1))
    {d : SimplexCategory} (f : d ⟶ ⦋n⦌) [IsIso f] :
    stdSimplex.objEquiv.{u}.symm f ∉ Λ[n, i].obj (op d) := by
  rw [mem_horn_iff, ne_eq, not_not]
  ext i
  simpa using Or.inr ⟨inv f i, by simp [stdSimplex.coe_asOrderHom_objEquiv_symm.{u}]⟩
/-
**SSet.objEquiv_symm_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_symm_δ_mem_horn_iff {n : ℕ} (i j : Fin (n + 2)) :
    (stdSimplex.objEquiv (m := op ⦋n⦌)).symm
      (SimplexCategory.δ i) ∈ (horn.{u} (n + 1) j).obj (op ⦋n⦌) ↔ i ≠ j := by
  dsimp
  rw [← Subcomplex.ofSimplex_le_iff, ← stdSimplex.face_singleton_compl, face_le_horn_iff]
  simp
/-
**SSet.objEquiv_symm_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_symm_δ_notMem_horn_iff {n : ℕ} (i j : Fin (n + 2)) :
    (stdSimplex.objEquiv (m := op ⦋n⦌)).symm
      (SimplexCategory.δ i) ∉ (horn.{u} _ j).obj (op ⦋n⦌) ↔ i = j := by
  simp [objEquiv_symm_δ_mem_horn_iff.{u}]
/-
**SSet.op_horn** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：op_horn {n : Nat} (i : Fin (n + 1)) : Λ[n, i].op.preimage (stdSimplex.opIs
o.{u} ⦋n⦌).inv = Λ[n, i.rev]
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.Subcomplex.preimage_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (
p : Y ⟶ X) (n : SimplexCategoryᵒᵖ),   (A.preimage p).obj n = ⇑(CategoryTheory.Co
ncreteCategory.hom…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `SSet.stdSimplex.opIso_inv_app_hom_apply`：∀ (n : SimplexCategory) (X : Si
mplexCategoryᵒᵖ) (x : (SSet.stdSimplex.obj n).obj X),   (CategoryTheory.Concrete
Category.hom ((SSet.stdSimple…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma op_horn {n : ℕ} (i : Fin (n + 1)) :
    Λ[n, i].op.preimage (stdSimplex.opIso.{u} ⦋n⦌).inv = Λ[n, i.rev] := by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_horn_iff_notMem_range, Set.mem_range, not_exists, ne_eq,
    exists_prop, stdSimplex.opObjEquiv_opObjEquiv_symm_apply]
  constructor
  · rintro ⟨k, h₁, h₂⟩
    exact ⟨k.rev, by simpa, fun l hl ↦ by grind [h₂ l.rev]⟩
  · rintro ⟨k, h₁, h₂⟩
    exact ⟨k.rev, by grind⟩

namespace horn

open SimplexCategory Finset Opposite

section

variable (n : ℕ) (i k : Fin (n + 3))

/-- The (degenerate) subsimplex of `Λ[n+2, i]` concentrated in vertex `k`. -/
/-
**SSet.horn.const** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：const (m : SimplexCategoryᵒᵖ) : Λ[n + 2, i].obj m
参数：m : SimplexCategoryᵒᵖ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The (degenerate) subsimplex of `Λ[n+2, i]` concentrated in vertex `k`.
-/
def const (m : SimplexCategoryᵒᵖ) : Λ[n + 2, i].obj m :=
  SSet.yonedaEquiv (X := Λ[n + 2, i])
    (SSet.const ⟨stdSimplex.obj₀Equiv.symm k, by simp⟩)

@[simp]
/-
**SSet.horn.const_val_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
形式化陈述：const_val_apply {m : Nat} (a : Fin (m + 1)) : (const n i k (op (.mk m))).v
al a = k
参数：a : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_val_apply {m : ℕ} (a : Fin (m + 1)) :
    (const n i k (op (.mk m))).val a = k :=
  rfl

end

/-- The edge of `Λ[n, i]` with endpoints `a` and `b`.

This edge only exists if `{i, a, b}` has cardinality less than `n`. -/
@[simps]
/-
**SSet.horn.edge** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：edge (n : Nat) (i a b : Fin (n + 1)) (hab : a <= b) (H : #{i, a, b} <= n) 
: (Λ[n, i] : SSet.{u}).obj (op ⦋1⦌)
参数：n : Nat；i a b : Fin (n + 1)；hab : a <= b；H : #{i, a, b} <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The edge of `Λ[n, i]` with endpoints `a` and `b`.

This edge only exists if `{i, a, b}` has cardinality less than `n`.
-/
def edge (n : ℕ) (i a b : Fin (n + 1)) (hab : a ≤ b) (H : #{i, a, b} ≤ n) :
    (Λ[n, i] : SSet.{u}).obj (op ⦋1⦌) :=
  ⟨stdSimplex.edge n a b hab, by
    have hS : ¬ ({i, a, b} = Finset.univ) := fun hS ↦ by
      have := Finset.card_le_card hS.symm.le
      simp only [card_univ, Fintype.card_fin] at this
      lia
    rw [Finset.eq_univ_iff_forall, not_forall] at hS
    obtain ⟨k, hk⟩ := hS
    simp only [mem_insert, mem_singleton, not_or] at hk
    -- this was produced by `simp? [horn_eq_iSup, -Fin.forall_fin_two]`
    simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff, Nat.reduceAdd, mem_compl,
      mem_singleton, exists_prop]
    refine ⟨k, hk.1, fun a ↦ ?_⟩
    fin_cases a
    · exact Ne.symm hk.2.1
    · exact Ne.symm hk.2.2⟩

/-- Alternative constructor for the edge of `Λ[n, i]` with endpoints `a` and `b`,
assuming `3 ≤ n`. -/
@[simps!]
/-
**SSet.horn.edge** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：edge (n : Nat) (i a b : Fin (n + 1)) (hab : a <= b) (H : #{i, a, b} <= n) 
: (Λ[n, i] : SSet.{u}).obj (op ⦋1⦌)
参数：n : Nat；i a b : Fin (n + 1)；hab : a <= b；H : #{i, a, b} <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for the edge of `Λ[n, i]` with endpoints `a` and `b`,
assuming `3 ≤ n`.
-/
def edge₃ (n : ℕ) (i a b : Fin (n + 1)) (hab : a ≤ b) (H : 3 ≤ n) :
    (Λ[n, i] : SSet.{u}) _⦋1⦌ :=
  edge n i a b hab <| Finset.card_le_three.trans H

/-- The edge of `Λ[n, i]` with endpoints `j` and `j+1`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicategories. -/
@[simps!]
/-
**SSet.horn.primitiveEdge** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：primitiveEdge {n : Nat} {i : Fin (n + 1)} (h₀ : 0 < i) (hₙ : i < Fin.last 
n) (j : Fin n) : (Λ[n, i] : SSet.{u}) _⦋1⦌
参数：n + 1；h₀ : 0 < i；hₙ : i < Fin.last n；j : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The edge of `Λ[n, i]` with endpoints `j` and `j+1`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicate
gories.
-/
def primitiveEdge {n : ℕ} {i : Fin (n + 1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    (Λ[n, i] : SSet.{u}) _⦋1⦌ := by
  refine edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.val_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl | hn : n = 2 ∨ 2 < n := by
    rw [eq_comm, or_comm, ← le_iff_lt_or_eq]; lia
  · revert i j; decide
  · exact Finset.card_le_three.trans hn

/-- The triangle in the standard simplex with vertices `k`, `k+1`, and `k+2`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicategories. -/
@[simps]
/-
**SSet.horn.primitiveTriangle** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：primitiveTriangle {n : Nat} (i : Fin (n + 4)) (h₀ : 0 < i) (hₙ : i < Fin.l
ast (n + 3)) (k : Nat) (h : k < n + 2) : (Λ[n + 3, i] : SSet.{u}).obj (op ⦋2⦌)
参数：i : Fin (n + 4)；h₀ : 0 < i；hₙ : i < Fin.last (n + 3)；k : Nat；h : k < n + 2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle in the standard simplex with vertices `k`, `k+1`, and `k+2`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicate
gories.
-/
def primitiveTriangle {n : ℕ} (i : Fin (n + 4))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 3))
    (k : ℕ) (h : k < n + 2) : (Λ[n + 3, i] : SSet.{u}).obj (op ⦋2⦌) := by
  refine ⟨stdSimplex.triangle
    (n := n+3) ⟨k, by lia⟩ ⟨k+1, by lia⟩ ⟨k+2, by lia⟩ ?_ ?_, ?_⟩
  · simp only [Fin.mk_le_mk, le_add_iff_nonneg_right, zero_le]
  · simp only [Fin.mk_le_mk, add_le_add_iff_left, one_le_two]
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, mem_compl, mem_singleton, exists_prop]
  have hS : ¬ ({i, (⟨k, by lia⟩ : Fin (n + 4)), (⟨k + 1, by lia⟩ : Fin (n + 4)),
      (⟨k + 2, by lia⟩ : Fin (n + 4))} = Finset.univ) := fun hS ↦ by
    obtain ⟨i, hi⟩ := i
    by_cases hk : k = 0
    · subst hk
      have := Finset.mem_univ (Fin.last _ : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [Fin.zero_eta, zero_add, Fin.mk_one, mem_insert, Fin.ext_iff, Fin.val_last,
        Fin.val_zero, AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        Fin.val_one, Nat.reduceEqDiff, mem_singleton, or_self, or_false] at this
      simp only [Fin.lt_def, Fin.val_last] at hₙ
      lia
    · have := Finset.mem_univ (0 : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [mem_insert, Fin.ext_iff, Fin.val_zero, right_eq_add,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, mem_singleton,
        OfNat.ofNat_ne_zero, or_self, or_false] at this
      obtain rfl | rfl := this <;> tauto
  rw [Finset.eq_univ_iff_forall, not_forall] at hS
  obtain ⟨l, hl⟩ := hS
  simp only [mem_insert, mem_singleton, not_or] at hl
  refine ⟨l, hl.1, fun a ↦ ?_⟩
  fin_cases a
  · exact Ne.symm hl.2.1
  · exact Ne.symm hl.2.2.1
  · exact Ne.symm hl.2.2.2

/-- The `j`th face of codimension `1` of the `i`-th horn. -/
/-
**SSet.horn.face** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：face {n : Nat} (i j : Fin (n + 2)) (h : j != i) : (Λ[n + 1, i] : SSet.{u})
 _⦋n⦌
参数：i j : Fin (n + 2)；h : j != i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `j`th face of codimension `1` of the `i`-th horn.
-/
def face {n : ℕ} (i j : Fin (n + 2)) (h : j ≠ i) : (Λ[n + 1, i] : SSet.{u}) _⦋n⦌ :=
  yonedaEquiv (Subfunctor.lift (stdSimplex.δ j) (by
    simpa using face_le_horn _ _ h))

/-- Two morphisms from a horn are equal if they are equal on all suitable faces. -/
protected
/-
**SSet.horn.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
形式化陈述：hom_ext {n : Nat} {i : Fin (n + 2)} {S : SSet} (σ₁ σ₂ : (Λ[n + 1, i] : SSe
t.{u}) ⟶ S) (h : forall (j) (h : j != i), σ₁.app _ (face i j h) = σ₂.app _ (face
 i j h)) : σ₁ = σ₂
参数：n + 2；σ₁ σ₂ : (Λ[n + 1, i] : SSet.{u}) ⟶ S；h : forall (j) (h : j != i), σ₁.ap
p _ (face i j h) = σ₂.app _ (face i j h)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Subfunctor.equalizer_eq_iff`：equalizer_eq_iff : Subfuncto
r.equalizer f g = A ↔ f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.Subfunctor.equalizer_le`：equalizer_le : Subfunctor.equali
zer f g <= A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.horn_eq_iSup`：horn_eq_iSup (n : Nat) (i : Fin (n + 1)) : horn.{u} n
 i = ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Subfunctor.mem_equalizer_iff`：mem_equalizer_iff {i : C} (
x : A.toFunctor.obj i) : x.1 in (Subfunctor.equalizer f g).obj i ↔ f.app i x = g
.app i x
-/
lemma hom_ext {n : ℕ} {i : Fin (n + 2)} {S : SSet} (σ₁ σ₂ : (Λ[n + 1, i] : SSet.{u}) ⟶ S)
    (h : ∀ (j) (h : j ≠ i), σ₁.app _ (face i j h) = σ₂.app _ (face i j h)) :
    σ₁ = σ₂ := by
  rw [← Subfunctor.equalizer_eq_iff]
  apply le_antisymm (Subfunctor.equalizer_le σ₁ σ₂)
  simp only [horn_eq_iSup, iSup_le_iff,
    Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff,
    ← stdSimplex.ofSimplex_yonedaEquiv_δ, Subcomplex.ofSimplex_le_iff]
  intro j hj
  exact (Subfunctor.mem_equalizer_iff σ₁ σ₂ (face i j hj)).2 (by apply h)


/-- Given `i` and `j` in `Fin (n + 1)` such that `j ≠ i`, this is
the inclusion of `stdSimplex.face {j}ᶜ` in the horn `horn n i`. -/
/-
**SSet.horn.face** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：face {n : Nat} (i j : Fin (n + 2)) (h : j != i) : (Λ[n + 1, i] : SSet.{u})
 _⦋n⦌
参数：i j : Fin (n + 2)；h : j != i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `i` and `j` in `Fin (n + 1)` such that `j ≠ i`, this is
the inclusion of `stdSimplex.face {j}ᶜ` in the horn `horn n i`.
-/
def faceι {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j ≠ i) :
    (stdSimplex.face {j}ᶜ : SSet.{u}) ⟶ (Λ[n, i] : SSet.{u}) :=
  Subcomplex.homOfLE (face_le_horn j i hij)

@[reassoc (attr := simp)]
/-
**SSet.horn.face** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
形式化陈述：face {n : Nat} (i j : Fin (n + 2)) (h : j != i) : (Λ[n + 1, i] : SSet.{u})
 _⦋n⦌
参数：i j : Fin (n + 2)；h : j != i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma faceι_ι {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j ≠ i) :
    faceι i j hij ≫ Λ[n, i].ι = (stdSimplex.face {j}ᶜ).ι := by
  simp [faceι]

/-- Given `i` and `j` in `Fin (n + 2)` such that `j ≠ i`, this is the inclusion
of `Δ[n]` in `horn (n + 1) i` given by `stdSimplex.δ j`. -/
/-
**SSet.horn.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.horn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `i` and `j` in `Fin (n + 2)` such that `j ≠ i`, this is the inclusion
of `Δ[n]` in `horn (n + 1) i` given by `stdSimplex.δ j`.
-/
def ι {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    Δ[n] ⟶ (Λ[n + 1, i] : SSet.{u}) :=
  yonedaEquiv.symm (face i j hij)
/-
**SSet.horn.yonedaEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaEquiv_ι {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    yonedaEquiv (ι i j hij) = face i j hij := by
  rw [ι, Equiv.apply_symm_apply]

@[reassoc (attr := simp)]
/-
**SSet.horn.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_ι {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    ι i j hij ≫ Λ[n + 1, i].ι =
      stdSimplex.{u}.δ j := by
  rw [ι, face, Equiv.symm_apply_apply, Subfunctor.lift_ι]

@[reassoc (attr := simp)]
/-
**SSet.horn.faceSingletonComplIso_inv_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.horn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma faceSingletonComplIso_inv_ι {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    (stdSimplex.faceSingletonComplIso.{u} j).inv ≫ ι i j hij = faceι i j hij := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} j).hom, Iso.hom_inv_id_assoc]
  rfl

end horn

end SSet

