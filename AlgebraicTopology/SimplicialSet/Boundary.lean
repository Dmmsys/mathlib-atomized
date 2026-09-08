/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# The boundary of the standard simplex

We introduce the boundary `∂Δ[n]` of the standard simplex `Δ[n]`.
(These notations become available by doing `open Simplicial`.)

## Future work

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order-preserving function `Fin n → Fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.


-/

@[expose] public section

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `stdSimplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
/-
**SSet.boundary** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：boundary (n : Nat) : (Δ[n] : SSet.{u}).Subcomplex where obj _
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `stdSimplex n` that are not surjective
(when viewed as monotone function `m → n`).
-/
def boundary (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ := Set.ofPred (fun s ↦ ¬Function.Surjective (stdSimplex.asOrderHom s))
  map _ _ hs h := hs (Function.Surjective.of_comp h)

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex -/
scoped[Simplicial] notation3 "∂Δ[" n "]" => SSet.boundary n

/-
**SSet.boundary_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：boundary_eq_iSup (n : Nat) : boundary.{u} n = ⨆ (i : Fin (n + 1)), stdSimp
lex.face {i}ᶜ
参数：n : Nat。
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
· 使用定理 `CategoryTheory.Subfunctor.mk.congr_simp`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (obj obj_1 :
 (U : C) → Set (F.obj U)) (e_…
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `SSet.stdSimplex.face_obj`：∀ {n : ℕ} (S : Finset (Fin (n + 1))) (U : Simp
lexCategoryᵒᵖ),   (SSet.stdSimplex.face S).obj U =     {f | Finset.image ⇑(Simpl
exCategory.Hom…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma boundary_eq_iSup (n : ℕ) :
    boundary.{u} n = ⨆ (i : Fin (n + 1)), stdSimplex.face {i}ᶜ := by
  ext
  simp [stdSimplex.face_obj, boundary, Function.Surjective]
  tauto
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : HasDimensionLT (boundary n) n := by
  rw [boundary_eq_iSup, hasDimensionLT_iSup_iff]
  intro i
  exact stdSimplex.hasDimensionLT_face _ _ (by simp [Finset.card_compl])
/-
**SSet.mem_boundary_iff_notMem_range** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：mem_boundary_iff_notMem_range {n d : Nat} (s : Δ[n] _⦋d⦌) : s in (boundary
 n).obj _ ↔ exists (j : Fin (n + 1)), j ∉ Set.range s
参数：s : Δ[n] _⦋d⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.boundary_eq_iSup`：boundary_eq_iSup (n : Nat) : boundary.{u} n = ⨆ (
i : Fin (n + 1)), stdSimplex.face {i}ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_boundary_iff_notMem_range {n d : ℕ} (s : Δ[n] _⦋d⦌) :
    s ∈ (boundary n).obj _ ↔ ∃ (j : Fin (n + 1)), j ∉ Set.range s := by
  rw [boundary_eq_iSup]
  simp
/-
**SSet.face_singleton_compl_le_boundary** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：face_singleton_compl_le_boundary {n : Nat} (i : Fin (n + 1)) : stdSimplex.
face.{u} {i}ᶜ <= boundary n
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.boundary_eq_iSup`：boundary_eq_iSup (n : Nat) : boundary.{u} n = ⨆ (
i : Fin (n + 1)), stdSimplex.face {i}ᶜ
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma face_singleton_compl_le_boundary {n : ℕ} (i : Fin (n + 1)) :
    stdSimplex.face.{u} {i}ᶜ ≤ boundary n := by
  rw [boundary_eq_iSup]
  exact le_iSup (fun (i : Fin (n +1)) ↦ stdSimplex.face {i}ᶜ) i
/-
**SSet.stdSimplex.notMem_boundary** 是 Mathlib 中的一个定理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：∀ (n : ℕ), SSet.stdSimplex.objMk OrderHom.id ∉ (SSet.boundary n).obj (Oppo
site.op { len := n })
参数：n : ℕ；SSet.boundary n；Opposite.op { len := n }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.boundary_eq_iSup`：boundary_eq_iSup (n : Nat) : boundary.{u} n = ⨆ (
i : Fin (n + 1)), stdSimplex.face {i}ᶜ
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
-/
lemma stdSimplex.notMem_boundary (n : ℕ) :
    stdSimplex.objMk (m := op ⦋n⦌) .id ∉ (boundary.{u} n).obj (op ⦋n⦌) := by
  rw [boundary_eq_iSup, Subfunctor.iSup_obj, Set.mem_iUnion, not_exists]
  intro i hi
  simpa using @hi i (by aesop)
/-
**SSet.boundary_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：boundary_lt_top (n : Nat) : boundary.{u} n < ⊤
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SSet.stdSimplex.notMem_boundary`：∀ (n : ℕ), SSet.stdSimplex.objMk OrderH
om.id ∉ (SSet.boundary n).obj (Opposite.op { len := n })
-/
lemma boundary_lt_top (n : ℕ) :
    boundary.{u} n < ⊤ :=
  lt_of_le_not_ge (by simp) (fun h ↦ stdSimplex.notMem_boundary n (h _ (by simp)))
/-
**SSet.boundary_obj_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：boundary_obj_eq_univ (m n : Nat) (h : m < n
参数：m n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `SimplexCategory.eq_comp_δ_of_not_surjective`：eq_comp_δ_of_not_surjective
 {n : Nat} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌) (hθ : ¬Function.Surjective θ.
toOrderHom) : exists (i : Fin (n …
· 使用定理 `SimplexCategory.len_le_of_epi`：len_le_of_epi {x y : SimplexCategory} (f 
: x ⟶ y) [Epi f] : y.len <= x.len
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimplexCategory.epi_iff_surjective`：epi_iff_surjective {n m : SimplexCat
egory} {f : n ⟶ m} : Epi f ↔ Function.Surjective f.toOrderHom
· 使用引理 `SSet.face_singleton_compl_le_boundary`：face_singleton_compl_le_boundary 
{n : Nat} (i : Fin (n + 1)) : stdSimplex.face.{u} {i}ᶜ <= boundary n
· 使用引理 `SSet.stdSimplex.face_singleton_compl`：face_singleton_compl {n : Nat} (i 
: Fin (n + 2)) : face.{u} {i}ᶜ = Subcomplex.ofSimplex (objEquiv.symm (SimplexCat
egory.δ i))
· 使用引理 `SSet.stdSimplex.objEquiv_symm_comp`：objEquiv_symm_comp {n n' : SimplexCa
tegory} {m : SimplexCategoryᵒᵖ} (f : m.unop ⟶ n) (g : n ⟶ n') : objEquiv.{u}.sym
m (f ≫ g) = (stdSimplex.…
· 使用引理 `SSet.Subcomplex.ofSimplex_le_iff`：ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌
) (A : X.Subcomplex) : ofSimplex x <= A ↔ x in A.obj _
· 使用引理 `SSet.Subcomplex.ofSimplex_map_le`：ofSimplex_map_le {X : SSet.{u}} {n m :
 Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) (x : X _⦋m⦌) : ofSimplex (X.map f.op x) <= ofSimplex x
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
lemma boundary_obj_eq_univ (m n : ℕ) (h : m < n := by lia) :
    (boundary.{u} n).obj (op ⦋m⦌) = .univ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  simp only [Set.mem_univ, iff_true]
  obtain _ | n := n
  · simp at h
  · obtain ⟨i, q, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f (fun hf ↦ by
      rw [← SimplexCategory.epi_iff_surjective] at hf
      have : n + 1 ≤ m := SimplexCategory.len_le_of_epi f
      lia)
    apply face_singleton_compl_le_boundary i
    rw [stdSimplex.face_singleton_compl, stdSimplex.objEquiv_symm_comp,
      ← Subcomplex.ofSimplex_le_iff]
    apply Subcomplex.ofSimplex_map_le

@[simp]
/-
**SSet.boundary_zero** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：boundary_zero : boundary.{u} 0 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
-/
lemma boundary_zero : boundary.{u} 0 = ⊥ := by
  ext m x
  simp only [boundary, Nat.reduceAdd, Set.mem_ofPred_eq, Subfunctor.bot_obj, Set.bot_eq_empty,
    Set.mem_empty_iff_false, iff_false, Decidable.not_not]
  intro x
  exact ⟨0, by subsingleton⟩
/-
**SSet.op_boundary** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：op_boundary (n : Nat) : ∂Δ[n].op.preimage (stdSimplex.opIso.{u} ⦋n⦌).inv =
 ∂Δ[n]
参数：n : Nat。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma op_boundary (n : ℕ) :
    ∂Δ[n].op.preimage (stdSimplex.opIso.{u} ⦋n⦌).inv = ∂Δ[n] := by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_boundary_iff_notMem_range, Set.mem_range,
    stdSimplex.opObjEquiv_opObjEquiv_symm_apply, not_exists]
  constructor
  all_goals
  · rintro ⟨k, hk⟩
    exact ⟨k.rev, fun l _ ↦ hk l.rev (by aesop)⟩

namespace stdSimplex

variable {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.stdSimplex.subcomplex_hasDimensionLT_of_neq_top** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.stdSimplex`。
形式化陈述：subcomplex_hasDimensionLT_of_neq_top (h : A != ⊤) : HasDimensionLT A n whe
re degenerate_eq_top i hi
参数：h : A != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.mem_degenerate_iff`：mem_degenerate_iff {n : Nat} (x : A.
obj (op ⦋n⦌)) : dsimp% x in degenerate A n ↔ x.val in X.degenerate n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.degenerate_eq_univ_of_hasDimensionLT`：degenerate_eq_univ_of_hasDime
nsionLT (hn : d <= n
· 使用定理 `SSet.stdSimplex.instHasDimensionLEObjSimplexCategoryMk`：∀ (n : ℕ), (SSet
.stdSimplex.obj { len := n }).HasDimensionLE n
· 使用引理 `SSet.mem_degenerate_iff_notMem_nonDegenerate`：mem_degenerate_iff_notMem_
nonDegenerate (x : X _⦋n⦌) : x in X.degenerate n ↔ x ∉ X.nonDegenerate n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `SSet.stdSimplex.nonDegenerate_top_dim`：nonDegenerate_top_dim (n : Nat) :
 (Δ[n] : SSet.{u}).nonDegenerate n = {(objEquiv (m
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma subcomplex_hasDimensionLT_of_neq_top (h : A ≠ ⊤) :
    HasDimensionLT A n where
  degenerate_eq_top i hi := by
    ext ⟨a, ha⟩
    rw [A.mem_degenerate_iff]
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain hi | rfl := hi.lt_or_eq
    · simp [Δ[n].degenerate_eq_univ_of_hasDimensionLT (n + 1) i]
    · rw [mem_degenerate_iff_notMem_nonDegenerate, nonDegenerate_top_dim]
      rintro rfl
      exact h (le_antisymm (by simp) (by simpa [← ofSimplex_objEquiv_symm_id]))

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.stdSimplex.le_boundary_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：le_boundary_iff : A <= boundary.{u} n ↔ A != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `SSet.boundary_lt_top`：boundary_lt_top (n : Nat) : boundary.{u} n < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.stdSimplex.subcomplex_hasDimensionLT_of_neq_top`：subcomplex_hasDime
nsionLT_of_neq_top (h : A != ⊤) : HasDimensionLT A n where degenerate_eq_top i h
i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.le_iff_contains_nonDegenerate`：le_iff_contains_nonDegene
rate (B : X.Subcomplex) : A <= B ↔ forall (n : Nat) (x : X.nonDegenerate n), x.v
al in A.obj _ -> x.val in B.obj _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.boundary_obj_eq_univ`：boundary_obj_eq_univ (m n : Nat) (h : m < n
· 使用引理 `SSet.Subcomplex.mem_nonDegenerate_iff`：mem_nonDegenerate_iff {n : Nat} (
x : A.obj (op ⦋n⦌)) : dsimp% x in nonDegenerate A n ↔ x.val in X.nonDegenerate n
· 使用引理 `SSet.nonDegenerate_eq_empty_of_hasDimensionLT`：nonDegenerate_eq_empty_of
_hasDimensionLT (hn : d <= n
-/
lemma le_boundary_iff :
    A ≤ boundary.{u} n ↔ A ≠ ⊤ := by
  refine ⟨fun h ↦ ?_, fun hA ↦ ?_⟩
  · rintro rfl
    exact lt_irrefl _ (lt_of_le_of_lt h (boundary_lt_top n))
  · have := subcomplex_hasDimensionLT_of_neq_top A hA
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro m ⟨x, h₁⟩ h₂
    dsimp at h₂ ⊢
    by_cases! h₃ : m < n
    · simp [boundary_obj_eq_univ m n h₃]
    · simp [← A.mem_nonDegenerate_iff ⟨x, h₂⟩,
        nonDegenerate_eq_empty_of_hasDimensionLT _ _ _ h₃] at h₁
/-
**SSet.stdSimplex.eq_boundary_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：eq_boundary_iff : A = boundary n ↔ boundary n <= A ∧ A != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `SSet.boundary_lt_top`：boundary_lt_top (n : Nat) : boundary.{u} n < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.le_boundary_iff`：le_boundary_iff : A <= boundary.{u} n ↔
 A != ⊤
-/
lemma eq_boundary_iff :
    A = boundary n ↔ boundary n ≤ A ∧ A ≠ ⊤ := by
  constructor
  · rintro rfl
    exact ⟨by rfl, (boundary_lt_top n).ne⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (by rwa [le_boundary_iff]) h₁

end stdSimplex

namespace boundary

/-- The inclusion of a face of `∂Δ[n]`. -/
/-
**SSet.boundary.face** 是 Mathlib 中的一个定义，位于命名空间 `SSet.boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a face of `∂Δ[n]`.
-/
def faceι {n : ℕ} (i : Fin (n + 1)) :
    (stdSimplex.face {i}ᶜ : SSet.{u}) ⟶ ∂Δ[n] :=
  Subcomplex.homOfLE (face_singleton_compl_le_boundary i)
/-
**SSet.boundary.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} (i : Fin (n + 1)) : Mono (faceι.{u} i) := by
  dsimp [faceι]; infer_instance

@[reassoc (attr := simp)]
/-
**SSet.boundary.face** 是 Mathlib 中的一个引理，位于命名空间 `SSet.boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma faceι_ι {n : ℕ} (i : Fin (n + 2)) :
    faceι i ≫ (boundary.{u} (n + 1)).ι = (stdSimplex.face {i}ᶜ).ι := by
  simp [faceι]

/-- The morphism `Δ[n] ⟶ ∂Δ[n + 1]` corresponding to face
the face `i : Fin (n + 2)`. -/
/-
**SSet.boundary.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `Δ[n] ⟶ ∂Δ[n + 1]` corresponding to face
the face `i : Fin (n + 2)`.
-/
def ι {n : ℕ} (i : Fin (n + 2)) :
    Δ[n] ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subcomplex.lift ((stdSimplex.{u}.map (SimplexCategory.δ i))) (by
    simp only [Subcomplex.range_eq_ofSimplex]
    refine le_trans ?_ (face_singleton_compl_le_boundary i)
    rw [stdSimplex.face_singleton_compl, yonedaEquiv_map])

@[reassoc (attr := simp)]
/-
**SSet.boundary.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_ι {n : ℕ} (i : Fin (n + 2)) :
    ι.{u} i ≫ ∂Δ[n + 1].ι = stdSimplex.δ i := rfl

@[reassoc (attr := simp)]
/-
**SSet.boundary.faceSingletonComplIso_inv_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.bound
ary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma faceSingletonComplIso_inv_ι {n : ℕ} (i : Fin (n + 2)) :
    (stdSimplex.faceSingletonComplIso i).inv ≫ ι i = boundary.faceι i := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso i).hom, Iso.hom_inv_id_assoc]
  rfl
/-
**SSet.boundary.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} (i : Fin (n + 2)) : Mono (ι.{u} i) := by
  rw [← mono_comp_iff_of_isIso (stdSimplex.faceSingletonComplIso i).inv,
    faceSingletonComplIso_inv_ι]
  infer_instance
/-
**SSet.boundary.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.boundary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} (i : Fin (n + 2)) : Mono (stdSimplex.{u}.δ i) := by
  rw [← ι_ι]
  infer_instance
/-
**SSet.boundary.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.boundary`。
形式化陈述：hom_ext {n : Nat} {X : SSet.{u}} {f g : (∂Δ[n + 1] : SSet) ⟶ X} (h : foral
l (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g) : f = g
参数：∂Δ[n + 1] : SSet；h : forall (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hom_ext`：hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : forall n, f.app n 
= g.app n) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SSet.boundary_eq_iSup`：boundary_eq_iSup (n : Nat) : boundary.{u} n = ⨆ (
i : Fin (n + 1)), stdSimplex.face {i}ᶜ
· 使用引理 `SSet.stdSimplex.face_singleton_compl`：face_singleton_compl {n : Nat} (i 
: Fin (n + 2)) : face.{u} {i}ᶜ = Subcomplex.ofSimplex (objEquiv.symm (SimplexCat
egory.δ i))
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
-/
lemma hom_ext {n : ℕ} {X : SSet.{u}} {f g : (∂Δ[n + 1] : SSet) ⟶ X}
    (h : ∀ (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g) :
    f = g := by
  ext m ⟨x, hx⟩
  simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff, op_unop] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact ConcreteCategory.congr_hom (congr_app (h i) _) _

@[ext]
/-
**SSet.boundary.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.boundary`。
形式化陈述：hom_ext {n : Nat} {X : SSet.{u}} {f g : (∂Δ[n + 1] : SSet) ⟶ X} (h : foral
l (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g) : f = g
参数：∂Δ[n + 1] : SSet；h : forall (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hom_ext`：hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : forall n, f.app n 
= g.app n) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SSet.boundary_eq_iSup`：boundary_eq_iSup (n : Nat) : boundary.{u} n = ⨆ (
i : Fin (n + 1)), stdSimplex.face {i}ᶜ
· 使用引理 `SSet.stdSimplex.face_singleton_compl`：face_singleton_compl {n : Nat} (i 
: Fin (n + 2)) : face.{u} {i}ᶜ = Subcomplex.ofSimplex (objEquiv.symm (SimplexCat
egory.δ i))
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
-/
lemma hom_ext₀ {X : SSet.{u}} {f g : (∂Δ[0] : SSet) ⟶ X} : f = g := by
  ext _ ⟨x, hx⟩
  simp at hx

end boundary

end SSet

