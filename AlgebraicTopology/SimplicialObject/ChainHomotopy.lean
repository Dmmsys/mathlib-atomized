/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Simplicial homotopies induce chain homotopies

Given a simplicial homotopy between morphisms of simplicial objects in a preadditive category,
we construct a chain homotopy between the induced morphisms on the alternating face map complexes.

Concretely, if `H : Homotopy f g` gives maps
`H.h i : X _⦋n⦌ ⟶ Y _⦋n+1⦌` indexed by `i : Fin (n + 1)`, we define the degree-`n` component
of the chain homotopy as the opposite of alternating sum `∑ i, (-1)^i • H.h i`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialObject
open SimplexCategory Simplicial Opposite AlgebraicTopology

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SimplicialObject C} {f g : X ⟶ Y}
variable (H : Homotopy f g)

namespace ToChainHomotopy

/-- The family of components of the induced chain homotopy -/
/-
**CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy`。
形式化陈述：hom (p q : Nat) : X _⦋p⦌ ⟶ Y _⦋q⦌
参数：p q : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of components of the induced chain homotopy
-/
noncomputable def hom (p q : ℕ) : X _⦋p⦌ ⟶ Y _⦋q⦌ :=
  if h : p + 1 = q then
    -∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • H.h k ≫ eqToHom (by simp [h])
  else 0

@[simp]
/-
**CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy`。
形式化陈述：hom_eq (p : Nat) : hom H p (p + 1) = -∑ k : Fin (p + 1), ((-1 : Int) ^ (k 
: Nat)) • H.h k
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma hom_eq (p : ℕ) :
    hom H p (p + 1) = -∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • H.h k := by
  simp [hom]

@[simp]
/-
**CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy`。
形式化陈述：hom_eq_zero (p q : Nat) (hpq : p + 1 != q) : hom H p q = 0
参数：p q : Nat；hpq : p + 1 != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma hom_eq_zero (p q : ℕ) (hpq : p + 1 ≠ q) :
    hom H p q = 0 :=
  dif_neg hpq
/-
**CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.comm_zero** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma comm_zero :
    letI d : Y _⦋1⦌ ⟶ Y _⦋0⦌ := ((alternatingFaceMapComplex C).obj Y).d 1 0
    f.app (op ⦋0⦌) = hom H 0 1 ≫ d + g.app (op ⦋0⦌) := by
  simp [← H.h_last_comp_δ_last 0]
/-
**CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.comm_succ** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma comm_succ (n : ℕ) :
    letI α : X _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌ :=
      ((alternatingFaceMapComplex C).obj X).d (n + 1) n ≫ ToChainHomotopy.hom H n (n + 1)
    letI β : X _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌ := hom H (n + 1) (n + 2) ≫
      ((alternatingFaceMapComplex C).obj Y).d (n + 2) (n + 1)
    f.app (op ⦋n + 1⦌) = α + β + g.app (op ⦋n + 1⦌) := by
  rw [← H.h_zero_comp_δ_zero, ← H.h_last_comp_δ_last]
  dsimp
  simp only [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, hom_eq,
    Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    smul_neg, Finset.sum_neg_distrib, ← Finset.sum_zsmul, smul_smul, ← pow_add]
  let α (x : Fin (n + 1) × Fin (n + 2)) := (-1) ^ ((x.1 + x.2 : ℕ)) • X.δ x.2 ≫ H.h x.1
  let β (x : Fin (n + 3) × Fin (n + 2)) := (-1) ^ ((x.1 + x.2 : ℕ)) • H.h x.2 ≫ Y.δ x.1
  have h₂ (x : Fin (n + 1) × Fin (n + 2)) (hx : x.1.castSucc < x.2) :
      α x = -β ⟨x.2.succ, x.1.castSucc⟩ := by
    dsimp [α, β]
    simp only [← H.h_castSucc_comp_δ_succ_of_lt x.2 x.1 hx,
      pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  rw [← Finset.sum_product .univ .univ α, ← Finset.sum_product .univ .univ β,
    Finset.univ_product_univ, Finset.univ_product_univ]
  let S : Finset (Fin (n + 1) × Fin (n + 2)) := { x | x.1.castSucc < x.2 }
  let γ₁ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.castSucc, x.1.succ)
  let γ₂ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.succ, x.1.castSucc)
  let γ₃ (i : Fin (n + 1)) := (i.castSucc.succ, i.succ)
  let γ₄ (i : Fin (n + 1)) := (i.castSucc.succ, i.castSucc)
  have hγ₁ : Function.Injective γ₁ := fun _ _ ↦ by aesop
  have hγ₂ : Function.Injective γ₂ := fun _ _ ↦ by aesop
  have hγ₃ : Function.Injective γ₃ := fun _ _ ↦ by aesop
  have hγ₄ : Function.Injective γ₄ := fun _ _ ↦ by aesop
  have eq₁ : H.h 0 ≫ Y.δ 0 = β ⟨0, 0⟩ := by simp [β]
  have eq₂ : H.h (Fin.last _) ≫ Y.δ (Fin.last _) = - β ⟨Fin.last _, Fin.last _⟩ := by
    dsimp [β]
    simp only [pow_add, even_two, Even.neg_pow, one_pow, mul_one,
      pow_one, mul_neg, neg_smul, neg_neg]
    rw [← pow_add, (Even.add_self n).neg_one_pow, one_smul]
  have eq₃ : ∑ x ∈ Sᶜ, α x = - ∑ y ∈ Finset.image γ₁ Sᶜ, β y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hγ₁.injOn]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    dsimp [α, β, γ₁]
    simp only [← H.h_succ_comp_δ_castSucc_of_lt x.2 x.1 (by simpa [S] using hx),
      pow_add, pow_one, mul_neg, mul_one, neg_smul, neg_neg]
    rw [mul_comm]
  have eq₄ : ∑ x ∈ S, α x = - ∑ y ∈ Finset.image γ₂ S, β y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hγ₂.injOn]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    dsimp [α, β, γ₂]
    simp only [← H.h_castSucc_comp_δ_succ_of_lt x.2 x.1 (by simpa [S] using hx),
      pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  have eq₅ : ∑ x, β (γ₄ x) = - ∑ x, β (γ₃ x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x hx ↦ by simp [h_succ_comp_δ_castSucc_succ, β, γ₃, γ₄])
  have h₁ : Disjoint (Finset.image γ₁ Sᶜ) (Finset.image γ₂ S) := by
    rw [Finset.disjoint_iff_ne]
    grind [Finset.mem_compl]
  have h₂ : Disjoint (Finset.image γ₃ .univ) (Finset.image γ₄ .univ) := by
    rw [Finset.disjoint_iff_ne]
    grind
  have h₃ : Disjoint (Finset.disjUnion _ _ h₂) {(0, 0), (Fin.last _, Fin.last _)} := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.mem_insert, forall_eq_or_imp, Prod.forall]
    rintro ⟨a, _⟩ ⟨b, _⟩
    simp
    grind
  have h₄ : Disjoint (Finset.disjUnion _ _ h₁) (Finset.disjUnion _ _ h₃) := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.compl_filter, not_lt, Finset.disjUnion_eq_union, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists, ne_eq,
      Finset.mem_insert, Finset.mem_singleton, Prod.forall, Prod.mk.injEq, not_and,
      S, γ₁, γ₂, γ₃, γ₄]
    rintro ⟨a, _⟩ ⟨b, _⟩ (⟨⟨j, _⟩, ⟨k, _⟩, h₁, h₂, h₃⟩ | ⟨⟨j, _⟩, ⟨k, _⟩, h₁, h₂, h₃⟩) _ _
      ((⟨⟨i, _⟩, h₄, h₅⟩ | ⟨⟨i, _⟩, h₄, h₅⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
        simp [Fin.ext_iff] at h₁ h₂ h₃ ⊢ <;> grind
  have H : (Finset.disjUnion _ _ h₁)ᶜ = Finset.disjUnion _ _ h₃ :=
    Finset.compl_eq_of_disjoint_of_card_add_eq h₄ (by
      rw [Finset.card_disjUnion, Finset.card_disjUnion, Finset.card_disjUnion,
        Finset.card_image_of_injective _ hγ₁, Finset.card_image_of_injective _ hγ₂,
        Finset.card_image_of_injective _ hγ₃, Finset.card_image_of_injective _ hγ₄]
      simp
      lia)
  rw [eq₁, eq₂, ← S.sum_add_sum_compl, eq₃, eq₄,
    neg_add_rev, neg_neg, neg_neg, ← Finset.sum_disjUnion h₁,
    ← (Finset.disjUnion _ _ h₁).sum_add_sum_compl, neg_add,
    ← add_assoc, add_neg_cancel, zero_add, H,
    Finset.sum_disjUnion, Finset.sum_disjUnion,
    Finset.sum_image hγ₃.injOn, Finset.sum_image hγ₄.injOn,
    Finset.sum_insert (by simp), Finset.sum_singleton,
    neg_add_rev, neg_add_rev, neg_add_rev, eq₅]
  simp

end ToChainHomotopy

set_option backward.isDefEq.respectTransparency false in
/-- A simplicial homotopy between `f` and `g` induces a chain homotopy
between the induced morphisms on the alternating face map complexes. -/
/-
**CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.SimplicialObject.Homotopy`。
形式化陈述：toChainHomotopy (H : Homotopy f g) : _root_.Homotopy ((alternatingFaceMapC
omplex C).map f) ((alternatingFaceMapComplex C).map g) where hom
参数：H : Homotopy f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero`：ho
m_eq_zero (p q : Nat) (hpq : p + 1 != q) : hom H p q = 0

--- 原说明 ---
A simplicial homotopy between `f` and `g` induces a chain homotopy
between the induced morphisms on the alternating face map complexes.
-/
noncomputable def toChainHomotopy (H : Homotopy f g) :
    _root_.Homotopy
      ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g) where
  hom := ToChainHomotopy.hom H
  zero i j hij := ToChainHomotopy.hom_eq_zero _ _ _ hij
  comm n := by
    cases n with
    | zero =>
      rw [prevD_eq (j' := 1) (w := by simp), dNext_eq_zero _ _ (by simp), zero_add]
      simp [ToChainHomotopy.comm_zero H]
    | succ n =>
      rw [dNext_eq (i' := n) (w := by simp), prevD_eq (j' := n + 2) (w := by simp)]
      simp [ToChainHomotopy.comm_succ H]
/-
**CategoryTheory.SimplicialObject.Homotopy.map_homology_eq** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.SimplicialObject.Homotopy`。
形式化陈述：map_homology_eq [CategoryWithHomology C] (H : Homotopy f g) (n : Nat) : (H
omologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map 
f) = (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex 
C).map g)
参数：H : Homotopy f g；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.homologyFunctor_map`：∀ (C : Type u_1) [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} (c : Com…
· 使用引理 `Homotopy.homologyMap_eq`：Homotopy.homologyMap_eq (ho : Homotopy f g) (i 
: ι) [K.HasHomology i] [L.HasHomology i] : homologyMap f i = homologyMap g i
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
-/
theorem map_homology_eq [CategoryWithHomology C] (H : Homotopy f g) (n : ℕ) :
    (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map f) =
    (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map g) := by
  simpa using! (H.toChainHomotopy).homologyMap_eq n

end CategoryTheory.SimplicialObject.Homotopy

