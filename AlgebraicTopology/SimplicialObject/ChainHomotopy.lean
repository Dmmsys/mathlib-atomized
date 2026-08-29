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

/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: (p q : Nat)
  body: if h : p + 1 = q then
    -∑ k : Fin (p + 1), ((-1 : Int) ^ (k : Nat)) • H.h k ≫ eqToHom (by simp [h])
  else 0

@[simp]

中文:
定义 hom
  签名: (p q : 自然数)
  定义体: if h : p + 1 = q then
    -∑ k : Fin (p + 1), ((-1 : Int) ^ (k : Nat)) • H.h k ≫ eqToHom (by simp [h])
  else 0

@[simp]

Depends on / 依赖: eqToHom
-/
noncomputable def hom (p q : Nat) : X _⦋p⦌ ⟶ Y _⦋q⦌ :=
  if h : p + 1 = q then
    -∑ k : Fin (p + 1), ((-1 : Int) ^ (k : Nat)) • H.h k ≫ eqToHom (by simp [h])
  else 0

@[simp]
/--
lemma `hom_eq` / 引理 `hom_eq`

English:
lemma hom_eq
  given: (p : Nat)
  proof: by
  simp [hom]

@[simp]

中文:
引理 hom_eq
  条件: (p : 自然数)
  证明: by
  simp [hom]

@[simp]
-/
lemma hom_eq (p : Nat) :
    hom H p (p + 1) = -∑ k : Fin (p + 1), ((-1 : Int) ^ (k : Nat)) • H.h k := by
  simp [hom]

@[simp]
/--
lemma `hom_eq_zero` / 引理 `hom_eq_zero`

English:
lemma hom_eq_zero
  given: (p q : Nat) (hpq : p + 1 != q)
  proof: dif_neg hpq

中文:
引理 hom_eq_zero
  条件: (p q : 自然数) (hpq : p + 1 != q)
  证明: dif_neg hpq

Depends on / 依赖: dif_neg
-/
lemma hom_eq_zero (p q : Nat) (hpq : p + 1 != q) :
    hom H p q = 0 :=
  dif_neg hpq

/--
lemma `comm_zero` / 引理 `comm_zero`

English:
lemma comm_zero
  proof: ((alternatingFaceMapComplex C).obj Y).d 1 0
    f.app (op ⦋0⦌) = hom H 0 1 ≫ d + g.app (op ⦋0⦌) := by
  simp [← H.h_last_comp_δ_last 0]

中文:
引理 comm_zero
  证明: ((alternatingFaceMapComplex C).obj Y).d 1 0
    f.app (op ⦋0⦌) = hom H 0 1 ≫ d + g.app (op ⦋0⦌) := by
  simp [← H.h_last_comp_δ_last 0]
-/
private lemma comm_zero :
    letI d : Y _⦋1⦌ ⟶ Y _⦋0⦌ := ((alternatingFaceMapComplex C).obj Y).d 1 0
    f.app (op ⦋0⦌) = hom H 0 1 ≫ d + g.app (op ⦋0⦌) := by
  simp [← H.h_last_comp_δ_last 0]

/--
lemma `comm_succ` / 引理 `comm_succ`

English:
lemma comm_succ
  given: (n : Nat)
  proof: ((alternatingFaceMapComplex C).obj X).d (n + 1) n ≫ ToChainHomotopy.hom H n (n + 1)
    letI β : X _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌ := hom H (n + 1) (n + 2) ≫
      ((alternatingFaceMapComplex C).obj Y).d (n + 2) (n + 1)
    f.app (op ⦋n + 1⦌) = α + β + g.app (op ⦋n + 1⦌) := by
  rw [← H.h_zero_comp_δ_zero]; r

中文:
引理 comm_succ
  条件: (n : 自然数)
  证明: ((alternatingFaceMapComplex C).obj X).d (n + 1) n ≫ ToChainHomotopy.hom H n (n + 1)
    letI β : X _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌ := hom H (n + 1) (n + 2) ≫
      ((alternatingFaceMapComplex C).obj Y).d (n + 2) (n + 1)
    f.app (op ⦋n + 1⦌) = α + β + g.app (op ⦋n + 1⦌) := by
  rw [← H.h_zero_comp_δ_zero]; r
-/
private lemma comm_succ (n : Nat) :
    letI α : X _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌ :=
      ((alternatingFaceMapComplex C).obj X).d (n + 1) n ≫ ToChainHomotopy.hom H n (n + 1)
    letI β : X _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌ := hom H (n + 1) (n + 2) ≫
      ((alternatingFaceMapComplex C).obj Y).d (n + 2) (n + 1)
    f.app (op ⦋n + 1⦌) = α + β + g.app (op ⦋n + 1⦌) := by
  rw [← H.h_zero_comp_δ_zero]; rw [← H.h_last_comp_δ_last]
  dsimp
  simp only [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, hom_eq,
    Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    smul_neg, Finset.sum_neg_distrib, ← Finset.sum_zsmul, smul_smul, ← pow_add]
  let α (x : Fin (n + 1) × Fin (n + 2)) := (-1) ^ ((x.1 + x.2 : Nat)) • X.δ x.2 ≫ H.h x.1
  let β (x : Fin (n + 3) × Fin (n + 2)) := (-1) ^ ((x.1 + x.2 : Nat)) • H.h x.2 ≫ Y.δ x.1
  have h₂ (x : Fin (n + 1) × Fin (n + 2)) (hx : x.1.castSucc < x.2) :
      α x = -β ⟨x.2.succ, x.1.castSucc⟩ := by
    dsimp [α, β]
    simp only [← H.h_castSucc_comp_δ_succ_of_lt x.2 x.1 hx,
      pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  rw [← Finset.sum_product .univ .univ α]; rw [← Finset.sum_product .univ .univ β]; rw [Finset.univ_product_univ]; rw [Finset.univ_product_univ]
  let S : Finset (Fin (n + 1) × Fin (n + 2)) := { x | x.1.castSucc < x.2 }
  let γ₁ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.castSucc, x.1.succ)
  let γ₂ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.succ, x.1.castSucc)
  let γ₃ (i : Fin (n + 1)) := (i.castSucc.succ, i.succ)
  let γ₄ (i : Fin (n + 1)) := (i.castSucc.succ, i.castSucc)
  have hγ₁ : Function.Injective γ₁ := fun _ _ => by aesop
  have hγ₂ : Function.Injective γ₂ := fun _ _ => by aesop
  have hγ₃ : Function.Injective γ₃ := fun _ _ => by aesop
  have hγ₄ : Function.Injective γ₄ := fun _ _ => by aesop
  have eq₁ : H.h 0 ≫ Y.δ 0 = β ⟨0, 0⟩ := by simp [β]
  have eq₂ : H.h (Fin.last _) ≫ Y.δ (Fin.last _) = - β ⟨Fin.last _, Fin.last _⟩ := by
    dsimp [β]
    simp only [pow_add, even_two, Even.neg_pow, one_pow, mul_one,
      pow_one, mul_neg, neg_smul, neg_neg]
    rw [← pow_add]; rw [(Even.add_self n).neg_one_pow]; rw [one_smul]
  have eq₃ : ∑ x in Sᶜ, α x = - ∑ y in Finset.image γ₁ Sᶜ, β y := by
    rw [← Finset.sum_neg_distrib]; rw [Finset.sum_image hγ₁.injOn]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    dsimp [α, β, γ₁]
    simp only [← H.h_succ_comp_δ_castSucc_of_lt x.2 x.1 (by simpa [S] using hx),
      pow_add, pow_one, mul_neg, mul_one, neg_smul, neg_neg]
    rw [mul_comm]
  have eq₄ : ∑ x in S, α x = - ∑ y in Finset.image γ₂ S, β y := by
    rw [← Finset.sum_neg_distrib]; rw [Finset.sum_image hγ₂.injOn]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    dsimp [α, β, γ₂]
    simp only [← H.h_castSucc_comp_δ_succ_of_lt x.2 x.1 (by simpa [S] using hx),
      pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  have eq₅ : ∑ x, β (γ₄ x) = - ∑ x, β (γ₃ x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x hx => by simp [h_succ_comp_δ_castSucc_succ, β, γ₃, γ₄])
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
      rw [Finset.card_disjUnion]; rw [Finset.card_disjUnion]; rw [Finset.card_disjUnion]; rw [Finset.card_image_of_injective _ hγ₁]; rw [Finset.card_image_of_injective _ hγ₂]; rw [Finset.card_image_of_injective _ hγ₃]; rw [Finset.card_image_of_injective _ hγ₄]
      simp
      lia)
  rw [eq₁]; rw [eq₂]; rw [← S.sum_add_sum_compl]; rw [eq₃]; rw [eq₄]; rw [neg_add_rev]; rw [neg_neg]; rw [neg_neg]; rw [← Finset.sum_disjUnion h₁]; rw [← (Finset.disjUnion _ _ h₁).sum_add_sum_compl]; rw [neg_add]; rw [← add_assoc]; rw [add_neg_cancel]; rw [zero_add]; rw [H]; rw [Finset.sum_disjUnion]; rw [Finset.sum_disjUnion]; rw [Finset.sum_image hγ₃.injOn]; rw [Finset.sum_image hγ₄.injOn]; rw [Finset.sum_insert (by simp)]; rw [Finset.sum_singleton]; rw [neg_add_rev]; rw [neg_add_rev]; rw [neg_add_rev]; rw [eq₅]
  simp

end ToChainHomotopy

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toChainHomotopy` / `toChainHomotopy` 的定义

English:
definition toChainHomotopy
  signature: (H : Homotopy f g)
  body: ToChainHomotopy.hom H
  zero i j hij := ToChainHomotopy.hom_eq_zero _ _ _ hij
  comm n := by
    cases n with
    | zero =>
      rw [prevD_eq (j' := 1) (w := by simp)]; rw [dNext_eq_zero _ _ (by simp)]; rw [zero_add]
      simp [ToChainHomotopy.comm_zero H]
    | succ n =>
      rw [dNext_eq (i' :=

中文:
定义 toChainHomotopy
  签名: (H : 同伦 f g)
  定义体: ToChainHomotopy.hom H
  zero i j hij := ToChainHomotopy.hom_eq_zero _ _ _ hij
  comm n := by
    cases n with
    | zero =>
      rw [prevD_eq (j' := 1) (w := by simp)]; rw [dNext_eq_zero _ _ (by simp)]; rw [zero_add]
      simp [ToChainHomotopy.comm_zero H]
    | succ n =>
      rw [dNext_eq (i' :=

Depends on / 依赖: ToChainHomotopy, ToChainHomotopy.hom
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
      rw [prevD_eq (j' := 1) (w := by simp)]; rw [dNext_eq_zero _ _ (by simp)]; rw [zero_add]
      simp [ToChainHomotopy.comm_zero H]
    | succ n =>
      rw [dNext_eq (i' := n) (w := by simp)]; rw [prevD_eq (j' := n + 2) (w := by simp)]
      simp [ToChainHomotopy.comm_succ H]

/--
theorem `map_homology_eq` / 定理 `map_homology_eq`

English:
theorem map_homology_eq
  given: [CategoryWithHomology C] (H : Homotopy f g) (n : Nat)
  proof: by
  simpa using! (H.toChainHomotopy).homologyMap_eq n

中文:
定理 map_homology_eq
  条件: [带同调范畴 C] (H : 同伦 f g) (n : 自然数)
  证明: by
  simpa using! (H.toChainHomotopy).homologyMap_eq n

Depends on / 依赖: H.toChainHomotopy, homologyMap_eq, toChainHomotopy
-/
theorem map_homology_eq [CategoryWithHomology C] (H : Homotopy f g) (n : Nat) :
    (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map f) =
    (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map g) := by
  simpa using! (H.toChainHomotopy).homologyMap_eq n

end CategoryTheory.SimplicialObject.Homotopy
