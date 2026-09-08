/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Logic.Embedding.Set

/-!
# Sums of matroids

The *sum* `M` of a collection `M₁, M₂, ..` of matroids is a matroid on the disjoint union of
the ground sets of the summands, in which the independent sets are precisely the unions of
independent sets of the summands.

We can ask for such a sum both for pairs and for arbitrary indexed collections of matroids,
and we can also ask for the 'disjoint union' to be either set-theoretic or type-theoretic.
To this end, we define five separate versions of the sum construction.

## Main definitions

* For an indexed collection `M : (i : ι) → Matroid (α i)` of matroids on different types,
  `Matroid.sigma M` is the sum of the `M i`, as a matroid on the sigma type `(Σ i, α i)`.

* For an indexed collection `M : ι → Matroid α` of matroids on the same type,
  `Matroid.sum' M` is the sum of the `M i`, as a matroid on the product type `ι × α`.

* For an indexed collection `M : ι → Matroid α` of matroids on the same type, and a
  proof `h : Pairwise (Disjoint on fun i ↦ (M i).E)` that they have disjoint ground sets,
  `Matroid.disjointSigma M h` is the sum of the `M` as a `Matroid α` with ground set `⋃ i, (M i).E`.

* `Matroid.sum (M : Matroid α) (N : Matroid β)` is the sum of `M` and `N` as a matroid on `α ⊕ β`.

* If `M N : Matroid α` and `h : Disjoint M.E N.E`, then `Matroid.disjointSum M N h` is the sum
  of `M` and `N` as a `Matroid α` with ground set `M.E ∪ N.E`.

## Implementation details

We only directly define a matroid for `Matroid.sigma`. All other versions of sum are
defined indirectly, using `Matroid.sigma` and the API in `Matroid.map`.
-/

@[expose] public section

assert_not_exists Field

universe u v

open Set
namespace Matroid

section Sigma

variable {ι : Type*} {α : ι → Type*} {M : (i : ι) → Matroid (α i)}

/-- The sum of an indexed collection of matroids, as a matroid on the sigma-type. -/
/-
**Matroid.sigma** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{ι : Type u_1} → {α : ι → Type u_2} → ((i : ι) → Matroid (α i)) → Matroid 
((i : ι) × α i)
参数：(i : ι) → Matroid (α i)；(i : ι) × α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of an indexed collection of matroids, as a matroid on the sigma-type.
-/
protected def sigma (M : (i : ι) → Matroid (α i)) : Matroid ((i : ι) × α i) where
  E := univ.sigma (fun i ↦ (M i).E)
  Indep I := ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I)
  IsBase B := ∀ i, (M i).IsBase (Sigma.mk i ⁻¹' B)

  indep_iff' I := by
    refine ⟨fun h ↦ ?_, fun ⟨B, hB, hIB⟩ i ↦ (hB i).indep.subset (preimage_mono hIB)⟩
    choose Bs hBs using fun i ↦ (h i).exists_isBase_superset
    refine ⟨univ.sigma Bs, fun i ↦ by simpa using (hBs i).1, ?_⟩
    rw [← univ_sigma_preimage_mk I]
    refine sigma_mono rfl.subset fun i ↦ (hBs i).2

  exists_isBase := by
    choose B hB using fun i ↦ (M i).exists_isBase
    exact ⟨univ.sigma B, by simpa⟩

  isBase_exchange B₁ B₂ h₁ h₂ := by
    simp only [mem_sdiff, Sigma.exists, and_imp, Sigma.forall]
    intro i e he₁ he₂
    have hf_ex := (h₁ i).exchange (h₂ i) ⟨he₁, by simpa⟩
    obtain ⟨f, ⟨hf₁, hf₂⟩, hfB⟩ := hf_ex
    refine ⟨i, f, ⟨hf₁, hf₂⟩, fun j ↦ ?_⟩
    rw [← union_singleton, preimage_union, preimage_sdiff]
    obtain (rfl | hne) := eq_or_ne i j
    · simpa only [show ∀ x, {⟨i,x⟩} = Sigma.mk i '' {x} by simp,
        preimage_image_eq _ sigma_mk_injective, union_singleton]
    rw [preimage_singleton_eq_empty.2 (by simpa), preimage_singleton_eq_empty.2 (by simpa),
      sdiff_empty, union_empty]
    exact h₁ j

  maximality X _ I hI hIX := by
    choose Js hJs using
      fun i ↦ (hI i).subset_isBasis'_of_subset (preimage_mono (f := Sigma.mk i) hIX)
    use univ.sigma Js
    simp only [maximal_subset_iff', mem_univ, mk_preimage_sigma, and_imp]
    refine ⟨?_, ⟨fun i ↦ (hJs i).1.indep, ?_⟩, fun S hS hSX hJS ↦ ?_⟩
    · rw [← univ_sigma_preimage_mk I]
      exact sigma_mono rfl.subset fun i ↦ (hJs i).2
    · rw [← univ_sigma_preimage_mk X]
      exact sigma_mono rfl.subset fun i ↦ (hJs i).1.subset
    rw [← univ_sigma_preimage_mk S]
    refine sigma_mono rfl.subset fun i ↦ ?_
    rw [sigma_subset_iff] at hJS
    rw [(hJs i).1.eq_of_subset_indep (hS i) (hJS <| mem_univ i)]
    exact preimage_mono hSX

  subset_ground B hB := by
    rw [← univ_sigma_preimage_mk B]
    apply sigma_mono Subset.rfl fun i ↦ (hB i).subset_ground
/-
**Matroid.sigma_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {M : (i : ι) → Matroid (α i)} {I : Set
 ((i : ι) × α i)},   (Matroid.sigma M).Indep I ↔ ∀ (i : ι), (M i).Indep (Sigma.m
k i ⁻¹' I)
参数：i : ι；α i；(i : ι) × α i；Matroid.sigma M；i : ι；M i；Sigma.mk i ⁻¹' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sigma_indep_iff {I} :
    (Matroid.sigma M).Indep I ↔ ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I) := Iff.rfl
/-
**Matroid.sigma_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {M : (i : ι) → Matroid (α i)} {B : Set
 ((i : ι) × α i)},   (Matroid.sigma M).IsBase B ↔ ∀ (i : ι), (M i).IsBase (Sigma
.mk i ⁻¹' B)
参数：i : ι；α i；(i : ι) × α i；Matroid.sigma M；i : ι；M i；Sigma.mk i ⁻¹' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sigma_isBase_iff {B} :
    (Matroid.sigma M).IsBase B ↔ ∀ i, (M i).IsBase (Sigma.mk i ⁻¹' B) := Iff.rfl
/-
**Matroid.sigma_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {M : (i : ι) → Matroid (α i)}, (Matroi
d.sigma M).E = Set.univ.sigma fun i => (M i).E
参数：i : ι；α i；Matroid.sigma M；M i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sigma_ground_eq : (Matroid.sigma M).E = univ.sigma fun i ↦ (M i).E := rfl
/-
**Matroid.sigma_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {M : (i : ι) → Matroid (α i)} {I X : S
et ((i : ι) × α i)},   (Matroid.sigma M).IsBasis I X ↔ ∀ (i : ι), (M i).IsBasis 
(Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X)
参数：i : ι；α i；(i : ι) × α i；Matroid.sigma M；i : ι；M i；Sigma.mk i ⁻¹' I；Sigma.mk i
 ⁻¹' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `sigma_mk_preimage_image_eq_self`：sigma_mk_preimage_image_eq_self : Sigma
.mk i ⁻¹' Sigma.mk i '' s = s
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用引理 `sigma_mk_preimage_image'`：sigma_mk_preimage_image' (h : i != j) : Sigma.
mk j ⁻¹' Sigma.mk i '' s = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.preimage_union`：preimage_union {s t : Set β} : f ⁻¹' (s union t) = f
 ⁻¹' s union f ⁻¹' t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.mk_preimage_sigma`：mk_preimage_sigma (hi : i in s) : Sigma.mk i ⁻¹' 
s.sigma t = t i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
@[simp] lemma sigma_isBasis_iff {I X} :
    (Matroid.sigma M).IsBasis I X ↔ ∀ i, (M i).IsBasis (Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X) := by
  simp only [IsBasis, sigma_indep_iff, maximal_subset_iff, and_imp, and_assoc, sigma_ground_eq,
    forall_and, and_congr_right_iff]
  refine fun hI ↦ ⟨fun ⟨hIX, h, h'⟩ ↦ ⟨fun i ↦ preimage_mono hIX, fun i I₀ hI₀ hI₀X hII₀ ↦ ?_, ?_⟩,
    fun ⟨hIX, h', h''⟩ ↦ ⟨?_, ?_, ?_⟩⟩
  · refine hII₀.antisymm ?_
    specialize h (t := I ∪ Sigma.mk i '' I₀)
    simp only [preimage_union, union_subset_iff, hIX, image_subset_iff, hI₀X, and_self,
      subset_union_left, true_implies] at h
    rw [h, preimage_union, sigma_mk_preimage_image_eq_self]
    · exact subset_union_right
    intro j
    obtain (rfl | hij) := eq_or_ne i j
    · rwa [sigma_mk_preimage_image_eq_self, union_eq_self_of_subset_left hII₀]
    rw [sigma_mk_preimage_image' hij, union_empty]
    apply hI
  · exact fun i ↦ by simpa using preimage_mono (f := Sigma.mk i) h'
  · exact fun ⟨i, x⟩ hx ↦ by simpa using hIX i hx
  · refine fun J hJ hJX hIJ ↦ hIJ.antisymm fun ⟨i,x⟩ hx ↦ ?_
    simpa using (h' i (hJ i) (preimage_mono hJX) (preimage_mono hIJ)).symm.subset hx
  exact fun ⟨i,x⟩ hx ↦ by simpa using h'' i hx
/-
**Matroid.Finitary.sigma** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Finitary`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {M : (i : ι) → Matroid (α i)},   (∀ (i
 : ι), (M i).Finitary) → (Matroid.sigma M).Finitary
参数：i : ι；α i；∀ (i : ι), (M i).Finitary；Matroid.sigma M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.indep_of_forall_finite_subset_indep`：indep_of_forall_finite_subs
et_indep {M : Matroid α} [Finitary M] (I : Set α) (h : forall J, J subseteq I ->
 J.Finite -> M.Indep J) : M.Indep…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sigma_mk_preimage_image_eq_self`：sigma_mk_preimage_image_eq_self : Sigma
.mk i ⁻¹' Sigma.mk i '' s = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
lemma Finitary.sigma (h : ∀ i, (M i).Finitary) : (Matroid.sigma M).Finitary := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [sigma_indep_iff] at hI ⊢
  intro i
  apply indep_of_forall_finite_subset_indep
  intro J hJI hJ
  convert! hI (Sigma.mk i '' J) (by simpa) (hJ.image _) i
  rw [sigma_mk_preimage_image_eq_self]

end Sigma

section sum'

variable {α ι : Type*} {M : ι → Matroid α}

/-- The sum of an indexed family `M : ι → Matroid α` of matroids on the same type,
as a matroid on the product type `ι × α`. -/
/-
**Matroid.sum'** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → {ι : Type u_2} → (ι → Matroid α) → Matroid (ι × α)
参数：ι → Matroid α；ι × α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of an indexed family `M : ι → Matroid α` of matroids on the same type,
as a matroid on the product type `ι × α`.
-/
protected def sum' (M : ι → Matroid α) : Matroid (ι × α) :=
  (Matroid.sigma M).mapEquiv <| Equiv.sigmaEquivProd ι α
/-
**Matroid.sum'_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : ι → Matroid α} {I : Set (ι × α)},   (
Matroid.sum' M).Indep I ↔ ∀ (i : ι), (M i).Indep (Prod.mk i ⁻¹' I)
参数：ι × α；Matroid.sum' M；i : ι；M i；Prod.mk i ⁻¹' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sum'_indep_iff {I} :
    (Matroid.sum' M).Indep I ↔ ∀ i, (M i).Indep (Prod.mk i ⁻¹' I) := by
  simp only [Matroid.sum', mapEquiv_indep_iff, Equiv.sigmaEquivProd_symm_apply, sigma_indep_iff]
  convert! Iff.rfl
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**Matroid.sum'_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} (M : ι → Matroid α), (Matroid.sum' M).E = 
⋃ i, Prod.mk i '' (M i).E
参数：M : ι → Matroid α；Matroid.sum' M；M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sum'_ground_eq (M : ι → Matroid α) :
    (Matroid.sum' M).E = ⋃ i, Prod.mk i '' (M i).E := by
  ext
  simp [Matroid.sum']
/-
**Matroid.sum'_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : ι → Matroid α} {B : Set (ι × α)},   (
Matroid.sum' M).IsBase B ↔ ∀ (i : ι), (M i).IsBase (Prod.mk i ⁻¹' B)
参数：ι × α；Matroid.sum' M；i : ι；M i；Prod.mk i ⁻¹' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sum'_isBase_iff {B} :
    (Matroid.sum' M).IsBase B ↔ ∀ i, (M i).IsBase (Prod.mk i ⁻¹' B) := by
  simp only [Matroid.sum', mapEquiv_isBase_iff, Equiv.sigmaEquivProd_symm_apply, sigma_isBase_iff]
  convert! Iff.rfl
  ext
  simp
/-
**Matroid.sum'_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : ι → Matroid α} {I X : Set (ι × α)},  
 (Matroid.sum' M).IsBasis I X ↔ ∀ (i : ι), (M i).IsBasis (Prod.mk i ⁻¹' I) (Prod
.mk i ⁻¹' X)
参数：ι × α；Matroid.sum' M；i : ι；M i；Prod.mk i ⁻¹' I；Prod.mk i ⁻¹' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sum'_isBasis_iff {I X} :
    (Matroid.sum' M).IsBasis I X ↔ ∀ i, (M i).IsBasis (Prod.mk i ⁻¹' I) (Prod.mk i ⁻¹' X) := by
  simp only [Matroid.sum', mapEquiv_isBasis_iff, Equiv.sigmaEquivProd_symm_apply, sigma_isBasis_iff]
  convert! Iff.rfl <;>
  exact ext <| by simp
/-
**Matroid.Finitary.sum'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Finitary`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : ι → Matroid α}, (∀ (i : ι), (M i).Fin
itary) → (Matroid.sum' M).Finitary
参数：∀ (i : ι), (M i).Finitary；Matroid.sum' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Finitary.sigma`：∀ {ι : Type u_1} {α : ι → Type u_2} {M : (i : ι)
 → Matroid (α i)},   (∀ (i : ι), (M i).Finitary) → (Matroid.sigma M).Finitary
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.sum'.eq_1`：∀ {α : Type u_1} {ι : Type u_2} (M : ι → Matroid α), 
  Matroid.sum' M = (Matroid.sigma M).mapEquiv (Equiv.sigmaEquivProd ι α)
· 使用定理 `Matroid.instFinitaryMapEquiv`：∀ {α : Type u_1} {β : Type u_2} {M : Matro
id α} [M.Finitary] {f : α ≃ β}, (M.mapEquiv f).Finitary
-/
lemma Finitary.sum' (h : ∀ i, (M i).Finitary) : (Matroid.sum' M).Finitary := by
  have := Finitary.sigma h
  rw [Matroid.sum']
  infer_instance

end sum'

section disjointSigma

open scoped Function -- required for scoped `on` notation

variable {α ι : Type*} {M : ι → Matroid α}

/-- The sum of an indexed collection of matroids on `α` with pairwise disjoint ground sets,
as a matroid on `α` -/
/-
**Matroid.disjointSigma** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → {ι : Type u_2} → (M : ι → Matroid α) → Pairwise (Function
.onFun Disjoint fun i => (M i).E) → Matroid α
参数：M : ι → Matroid α；Function.onFun Disjoint fun i => (M i).E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of an indexed collection of matroids on `α` with pairwise disjoint groun
d sets,
as a matroid on `α`
-/
protected def disjointSigma (M : ι → Matroid α) (h : Pairwise (Disjoint on fun i ↦ (M i).E)) :
    Matroid α :=
  (Matroid.sigma (fun i ↦ (M i).restrictSubtype (M i).E)).mapEmbedding
    (Function.Embedding.sigmaSet h)
/-
**Matroid.disjointSigma_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : ι → Matroid α} {h : Pairwise (Functio
n.onFun Disjoint fun i => (M i).E)},   (Matroid.disjointSigma M h).E = ⋃ i, (M i
).E
参数：Function.onFun Disjoint fun i => (M i).E；Matroid.disjointSigma M h；M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
· 使用定理 `Matroid.map.congr_simp`：∀ {α : Type u_1} {β : Type u_2} (M M_1 : Matroid
 α) (e_M : M = M_1) (f f_1 : α → β) (e_f : f = f_1)   (hf : Set.InjOn f M.E), M.
map f hf = M…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Function.Embedding.sigmaSet_apply`：∀ {α : Type u_1} {ι : Type u_2} {s : 
ι → Set α} (h : Pairwise (Function.onFun Disjoint s)) (x : (i : ι) × ↑(s i)),   
(Function.Embedding.sig…
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.sigma_univ`：sigma_univ : s.sigma (fun _ => univ : forall i, Set (α i
)) = Sigma.fst ⁻¹' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjointSigma_ground_eq {h} : (Matroid.disjointSigma M h).E = ⋃ i : ι, (M i).E := by
  ext; simp [Matroid.disjointSigma, mapEmbedding, restrictSubtype]
/-
**Matroid.disjointSigma_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : ι → Matroid α} {h : Pairwise (Functio
n.onFun Disjoint fun i => (M i).E)}   {I : Set α}, (Matroid.disjointSigma M h).I
ndep I ↔ (∀ (i : ι), (M i).Indep (I ∩ (M i).E)) ∧ I ⊆ ⋃ i, (M i).E
参数：Function.onFun Disjoint fun i => (M i).E；Matroid.disjointSigma M h；∀ (i : ι),
 (M i).Indep (I ∩ (M i).E)；M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Embedding.sigmaSet_preimage`：∀ {α : Type u_1} {ι : Type u_2} {s
 : ι → Set α} (h : Pairwise (Function.onFun Disjoint s)) (i : ι) (r : Set α),   
Subtype.val '' Sigma.mk i …
· 使用定理 `Function.Embedding.sigmaSet_range`：∀ {α : Type u_1} {ι : Type u_2} {s : 
ι → Set α} (h : Pairwise (Function.onFun Disjoint s)),   Set.range ⇑(Function.Em
bedding.sigmaSet h) = ⋃…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjointSigma_indep_iff {h I} :
    (Matroid.disjointSigma M h).Indep I ↔
      (∀ i, (M i).Indep (I ∩ (M i).E)) ∧ I ⊆ ⋃ i, (M i).E := by
  simp [Matroid.disjointSigma, (Function.Embedding.sigmaSet_preimage h)]
/-
**Matroid.disjointSigma_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : ι → Matroid α} {h : Pairwise (Functio
n.onFun Disjoint fun i => (M i).E)}   {B : Set α}, (Matroid.disjointSigma M h).I
sBase B ↔ (∀ (i : ι), (M i).IsBase (B ∩ (M i).E)) ∧ B ⊆ ⋃ i, (M i).E
参数：Function.onFun Disjoint fun i => (M i).E；Matroid.disjointSigma M h；∀ (i : ι),
 (M i).IsBase (B ∩ (M i).E)；M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Embedding.sigmaSet_preimage`：∀ {α : Type u_1} {ι : Type u_2} {s
 : ι → Set α} (h : Pairwise (Function.onFun Disjoint s)) (i : ι) (r : Set α),   
Subtype.val '' Sigma.mk i …
· 使用定理 `Function.Embedding.sigmaSet_range`：∀ {α : Type u_1} {ι : Type u_2} {s : 
ι → Set α} (h : Pairwise (Function.onFun Disjoint s)),   Set.range ⇑(Function.Em
bedding.sigmaSet h) = ⋃…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjointSigma_isBase_iff {h B} :
    (Matroid.disjointSigma M h).IsBase B ↔
      (∀ i, (M i).IsBase (B ∩ (M i).E)) ∧ B ⊆ ⋃ i, (M i).E := by
  simp [Matroid.disjointSigma, (Function.Embedding.sigmaSet_preimage h)]
/-
**Matroid.disjointSigma_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : ι → Matroid α} {h : Pairwise (Functio
n.onFun Disjoint fun i => (M i).E)}   {I X : Set α},   (Matroid.disjointSigma M 
h).IsBasis I X ↔     (∀ (i : ι), (M i).IsBasis (I ∩ (M i).E) (X ∩ (M i).E)) ∧ I 
⊆ X ∧ X ⊆ ⋃ i, (M i).E
参数：Function.onFun Disjoint fun i => (M i).E；Matroid.disjointSigma M h；∀ (i : ι),
 (M i).IsBasis (I ∩ (M i).E) (X ∩ (M i).E)；M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Embedding.sigmaSet_preimage`：∀ {α : Type u_1} {ι : Type u_2} {s
 : ι → Set α} (h : Pairwise (Function.onFun Disjoint s)) (i : ι) (r : Set α),   
Subtype.val '' Sigma.mk i …
· 使用定理 `Function.Embedding.sigmaSet_range`：∀ {α : Type u_1} {ι : Type u_2} {s : 
ι → Set α} (h : Pairwise (Function.onFun Disjoint s)),   Set.range ⇑(Function.Em
bedding.sigmaSet h) = ⋃…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjointSigma_isBasis_iff {h I X} :
    (Matroid.disjointSigma M h).IsBasis I X ↔
      (∀ i, (M i).IsBasis (I ∩ (M i).E) (X ∩ (M i).E)) ∧ I ⊆ X ∧ X ⊆ ⋃ i, (M i).E := by
  simp [Matroid.disjointSigma, Function.Embedding.sigmaSet_preimage h]

end disjointSigma

section Sum

variable {α : Type u} {β : Type v} {M N : Matroid α}

/-- The sum of two matroids as a matroid on the sum type. -/
/-
**Matroid.sum** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{α : Type u} → {β : Type v} → Matroid α → Matroid β → Matroid (α ⊕ β)
参数：α ⊕ β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The sum of two matroids as a matroid on the sum type.
-/
protected def sum (M : Matroid α) (N : Matroid β) : Matroid (α ⊕ β) :=
  let S := Matroid.sigma (Bool.rec (M.mapEquiv Equiv.ulift.symm) (N.mapEquiv Equiv.ulift.symm))
  let e := Equiv.sumEquivSigmaBool (ULift.{v} α) (ULift.{u} β)
  (S.mapEquiv e.symm).mapEquiv (Equiv.sumCongr Equiv.ulift Equiv.ulift)

set_option backward.isDefEq.respectTransparency false in
/-
**Matroid.sum_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} {β : Type v} (M : Matroid α) (N : Matroid β), (M.sum N).E =
 Sum.inl '' M.E ∪ Sum.inr '' N.E
参数：M : Matroid α；N : Matroid β；M.sum N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ULift.up_down`：∀ {α : Type u} (b : ULift.{v, u} α), { down := b.down } =
 b
· 使用定理 `ULift.down_up`：∀ {α : Type u} (a : α), { down := a }.down = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `Bool.univ_eq`：univ_eq : (univ : Set Bool) = {false, true}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma sum_ground (M : Matroid α) (N : Matroid β) :
    (M.sum N).E = (.inl '' M.E) ∪ (.inr '' N.E) := by
  simp [Matroid.sum, Set.ext_iff, mapEquiv, mapEmbedding, Equiv.ulift, Equiv.sumEquivSigmaBool]

set_option backward.isDefEq.respectTransparency false in
/-
**Matroid.sum_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} {β : Type v} (M : Matroid α) (N : Matroid β) {I : Set (α ⊕ 
β)},   (M.sum N).Indep I ↔ M.Indep (Sum.inl ⁻¹' I) ∧ N.Indep (Sum.inr ⁻¹' I)
参数：M : Matroid α；N : Matroid β；α ⊕ β；M.sum N；Sum.inl ⁻¹' I；Sum.inr ⁻¹' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sum_indep_iff (M : Matroid α) (N : Matroid β) {I : Set (α ⊕ β)} :
    (M.sum N).Indep I ↔ M.Indep (.inl ⁻¹' I) ∧ N.Indep (.inr ⁻¹' I) := by
  simp only [Matroid.sum, mapEquiv_indep_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.symm_symm, sigma_indep_iff, Bool.forall_bool]
  convert! Iff.rfl <;>
    simp [Set.ext_iff, Equiv.ulift, Equiv.sumEquivSigmaBool]

set_option backward.isDefEq.respectTransparency false in
/-
**Matroid.sum_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} {β : Type v} {M : Matroid α} {N : Matroid β} {B : Set (α ⊕ 
β)},   (M.sum N).IsBase B ↔ M.IsBase (Sum.inl ⁻¹' B) ∧ N.IsBase (Sum.inr ⁻¹' B)
参数：α ⊕ β；M.sum N；Sum.inl ⁻¹' B；Sum.inr ⁻¹' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sum_isBase_iff {M : Matroid α} {N : Matroid β} {B : Set (α ⊕ β)} :
    (M.sum N).IsBase B ↔ M.IsBase (.inl ⁻¹' B) ∧ N.IsBase (.inr ⁻¹' B) := by
  simp only [Matroid.sum, mapEquiv_isBase_iff, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Equiv.symm_symm, sigma_isBase_iff, Bool.forall_bool]
  convert! Iff.rfl <;>
    simp [Set.ext_iff, Equiv.ulift, Equiv.sumEquivSigmaBool]

set_option backward.isDefEq.respectTransparency false in
/-
**Matroid.sum_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} {β : Type v} {M : Matroid α} {N : Matroid β} {I X : Set (α 
⊕ β)},   (M.sum N).IsBasis I X ↔ M.IsBasis (Sum.inl ⁻¹' I) (Sum.inl ⁻¹' X) ∧ N.I
sBasis (Sum.inr ⁻¹' I) (Sum.inr ⁻¹' X)
参数：α ⊕ β；M.sum N；Sum.inl ⁻¹' I；Sum.inl ⁻¹' X；Sum.inr ⁻¹' I；Sum.inr ⁻¹' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ULift.up_down`：∀ {α : Type u} (b : ULift.{v, u} α), { down := b.down } =
 b
· 使用定理 `ULift.down_up`：∀ {α : Type u} (a : α), { down := a }.down = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 32 条，此处仅展示前 30 条）
-/
@[simp] lemma sum_isBasis_iff {M : Matroid α} {N : Matroid β} {I X : Set (α ⊕ β)} :
    (M.sum N).IsBasis I X ↔
      (M.IsBasis (Sum.inl ⁻¹' I) (Sum.inl ⁻¹' X) ∧ N.IsBasis (Sum.inr ⁻¹' I) (Sum.inr ⁻¹' X)) := by
  simp only [Matroid.sum, mapEquiv_isBasis_iff, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Equiv.symm_symm, sigma_isBasis_iff, Bool.forall_bool,
    Equiv.sumEquivSigmaBool, Equiv.coe_fn_mk, Equiv.ulift]
  convert! Iff.rfl <;> exact ext <| by simp

end Sum

section disjointSum

variable {α : Type*} {M N : Matroid α}

/-- The sum of two matroids on `α` with disjoint ground sets, as a `Matroid α`. -/
/-
**Matroid.disjointSum** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：disjointSum (M N : Matroid α) (h : Disjoint M.E N.E) : Matroid α
参数：M N : Matroid α；h : Disjoint M.E N.E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two matroids on `α` with disjoint ground sets, as a `Matroid α`.
-/
def disjointSum (M N : Matroid α) (h : Disjoint M.E N.E) : Matroid α :=
  ((M.restrictSubtype M.E).sum (N.restrictSubtype N.E)).mapEmbedding <| Function.Embedding.sumSet h
/-
**Matroid.disjointSum_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {h : Disjoint M.E N.E}, (M.disjointSum 
N h).E = M.E ∪ N.E
参数：M.disjointSum N h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
· 使用定理 `Matroid.map.congr_simp`：∀ {α : Type u_1} {β : Type u_2} (M M_1 : Matroid
 α) (e_M : M = M_1) (f f_1 : α → β) (e_f : f = f_1)   (hf : Set.InjOn f M.E), M.
map f hf = M…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Function.Embedding.sumSet_apply`：∀ {α : Type u_1} {s t : Set α} (h : Dis
joint s t) (a : ↑s ⊕ ↑t),   (Function.Embedding.sumSet h) a = Sum.elim Subtype.v
al Subtype.val a
· 使用定理 `Matroid.sum_ground`：∀ {α : Type u} {β : Type v} (M : Matroid α) (N : Mat
roid β), (M.sum N).E = Sum.inl '' M.E ∪ Sum.inr '' N.E
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.range_inl_union_range_inr`：range_inl_union_range_inr : range (Sum.in
l : α -> α oplus β) union range Sum.inr = univ
· 使用定理 `Set.Sum.elim_range`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : 
α → γ) (g : β → γ),   Set.range (Sum.elim f g) = Set.range f ∪ Set.range g
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma disjointSum_ground_eq {h} : (M.disjointSum N h).E = M.E ∪ N.E := by
  simp [disjointSum, restrictSubtype, mapEmbedding]
/-
**Matroid.disjointSum_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {h : Disjoint M.E N.E} {I : Set α},   (
M.disjointSum N h).Indep I ↔ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) ∧ I ⊆ M.E ∪ N
.E
参数：M.disjointSum N h；I ∩ M.E；I ∩ N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Embedding.sumSet_preimage_inl`：∀ {α : Type u_1} {s t r : Set α}
 (h : Disjoint s t),   Subtype.val '' Sum.inl ⁻¹' ⇑(Function.Embedding.sumSet h)
 ⁻¹' r = r ∩ s
· 使用定理 `Function.Embedding.sumSet_preimage_inr`：∀ {α : Type u_1} {s t r : Set α}
 (h : Disjoint s t),   Subtype.val '' Sum.inr ⁻¹' ⇑(Function.Embedding.sumSet h)
 ⁻¹' r = r ∩ t
· 使用定理 `Function.Embedding.sumSet_range`：∀ {α : Type u_1} {s t : Set α} (h : Dis
joint s t), Set.range ⇑(Function.Embedding.sumSet h) = s ∪ t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjointSum_indep_iff {h I} :
    (M.disjointSum N h).Indep I ↔ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) ∧ I ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]
/-
**Matroid.disjointSum_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {h : Disjoint M.E N.E} {B : Set α},   (
M.disjointSum N h).IsBase B ↔ M.IsBase (B ∩ M.E) ∧ N.IsBase (B ∩ N.E) ∧ B ⊆ M.E 
∪ N.E
参数：M.disjointSum N h；B ∩ M.E；B ∩ N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Embedding.sumSet_preimage_inl`：∀ {α : Type u_1} {s t r : Set α}
 (h : Disjoint s t),   Subtype.val '' Sum.inl ⁻¹' ⇑(Function.Embedding.sumSet h)
 ⁻¹' r = r ∩ s
· 使用定理 `Function.Embedding.sumSet_preimage_inr`：∀ {α : Type u_1} {s t r : Set α}
 (h : Disjoint s t),   Subtype.val '' Sum.inr ⁻¹' ⇑(Function.Embedding.sumSet h)
 ⁻¹' r = r ∩ t
· 使用定理 `Function.Embedding.sumSet_range`：∀ {α : Type u_1} {s t : Set α} (h : Dis
joint s t), Set.range ⇑(Function.Embedding.sumSet h) = s ∪ t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjointSum_isBase_iff {h B} :
    (M.disjointSum N h).IsBase B ↔ M.IsBase (B ∩ M.E) ∧ N.IsBase (B ∩ N.E) ∧ B ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]
/-
**Matroid.disjointSum_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {h : Disjoint M.E N.E} {I X : Set α},  
 (M.disjointSum N h).IsBasis I X ↔     M.IsBasis (I ∩ M.E) (X ∩ M.E) ∧ N.IsBasis
 (I ∩ N.E) (X ∩ N.E) ∧ I ⊆ X ∧ X ⊆ M.E ∪ N.E
参数：M.disjointSum N h；I ∩ M.E；X ∩ M.E；I ∩ N.E；X ∩ N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Embedding.sumSet_preimage_inl`：∀ {α : Type u_1} {s t r : Set α}
 (h : Disjoint s t),   Subtype.val '' Sum.inl ⁻¹' ⇑(Function.Embedding.sumSet h)
 ⁻¹' r = r ∩ s
· 使用定理 `Function.Embedding.sumSet_preimage_inr`：∀ {α : Type u_1} {s t r : Set α}
 (h : Disjoint s t),   Subtype.val '' Sum.inr ⁻¹' ⇑(Function.Embedding.sumSet h)
 ⁻¹' r = r ∩ t
· 使用定理 `Function.Embedding.sumSet_range`：∀ {α : Type u_1} {s t : Set α} (h : Dis
joint s t), Set.range ⇑(Function.Embedding.sumSet h) = s ∪ t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjointSum_isBasis_iff {h I X} :
    (M.disjointSum N h).IsBasis I X ↔ M.IsBasis (I ∩ M.E) (X ∩ M.E) ∧
      N.IsBasis (I ∩ N.E) (X ∩ N.E) ∧ I ⊆ X ∧ X ⊆ M.E ∪ N.E := by
  simp [disjointSum, and_assoc]
/-
**Matroid.disjointSum_comm** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：disjointSum_comm {h} : M.disjointSum N h = N.disjointSum M h.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.disjointSum_ground_eq`：∀ {α : Type u_1} {M N : Matroid α} {h : D
isjoint M.E N.E}, (M.disjointSum N h).E = M.E ∪ N.E
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma disjointSum_comm {h} : M.disjointSum N h = N.disjointSum M h.symm := by
  ext
  · simp [union_comm]
  repeat simpa [union_comm] using ⟨fun ⟨m, n, h⟩ ↦ ⟨n, m, M.E.union_comm N.E ▸ h⟩,
    fun ⟨n, m, h⟩ ↦ ⟨m, n, M.E.union_comm N.E ▸ h⟩⟩
/-
**Matroid.Indep.eq_union_image_of_disjointSum** 是 Mathlib 中的一个定理，位于命名空间 `Matroid
.Indep`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {h : Disjoint M.E N.E} {I : Set α},   (
M.disjointSum N h).Indep I → ∃ IM IN, M.Indep IM ∧ N.Indep IN ∧ Disjoint IM IN ∧
 I = IM ∪ IN
参数：M.disjointSum N h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.disjointSum_indep_iff`：∀ {α : Type u_1} {M N : Matroid α} {h : D
isjoint M.E N.E} {I : Set α},   (M.disjointSum N h).Indep I ↔ M.Indep (I ∩ M.E) 
∧ N.Indep (I ∩ N.E)…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
-/
lemma Indep.eq_union_image_of_disjointSum {h I} (hI : (disjointSum M N h).Indep I) :
    ∃ IM IN, M.Indep IM ∧ N.Indep IN ∧ Disjoint IM IN ∧ I = IM ∪ IN := by
  rw [disjointSum_indep_iff] at hI
  refine ⟨_, _, hI.1, hI.2.1, h.mono inter_subset_right inter_subset_right, ?_⟩
  rw [← inter_union_distrib_left, inter_eq_self_of_subset_left hI.2.2]
/-
**Matroid.IsBase.eq_union_image_of_disjointSum** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsBase`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {h : Disjoint M.E N.E} {B : Set α},   (
M.disjointSum N h).IsBase B → ∃ BM BN, M.IsBase BM ∧ N.IsBase BN ∧ Disjoint BM B
N ∧ B = BM ∪ BN
参数：M.disjointSum N h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.disjointSum_isBase_iff`：∀ {α : Type u_1} {M N : Matroid α} {h : 
Disjoint M.E N.E} {B : Set α},   (M.disjointSum N h).IsBase B ↔ M.IsBase (B ∩ M.
E) ∧ N.IsBase (B ∩ N…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
-/
lemma IsBase.eq_union_image_of_disjointSum {h B} (hB : (disjointSum M N h).IsBase B) :
    ∃ BM BN, M.IsBase BM ∧ N.IsBase BN ∧ Disjoint BM BN ∧ B = BM ∪ BN := by
  rw [disjointSum_isBase_iff] at hB
  refine ⟨_, _, hB.1, hB.2.1, h.mono inter_subset_right inter_subset_right, ?_⟩
  rw [← inter_union_distrib_left, inter_eq_self_of_subset_left hB.2.2]

end disjointSum

end Matroid

