/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# The set lattice and (pre)images of functions

This file contains lemmas on the interaction between the indexed union/intersection of sets
and the image and preimage operations: `Set.image`, `Set.preimage`, `Set.image2`, `Set.kernImage`.
It also covers `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`.

In order to accommodate `Set.image2`, the file includes results on union/intersection in products.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `iUnion`
* `⋂ i, s i` is called `iInter`
* `⋃ i j, s i j` is called `iUnion₂`. This is an `iUnion` inside an `iUnion`.
* `⋂ i j, s i j` is called `iInter₂`. This is an `iInter` inside an `iInter`.
* `⋃ i ∈ s, t i` is called `biUnion` for "bounded `iUnion`". This is the special case of `iUnion₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `biInter` for "bounded `iInter`". This is the special case of `iInter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.iUnion`
* `⋂`: `Set.iInter`
* `⋃₀`: `Set.sUnion`
* `⋂₀`: `Set.sInter`
-/

public section

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ : ι → Sort*}

namespace Set

section GaloisConnection

variable {f : α → β}

/-
**Set.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisConnection (Set.image f
) (Set.preimage f)
参数：Set.image f；Set.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
protected theorem image_preimage : GaloisConnection (image f) (preimage f) := fun _ _ =>
  image_subset_iff
/-
**Set.preimage_kernImage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisConnection (Set.preimag
e f) (Set.kernImage f)
参数：Set.preimage f；Set.kernImage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Set.subset_kernImage_iff`：subset_kernImage_iff {s : Set β} {t : Set α} {
f : α -> β} : s subseteq kernImage f t ↔ f ⁻¹' s subseteq t
-/
protected theorem preimage_kernImage : GaloisConnection (preimage f) (kernImage f) := fun _ _ =>
  subset_kernImage_iff.symm

end GaloisConnection

section kernImage

variable {f : α → β}

/-
**Set.kernImage_mono** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：kernImage_mono : Monotone (kernImage f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `Set.preimage_kernImage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Gal
oisConnection (Set.preimage f) (Set.kernImage f)
-/
lemma kernImage_mono : Monotone (kernImage f) :=
  Set.preimage_kernImage.monotone_u
/-
**Set.kernImage_eq_compl** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：kernImage_eq_compl {s : Set α} : kernImage f s = (f '' sᶜ)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_unique`：u_unique {l' : α -> β} {u' : β -> α} (gc' : G
aloisConnection l' u') (hl : forall a, l a = l' a) {b : β} : u b = u' b
· 使用定理 `Set.preimage_kernImage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Gal
oisConnection (Set.preimage f) (Set.kernImage f)
· 使用定理 `GaloisConnection.compl`：∀ {α : Type u} {β : Type v} [inst : BooleanAlgeb
ra α] [inst_1 : BooleanAlgebra β] {l : α → β} {u : β → α},   GaloisConnection l 
u → GaloisCo…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
lemma kernImage_eq_compl {s : Set α} : kernImage f s = (f '' sᶜ)ᶜ :=
  Set.preimage_kernImage.u_unique (Set.image_preimage.compl)
    (fun t ↦ compl_compl (f ⁻¹' t) ▸ Set.preimage_compl)
/-
**Set.kernImage_compl** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：kernImage_compl {s : Set α} : kernImage f (sᶜ) = (f '' s)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
lemma kernImage_compl {s : Set α} : kernImage f (sᶜ) = (f '' s)ᶜ := by
  rw [kernImage_eq_compl, compl_compl]
/-
**Set.kernImage_empty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：kernImage_empty : kernImage f ∅ = (range f)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma kernImage_empty : kernImage f ∅ = (range f)ᶜ := by
  rw [kernImage_eq_compl, compl_empty, image_univ]
/-
**Set.kernImage_preimage_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：kernImage_preimage_eq_iff {s : Set β} : kernImage f (f ⁻¹' s) = s ↔ (range
 f)ᶜ subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `compl_eq_comm`：compl_eq_comm : xᶜ = y ↔ yᶜ = x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma kernImage_preimage_eq_iff {s : Set β} : kernImage f (f ⁻¹' s) = s ↔ (range f)ᶜ ⊆ s := by
  rw [kernImage_eq_compl, ← preimage_compl, compl_eq_comm, eq_comm, image_preimage_eq_iff,
      compl_subset_comm]
/-
**Set.compl_range_subset_kernImage** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：compl_range_subset_kernImage {s : Set α} : (range f)ᶜ subseteq kernImage f
 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.kernImage_empty`：kernImage_empty : kernImage f ∅ = (range f)ᶜ
· 使用引理 `Set.kernImage_mono`：kernImage_mono : Monotone (kernImage f)
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
lemma compl_range_subset_kernImage {s : Set α} : (range f)ᶜ ⊆ kernImage f s := by
  rw [← kernImage_empty]
  exact kernImage_mono (empty_subset _)
/-
**Set.kernImage_union_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：kernImage_union_preimage {s : Set α} {t : Set β} : kernImage f (s union f 
⁻¹' t) = kernImage f s union t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.kernImage_eq_compl`：kernImage_eq_compl {s : Set α} : kernImage f s =
 (f '' sᶜ)ᶜ
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
lemma kernImage_union_preimage {s : Set α} {t : Set β} :
    kernImage f (s ∪ f ⁻¹' t) = kernImage f s ∪ t := by
  rw [kernImage_eq_compl, kernImage_eq_compl, compl_union, ← preimage_compl, image_inter_preimage,
      compl_inter, compl_compl]
/-
**Set.kernImage_preimage_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：kernImage_preimage_union {s : Set α} {t : Set β} : kernImage f (f ⁻¹' t un
ion s) = t union kernImage f s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Set.kernImage_union_preimage`：kernImage_union_preimage {s : Set α} {t : 
Set β} : kernImage f (s union f ⁻¹' t) = kernImage f s union t
-/
lemma kernImage_preimage_union {s : Set α} {t : Set β} :
    kernImage f (f ⁻¹' t ∪ s) = t ∪ kernImage f s := by
  rw [union_comm, kernImage_union_preimage, union_comm]

end kernImage

/-
**Set.image_projection_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_projection_prod {ι : Type*} {α : ι -> Type*} {v : forall i : ι, Set 
(α i)} (hv : (pi univ v).Nonempty) (i : ι) : ((fun x : forall i : ι, α i => x i)
 '' ⋂ k, (fun x : forall j : ι, α j => x k) ⁻¹' v k) = v i
参数：α i；hv : (pi univ v).Nonempty；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem image_projection_prod {ι : Type*} {α : ι → Type*} {v : ∀ i : ι, Set (α i)}
    (hv : (pi univ v).Nonempty) (i : ι) :
    ((fun x : ∀ i : ι, α i => x i) '' ⋂ k, (fun x : ∀ j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical
    apply Subset.antisymm
    · simp [iInter_subset]
    · intro y y_in
      simp only [mem_image, mem_iInter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine ⟨Function.update z i y, ?_, update_self i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t ∈ v i]
      exact ⟨y_in, fun j _ => by simpa using hz j⟩

/-! ### Bounded unions and intersections -/

section Function

/-! ### Lemmas about `Set.MapsTo` -/

@[simp]
/-
**Set.mapsTo_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_sUnion {S : Set (Set α)} {t : Set β} {f : α -> β} : MapsTo f (⋃₀ S)
 t ↔ forall s in S, MapsTo f s t
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mapsTo_iff_subset_preimage`：mapsTo_iff_subset_preimage : MapsTo f s 
t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.sUnion_subset_iff`：sUnion_subset_iff {s : Set (Set α)} {t : Set α} :
 ⋃₀ s subseteq t ↔ forall t' in s, t' subseteq t

--- 原说明 ---
### Lemmas about `Set.MapsTo`
-/
theorem mapsTo_sUnion {S : Set (Set α)} {t : Set β} {f : α → β} :
    MapsTo f (⋃₀ S) t ↔ ∀ s ∈ S, MapsTo f s t :=
  mapsTo_iff_subset_preimage.trans sUnion_subset_iff

@[simp]
/-
**Set.mapsTo_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iUnion {s : ι -> Set α} {t : Set β} {f : α -> β} : MapsTo f (⋃ i, s
 i) t ↔ forall i, MapsTo f (s i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mapsTo_iff_subset_preimage`：mapsTo_iff_subset_preimage : MapsTo f s 
t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
-/
theorem mapsTo_iUnion {s : ι → Set α} {t : Set β} {f : α → β} :
    MapsTo f (⋃ i, s i) t ↔ ∀ i, MapsTo f (s i) t :=
  mapsTo_iff_subset_preimage.trans iUnion_subset_iff
/-
**Set.mapsTo_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iUnion {s : ι -> Set α} {t : Set β} {f : α -> β} : MapsTo f (⋃ i, s
 i) t ↔ forall i, MapsTo f (s i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mapsTo_iff_subset_preimage`：mapsTo_iff_subset_preimage : MapsTo f s 
t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
-/
theorem mapsTo_iUnion₂ {s : ∀ i, κ i → Set α} {t : Set β} {f : α → β} :
    MapsTo f (⋃ (i) (j), s i j) t ↔ ∀ i j, MapsTo f (s i j) t :=
  mapsTo_iff_subset_preimage.trans iUnion₂_subset_iff
/-
**Set.mapsTo_iUnion_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iUnion_iUnion {s : ι -> Set α} {t : ι -> Set β} {f : α -> β} (H : f
orall i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i) (⋃ i, t i)
参数：H : forall i, MapsTo f (s i) (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iUnion`：mapsTo_iUnion {s : ι -> Set α} {t : Set β} {f : α -> 
β} : MapsTo f (⋃ i, s i) t ↔ forall i, MapsTo f (s i) t
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem mapsTo_iUnion_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i) (⋃ i, t i) :=
  mapsTo_iUnion.2 fun i ↦ (H i).mono_right (subset_iUnion t i)
/-
**Set.mapsTo_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iUnion {s : ι -> Set α} {t : Set β} {f : α -> β} : MapsTo f (⋃ i, s
 i) t ↔ forall i, MapsTo f (s i) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mapsTo_iff_subset_preimage`：mapsTo_iff_subset_preimage : MapsTo f s 
t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
-/
theorem mapsTo_iUnion₂_iUnion₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  mapsTo_iUnion_iUnion fun i => mapsTo_iUnion_iUnion (H i)

@[simp]
/-
**Set.mapsTo_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_sInter {s : Set α} {T : Set (Set β)} {f : α -> β} : MapsTo f s (⋂₀ 
T) ↔ forall t in T, MapsTo f s t
参数：Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem mapsTo_sInter {s : Set α} {T : Set (Set β)} {f : α → β} :
    MapsTo f s (⋂₀ T) ↔ ∀ t ∈ T, MapsTo f s t :=
  forall₂_comm

@[simp]
/-
**Set.mapsTo_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iInter {s : Set α} {t : ι -> Set β} {f : α -> β} : MapsTo f s (⋂ i,
 t i) ↔ forall i, MapsTo f s (t i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mapsTo_sInter`：mapsTo_sInter {s : Set α} {T : Set (Set β)} {f : α ->
 β} : MapsTo f s (⋂₀ T) ↔ forall t in T, MapsTo f s t
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem mapsTo_iInter {s : Set α} {t : ι → Set β} {f : α → β} :
    MapsTo f s (⋂ i, t i) ↔ ∀ i, MapsTo f s (t i) :=
  mapsTo_sInter.trans forall_mem_range
/-
**Set.mapsTo_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iInter {s : Set α} {t : ι -> Set β} {f : α -> β} : MapsTo f s (⋂ i,
 t i) ↔ forall i, MapsTo f s (t i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mapsTo_sInter`：mapsTo_sInter {s : Set α} {T : Set (Set β)} {f : α ->
 β} : MapsTo f s (⋂₀ T) ↔ forall t in T, MapsTo f s t
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem mapsTo_iInter₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β} :
    MapsTo f s (⋂ (i) (j), t i j) ↔ ∀ i j, MapsTo f s (t i j) := by
  simp only [mapsTo_iInter]
/-
**Set.mapsTo_iInter_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iInter_iInter {s : ι -> Set α} {t : ι -> Set β} {f : α -> β} (H : f
orall i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i) (⋂ i, t i)
参数：H : forall i, MapsTo f (s i) (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iInter`：mapsTo_iInter {s : Set α} {t : ι -> Set β} {f : α -> 
β} : MapsTo f s (⋂ i, t i) ↔ forall i, MapsTo f s (t i)
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem mapsTo_iInter_iInter {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i) (⋂ i, t i) :=
  mapsTo_iInter.2 fun i => (H i).mono_left (iInter_subset s i)
/-
**Set.mapsTo_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iInter {s : Set α} {t : ι -> Set β} {f : α -> β} : MapsTo f s (⋂ i,
 t i) ↔ forall i, MapsTo f s (t i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mapsTo_sInter`：mapsTo_sInter {s : Set α} {T : Set (Set β)} {f : α ->
 β} : MapsTo f s (⋂₀ T) ↔ forall t in T, MapsTo f s t
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem mapsTo_iInter₂_iInter₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋂ (i) (j), s i j) (⋂ (i) (j), t i j) :=
  mapsTo_iInter_iInter fun i => mapsTo_iInter_iInter (H i)
/-
**Set.image_iInter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_iInter_subset (s : ι -> Set α) (f : α -> β) : (f '' ⋂ i, s i) subset
eq ⋂ i, f '' s i
参数：s : ι -> Set α；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.mapsTo_iInter_iInter`：mapsTo_iInter_iInter {s : ι -> Set α} {t : ι -
> Set β} {f : α -> β} (H : forall i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i)
 (⋂ i, t i)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem image_iInter_subset (s : ι → Set α) (f : α → β) : (f '' ⋂ i, s i) ⊆ ⋂ i, f '' s i :=
  (mapsTo_iInter_iInter fun i => mapsTo_image f (s i)).image_subset
/-
**Set.image_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_iInter {f : α -> β} (hf : Bijective f) (s : ι -> Set α) : (f '' ⋂ i,
 s i) = ⋂ i, f '' s i
参数：hf : Bijective f；s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
theorem image_iInter₂_subset (s : ∀ i, κ i → Set α) (f : α → β) :
    (f '' ⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), f '' s i j :=
  (mapsTo_iInter₂_iInter₂ fun i hi => mapsTo_image f (s i hi)).image_subset
/-
**Set.image_sInter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sInter_subset (S : Set (Set α)) (f : α -> β) : f '' ⋂₀ S subseteq ⋂ 
s in S, f '' s
参数：S : Set (Set α)；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.image_iInter₂_subset`：image_iInter₂_subset (s : forall i, κ i -> Set
 α) (f : α -> β) : (f '' ⋂ (i) (j), s i j) subseteq ⋂ (i) (j), f '' s i j
-/
theorem image_sInter_subset (S : Set (Set α)) (f : α → β) : f '' ⋂₀ S ⊆ ⋂ s ∈ S, f '' s := by
  rw [sInter_eq_biInter]
  apply image_iInter₂_subset
/-
**Set.image2_sInter_right_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_sInter_right_subset (t : Set α) (S : Set (Set β)) (f : α -> β -> γ)
 : image2 f t (⋂₀ S) subseteq ⋂ s in S, image2 f t s
参数：t : Set α；S : Set (Set β)；f : α -> β -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem image2_sInter_right_subset (t : Set α) (S : Set (Set β)) (f : α → β → γ) :
    image2 f t (⋂₀ S) ⊆ ⋂ s ∈ S, image2 f t s := by
  aesop
/-
**Set.image2_sInter_left_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_sInter_left_subset (S : Set (Set α)) (t : Set β) (f : α -> β -> γ) 
: image2 f (⋂₀ S) t subseteq ⋂ s in S, image2 f s t
参数：S : Set (Set α)；t : Set β；f : α -> β -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem image2_sInter_left_subset (S : Set (Set α)) (t : Set β) (f : α → β → γ) :
    image2 f (⋂₀ S) t ⊆ ⋂ s ∈ S, image2 f s t := by
  aesop

/-! ### `restrictPreimage` -/


section

open Function

variable {f : α → β} {U : ι → Set β} (hU : iUnion U = univ)
include hU

/-
**Set.injective_iff_injective_of_iUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injective_iff_injective_of_iUnion_eq_univ : Injective f ↔ forall i, Inject
ive ((U i).restrictPreimage f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.restrictPreimage_injective`：restrictPreimage_injective (hf : Injecti
ve f) : Injective (t.restrictPreimage f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem injective_iff_injective_of_iUnion_eq_univ :
    Injective f ↔ ∀ i, Injective ((U i).restrictPreimage f) := by
  refine ⟨fun H i => (U i).restrictPreimage_injective H, fun H x y e => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show f x ∈ Set.iUnion U by rw [hU]; trivial)
  injection @H i ⟨x, hi⟩ ⟨y, show f y ∈ U i from e ▸ hi⟩ (Subtype.ext e)
/-
**Set.surjective_iff_surjective_of_iUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set
`。
形式化陈述：surjective_iff_surjective_of_iUnion_eq_univ : Surjective f ↔ forall i, Sur
jective ((U i).restrictPreimage f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.restrictPreimage_surjective`：restrictPreimage_surjective (hf : Surje
ctive f) : Surjective (t.restrictPreimage f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem surjective_iff_surjective_of_iUnion_eq_univ :
    Surjective f ↔ ∀ i, Surjective ((U i).restrictPreimage f) := by
  refine ⟨fun H i => (U i).restrictPreimage_surjective H, fun H x => ?_⟩
  obtain ⟨i, hi⟩ :=
    Set.mem_iUnion.mp
      (show x ∈ Set.iUnion U by rw [hU]; trivial)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).choose_spec⟩
/-
**Set.bijective_iff_bijective_of_iUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bijective_iff_bijective_of_iUnion_eq_univ : Bijective f ↔ forall i, Biject
ive ((U i).restrictPreimage f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Bijective.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} (f : α → β), Func
tion.Bijective f = (Function.Injective f ∧ Function.Surjective f)
· 使用定理 `Set.injective_iff_injective_of_iUnion_eq_univ`：injective_iff_injective_o
f_iUnion_eq_univ : Injective f ↔ forall i, Injective ((U i).restrictPreimage f)
· 使用定理 `Set.surjective_iff_surjective_of_iUnion_eq_univ`：surjective_iff_surjecti
ve_of_iUnion_eq_univ : Surjective f ↔ forall i, Surjective ((U i).restrictPreima
ge f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bijective_iff_bijective_of_iUnion_eq_univ :
    Bijective f ↔ ∀ i, Bijective ((U i).restrictPreimage f) := by
  rw [Bijective, injective_iff_injective_of_iUnion_eq_univ hU,
    surjective_iff_surjective_of_iUnion_eq_univ hU]
  simp [Bijective, forall_and]

end

/-! ### `InjOn` -/


/-
**Set.InjOn.image_iInter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5} [Nonempty ι] {s : ι → Set α
} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i, s i = ⋂ i, f '' s i
参数：⋃ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.image_iInter_subset`：image_iInter_subset (s : ι -> Set α) (f : α -> 
β) : (f '' ⋂ i, s i) subseteq ⋂ i, f '' s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
### `InjOn`
-/
theorem InjOn.image_iInter_eq [Nonempty ι] {s : ι → Set α} {f : α → β} (h : InjOn f (⋃ i, s i)) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  inhabit ι
  refine Subset.antisymm (image_iInter_subset s f) fun y hy => ?_
  simp only [mem_iInter, mem_image] at hy
  choose x hx hy using hy
  refine ⟨x default, mem_iInter.2 fun i => ?_, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_iUnion _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]
/-
**Set.InjOn.image_biInter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5} {p : ι → Prop} {s : (i : ι)
 → p i → Set α},   (∃ i, p i) →     ∀ {f : α → β},       Set.InjOn f (⋃ i, ⋃ (hi
 : p i), s i hi) → f '' ⋂ i, ⋂ (hi : p i), s i hi = ⋂ i, ⋂ (hi : p i), f '' s i 
hi
参数：i : ι；∃ i, p i；⋃ i, ⋃ (hi : p i), s i hi；hi : p i；hi : p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
-/
theorem InjOn.image_biInter_eq {p : ι → Prop} {s : ∀ i, p i → Set α} (hp : ∃ i, p i)
    {f : α → β} (h : InjOn f (⋃ (i) (hi), s i hi)) :
    (f '' ⋂ (i) (hi), s i hi) = ⋂ (i) (hi), f '' s i hi := by
  simp only [iInter, iInf_subtype']
  have : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply InjOn.image_iInter_eq
  simpa only [iUnion, iSup_subtype'] using h
/-
**Set.image_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_iInter {f : α -> β} (hf : Bijective f) (s : ι -> Set α) : (f '' ⋂ i,
 s i) = ⋂ i, f '' s i
参数：hf : Bijective f；s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
theorem image_iInter {f : α → β} (hf : Bijective f) (s : ι → Set α) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iInter_of_empty, image_univ_of_surjective hf.surjective]
  · exact hf.injective.injOn.image_iInter_eq
/-
**Set.image_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_iInter {f : α -> β} (hf : Bijective f) (s : ι -> Set α) : (f '' ⋂ i,
 s i) = ⋂ i, f '' s i
参数：hf : Bijective f；s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
theorem image_iInter₂ {f : α → β} (hf : Bijective f) (s : ∀ i, κ i → Set α) :
    (f '' ⋂ (i) (j), s i j) = ⋂ (i) (j), f '' s i j := by simp_rw [image_iInter hf]
/-
**Set.inj_on_iUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inj_on_iUnion_of_directed {s : ι -> Set α} (hs : Directed (· subseteq ·) s
) {f : α -> β} (hf : forall i, InjOn f (s i)) : InjOn f (⋃ i, s i)
参数：hs : Directed (· subseteq ·) s；hf : forall i, InjOn f (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem inj_on_iUnion_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {f : α → β}
    (hf : ∀ i, InjOn f (s i)) : InjOn f (⋃ i, s i) := by
  intro x hx y hy hxy
  rcases mem_iUnion.1 hx with ⟨i, hx⟩
  rcases mem_iUnion.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy

/-! ### `SurjOn` -/


/-
**Set.surjOn_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_sUnion {s : Set α} {T : Set (Set β)} {f : α -> β} (H : forall t in 
T, SurjOn f s t) : SurjOn f s (⋃₀ T)
参数：Set β；H : forall t in T, SurjOn f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `SurjOn`
-/
theorem surjOn_sUnion {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, SurjOn f s t) :
    SurjOn f s (⋃₀ T) := fun _ ⟨t, ht, hx⟩ => H t ht hx
/-
**Set.surjOn_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iUnion {s : Set α} {t : ι -> Set β} {f : α -> β} (H : forall i, Sur
jOn f s (t i)) : SurjOn f s (⋃ i, t i)
参数：H : forall i, SurjOn f s (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.surjOn_sUnion`：surjOn_sUnion {s : Set α} {T : Set (Set β)} {f : α ->
 β} (H : forall t in T, SurjOn f s t) : SurjOn f s (⋃₀ T)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem surjOn_iUnion {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, SurjOn f s (t i)) :
    SurjOn f s (⋃ i, t i) :=
  surjOn_sUnion <| forall_mem_range.2 H
/-
**Set.surjOn_iUnion_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iUnion_iUnion {s : ι -> Set α} {t : ι -> Set β} {f : α -> β} (H : f
orall i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i) (⋃ i, t i)
参数：H : forall i, SurjOn f (s i) (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.surjOn_iUnion`：surjOn_iUnion {s : Set α} {t : ι -> Set β} {f : α -> 
β} (H : forall i, SurjOn f s (t i)) : SurjOn f s (⋃ i, t i)
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem surjOn_iUnion_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i) (⋃ i, t i) :=
  surjOn_iUnion fun i => (H i).mono (subset_iUnion _ _) (Subset.refl _)
/-
**Set.surjOn_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iUnion {s : Set α} {t : ι -> Set β} {f : α -> β} (H : forall i, Sur
jOn f s (t i)) : SurjOn f s (⋃ i, t i)
参数：H : forall i, SurjOn f s (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.surjOn_sUnion`：surjOn_sUnion {s : Set α} {T : Set (Set β)} {f : α ->
 β} (H : forall t in T, SurjOn f s t) : SurjOn f s (⋃₀ T)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem surjOn_iUnion₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f s (t i j)) : SurjOn f s (⋃ (i) (j), t i j) :=
  surjOn_iUnion fun i => surjOn_iUnion (H i)
/-
**Set.surjOn_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iUnion {s : Set α} {t : ι -> Set β} {f : α -> β} (H : forall i, Sur
jOn f s (t i)) : SurjOn f s (⋃ i, t i)
参数：H : forall i, SurjOn f s (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.surjOn_sUnion`：surjOn_sUnion {s : Set α} {T : Set (Set β)} {f : α ->
 β} (H : forall t in T, SurjOn f s t) : SurjOn f s (⋃₀ T)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem surjOn_iUnion₂_iUnion₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f (s i j) (t i j)) : SurjOn f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  surjOn_iUnion_iUnion fun i => surjOn_iUnion_iUnion (H i)
/-
**Set.surjOn_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iInter [Nonempty ι] {s : ι -> Set α} {t : Set β} {f : α -> β} (H : 
forall i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t
参数：H : forall i, SurjOn f (s i) t；Hinj : InjOn f (⋃ i, s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem surjOn_iInter [Nonempty ι] {s : ι → Set α} {t : Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t := by
  intro y hy
  rw [Hinj.image_iInter_eq, mem_iInter]
  exact fun i => H i hy
/-
**Set.surjOn_iInter_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iInter_iInter [Nonempty ι] {s : ι -> Set α} {t : ι -> Set β} {f : α
 -> β} (H : forall i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn
 f (⋂ i, s i) (⋂ i, t i)
参数：H : forall i, SurjOn f (s i) (t i)；Hinj : InjOn f (⋃ i, s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.surjOn_iInter`：surjOn_iInter [Nonempty ι] {s : ι -> Set α} {t : Set 
β} {f : α -> β} (H : forall i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : S
urjOn f…
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem surjOn_iInter_iInter [Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) (⋂ i, t i) :=
  surjOn_iInter (fun i => (H i).mono (Subset.refl _) (iInter_subset _ _)) Hinj

/-! ### `BijOn` -/


/-
**Set.bijOn_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bijOn_iUnion {s : ι -> Set α} {t : ι -> Set β} {f : α -> β} (H : forall i,
 BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i
)
参数：H : forall i, BijOn f (s i) (t i)；Hinj : InjOn f (⋃ i, s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_iUnion_iUnion`：mapsTo_iUnion_iUnion {s : ι -> Set α} {t : ι -
> Set β} {f : α -> β} (H : forall i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i)
 (⋃ i, t i)
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.surjOn_iUnion_iUnion`：surjOn_iUnion_iUnion {s : ι -> Set α} {t : ι -
> Set β} {f : α -> β} (H : forall i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i)
 (⋃ i, t i)
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t

--- 原说明 ---
### `BijOn`
-/
theorem bijOn_iUnion {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  ⟨mapsTo_iUnion_iUnion fun i => (H i).mapsTo, Hinj, surjOn_iUnion_iUnion fun i => (H i).surjOn⟩
/-
**Set.bijOn_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bijOn_iInter [hi : Nonempty ι] {s : ι -> Set α} {t : ι -> Set β} {f : α ->
 β} (H : forall i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂
 i, s i) (⋂ i, t i)
参数：H : forall i, BijOn f (s i) (t i)；Hinj : InjOn f (⋃ i, s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_iInter_iInter`：mapsTo_iInter_iInter {s : ι -> Set α} {t : ι -
> Set β} {f : α -> β} (H : forall i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i)
 (⋂ i, t i)
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.surjOn_iInter_iInter`：surjOn_iInter_iInter [Nonempty ι] {s : ι -> Se
t α} {t : ι -> Set β} {f : α -> β} (H : forall i, SurjOn f (s i) (t i)) (Hinj : 
InjOn f (⋃ i, …
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem bijOn_iInter [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  ⟨mapsTo_iInter_iInter fun i => (H i).mapsTo,
    hi.elim fun i => (H i).injOn.mono (iInter_subset _ _),
    surjOn_iInter_iInter (fun i => (H i).surjOn) Hinj⟩
/-
**Set.bijOn_iUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bijOn_iUnion_of_directed {s : ι -> Set α} (hs : Directed (· subseteq ·) s)
 {t : ι -> Set β} {f : α -> β} (H : forall i, BijOn f (s i) (t i)) : BijOn f (⋃ 
i, s i) (⋃ i, t i)
参数：hs : Directed (· subseteq ·) s；H : forall i, BijOn f (s i) (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bijOn_iUnion`：bijOn_iUnion {s : ι -> Set α} {t : ι -> Set β} {f : α 
-> β} (H : forall i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f 
(⋃ i, …
· 使用定理 `Set.inj_on_iUnion_of_directed`：inj_on_iUnion_of_directed {s : ι -> Set α
} (hs : Directed (· subseteq ·) s) {f : α -> β} (hf : forall i, InjOn f (s i)) :
 InjOn f (⋃ i, s i)
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
-/
theorem bijOn_iUnion_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {t : ι → Set β}
    {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  bijOn_iUnion H <| inj_on_iUnion_of_directed hs fun i => (H i).injOn
/-
**Set.bijOn_iInter_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bijOn_iInter_of_directed [Nonempty ι] {s : ι -> Set α} (hs : Directed (· s
ubseteq ·) s) {t : ι -> Set β} {f : α -> β} (H : forall i, BijOn f (s i) (t i)) 
: BijOn f (⋂ i, s i) (⋂ i, t i)
参数：hs : Directed (· subseteq ·) s；H : forall i, BijOn f (s i) (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.bijOn_iInter`：bijOn_iInter [hi : Nonempty ι] {s : ι -> Set α} {t : ι
 -> Set β} {f : α -> β} (H : forall i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i
, s i)…
· 使用定理 `Set.inj_on_iUnion_of_directed`：inj_on_iUnion_of_directed {s : ι -> Set α
} (hs : Directed (· subseteq ·) s) {f : α -> β} (hf : forall i, InjOn f (s i)) :
 InjOn f (⋃ i, s i)
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
-/
theorem bijOn_iInter_of_directed [Nonempty ι] {s : ι → Set α} (hs : Directed (· ⊆ ·) s)
    {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  bijOn_iInter H <| inj_on_iUnion_of_directed hs fun i => (H i).injOn

end Function

/-! ### `image`, `preimage` -/


section Image

/-
**Set.image_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s
 i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_iUnion {f : α → β} {s : ι → Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s i := by
  ext1 x
  simp only [mem_image, mem_iUnion, ← exists_and_right, exists_comm (α := α)]
/-
**Set.image_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s
 i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_iUnion₂ (f : α → β) (s : ∀ i, κ i → Set α) :
    (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j := by simp_rw [image_iUnion]
/-
**Set.univ_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_subtype {p : α -> Prop} : (univ : Set (Subtype p)) = ⋃ (x) (h : p x),
 {⟨x, h⟩}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem univ_subtype {p : α → Prop} : (univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩} :=
  Set.ext fun ⟨x, h⟩ => by simp [h]
/-
**Set.range_eq_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_eq_iUnion {ι} (f : ι -> α) : range f = ⋃ i, {f i}
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_eq_iUnion {ι} (f : ι → α) : range f = ⋃ i, {f i} :=
  Set.ext fun a => by simp [@eq_comm α a]
/-
**Set.image_eq_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eq_iUnion (f : α -> β) (s : Set α) : f '' s = ⋃ i in s, {f i}
参数：f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_eq_iUnion (f : α → β) (s : Set α) : f '' s = ⋃ i ∈ s, {f i} :=
  Set.ext fun b => by simp [@eq_comm β b]
/-
**Set.biUnion_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in range f, g x = ⋃ y, g
 (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
theorem biUnion_range {f : ι → α} {g : α → Set β} : ⋃ x ∈ range f, g x = ⋃ y, g (f y) :=
  iSup_range

@[simp]
/-
**Set.iUnion_iUnion_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} : ⋃ (x) (y) (_ : f y = x),
 g x = ⋃ y, g (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
-/
theorem iUnion_iUnion_eq' {f : ι → α} {g : α → Set β} :
    ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y) := by simpa using biUnion_range
/-
**Set.biInter_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_range {f : ι -> α} {g : α -> Set β} : ⋂ x in range f, g x = ⋂ y, g
 (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
theorem biInter_range {f : ι → α} {g : α → Set β} : ⋂ x ∈ range f, g x = ⋂ y, g (f y) :=
  iInf_range

@[simp]
/-
**Set.iInter_iInter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} : ⋂ (x) (y) (_ : f y = x),
 g x = ⋂ y, g (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_range`：biInter_range {f : ι -> α} {g : α -> Set β} : ⋂ x in 
range f, g x = ⋂ y, g (f y)
-/
theorem iInter_iInter_eq' {f : ι → α} {g : α → Set β} :
    ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y) := by simpa using biInter_range

variable {s : Set γ} {f : γ → α} {g : α → Set β}
/-
**Set.biUnion_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
-/
theorem biUnion_image : ⋃ x ∈ f '' s, g x = ⋃ y ∈ s, g (f y) :=
  iSup_image
/-
**Set.biInter_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biInter_image : ⋂ x in f '' s, g x = ⋂ y in s, g (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
-/
theorem biInter_image : ⋂ x ∈ f '' s, g x = ⋂ y ∈ s, g (f y) :=
  iInf_image
/-
**Set.biUnion_image2** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biUnion_image2 (s : Set α) (t : Set β) (f : α -> β -> γ) (g : γ -> Set δ) 
: ⋃ c in image2 f s t, g c = ⋃ a in s, ⋃ b in t, g (f a b)
参数：s : Set α；t : Set β；f : α -> β -> γ；g : γ -> Set δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_image2`：iSup_image2 {γ δ} (f : β -> γ -> δ) (s : Set β) (t : Set γ)
 (g : δ -> α) : ⨆ d in image2 f s t, g d = ⨆ b in s, ⨆ c in t, g (f b c)
-/
lemma biUnion_image2 (s : Set α) (t : Set β) (f : α → β → γ) (g : γ → Set δ) :
    ⋃ c ∈ image2 f s t, g c = ⋃ a ∈ s, ⋃ b ∈ t, g (f a b) := iSup_image2 ..
/-
**Set.biInter_image2** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biInter_image2 (s : Set α) (t : Set β) (f : α -> β -> γ) (g : γ -> Set δ) 
: ⋂ c in image2 f s t, g c = ⋂ a in s, ⋂ b in t, g (f a b)
参数：s : Set α；t : Set β；f : α -> β -> γ；g : γ -> Set δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_image2`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{γ : Type u_8} {δ : Type u_9} (f : β → γ → δ) (s : Set β)   (t : Set γ) (g : δ →
 …
-/
lemma biInter_image2 (s : Set α) (t : Set β) (f : α → β → γ) (g : γ → Set δ) :
    ⋂ c ∈ image2 f s t, g c = ⋂ a ∈ s, ⋂ b ∈ t, g (f a b) := iInf_image2 ..
/-
**Set.iUnion_inter_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_inter_iUnion {ι κ : Sort*} (f : ι -> Set α) (g : κ -> Set α) : (⋃ i
, f i) inter ⋃ j, g j = ⋃ i, ⋃ j, f i inter g j
参数：f : ι -> Set α；g : κ -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iUnion_inter_iUnion {ι κ : Sort*} (f : ι → Set α) (g : κ → Set α) :
    (⋃ i, f i) ∩ ⋃ j, g j = ⋃ i, ⋃ j, f i ∩ g j := by simp_rw [iUnion_inter, inter_iUnion]
/-
**Set.iInter_union_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iInter_union_iInter {ι κ : Sort*} (f : ι -> Set α) (g : κ -> Set α) : (⋂ i
, f i) union ⋂ j, g j = ⋂ i, ⋂ j, f i union g j
参数：f : ι -> Set α；g : κ -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_union`：iInter_union (s : ι -> Set β) (t : Set β) : (⋂ i, s i)
 union t = ⋂ i, s i union t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.union_iInter`：union_iInter (s : Set β) (t : ι -> Set β) : (s union ⋂
 i, t i) = ⋂ i, s union t i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iInter_union_iInter {ι κ : Sort*} (f : ι → Set α) (g : κ → Set α) :
    (⋂ i, f i) ∪ ⋂ j, g j = ⋂ i, ⋂ j, f i ∪ g j := by simp_rw [iInter_union, union_iInter]
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iUnion₂_inter_iUnion₂ {ι₁ κ₁ : Sort*} {ι₂ : ι₁ → Sort*} {k₂ : κ₁ → Sort*}
    (f : ∀ i₁, ι₂ i₁ → Set α) (g : ∀ j₁, k₂ j₁ → Set α) :
    (⋃ i₁, ⋃ i₂, f i₁ i₂) ∩ ⋃ j₁, ⋃ j₂, g j₁ j₂ = ⋃ i₁, ⋃ i₂, ⋃ j₁, ⋃ j₂, f i₁ i₂ ∩ g j₁ j₂ := by
  simp_rw [iUnion_inter, inter_iUnion]
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iInter₂_union_iInter₂ {ι₁ κ₁ : Sort*} {ι₂ : ι₁ → Sort*} {k₂ : κ₁ → Sort*}
    (f : ∀ i₁, ι₂ i₁ → Set α) (g : ∀ j₁, k₂ j₁ → Set α) :
    (⋂ i₁, ⋂ i₂, f i₁ i₂) ∪ ⋂ j₁, ⋂ j₂, g j₁ j₂ = ⋂ i₁, ⋂ i₂, ⋂ j₁, ⋂ j₂, f i₁ i₂ ∪ g j₁ j₂ := by
  simp_rw [iInter_union, union_iInter]
/-
**Set.biUnion_inter_of_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_inter_of_pairwise_disjoint {ι : Type*} {f : ι -> Set α} (h : Pairw
ise (Disjoint on f)) (s t : Set ι) : (⋃ i in (s inter t), f i) = (⋃ i in s, f i)
 inter (⋃ i in t, f i)
参数：h : Pairwise (Disjoint on f)；s t : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_inter_of_pairwise_disjoint`：∀ {α : Type u} [inst : Order.Frame α] 
{ι : Type u_1} {f : ι → α},   Pairwise (Function.onFun Disjoint f) → ∀ (s t : Se
t ι), ⨆ i ∈ s ∩ t, f i…
-/
theorem biUnion_inter_of_pairwise_disjoint {ι : Type*} {f : ι → Set α}
    (h : Pairwise (Disjoint on f)) (s t : Set ι) :
    (⋃ i ∈ (s ∩ t), f i) = (⋃ i ∈ s, f i) ∩ (⋃ i ∈ t, f i) :=
  biSup_inter_of_pairwise_disjoint h s t
/-
**Set.biUnion_iInter_of_pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_iInter_of_pairwise_disjoint {ι κ : Type*} [hκ : Nonempty κ] {f : ι
 -> Set α} (h : Pairwise (Disjoint on f)) (s : κ -> Set ι) : (⋃ i in (⋂ j, s j),
 f i) = ⋂ j, (⋃ i in s j, f i)
参数：h : Pairwise (Disjoint on f)；s : κ -> Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_iInter_of_pairwise_disjoint`：∀ {α : Type u} [inst : CompletelyDist
ribLattice α] {ι : Type u_1} {κ : Type u_2} [hκ : Nonempty κ] {f : ι → α},   Pai
rwise (Function.onFun D…
-/
theorem biUnion_iInter_of_pairwise_disjoint {ι κ : Type*}
    [hκ : Nonempty κ] {f : ι → Set α} (h : Pairwise (Disjoint on f)) (s : κ → Set ι) :
    (⋃ i ∈ (⋂ j, s j), f i) = ⋂ j, (⋃ i ∈ s j, f i) :=
  biSup_iInter_of_pairwise_disjoint h s

end Image

section Preimage

/-
**Set.monotone_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotone_preimage {f : α -> β} : Monotone (preimage f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem monotone_preimage {f : α → β} : Monotone (preimage f) := fun _ _ h => preimage_mono h

@[simp]
/-
**Set.preimage_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f 
⁻¹' s i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem preimage_iUnion {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i :=
  Set.ext <| by simp [preimage]
/-
**Set.preimage_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f 
⁻¹' s i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem preimage_iUnion₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_iUnion]
/-
**Set.image_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sUnion {f : α -> β} {s : Set (Set α)} : (f '' ⋃₀ s) = ⋃₀ (image f ''
 s)
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem image_sUnion {f : α → β} {s : Set (Set α)} : (f '' ⋃₀ s) = ⋃₀ (image f '' s) := by
  ext
  simp only [Set.mem_iUnion, Set.sUnion_image]
  grind

@[simp]
/-
**Set.preimage_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_sUnion {f : α -> β} {s : Set (Set β)} : f ⁻¹' ⋃₀ s = ⋃ t in s, f 
⁻¹' t
参数：Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.preimage_iUnion₂`：preimage_iUnion₂ {f : α -> β} {s : forall i, κ i -
> Set β} : (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j
-/
theorem preimage_sUnion {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋃₀ s = ⋃ t ∈ s, f ⁻¹' t := by
  rw [sUnion_eq_biUnion, preimage_iUnion₂]
/-
**Set.preimage_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f 
⁻¹' s i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_iInter {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i := by
  ext; simp
/-
**Set.preimage_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f 
⁻¹' s i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_iInter₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_iInter]

@[simp]
/-
**Set.preimage_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_sInter {f : α -> β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t in s, f 
⁻¹' t
参数：Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.preimage_iInter₂`：preimage_iInter₂ {f : α -> β} {s : forall i, κ i -
> Set β} : (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j
-/
theorem preimage_sInter {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t ∈ s, f ⁻¹' t := by
  rw [sInter_eq_biInter, preimage_iInter₂]

@[simp]
/-
**Set.biUnion_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_preimage_singleton (f : α -> β) (s : Set β) : ⋃ y in s, f ⁻¹' {y} 
= f ⁻¹' s
参数：f : α -> β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_iUnion₂`：preimage_iUnion₂ {f : α -> β} {s : forall i, κ i -
> Set β} : (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
theorem biUnion_preimage_singleton (f : α → β) (s : Set β) : ⋃ y ∈ s, f ⁻¹' {y} = f ⁻¹' s := by
  rw [← preimage_iUnion₂, biUnion_of_singleton]
/-
**Set.biUnion_range_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_range_preimage_singleton (f : α -> β) : ⋃ y in range f, f ⁻¹' {y} 
= univ
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
-/
theorem biUnion_range_preimage_singleton (f : α → β) : ⋃ y ∈ range f, f ⁻¹' {y} = univ := by
  rw [biUnion_preimage_singleton, preimage_range]

end Preimage

section Prod

/-
**Set.prod_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_iUnion {s : Set α} {t : ι -> Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_iUnion {s : Set α} {t : ι → Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i := by
  ext
  simp
/-
**Set.prod_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_iUnion {s : Set α} {t : ι -> Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_iUnion₂ {s : Set α} {t : ∀ i, κ i → Set β} :
    (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j := by simp_rw [prod_iUnion]
/-
**Set.prod_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_sUnion {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀ C = ⋃₀ ((fun t => s ×ˢ
 t) '' C)
参数：Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.prod_iUnion₂`：prod_iUnion₂ {s : Set α} {t : forall i, κ i -> Set β} 
: (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_sUnion {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀ C = ⋃₀ ((fun t => s ×ˢ t) '' C) := by
  simp_rw [sUnion_eq_biUnion, biUnion_image, prod_iUnion₂]
/-
**Set.iUnion_prod_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_prod_const {s : ι -> Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s 
i ×ˢ t
该定理/引理给出了一组等式。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_prod_const {s : ι → Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t := by
  ext
  simp
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_prod_const {s : ∀ i, κ i → Set α} {t : Set β} :
    (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t := by simp_rw [iUnion_prod_const]
/-
**Set.sUnion_prod_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_prod_const {C : Set (Set α)} {t : Set β} : ⋃₀ C ×ˢ t = ⋃₀ ((fun s :
 Set α => s ×ˢ t) '' C)
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.iUnion₂_prod_const`：iUnion₂_prod_const {s : forall i, κ i -> Set α} 
{t : Set β} : (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t
· 使用定理 `Set.biUnion_image`：biUnion_image : ⋃ x in f '' s, g x = ⋃ y in s, g (f y
)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sUnion_prod_const {C : Set (Set α)} {t : Set β} :
    ⋃₀ C ×ˢ t = ⋃₀ ((fun s : Set α => s ×ˢ t) '' C) := by
  simp only [sUnion_eq_biUnion, iUnion₂_prod_const, biUnion_image]
/-
**Set.iUnion_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_prod {ι ι' α β} (s : ι -> Set α) (t : ι' -> Set β) : ⋃ x : ι × ι', 
s x.1 ×ˢ t x.2 = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i
参数：s : ι -> Set α；t : ι' -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_prod {ι ι' α β} (s : ι → Set α) (t : ι' → Set β) :
    ⋃ x : ι × ι', s x.1 ×ˢ t x.2 = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i := by
  ext
  simp

/-- Analogue of `iSup_prod` for sets. -/
/-
**Set.iUnion_prod'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_prod' (f : β × γ -> Set α) : ⋃ x : β × γ, f x = ⋃ (i : β) (j : γ), 
f (i, j)
参数：f : β × γ -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)

--- 原说明 ---
Analogue of `iSup_prod` for sets.
-/
lemma iUnion_prod' (f : β × γ → Set α) : ⋃ x : β × γ, f x = ⋃ (i : β) (j : γ), f (i, j) :=
  iSup_prod
/-
**Set.iUnion_prod_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_prod_of_monotone [SemilatticeSup α] {s : α -> Set β} {t : α -> Set 
γ} (hs : Monotone s) (ht : Monotone t) : ⋃ x, s x ×ˢ t x = (⋃ x, s x) ×ˢ ⋃ x, t 
x
参数：hs : Monotone s；ht : Monotone t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem iUnion_prod_of_monotone [SemilatticeSup α] {s : α → Set β} {t : α → Set γ} (hs : Monotone s)
    (ht : Monotone t) : ⋃ x, s x ×ˢ t x = (⋃ x, s x) ×ˢ ⋃ x, t x := by
  ext ⟨z, w⟩; simp only [mem_prod, mem_iUnion, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩
/-
**Set.biUnion_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biUnion_prod {α β γ} (s : Set α) (t : Set β) (f : α -> Set γ) (g : β -> Se
t δ) : ⋃ x in s ×ˢ t, f x.1 ×ˢ g x.2 = (⋃ x in s, f x) ×ˢ (⋃ x in t, g x)
参数：s : Set α；t : Set β；f : α -> Set γ；g : β -> Set δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
lemma biUnion_prod {α β γ} (s : Set α) (t : Set β) (f : α → Set γ) (g : β → Set δ) :
    ⋃ x ∈ s ×ˢ t, f x.1 ×ˢ g x.2 = (⋃ x ∈ s, f x) ×ˢ (⋃ x ∈ t, g x) := by
  ext ⟨_, _⟩
  simp only [mem_iUnion, mem_prod, exists_prop, Prod.exists]; tauto

/-- Analogue of `biSup_prod` for sets. -/
/-
**Set.biUnion_prod'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：biUnion_prod' (s : Set β) (t : Set γ) (f : β × γ -> Set α) : ⋃ x in s ×ˢ t
, f x = ⋃ (i in s) (j in t), f (i, j)
参数：s : Set β；t : Set γ；f : β × γ -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_prod`：biSup_prod {f : β × γ -> α} {s : Set β} {t : Set γ} : ⨆ x in
 s ×ˢ t, f x = ⨆ (a in s) (b in t), f (a, b)

--- 原说明 ---
Analogue of `biSup_prod` for sets.
-/
lemma biUnion_prod' (s : Set β) (t : Set γ) (f : β × γ → Set α) :
    ⋃ x ∈ s ×ˢ t, f x = ⋃ (i ∈ s) (j ∈ t), f (i, j) :=
  biSup_prod
/-
**Set.sInter_prod_sInter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_prod_sInter_subset (S : Set (Set α)) (T : Set (Set β)) : ⋂₀ S ×ˢ ⋂₀
 T subseteq ⋂ r in S ×ˢ T, r.1 ×ˢ r.2
参数：S : Set (Set α)；T : Set (Set β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sInter_prod_sInter_subset (S : Set (Set α)) (T : Set (Set β)) :
    ⋂₀ S ×ˢ ⋂₀ T ⊆ ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
  subset_iInter₂ fun x hx _ hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩
/-
**Set.sInter_prod_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_prod_sInter {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (
hT : T.Nonempty) : ⋂₀ S ×ˢ ⋂₀ T = ⋂ r in S ×ˢ T, r.1 ×ˢ r.2
参数：Set α；Set β；hS : S.Nonempty；hT : T.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.sInter_prod_sInter_subset`：sInter_prod_sInter_subset (S : Set (Set α
)) (T : Set (Set β)) : ⋂₀ S ×ˢ ⋂₀ T subseteq ⋂ r in S ×ˢ T, r.1 ×ˢ r.2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sInter_prod_sInter {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (hT : T.Nonempty) :
    ⋂₀ S ×ˢ ⋂₀ T = ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 := by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine Set.Subset.antisymm (sInter_prod_sInter_subset S T) fun x hx => ?_
  rw [mem_iInter₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩
/-
**Set.sInter_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_prod {S : Set (Set α)} (hS : S.Nonempty) (t : Set β) : ⋂₀ S ×ˢ t = 
⋂ s in S, s ×ˢ t
参数：Set α；hS : S.Nonempty；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_singleton`：sInter_singleton (s : Set α) : ⋂₀ {s} = s
· 使用定理 `Set.sInter_prod_sInter`：sInter_prod_sInter {S : Set (Set α)} {T : Set (S
et β)} (hS : S.Nonempty) (hT : T.Nonempty) : ⋂₀ S ×ˢ ⋂₀ T = ⋂ r in S ×ˢ T, r.1 ×
ˢ r.2
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.prod_singleton`：prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, 
b)) '' s
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInter_prod {S : Set (Set α)} (hS : S.Nonempty) (t : Set β) :
    ⋂₀ S ×ˢ t = ⋂ s ∈ S, s ×ˢ t := by
  rw [← sInter_singleton t, sInter_prod_sInter hS (singleton_nonempty t), sInter_singleton]
  simp_rw [prod_singleton, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]
/-
**Set.prod_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_sInter {T : Set (Set β)} (hT : T.Nonempty) (s : Set α) : s ×ˢ ⋂₀ T = 
⋂ t in T, s ×ˢ t
参数：Set β；hT : T.Nonempty；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_singleton`：sInter_singleton (s : Set α) : ⋂₀ {s} = s
· 使用定理 `Set.sInter_prod_sInter`：sInter_prod_sInter {S : Set (Set α)} {T : Set (S
et β)} (hS : S.Nonempty) (hT : T.Nonempty) : ⋂₀ S ×ˢ ⋂₀ T = ⋂ r in S ×ˢ T, r.1 ×
ˢ r.2
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_sInter {T : Set (Set β)} (hT : T.Nonempty) (s : Set α) :
    s ×ˢ ⋂₀ T = ⋂ t ∈ T, s ×ˢ t := by
  rw [← sInter_singleton s, sInter_prod_sInter (singleton_nonempty s) hT, sInter_singleton]
  simp_rw [singleton_prod, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]
/-
**Set.prod_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_iInter {s : Set α} {t : ι -> Set β} [hι : Nonempty ι] : (s ×ˢ ⋂ i, t 
i) = ⋂ i, s ×ˢ t i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prod_iInter {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (s ×ˢ ⋂ i, t i) = ⋂ i, s ×ˢ t i := by
  ext x
  simp only [mem_prod, mem_iInter]
  exact ⟨fun h i => ⟨h.1, h.2 i⟩, fun h => ⟨(h hι.some).1, fun i => (h i).2⟩⟩

end Prod

section Image2

variable (f : α → β → γ) {s : Set α} {t : Set β}

/-- The `Set.image2` version of `Set.image_eq_iUnion` -/
/-
**Set.image2_eq_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_eq_iUnion (s : Set α) (t : Set β) : image2 f s t = ⋃ (i in s) (j in
 t), {f i j}
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The `Set.image2` version of `Set.image_eq_iUnion`
-/
theorem image2_eq_iUnion (s : Set α) (t : Set β) : image2 f s t = ⋃ (i ∈ s) (j ∈ t), {f i j} := by
  ext; simp [eq_comm]
/-
**Set.iUnion_image_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_image_left : ⋃ a in s, f a '' t = image2 f s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.image_eq_iUnion`：image_eq_iUnion (f : α -> β) (s : Set α) : f '' s =
 ⋃ i in s, {f i}
· 使用定理 `Set.image2_eq_iUnion`：image2_eq_iUnion (s : Set α) (t : Set β) : image2 
f s t = ⋃ (i in s) (j in t), {f i j}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_image_left : ⋃ a ∈ s, f a '' t = image2 f s t := by
  simp only [image2_eq_iUnion, image_eq_iUnion]
/-
**Set.iUnion_image_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_image_right : ⋃ b in t, (f · b) '' s = image2 f s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
theorem iUnion_image_right : ⋃ b ∈ t, (f · b) '' s = image2 f s t := by
  rw [image2_swap, iUnion_image_left]
/-
**Set.image2_iUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_iUnion_left (s : ι -> Set α) (t : Set β) : image2 f (⋃ i, s i) t = 
⋃ i, image2 f (s i) t
参数：s : ι -> Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_prod_const`：iUnion_prod_const {s : ι -> Set α} {t : Set β} : 
(⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image2_iUnion_left (s : ι → Set α) (t : Set β) :
    image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t := by
  simp only [← image_prod, iUnion_prod_const, image_iUnion]
/-
**Set.image2_iUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_iUnion_right (s : Set α) (t : ι -> Set β) : image2 f s (⋃ i, t i) =
 ⋃ i, image2 f s (t i)
参数：s : Set α；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_iUnion`：prod_iUnion {s : Set α} {t : ι -> Set β} : (s ×ˢ ⋃ i, t
 i) = ⋃ i, s ×ˢ t i
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image2_iUnion_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i) := by
  simp only [← image_prod, prod_iUnion, image_iUnion]
/-
**Set.image2_sUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_sUnion_left (S : Set (Set α)) (t : Set β) : image2 f (⋃₀ S) t = ⋃ s
 in S, image2 f s t
参数：S : Set (Set α)；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem image2_sUnion_left (S : Set (Set α)) (t : Set β) :
    image2 f (⋃₀ S) t = ⋃ s ∈ S, image2 f s t := by
  aesop
/-
**Set.image2_sUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_sUnion_right (s : Set α) (T : Set (Set β)) : image2 f s (⋃₀ T) = ⋃ 
t in T, image2 f s t
参数：s : Set α；T : Set (Set β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem image2_sUnion_right (s : Set α) (T : Set (Set β)) :
    image2 f s (⋃₀ T) = ⋃ t ∈ T, image2 f s t := by
  aesop
/-
**Set.image2_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image2_iUnion₂_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋃ (i) (j), s i j) t = ⋃ (i) (j), image2 f (s i j) t := by simp_rw [image2_iUnion_left]
/-
**Set.image2_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image2_iUnion₂_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋃ (i) (j), t i j) = ⋃ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_iUnion_right]
/-
**Set.image2_iInter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_iInter_subset_left (s : ι -> Set α) (t : Set β) : image2 f (⋂ i, s 
i) t subseteq ⋂ i, image2 f (s i) t
参数：s : ι -> Set α；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem image2_iInter_subset_left (s : ι → Set α) (t : Set β) :
    image2 f (⋂ i, s i) t ⊆ ⋂ i, image2 f (s i) t := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy
/-
**Set.image2_iInter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_iInter_subset_right (s : Set α) (t : ι -> Set β) : image2 f s (⋂ i,
 t i) subseteq ⋂ i, image2 f s (t i)
参数：s : Set α；t : ι -> Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem image2_iInter_subset_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋂ i, t i) ⊆ ⋂ i, image2 f s (t i) := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)
/-
**Set.image2_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image2_iInter₂_subset_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋂ (i) (j), s i j) t ⊆ ⋂ (i) (j), image2 f (s i j) t := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy
/-
**Set.image2_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image2_iInter₂_subset_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_subset_iff, mem_iInter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)
/-
**Set.image2_sInter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_sInter_subset_left (S : Set (Set α)) (t : Set β) : image2 f (⋂₀ S) 
t subseteq ⋂ s in S, image2 f s t
参数：S : Set (Set α)；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.image2_iInter₂_subset_left`：image2_iInter₂_subset_left (s : forall i
, κ i -> Set α) (t : Set β) : image2 f (⋂ (i) (j), s i j) t subseteq ⋂ (i) (j), 
image2 f (s i j) t
-/
theorem image2_sInter_subset_left (S : Set (Set α)) (t : Set β) :
    image2 f (⋂₀ S) t ⊆ ⋂ s ∈ S, image2 f s t := by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_left ..
/-
**Set.image2_sInter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_sInter_subset_right (s : Set α) (T : Set (Set β)) : image2 f s (⋂₀ 
T) subseteq ⋂ t in T, image2 f s t
参数：s : Set α；T : Set (Set β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.image2_iInter₂_subset_right`：image2_iInter₂_subset_right (s : Set α)
 (t : forall i, κ i -> Set β) : image2 f s (⋂ (i) (j), t i j) subseteq ⋂ (i) (j)
, image2 f s (t i j)
-/
theorem image2_sInter_subset_right (s : Set α) (T : Set (Set β)) :
    image2 f s (⋂₀ T) ⊆ ⋂ t ∈ T, image2 f s t := by
  rw [sInter_eq_biInter]
  exact image2_iInter₂_subset_right ..
/-
**Set.prod_eq_biUnion_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_eq_biUnion_left : s ×ˢ t = ⋃ a in s, (fun b => (a, b)) '' t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
· 使用定理 `Set.image2_mk_eq_prod`：∀ {α : Type u_1} {β : Type u_3} {s : Set α} {t : 
Set β}, Set.image2 Prod.mk s t = s ×ˢ t
-/
theorem prod_eq_biUnion_left : s ×ˢ t = ⋃ a ∈ s, (fun b => (a, b)) '' t := by
  rw [iUnion_image_left, image2_mk_eq_prod]
/-
**Set.prod_eq_biUnion_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_eq_biUnion_right : s ×ˢ t = ⋃ b in t, (fun a => (a, b)) '' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
· 使用定理 `Set.image2_mk_eq_prod`：∀ {α : Type u_1} {β : Type u_3} {s : Set α} {t : 
Set β}, Set.image2 Prod.mk s t = s ×ˢ t
-/
theorem prod_eq_biUnion_right : s ×ˢ t = ⋃ b ∈ t, (fun a => (a, b)) '' s := by
  rw [iUnion_image_right, image2_mk_eq_prod]

end Image2

section Seq

/-
**Set.seq_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seq_def {s : Set (α -> β)} {t : Set α} : seq s t = ⋃ f in s, f '' t
参数：α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.seq_eq_image2`：seq_eq_image2 (s : Set (α -> β)) (t : Set α) : seq s 
t = image2 (fun f a => f a) s t
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
theorem seq_def {s : Set (α → β)} {t : Set α} : seq s t = ⋃ f ∈ s, f '' t := by
  rw [seq_eq_image2, iUnion_image_left]
/-
**Set.seq_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seq_subset {s : Set (α -> β)} {t : Set α} {u : Set β} : seq s t subseteq u
 ↔ forall f in s, forall a in t, (f : α -> β) a in u
参数：α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
-/
theorem seq_subset {s : Set (α → β)} {t : Set α} {u : Set β} :
    seq s t ⊆ u ↔ ∀ f ∈ s, ∀ a ∈ t, (f : α → β) a ∈ u :=
  image2_subset_iff

@[gcongr, mono]
/-
**Set.seq_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seq_mono {s₀ s₁ : Set (α -> β)} {t₀ t₁ : Set α} (hs : s₀ subseteq s₁) (ht 
: t₀ subseteq t₁) : seq s₀ t₀ subseteq seq s₁ t₁
参数：α -> β；hs : s₀ subseteq s₁；ht : t₀ subseteq t₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
-/
theorem seq_mono {s₀ s₁ : Set (α → β)} {t₀ t₁ : Set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) :
    seq s₀ t₀ ⊆ seq s₁ t₁ := image2_subset hs ht
/-
**Set.singleton_seq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_seq {f : α -> β} {t : Set α} : Set.seq ({f} : Set (α -> β)) t = 
f '' t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_left`：image2_singleton_left : image2 f {a} t = f a 
'' t
-/
theorem singleton_seq {f : α → β} {t : Set α} : Set.seq ({f} : Set (α → β)) t = f '' t :=
  image2_singleton_left
/-
**Set.seq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seq_singleton {s : Set (α -> β)} {a : α} : Set.seq s {a} = (fun f : α -> β
 => f a) '' s
参数：α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
-/
theorem seq_singleton {s : Set (α → β)} {a : α} : Set.seq s {a} = (fun f : α → β => f a) '' s :=
  image2_singleton_right
/-
**Set.seq_seq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seq_seq {s : Set (β -> γ)} {t : Set (α -> β)} {u : Set α} : seq s (seq t u
) = seq (seq ((· ∘ ·) '' s) t) u
参数：β -> γ；α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_assoc`：image2_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' :
 α -> ε' -> ε} {g' : β -> γ -> ε'} (h_assoc : forall a b c, f (g a b) c = f' a (
g' b c…
-/
theorem seq_seq {s : Set (β → γ)} {t : Set (α → β)} {u : Set α} :
    seq s (seq t u) = seq (seq ((· ∘ ·) '' s) t) u := by
  simp only [seq_eq_image2, image2_image_left]
  exact .symm <| image2_assoc fun _ _ _ ↦ rfl
/-
**Set.image_seq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_seq {f : β -> γ} {s : Set (α -> β)} {t : Set α} : f '' seq s t = seq
 ((f ∘ ·) '' s) t
参数：α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image2`：image_image2 (f : α -> β -> γ) (g : γ -> δ) : g '' ima
ge2 f s t = image2 (fun a b => g (f a b)) s t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_seq {f : β → γ} {s : Set (α → β)} {t : Set α} :
    f '' seq s t = seq ((f ∘ ·) '' s) t := by
  simp only [seq, image_image2, image2_image_left, comp_apply]
/-
**Set.prod_eq_seq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.seq_eq_image2`：seq_eq_image2 (s : Set (α -> β)) (t : Set α) : seq s 
t = image2 (fun f a => f a) s t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_mk_eq_prod`：∀ {α : Type u_1} {β : Type u_3} {s : Set α} {t : 
Set β}, Set.image2 Prod.mk s t = s ×ˢ t
-/
theorem prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t := by
  rw [seq_eq_image2, image2_image_left, image2_mk_eq_prod]
/-
**Set.prod_image_seq_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_image_seq_comm (s : Set α) (t : Set β) : (Prod.mk '' s).seq t = seq (
(fun b a => (a, b)) '' t) s
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_eq_seq`：prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk
 '' s).seq t
· 使用定理 `Set.image_swap_prod`：image_swap_prod (s : Set α) (t : Set β) : Prod.swap
 '' s ×ˢ t = t ×ˢ s
· 使用定理 `Set.image_seq`：image_seq {f : β -> γ} {s : Set (α -> β)} {t : Set α} : f
 '' seq s t = seq ((f ∘ ·) '' s) t
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem prod_image_seq_comm (s : Set α) (t : Set β) :
    (Prod.mk '' s).seq t = seq ((fun b a => (a, b)) '' t) s := by
  rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp]; rfl
/-
**Set.image2_eq_seq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_eq_seq (f : α -> β -> γ) (s : Set α) (t : Set β) : image2 f s t = s
eq (f '' s) t
参数：f : α -> β -> γ；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.seq_eq_image2`：seq_eq_image2 (s : Set (α -> β)) (t : Set α) : seq s 
t = image2 (fun f a => f a) s t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
-/
theorem image2_eq_seq (f : α → β → γ) (s : Set α) (t : Set β) : image2 f s t = seq (f '' s) t := by
  rw [seq_eq_image2, image2_image_left]

end Seq

end Set

