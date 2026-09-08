/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Constructions
public import Mathlib.Data.Set.Notation

/-!
# Maps between matroids

This file defines maps and comaps, which move a matroid on one type to a matroid on another
using a function between the types. The constructions are (up to isomorphism)
just combinations of restrictions and parallel extensions, so are not mathematically difficult.

Because a matroid `M : Matroid α` is defined with am embedded ground set `M.E : Set α`
which contains all the structure of `M`, there are several types of map and comap
one could reasonably ask for;
for instance, we could map `M : Matroid α` to a `Matroid β` using either
a function `f : α → β`, a function `f : ↑M.E → β` or indeed a function `f : ↑M.E → ↑E`
for some `E : Set β`. We attempt to give definitions that capture most reasonable use cases.

`Matroid.map` and `Matroid.comap` are defined in terms of bare functions rather than
functions defined on subtypes, so are often easier to work in practice than the subtype variants.
In fact, the statement that `N = Matroid.map M f _` for some `f : α → β`
is equivalent to the existence of an isomorphism from `M` to `N`,
except in the trivial degenerate case where `M` is an empty matroid on a nonempty type and `N`
is an empty matroid on an empty type.
This can be simpler to use than an actual formal isomorphism, which requires subtypes.

## Main definitions

In the definitions below, `M` and `N` are matroids on `α` and `β` respectively.

* For `f : α → β`, `Matroid.comap N f` is the matroid on `α` with ground set `f ⁻¹' N.E`
  in which each `I` is independent if and only if `f` is injective on `I` and
  `f '' I` is independent in `N`.
  (For each nonloop `x` of `N`, the set `f ⁻¹' {x}` is a parallel class of `N.comap f`)

* `Matroid.comapOn N f E` is the restriction of `N.comap f` to `E` for some `E : Set α`.

* For an embedding `f : M.E ↪ β` defined on the subtype `↑M.E`,
  `Matroid.mapSetEmbedding M f` is the matroid on `β` with ground set `range f`
  whose independent sets are the images of those in `M`. This matroid is isomorphic to `M`.

* For a function `f : α → β` and a proof `hf` that `f` is injective on `M.E`,
  `Matroid.map f hf` is the matroid on `β` with ground set `f '' M.E`
  whose independent sets are the images of those in `M`. This matroid is isomorphic to `M`,
  and does not depend on the values `f` takes outside `M.E`.

* `Matroid.mapEmbedding f` is a version of `Matroid.map` where `f : α ↪ β` is a bundled embedding.
  It is defined separately because the global injectivity of `f` gives some nicer `simp` lemmas.

* `Matroid.mapEquiv f` is a version of `Matroid.map` where `f : α ≃ β` is a bundled equivalence.
  It is defined separately because we get even nicer `simp` lemmas.

* `Matroid.mapSetEquiv f` is a version of `Matroid.map` where `f : M.E ≃ E` is an equivalence on
  subtypes. It gives a matroid on `β` with ground set `E`.

* For `X : Set α`, `Matroid.restrictSubtype M X` is the `Matroid ↥X` with ground set
  `univ : Set ↥X`. This matroid is isomorphic to `M ↾ X`.

## Implementation details

The definition of `comap` is the only place where we need to actually define a matroid from scratch.
After `comap` is defined, we can define `map` and its variants indirectly in terms of `comap`.

If `f : α → β` is injective on `M.E`, the independent sets of `M.map f hf` are the images of
the independent set of `M`; i.e. `(M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀`.
But if `f` is globally injective, we can phrase this more directly;
indeed, `(M.map f _).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I ⊆ range f`.
If `f` is an equivalence we have `(M.map f _).Indep I ↔ M.Indep (f.symm '' I)`.
In order that these stronger statements can be `@[simp]`,
we define `mapEmbedding` and `mapEquiv` separately from `map`.

## Notes

For finite matroids, both maps and comaps are a special case of a construction of
Perfect [perfect1969matroid] in which a matroid structure can be transported across an arbitrary
bipartite graph that may not correspond to a function at all (See [oxley2011], Theorem 11.2.12).
It would have been nice to use this more general construction as a basis for the definition
of both `Matroid.map` and `Matroid.comap`.

Unfortunately, we can't do this, because the construction doesn't extend to infinite matroids.
Specifically, if `M₁` and `M₂` are matroids on the same type `α`,
and `f` is the natural function from `α ⊕ α` to `α`,
then the images under `f` of the independent sets of the direct sum `M₁ ⊕ M₂` are
the independent sets of a matroid if and only if the union of `M₁` and `M₂` is a matroid,
and unions do not exist for some pairs of infinite matroids: see [aignerhorev2012infinite].
For this reason, `Matroid.map` requires injectivity to be well-defined in general.

## TODO

* Bundled matroid isomorphisms.
* Maps of finite matroids across bipartite graphs.

## References

* [E. Aigner-Horev, J. Carmesin, J. Fröhlich, Infinite Matroid Union][aignerhorev2012infinite]
* [H. Perfect, Independence Spaces and Combinatorial Problems][perfect1969matroid]
* [J. Oxley, Matroid Theory][oxley2011]
-/

@[expose] public section

assert_not_exists Field

open Set Function Set.Notation
namespace Matroid
variable {α β : Type*} {f : α → β} {E I : Set α} {M : Matroid α} {N : Matroid β}

section comap

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`.
Elements with the same (nonloop) image are parallel and the ground set is `f ⁻¹' M.E`.
The matroids `M.comap f` and `M ↾ range f` have isomorphic simplifications;
the preimage of each nonloop of `M ↾ range f` is a parallel class. -/
/-
**Matroid.comap** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：comap (N : Matroid β) (f : α -> β) : Matroid α
参数：N : Matroid β；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`.
Elements with the same (nonloop) image are parallel and the ground set is `f ⁻¹'
 M.E`.
The matroids `M.comap f` and `M ↾ range f` have isomorphic simplifications;
the preimage of each nonloop of `M ↾ range f` is a parallel class.
-/
def comap (N : Matroid β) (f : α → β) : Matroid α :=
  IndepMatroid.matroid <|
  { E := f ⁻¹' N.E
    Indep := fun I ↦ N.Indep (f '' I) ∧ InjOn f I
    indep_empty := by simp
    indep_subset := fun _ _ h hIJ ↦ ⟨h.1.subset (image_mono hIJ), InjOn.mono hIJ h.2⟩
    indep_aug := by
      rintro I B ⟨hI, hIinj⟩ hImax hBmax
      obtain ⟨I', hII', hI', hI'inj⟩ := (not_maximal_subset_iff ⟨hI, hIinj⟩).1 hImax
      have h₁ : ¬(N ↾ range f).IsBase (f '' I) := by
        refine fun hB ↦ hII'.ne ?_
        have h_im := hB.eq_of_subset_indep (by simpa) (image_mono hII'.subset)
        rwa [hI'inj.image_eq_image_iff hII'.subset Subset.rfl] at h_im
      have h₂ : (N ↾ range f).IsBase (f '' B) := by
        refine Indep.isBase_of_forall_insert (by simpa using hBmax.1.1) ?_
        rintro _ ⟨⟨e, heB, rfl⟩, hfe⟩ hi
        rw [restrict_indep_iff, ← image_insert_eq] at hi
        have hinj : InjOn f (insert e B) := by
          rw [injOn_insert (fun heB ↦ hfe (mem_image_of_mem f heB))]
          exact ⟨hBmax.1.2, hfe⟩
        refine hBmax.not_prop_of_ssuperset (t := insert e B) (ssubset_insert ?_) ⟨hi.1, hinj⟩
        exact fun heB ↦ hfe <| mem_image_of_mem f heB
      obtain ⟨_, ⟨⟨e, he, rfl⟩, he'⟩, hei⟩ := Indep.exists_insert_of_not_isBase (by simpa) h₁ h₂
      have heI : e ∉ I := fun heI ↦ he' (mem_image_of_mem f heI)
      rw [← image_insert_eq, restrict_indep_iff] at hei
      exact ⟨e, ⟨he, heI⟩, hei.1, (injOn_insert heI).2 ⟨hIinj, he'⟩⟩

    indep_maximal := by
      rintro X - I ⟨hI, hIinj⟩ hIX
      obtain ⟨J, hJ⟩ := (N ↾ range f).existsMaximalSubsetProperty_indep (f '' X) (by simp)
        (f '' I) (by simpa) (image_mono hIX)
      simp only [restrict_indep_iff, image_subset_iff, maximal_subset_iff, and_imp,
        and_assoc] at hJ ⊢
      obtain ⟨hIJ, hJ, hJf, hJX, hJmax⟩ := hJ
      obtain ⟨J₀, hIJ₀, hJ₀X, hbj⟩ := hIinj.bijOn_image.exists_extend_of_subset hIX
        (image_mono hIJ) (image_subset_iff.2 <| preimage_mono hJX)
      obtain rfl : f '' J₀ = J := by rw [← image_preimage_eq_of_subset hJf, hbj.image_eq]
      refine ⟨J₀, hIJ₀, hJ, hbj.injOn, hJ₀X, fun K hK hKinj hKX hJ₀K ↦ ?_⟩
      rw [← hKinj.image_eq_image_iff hJ₀K Subset.rfl, hJmax hK (image_subset_range _ _)
        (image_mono hKX) (image_mono hJ₀K)]
    subset_ground := fun _ hI e heI ↦ hI.1.subset_ground ⟨e, heI, rfl⟩ }
/-
**Matroid.comap_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {I : Set α} {N : Matroid β},  
 (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ Set.InjOn f I
参数：N.comap f；f '' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma comap_indep_iff : (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ InjOn f I := Iff.rfl
/-
**Matroid.comap_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (N : Matroid β) (f : α → β), (N.comap f).E
 = f ⁻¹' N.E
参数：N : Matroid β；f : α → β；N.comap f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_ground_eq (N : Matroid β) (f : α → β) : (N.comap f).E = f ⁻¹' N.E := rfl
/-
**Matroid.comap_dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {I : Set α} {N : Matroid β},  
 (N.comap f).Dep I ↔ N.Dep (f '' I) ∨ N.Indep (f '' I) ∧ ¬Set.InjOn f I
参数：N.comap f；f '' I；f '' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Dep.eq_1`：∀ {α : Type u_1} (M : Matroid α) (D : Set α), M.Dep D 
= (¬M.Indep D ∧ D ⊆ M.E)
· 使用定理 `Matroid.comap_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {I 
: Set α} {N : Matroid β},   (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ Set.InjOn f
 I
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `Matroid.comap_ground_eq`：∀ {α : Type u_1} {β : Type u_2} (N : Matroid β)
 (f : α → β), (N.comap f).E = f ⁻¹' N.E
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
@[simp] lemma comap_dep_iff :
    (N.comap f).Dep I ↔ N.Dep (f '' I) ∨ (N.Indep (f '' I) ∧ ¬ InjOn f I) := by
  rw [Dep, comap_indep_iff, not_and, comap_ground_eq, Dep, image_subset_iff]
  refine ⟨by grind, ?_⟩
  rintro (⟨hI, hIE⟩ | hI)
  · exact ⟨fun h ↦ (hI h).elim, hIE⟩
  rw [iff_true_intro hI.1, iff_true_intro hI.2, implies_true, true_and]
  simpa using hI.1.subset_ground
/-
**Matroid.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {β : Type u_2} (N : Matroid β), N.comap id = N
参数：N : Matroid β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma comap_id (N : Matroid β) : N.comap id = N :=
  ext_indep rfl <| by simp [injective_id.injOn]
/-
**Matroid.comap_indep_iff_of_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comap_indep_iff_of_injOn (hf : InjOn f (f ⁻¹' N.E)) : (N.comap f).Indep I 
↔ N.Indep (f '' I)
参数：hf : InjOn f (f ⁻¹' N.E)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.comap_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {I 
: Set α} {N : Matroid β},   (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ Set.InjOn f
 I
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
lemma comap_indep_iff_of_injOn (hf : InjOn f (f ⁻¹' N.E)) :
    (N.comap f).Indep I ↔ N.Indep (f '' I) := by
  rw [comap_indep_iff, and_iff_left_iff_imp]
  refine fun hi ↦ hf.mono <| subset_trans ?_ (preimage_mono hi.subset_ground)
  apply subset_preimage_image
/-
**Matroid.comap_emptyOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β), (Matroid.emptyOn β).comap f =
 Matroid.emptyOn α
参数：f : α → β；Matroid.emptyOn β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma comap_emptyOn (f : α → β) : comap (emptyOn β) f = emptyOn α := by
  simp [← ground_eq_empty_iff]
/-
**Matroid.comap_loopyOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (E : Set β), (Matroid.loopyOn 
E).comap f = Matroid.loopyOn (f ⁻¹' E)
参数：f : α → β；E : Set β；Matroid.loopyOn E；f ⁻¹' E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.eq_loopyOn_iff`：eq_loopyOn_iff : M = loopyOn E ↔ M.E = E ∧ foral
l X subseteq M.E, M.Indep X -> X = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma comap_loopyOn (f : α → β) (E : Set β) : comap (loopyOn E) f = loopyOn (f ⁻¹' E) := by
  rw [eq_loopyOn_iff]; aesop
/-
**Matroid.comap_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {N : Matroid β} {I X : Set α},
   (N.comap f).IsBasis I X ↔ N.IsBasis (f '' I) (f '' X) ∧ Set.InjOn f I ∧ I ⊆ X
参数：N.comap f；f '' I；f '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.comap_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {I 
: Set α} {N : Matroid β},   (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ Set.InjOn f
 I
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.Indep.isBasis_of_forall_insert`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α}, M.Indep I → I ⊆ X → (∀ e ∈ X \ I, M.Dep (insert e I)) → M.IsBasi
s I X
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matroid.IsBasis.insert_dep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set 
α} {e : α}, M.IsBasis I X → e ∈ X \ I → M.Dep (insert e I)
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.injOn_insert`：injOn_insert {f : α -> β} {s : Set α} {a : α} (has : a
 ∉ s) : Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.IsBasis.mem_of_insert_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 X : Set α} {e : α}, M.IsBasis I X → e ∈ X → M.Indep (insert e I) → e ∈ I
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
-/
@[simp] lemma comap_isBasis_iff {I X : Set α} :
    (N.comap f).IsBasis I X ↔ N.IsBasis (f '' I) (f '' X) ∧ I.InjOn f ∧ I ⊆ X := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨hI, hinj⟩ := comap_indep_iff.1 h.indep
    refine ⟨hI.isBasis_of_forall_insert (image_mono h.subset) fun e he ↦ ?_, hinj, h.subset⟩
    simp only [mem_sdiff, mem_image, not_exists, not_and] at he
    obtain ⟨⟨e, heX, rfl⟩, he⟩ := he
    have heI : e ∉ I := fun heI ↦ (he e heI rfl)
    replace h := h.insert_dep ⟨heX, heI⟩
    simp only [comap_dep_iff, image_insert_eq, or_iff_not_imp_right, injOn_insert heI,
      hinj, mem_image, not_exists, not_and, true_and, not_forall, not_not] at h
    exact h (fun _ ↦ he)
  refine Indep.isBasis_of_forall_insert ?_ h.2.2 fun e ⟨heX, heI⟩ ↦ ?_
  · simp [comap_indep_iff, h.1.indep, h.2]
  have hIE : insert e I ⊆ (N.comap f).E := by
      simp_rw [comap_ground_eq, ← image_subset_iff]
      exact (image_mono (insert_subset heX h.2.2)).trans h.1.subset_ground
  suffices N.Indep (insert (f e) (f '' I)) → ∃ x ∈ I, f x = f e
    by simpa [← not_indep_iff hIE, injOn_insert heI, h.2.1, image_insert_eq]
  exact h.1.mem_of_insert_indep (mem_image_of_mem f heX)
/-
**Matroid.comap_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {N : Matroid β} {B : Set α},  
 (N.comap f).IsBase B ↔ N.IsBasis (f '' B) (f '' f ⁻¹' N.E) ∧ Set.InjOn f B ∧ B 
⊆ f ⁻¹' N.E
参数：N.comap f；f '' B；f '' f ⁻¹' N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用定理 `Matroid.comap_isBasis_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
N : Matroid β} {I X : Set α},   (N.comap f).IsBasis I X ↔ N.IsBasis (f '' I) (f 
'' X) ∧ Set.Inj…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma comap_isBase_iff {B : Set α} :
    (N.comap f).IsBase B ↔ N.IsBasis (f '' B) (f '' f ⁻¹' N.E) ∧ B.InjOn f ∧ B ⊆ f ⁻¹' N.E := by
  rw [← isBasis_ground_iff, comap_isBasis_iff]; rfl
/-
**Matroid.comap_isBasis'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {N : Matroid β} {I X : Set α},
   (N.comap f).IsBasis' I X ↔ N.IsBasis' (f '' I) (f '' X) ∧ Set.InjOn f I ∧ I ⊆
 X
参数：N.comap f；f '' I；f '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
@[simp] lemma comap_isBasis'_iff {I X : Set α} :
    (N.comap f).IsBasis' I X ↔ N.IsBasis' (f '' I) (f '' X) ∧ I.InjOn f ∧ I ⊆ X := by
  simp only [isBasis'_iff_isBasis_inter_ground, comap_ground_eq, comap_isBasis_iff,
    image_inter_preimage, subset_inter_iff, ← and_assoc, and_iff_left_iff_imp,
    and_imp]
  exact fun h _ _ ↦ (image_subset_iff.1 h.indep.subset_ground)
/-
**Matroid.comap_finitary** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：comap_finitary (N : Matroid β) [N.Finitary] (f : α -> β) : (N.comap f).Fin
itary
参数：N : Matroid β；f : α -> β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.comap_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {I 
: Set α} {N : Matroid β},   (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ Set.InjOn f
 I
· 使用定理 `Matroid.indep_iff_forall_finite_subset_indep`：indep_iff_forall_finite_su
bset_indep {M : Matroid α} [Finitary M] : M.Indep I ↔ forall J, J subseteq I -> 
J.Finite -> M.Indep J
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.SurjOn.exists_bijOn_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β}, Set.SurjOn f s t → ∃ s' ⊆ s, Set.BijOn f s' t
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.pair_subset`：pair_subset (ha : a in s) (hb : b in s) : {a, b} subset
eq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
instance comap_finitary (N : Matroid β) [N.Finitary] (f : α → β) : (N.comap f).Finitary := by
  refine ⟨fun I hI ↦ ?_⟩
  rw [comap_indep_iff, indep_iff_forall_finite_subset_indep]
  simp only [forall_subset_image_iff]
  refine ⟨fun J hJ hfin ↦ ?_,
    fun x hx y hy ↦ (hI _ (pair_subset hx hy) (by simp)).2 (by simp) (by simp)⟩
  obtain ⟨J', hJ'J, hJ'⟩ := (surjOn_image f J).exists_bijOn_subset
  rw [← hJ'.image_eq] at hfin ⊢
  exact (hI J' (hJ'J.trans hJ) (hfin.of_finite_image hJ'.injOn)).1
/-
**Matroid.comap_rankFinite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：comap_rankFinite (N : Matroid β) [N.RankFinite] (f : α -> β) : (N.comap f)
.RankFinite
参数：N : Matroid β；f : α -> β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.IsBase.rankFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} {B
 : Set α}, M.IsBase B → B.Finite → M.RankFinite
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Matroid.Indep.finite`：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [M.Ra
nkFinite], M.Indep I → I.Finite
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance comap_rankFinite (N : Matroid β) [N.RankFinite] (f : α → β) : (N.comap f).RankFinite := by
  obtain ⟨B, hB⟩ := (N.comap f).exists_isBase
  refine hB.rankFinite_of_finite ?_
  simp only [comap_isBase_iff] at hB
  exact (hB.1.indep.finite.of_finite_image hB.2.1)

end comap

section comapOn

variable {E B I : Set α}

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`,
restricted to a ground set `E`.
The matroids `M.comapOn f E` and `M ↾ (f '' E)` have isomorphic simplifications;
elements with the same nonloop image are parallel. -/
/-
**Matroid.comapOn** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：comapOn (N : Matroid β) (E : Set α) (f : α -> β) : Matroid α
参数：N : Matroid β；E : Set α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`,
restricted to a ground set `E`.
The matroids `M.comapOn f E` and `M ↾ (f '' E)` have isomorphic simplifications;
elements with the same nonloop image are parallel.
-/
def comapOn (N : Matroid β) (E : Set α) (f : α → β) : Matroid α := (N.comap f) ↾ E
/-
**Matroid.comapOn_preimage_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comapOn_preimage_eq (N : Matroid β) (f : α -> β) : N.comapOn (f ⁻¹' N.E) f
 = N.comap f
参数：N : Matroid β；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.comapOn.eq_1`：∀ {α : Type u_1} {β : Type u_2} (N : Matroid β) (E
 : Set α) (f : α → β), N.comapOn E f = (N.comap f).restrict E
· 使用定理 `Matroid.restrict_eq_self_iff`：∀ {α : Type u_1} {M : Matroid α} {R : Set 
α}, M.restrict R = M ↔ R = M.E
-/
lemma comapOn_preimage_eq (N : Matroid β) (f : α → β) : N.comapOn (f ⁻¹' N.E) f = N.comap f := by
  rw [comapOn, restrict_eq_self_iff]; rfl
/-
**Matroid.comapOn_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {N : Matroid β} {E I : Set α},
   (N.comapOn E f).Indep I ↔ N.Indep (f '' I) ∧ Set.InjOn f I ∧ I ⊆ E
参数：N.comapOn E f；f '' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma comapOn_indep_iff :
    (N.comapOn E f).Indep I ↔ (N.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by
  simp [comapOn, and_assoc]
/-
**Matroid.comapOn_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {N : Matroid β} {E : Set α}, (
N.comapOn E f).E = E
参数：N.comapOn E f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comapOn_ground_eq : (N.comapOn E f).E = E := rfl
/-
**Matroid.comapOn_isBase_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comapOn_isBase_iff : (N.comapOn E f).IsBase B ↔ N.IsBasis' (f '' B) (f '' 
E) ∧ B.InjOn f ∧ B subseteq E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.comapOn.eq_1`：∀ {α : Type u_1} {β : Type u_2} (N : Matroid β) (E
 : Set α) (f : α → β), N.comapOn E f = (N.comap f).restrict E
· 使用定理 `Matroid.isBase_restrict_iff'`：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ 
M.IsBasis' I X
· 使用定理 `Matroid.comap_isBasis'_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{N : Matroid β} {I X : Set α},   (N.comap f).IsBasis' I X ↔ N.IsBasis' (f '' I) 
(f '' X) ∧ Set.I…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma comapOn_isBase_iff :
    (N.comapOn E f).IsBase B ↔ N.IsBasis' (f '' B) (f '' E) ∧ B.InjOn f ∧ B ⊆ E := by
  rw [comapOn, isBase_restrict_iff', comap_isBasis'_iff]
/-
**Matroid.comapOn_isBase_iff_of_surjOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comapOn_isBase_iff_of_surjOn (h : SurjOn f E N.E) : (N.comapOn E f).IsBase
 B ↔ (N.IsBase (f '' B) ∧ InjOn f B ∧ B subseteq E)
参数：h : SurjOn f E N.E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma comapOn_isBase_iff_of_surjOn (h : SurjOn f E N.E) :
    (N.comapOn E f).IsBase B ↔ (N.IsBase (f '' B) ∧ InjOn f B ∧ B ⊆ E) := by
  simp_rw [comapOn_isBase_iff, and_congr_left_iff, and_imp, isBasis'_iff_isBasis_inter_ground,
    inter_eq_self_of_subset_right h, isBasis_ground_iff, implies_true]
/-
**Matroid.comapOn_isBase_iff_of_bijOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comapOn_isBase_iff_of_bijOn (h : BijOn f E N.E) : (N.comapOn E f).IsBase B
 ↔ N.IsBase (f '' B) ∧ B subseteq E
参数：h : BijOn f E N.E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Matroid.comapOn_ground_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
N : Matroid β} {E : Set α}, (N.comapOn E f).E = E
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matroid.comapOn_isBase_iff_of_surjOn`：comapOn_isBase_iff_of_surjOn (h : 
SurjOn f E N.E) : (N.comapOn E f).IsBase B ↔ (N.IsBase (f '' B) ∧ InjOn f B ∧ B 
subseteq E)
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comapOn_isBase_iff_of_bijOn (h : BijOn f E N.E) :
    (N.comapOn E f).IsBase B ↔ N.IsBase (f '' B) ∧ B ⊆ E := by
  rw [← and_iff_left_of_imp (IsBase.subset_ground (M := N.comapOn E f) (B := B)),
    comapOn_ground_eq, and_congr_left_iff]
  suffices h' : B ⊆ E → InjOn f B from fun hB ↦
    by simp [hB, comapOn_isBase_iff_of_surjOn h.surjOn, h']
  exact fun hBE ↦ h.injOn.mono hBE
/-
**Matroid.comapOn_dual_eq_of_bijOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comapOn_dual_eq_of_bijOn (h : BijOn f E N.E) : (N.comapOn E f)✶ = N✶.comap
On E f
参数：h : BijOn f E N.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_isBase`：ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h
 : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.comapOn_isBase_iff_of_bijOn`：comapOn_isBase_iff_of_bijOn (h : Bi
jOn f E N.E) : (N.comapOn E f).IsBase B ↔ N.IsBase (f '' B) ∧ B subseteq E
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Matroid.comapOn_ground_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
N : Matroid β} {E : Set α}, (N.comapOn E f).E = E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.InjOn.image_sdiff_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {f : α → β} {t : Set α},   Set.InjOn f s → t ⊆ s → f '' (s \ t) = f '' s \ f '
' t
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma comapOn_dual_eq_of_bijOn (h : BijOn f E N.E) :
    (N.comapOn E f)✶ = N✶.comapOn E f := by
  refine ext_isBase (by simp) (fun B hB ↦ ?_)
  rw [comapOn_isBase_iff_of_bijOn (by simpa), dual_isBase_iff, comapOn_isBase_iff_of_bijOn h,
    dual_isBase_iff _, comapOn_ground_eq, and_iff_left sdiff_subset, and_iff_left (by simpa),
    h.injOn.image_sdiff_subset (by simpa), h.image_eq]
  exact (h.mapsTo.mono_left (show B ⊆ E by simpa)).image_subset
/-
**Matroid.comapOn_finitary** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：comapOn_finitary [N.Finitary] : (N.comapOn E f).Finitary
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.comapOn.eq_1`：∀ {α : Type u_1} {β : Type u_2} (N : Matroid β) (E
 : Set α) (f : α → β), N.comapOn E f = (N.comap f).restrict E
-/
instance comapOn_finitary [N.Finitary] : (N.comapOn E f).Finitary := by
  rw [comapOn]; infer_instance
/-
**Matroid.comapOn_rankFinite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：comapOn_rankFinite [N.RankFinite] : (N.comapOn E f).RankFinite
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.comapOn.eq_1`：∀ {α : Type u_1} {β : Type u_2} (N : Matroid β) (E
 : Set α) (f : α → β), N.comapOn E f = (N.comap f).restrict E
-/
instance comapOn_rankFinite [N.RankFinite] : (N.comapOn E f).RankFinite := by
  rw [comapOn]; infer_instance

end comapOn
section mapSetEmbedding

set_option backward.isDefEq.respectTransparency false in
/-- Map a matroid `M` to an isomorphic copy in `β` using an embedding `M.E ↪ β`. -/
/-
**Matroid.mapSetEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：mapSetEmbedding (M : Matroid α) (f : M.E ↪ β) : Matroid β
参数：M : Matroid α；f : M.E ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a matroid `M` to an isomorphic copy in `β` using an embedding `M.E ↪ β`.
-/
def mapSetEmbedding (M : Matroid α) (f : M.E ↪ β) : Matroid β := Matroid.ofExistsMatroid
  (E := range f)
  (Indep := fun I ↦ M.Indep ↑(f ⁻¹' I) ∧ I ⊆ range f)
  (hM := by
    obtain (rfl | ⟨⟨e, he⟩⟩) := eq_emptyOn_or_nonempty M
    · refine ⟨emptyOn β, ?_⟩
      simp only [emptyOn_ground] at f
      simp [range_eq_empty f, subset_empty_iff]
    have _ : Nonempty M.E := ⟨⟨e,he⟩⟩
    have _ : Nonempty α := ⟨e⟩
    refine ⟨M.comapOn (range f) (fun x ↦ ↑(invFunOn f univ x)), rfl, ?_⟩
    simp_rw [comapOn_indep_iff, ← and_assoc, and_congr_left_iff, subset_range_iff_exists_image_eq]
    rintro _ ⟨I, rfl⟩
    rw [← image_image, InjOn.invFunOn_image f.injective.injOn (subset_univ _),
      preimage_image_eq _ f.injective, and_iff_left_iff_imp]
    rintro - x hx y hy
    simp only [Subtype.val_inj]
    exact (invFunOn_injOn_image f univ) (image_mono (subset_univ I) hx)
      (image_mono (subset_univ I) hy))
/-
**Matroid.mapSetEmbedding_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) (f : ↑M.E ↪ β), (M.mapSetE
mbedding f).E = Set.range ⇑f
参数：M : Matroid α；f : ↑M.E ↪ β；M.mapSetEmbedding f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapSetEmbedding_ground (M : Matroid α) (f : M.E ↪ β) :
    (M.mapSetEmbedding f).E = range f := rfl
/-
**Matroid.mapSetEmbedding_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {f : ↑M.E ↪ β} {I : Set β}
,   (M.mapSetEmbedding f).Indep I ↔ M.Indep (Subtype.val '' ⇑f ⁻¹' I) ∧ I ⊆ Set.
range ⇑f
参数：M.mapSetEmbedding f；Subtype.val '' ⇑f ⁻¹' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mapSetEmbedding_indep_iff {f : M.E ↪ β} {I : Set β} :
    (M.mapSetEmbedding f).Indep I ↔ M.Indep ↑(f ⁻¹' I) ∧ I ⊆ range f := Iff.rfl
/-
**Matroid.Indep.exists_eq_image_of_mapSetEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Ma
troid.Indep`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {f : ↑M.E ↪ β} {I : Set β}
,   (M.mapSetEmbedding f).Indep I → ∃ I₀, M.Indep (Subtype.val '' I₀) ∧ I = ⇑f '
' I₀
参数：M.mapSetEmbedding f；Subtype.val '' I₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Indep.exists_eq_image_of_mapSetEmbedding {f : M.E ↪ β} {I : Set β}
    (hI : (M.mapSetEmbedding f).Indep I) : ∃ (I₀ : Set M.E), M.Indep I₀ ∧ I = f '' I₀ :=
  ⟨f ⁻¹' I, hI.1, Eq.symm <| image_preimage_eq_of_subset hI.2⟩
/-
**Matroid.mapSetEmbedding_indep_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mapSetEmbedding_indep_iff' {f : M.E ↪ β} {I : Set β} : (M.mapSetEmbedding 
f).Indep I ↔ exists (I₀ : Set M.E), M.Indep ↑I₀ ∧ I = f '' I₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mapSetEmbedding_indep_iff' {f : M.E ↪ β} {I : Set β} :
    (M.mapSetEmbedding f).Indep I ↔ ∃ (I₀ : Set M.E), M.Indep ↑I₀ ∧ I = f '' I₀ := by
  simp only [mapSetEmbedding_indep_iff, subset_range_iff_exists_image_eq]
  constructor
  · rintro ⟨hI, I, rfl⟩
    exact ⟨I, by rwa [preimage_image_eq _ f.injective] at hI, rfl⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, _, rfl⟩

end mapSetEmbedding

section map

/-- Given a function `f` that is injective on `M.E`, the copy of `M` in `β` whose independent sets
are the images of those in `M`. If `β` is a nonempty type, then `N : Matroid β` is a map of `M`
if and only if `M` and `N` are isomorphic. -/
/-
**Matroid.map** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：map (M : Matroid α) (f : α -> β) (hf : InjOn f M.E) : Matroid β
参数：M : Matroid α；f : α -> β；hf : InjOn f M.E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f` that is injective on `M.E`, the copy of `M` in `β` whose in
dependent sets
are the images of those in `M`. If `β` is a nonempty type, then `N : Matroid β` 
is a map of `M`
if and only if `M` and `N` are isomorphic.
-/
def map (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Matroid β := Matroid.ofExistsMatroid
  (E := f '' M.E)
  (Indep := fun I ↦ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀)
  (hM := by
    refine ⟨M.mapSetEmbedding ⟨_, hf.injective⟩, by simp, fun I ↦ ?_⟩
    simp_rw [mapSetEmbedding_indep_iff', Embedding.coeFn_mk, domRestrict_apply,
      ← image_image f Subtype.val, Subtype.exists_set_subtype (p := fun J ↦ M.Indep J ∧ I = f '' J)]
    exact ⟨fun ⟨I₀, _, hI₀⟩ ↦ ⟨I₀, hI₀⟩, fun ⟨I₀, hI₀⟩ ↦ ⟨I₀, hI₀.1.subset_ground, hI₀⟩⟩)
/-
**Matroid.map_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) (f : α → β) (hf : Set.InjO
n f M.E), (M.map f hf).E = f '' M.E
参数：M : Matroid α；f : α → β；hf : Set.InjOn f M.E；M.map f hf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_ground (M : Matroid α) (f : α → β) (hf) : (M.map f hf).E = f '' M.E := rfl
/-
**Matroid.map_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : Matroid α} {hf : Set.InjO
n f M.E} {I : Set β},   (M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀
参数：M.map f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma map_indep_iff {hf} {I : Set β} :
    (M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀ := Iff.rfl
/-
**Matroid.Indep.map** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Matroid α},   M.Indep I →
 ∀ (f : α → β) (hf : Set.InjOn f M.E), (M.map f hf).Indep (f '' I)
参数：f : α → β；hf : Set.InjOn f M.E；M.map f hf；f '' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.map_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : 
Matroid α} {hf : Set.InjOn f M.E} {I : Set β},   (M.map f hf).Indep I ↔ ∃ I₀, M.
Indep I₀ ∧ …
-/
lemma Indep.map (hI : M.Indep I) (f : α → β) (hf) : (M.map f hf).Indep (f '' I) :=
  map_indep_iff.2 ⟨I, hI, rfl⟩
/-
**Matroid.Indep.exists_bijOn_of_map** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : Matroid α} {I : Set β} (h
f : Set.InjOn f M.E),   (M.map f hf).Indep I → ∃ I₀, M.Indep I₀ ∧ Set.BijOn f I₀
 I
参数：hf : Set.InjOn f M.E；M.map f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Indep.exists_bijOn_of_map {I : Set β} (hf) (hI : (M.map f hf).Indep I) :
    ∃ I₀, M.Indep I₀ ∧ BijOn f I₀ I := by
  obtain ⟨I₀, hI₀, rfl⟩ := hI
  exact ⟨I₀, hI₀, (hf.mono hI₀.subset_ground).bijOn_image⟩
/-
**Matroid.map_image_indep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_image_indep_iff {hf} {I : Set α} (hI : I subseteq M.E) : (M.map f hf).
Indep (f '' I) ↔ M.Indep I
参数：hI : I subseteq M.E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.map_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : 
Matroid α} {hf : Set.InjOn f M.E} {I : Set β},   (M.map f hf).Indep I ↔ ∃ I₀, M.
Indep I₀ ∧ …
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
lemma map_image_indep_iff {hf} {I : Set α} (hI : I ⊆ M.E) :
    (M.map f hf).Indep (f '' I) ↔ M.Indep I := by
  rw [map_indep_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ ↦ ?_, fun h ↦ ⟨I, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hI hJ.subset_ground] at hIJ; rwa [hIJ]
/-
**Matroid.map_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) (f : α → β) (hf : Set.InjO
n f M.E) {B : Set β},   (M.map f hf).IsBase B ↔ ∃ B₀, M.IsBase B₀ ∧ B = f '' B₀
参数：M : Matroid α；f : α → β；hf : Set.InjOn f M.E；M.map f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_iff_maximal_indep`：isBase_iff_maximal_indep : M.IsBase B 
↔ Maximal M.Indep B
· 使用定理 `Matroid.Indep.exists_bijOn_of_map`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β} {M : Matroid α} {I : Set β} (hf : Set.InjOn f M.E),   (M.map f hf).Indep 
I → ∃ I₀, M.Indep I₀ ∧ …
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Matroid.Indep.isBase_of_maximal`：∀ {α : Type u_1} {M : Matroid α} {I : S
et α}, M.Indep I → (∀ ⦃J : Set α⦄, M.Indep J → I ⊆ J → I = J) → M.IsBase I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Maximal.eq_of_subset`：Maximal.eq_of_subset (h : Maximal P s) (ht : P t) 
(hst : s subseteq t) : s = t
· 使用定理 `Matroid.Indep.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Matr
oid α},   M.Indep I → ∀ (f : α → β) (hf : Set.InjOn f M.E), (M.map f hf).Indep (
f '' I)
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `maximal_subset_iff`：maximal_subset_iff : Maximal P s ↔ P s ∧ forall ⦃t⦄,
 P t -> s subseteq t -> s = t
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Matroid.IsBase.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {B I
 : Set α}, M.IsBase B → M.Indep I → B ⊆ I → B = I
· 使用定理 `Set.InjOn.image_subset_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ 
s₂ : Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ ⊆ f '' s₂ 
↔ s₁ ⊆ s₂)
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
@[simp] lemma map_isBase_iff (M : Matroid α) (f : α → β) (hf) {B : Set β} :
    (M.map f hf).IsBase B ↔ ∃ B₀, M.IsBase B₀ ∧ B = f '' B₀ := by
  rw [isBase_iff_maximal_indep]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨B₀, hB₀, hbij⟩ := h.prop.exists_bijOn_of_map
    refine ⟨B₀, hB₀.isBase_of_maximal fun J hJ hB₀J ↦ ?_, hbij.image_eq.symm⟩
    rw [← hf.image_eq_image_iff hB₀.subset_ground hJ.subset_ground, hbij.image_eq]
    exact h.eq_of_subset (hJ.map f hf) (hbij.image_eq ▸ image_mono hB₀J)
  rintro ⟨B, hB, rfl⟩
  rw [maximal_subset_iff]
  refine ⟨hB.indep.map f hf, fun I hI hBI ↦ ?_⟩
  obtain ⟨I₀, hI₀, hbij⟩ := hI.exists_bijOn_of_map
  rw [← hbij.image_eq, hf.image_subset_image_iff hB.subset_ground hI₀.subset_ground] at hBI
  rw [hB.eq_of_subset_indep hI₀ hBI, hbij.image_eq]
/-
**Matroid.IsBase.map** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {B : Set α},   M.IsBase B 
→ ∀ {f : α → β} (hf : Set.InjOn f M.E), (M.map f hf).IsBase (f '' B)
参数：hf : Set.InjOn f M.E；M.map f hf；f '' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.map_isBase_iff`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) 
(f : α → β) (hf : Set.InjOn f M.E) {B : Set β},   (M.map f hf).IsBase B ↔ ∃ B₀, 
M.IsBase B₀ …
-/
lemma IsBase.map {B : Set α} (hB : M.IsBase B) {f : α → β} (hf) : (M.map f hf).IsBase (f '' B) := by
  rw [map_isBase_iff]; exact ⟨B, hB, rfl⟩
/-
**Matroid.map_dep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_dep_iff {hf} {D : Set β} : (M.map f hf).Dep D ↔ exists D₀, M.Dep D₀ ∧ 
D = f '' D₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma map_dep_iff {hf} {D : Set β} :
    (M.map f hf).Dep D ↔ ∃ D₀, M.Dep D₀ ∧ D = f '' D₀ := by
  simp only [Dep, map_indep_iff, not_exists, not_and, map_ground, subset_image_iff]
  constructor
  · rintro ⟨h, D₀, hD₀E, rfl⟩
    exact ⟨D₀, ⟨fun hd ↦ h _ hd rfl, hD₀E⟩, rfl⟩
  rintro ⟨D₀, ⟨hD₀, hD₀E⟩, rfl⟩
  refine ⟨fun I hI h_eq ↦ ?_, ⟨_, hD₀E, rfl⟩⟩
  rw [hf.image_eq_image_iff hD₀E hI.subset_ground] at h_eq
  subst h_eq; contradiction
/-
**Matroid.map_image_isBase_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_image_isBase_iff {hf} {B : Set α} (hB : B subseteq M.E) : (M.map f hf)
.IsBase (f '' B) ↔ M.IsBase B
参数：hB : B subseteq M.E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.map_isBase_iff`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) 
(f : α → β) (hf : Set.InjOn f M.E) {B : Set β},   (M.map f hf).IsBase B ↔ ∃ B₀, 
M.IsBase B₀ …
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
lemma map_image_isBase_iff {hf} {B : Set α} (hB : B ⊆ M.E) :
    (M.map f hf).IsBase (f '' B) ↔ M.IsBase B := by
  rw [map_isBase_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ ↦ ?_, fun h ↦ ⟨B, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hB hJ.subset_ground] at hIJ; rwa [hIJ]
/-
**Matroid.IsBasis.map** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Matroid α} {X : Set α},  
 M.IsBasis I X → ∀ {f : α → β} (hf : Set.InjOn f M.E), (M.map f hf).IsBasis (f '
' I) (f '' X)
参数：hf : Set.InjOn f M.E；M.map f hf；f '' I；f '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBasis_of_forall_insert`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α}, M.Indep I → I ⊆ X → (∀ e ∈ X \ I, M.Dep (insert e I)) → M.IsBasi
s I X
· 使用定理 `Matroid.Indep.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Matr
oid α},   M.Indep I → ∀ (f : α → β) (hf : Set.InjOn f M.E), (M.map f hf).Indep (
f '' I)
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Matroid.IsBasis.mem_of_insert_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 X : Set α} {e : α}, M.IsBasis I X → e ∈ X → M.Indep (insert e I) → e ∈ I
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
-/
lemma IsBasis.map {X : Set α} (hIX : M.IsBasis I X) {f : α → β} (hf) :
    (M.map f hf).IsBasis (f '' I) (f '' X) := by
  refine (hIX.indep.map f hf).isBasis_of_forall_insert (image_mono hIX.subset) ?_
  rintro _ ⟨⟨e, he, rfl⟩, he'⟩
  have hss := insert_subset (hIX.subset_ground he) hIX.indep.subset_ground
  rw [← not_indep_iff (by simpa [← image_insert_eq] using image_mono hss)]
  simp only [map_indep_iff, not_exists, not_and]
  intro J hJ hins
  rw [← image_insert_eq, hf.image_eq_image_iff hss hJ.subset_ground] at hins
  obtain rfl := hins
  exact he' (mem_image_of_mem f (hIX.mem_of_insert_indep he hJ))
/-
**Matroid.map_isBasis_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_isBasis_iff {I X : Set α} (f : α -> β) (hf) (hI : I subseteq M.E) (hX 
: X subseteq M.E) : (M.map f hf).IsBasis (f '' I) (f '' X) ↔ M.IsBasis I X
参数：f : α -> β；hf；hI : I subseteq M.E；hX : X subseteq M.E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.map_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : 
Matroid α} {hf : Set.InjOn f M.E} {I : Set β},   (M.map f hf).Indep I ↔ ∃ I₀, M.
Indep I₀ ∧ …
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.InjOn.image_subset_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ 
s₂ : Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ ⊆ f '' s₂ 
↔ s₁ ⊆ s₂)
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.Indep.isBasis_of_maximal_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α},   M.Indep I →     I ⊆ X →       (∀ ⦃J : Set α⦄, M.Indep J → I ⊆
 J → J ⊆ X → J ⊆ I) →        …
· 使用定理 `Matroid.IsBasis.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `Matroid.Indep.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Matr
oid α},   M.Indep I → ∀ (f : α → β) (hf : Set.InjOn f M.E), (M.map f hf).Indep (
f '' I)
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Ma
troid α} {X : Set α},   M.IsBasis I X → ∀ {f : α → β} (hf : Set.InjOn f M.E), (M
.map f hf…
-/
lemma map_isBasis_iff {I X : Set α} (f : α → β) (hf) (hI : I ⊆ M.E) (hX : X ⊆ M.E) :
    (M.map f hf).IsBasis (f '' I) (f '' X) ↔ M.IsBasis I X := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map hf⟩
  obtain ⟨I', hI', hII'⟩ := map_indep_iff.1 h.indep
  rw [hf.image_eq_image_iff hI hI'.subset_ground] at hII'
  obtain rfl := hII'
  have hss := (hf.image_subset_image_iff hI hX).1 h.subset
  refine hI'.isBasis_of_maximal_subset hss (fun J hJ hIJ hJX ↦ ?_)
  have hIJ' := h.eq_of_subset_indep (hJ.map f hf) (image_mono hIJ) (image_mono hJX)
  rw [hf.image_eq_image_iff hI hJ.subset_ground] at hIJ'
  exact hIJ'.symm.subset
/-
**Matroid.map_isBasis_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_isBasis_iff' {I X : Set β} {hf} : (M.map f hf).IsBasis I X ↔ exists I₀
 X₀, M.IsBasis I₀ X₀ ∧ I = f '' I₀ ∧ X = f '' X₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_image_iff`：subset_image_iff {t : Set β} : t subseteq f '' s ↔
 exists u, u subseteq s ∧ f '' u = t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.map_isBasis_iff`：map_isBasis_iff {I X : Set α} (f : α -> β) (hf)
 (hI : I subseteq M.E) (hX : X subseteq M.E) : (M.map f hf).IsBasis (f '' I) (f 
'' X) ↔ M.IsB…
· 使用定理 `Matroid.IsBasis.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Ma
troid α} {X : Set α},   M.IsBasis I X → ∀ {f : α → β} (hf : Set.InjOn f M.E), (M
.map f hf…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma map_isBasis_iff' {I X : Set β} {hf} :
    (M.map f hf).IsBasis I X ↔ ∃ I₀ X₀, M.IsBasis I₀ X₀ ∧ I = f '' I₀ ∧ X = f '' X₀ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨I, hI, rfl⟩ := subset_image_iff.1 h.indep.subset_ground
    obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 h.subset_ground
    rw [map_isBasis_iff _ _ hI hX] at h
    exact ⟨I, X, h, rfl, rfl⟩
  rintro ⟨I, X, hIX, rfl, rfl⟩
  exact hIX.map hf

set_option backward.isDefEq.respectTransparency false in
/-
**Matroid.map_dual** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : Matroid α} {hf : Set.InjO
n f M.E}, (M.map f hf)✶ = M✶.map f hf
参数：M.map f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_isBase`：ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h
 : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.image_sdiff_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {f : α → β} {t : Set α},   Set.InjOn f s → t ⊆ s → f '' (s \ t) = f '' s \ f '
' t
· 使用引理 `Matroid.map_image_isBase_iff`：map_image_isBase_iff {hf} {B : Set α} (hB 
: B subseteq M.E) : (M.map f hf).IsBase (f '' B) ↔ M.IsBase B
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
-/
@[simp] lemma map_dual {hf} : (M.map f hf)✶ = M✶.map f hf := by
  apply ext_isBase (by simp)
  simp only [dual_ground, map_ground, subset_image_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, dual_isBase_iff']
  intro B hB
  simp_rw [← hf.image_sdiff_subset hB, map_image_isBase_iff sdiff_subset,
    map_image_isBase_iff (show B ⊆ M✶.E from hB), dual_isBase_iff hB, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨B, hB, rfl⟩
/-
**Matroid.map_emptyOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β), (Matroid.emptyOn α).map f ⋯ =
 Matroid.emptyOn β
参数：f : α → β；Matroid.emptyOn α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_emptyOn (f : α → β) : (emptyOn α).map f (by simp) = emptyOn β := by
  simp [← ground_eq_empty_iff]
/-
**Matroid.map_loopyOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Set α} (f : α → β) (hf : Set.InjOn f 
(Matroid.loopyOn E).E),   (Matroid.loopyOn E).map f hf = Matroid.loopyOn (f '' E
)
参数：f : α → β；hf : Set.InjOn f (Matroid.loopyOn E).E；Matroid.loopyOn E；f '' E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma map_loopyOn (f : α → β) (hf) : (loopyOn E).map f hf = loopyOn (f '' E) := by
  simp [eq_loopyOn_iff]
/-
**Matroid.map_freeOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Set α} (f : α → β) (hf : Set.InjOn f 
(Matroid.freeOn E).E),   (Matroid.freeOn E).map f hf = Matroid.freeOn (f '' E)
参数：f : α → β；hf : Set.InjOn f (Matroid.freeOn E).E；Matroid.freeOn E；f '' E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_inj`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ =
 M₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.map_dual`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : Matro
id α} {hf : Set.InjOn f M.E}, (M.map f hf)✶ = M✶.map f hf
· 使用定理 `Matroid.freeOn_dual_eq`：∀ {α : Type u_1} {E : Set α}, (Matroid.freeOn E)
✶ = Matroid.loopyOn E
· 使用定理 `Matroid.map.congr_simp`：∀ {α : Type u_1} {β : Type u_2} (M M_1 : Matroid
 α) (e_M : M = M_1) (f f_1 : α → β) (e_f : f = f_1)   (hf : Set.InjOn f M.E), M.
map f hf = M…
· 使用定理 `Matroid.map_loopyOn`：∀ {α : Type u_1} {β : Type u_2} {E : Set α} (f : α 
→ β) (hf : Set.InjOn f (Matroid.loopyOn E).E),   (Matroid.loopyOn E).map f hf = 
Matroid.l…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_freeOn (f : α → β) (hf) : (freeOn E).map f hf = freeOn (f '' E) := by
  rw [← dual_inj]; simp
/-
**Matroid.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α}, M.map id ⋯ = M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Set.injOn_id`：injOn_id (s : Set α) : InjOn id s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma map_id : M.map id (injOn_id M.E) = M := by
  simp [ext_iff_indep]

set_option backward.isDefEq.respectTransparency false in
/-
**Matroid.map_comap** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_comap {f : α -> β} (h_range : N.E subseteq range f) (hf : InjOn f (f ⁻
¹' N.E)) : (N.comap f).map f hf = N
参数：h_range : N.E subseteq range f；hf : InjOn f (f ⁻¹' N.E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
-/
lemma map_comap {f : α → β} (h_range : N.E ⊆ range f) (hf : InjOn f (f ⁻¹' N.E)) :
    (N.comap f).map f hf = N := by
  refine ext_indep (by simpa [image_preimage_eq_iff]) ?_
  simp only [map_ground, comap_ground_eq, map_indep_iff, comap_indep_iff, forall_subset_image_iff]
  exact fun I hI ↦ ⟨by grind, fun h ↦ ⟨_, ⟨h, hf.mono hI⟩, rfl⟩⟩
/-
**Matroid.comap_map** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comap_map {f : α -> β} (hf : f.Injective) : (M.map f hf.injOn).comap f = M
参数：hf : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_eq_image`：image_eq_image {f : α -> β} (hf : Injective f) : f '
' s = f '' t ↔ s = t
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma comap_map {f : α → β} (hf : f.Injective) : (M.map f hf.injOn).comap f = M := by
  simp [ext_iff_indep, preimage_image_eq _ hf, and_iff_left hf.injOn,
    image_eq_image hf]
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Nonempty] {f : α → β} (hf) : (M.map f hf).Nonempty :=
  ⟨by simp [M.ground_nonempty]⟩
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Finite] {f : α → β} (hf) : (M.map f hf).Finite :=
  ⟨M.ground_finite.image f⟩
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Finitary] {f : α → β} (hf) : (M.map f hf).Finitary := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [map_indep_iff]
  have h' : I ⊆ f '' M.E := by
    intro e he
    obtain ⟨I₀, hI₀, h_eq⟩ := hI {e} (by simpa) (by simp)
    exact image_mono hI₀.subset_ground <| h_eq.subset rfl
  obtain ⟨I₀, hI₀E, rfl⟩ := subset_image_iff.1 h'
  refine ⟨I₀, indep_of_forall_finite_subset_indep _ fun J₀ hJ₀I₀ hJ₀ ↦ ?_, rfl⟩
  specialize hI (f '' J₀) (image_mono hJ₀I₀) (hJ₀.image _)
  rwa [map_image_indep_iff (hJ₀I₀.trans hI₀E)] at hI
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.RankFinite] {f : α → β} (hf) : (M.map f hf).RankFinite :=
  let ⟨_, hB⟩ := M.exists_isBase
  (hB.map hf).rankFinite_of_finite (hB.finite.image _)
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.RankPos] {f : α → β} (hf) : (M.map f hf).RankPos :=
  let ⟨_, hB⟩ := M.exists_isBase
  (hB.map hf).rankPos_of_nonempty (hB.nonempty.image _)

end map

section mapSetEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Map `M : Matroid α` to a `Matroid β` with ground set `E` using an equivalence `M.E ≃ E`.
Defined using `Matroid.ofExistsMatroid` for better defeq. -/
/-
**Matroid.mapSetEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：mapSetEquiv (M : Matroid α) {E : Set β} (e : M.E ≃ E) : Matroid β
参数：M : Matroid α；e : M.E ≃ E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Map `M : Matroid α` to a `Matroid β` with ground set `E` using an equivalence `M
.E ≃ E`.
Defined using `Matroid.ofExistsMatroid` for better defeq.
-/
def mapSetEquiv (M : Matroid α) {E : Set β} (e : M.E ≃ E) : Matroid β :=
  Matroid.ofExistsMatroid E (fun I ↦ (M.Indep ↑(e.symm '' (E ↓∩ I)) ∧ I ⊆ E))
  ⟨M.mapSetEmbedding (e.toEmbedding.trans <| Function.Embedding.subtype _), by
    have hrw : ∀ I : Set β, Subtype.val ∘ ⇑e ⁻¹' I = ⇑e.symm '' E ↓∩ I := fun I ↦ by ext; simp
    simp [Equiv.toEmbedding, Embedding.subtype, Embedding.trans, hrw]⟩
/-
**Matroid.mapSetEquiv_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) {E : Set β} (e : ↑M.E ≃ ↑E
) {I : Set β},   (M.mapSetEquiv e).Indep I ↔ M.Indep (Subtype.val '' ⇑e.symm '' 
Subtype.val ⁻¹' I) ∧ I ⊆ E
参数：M : Matroid α；e : ↑M.E ≃ ↑E；M.mapSetEquiv e；Subtype.val '' ⇑e.symm '' Subtype
.val ⁻¹' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mapSetEquiv_indep_iff (M : Matroid α) {E : Set β} (e : M.E ≃ E) {I : Set β} :
    (M.mapSetEquiv e).Indep I ↔ M.Indep ↑(e.symm '' (E ↓∩ I)) ∧ I ⊆ E := Iff.rfl
/-
**Matroid.mapSetEquiv.ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.mapSetEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) {E : Set β} (e : ↑M.E ≃ ↑E
), (M.mapSetEquiv e).E = E
参数：M : Matroid α；e : ↑M.E ≃ ↑E；M.mapSetEquiv e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapSetEquiv.ground (M : Matroid α) {E : Set β} (e : M.E ≃ E) :
    (M.mapSetEquiv e).E = E := rfl

end mapSetEquiv
section mapEmbedding

/-- Map `M : Matroid α` across an embedding defined on all of `α` -/
/-
**Matroid.mapEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：mapEmbedding (M : Matroid α) (f : α ↪ β) : Matroid β
参数：M : Matroid α；f : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map `M : Matroid α` across an embedding defined on all of `α`
-/
def mapEmbedding (M : Matroid α) (f : α ↪ β) : Matroid β := M.map f f.injective.injOn
/-
**Matroid.mapEmbedding_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) (f : α ↪ β), (M.mapEmbeddi
ng f).E = ⇑f '' M.E
参数：M : Matroid α；f : α ↪ β；M.mapEmbedding f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapEmbedding_ground_eq (M : Matroid α) (f : α ↪ β) :
    (M.mapEmbedding f).E = f '' M.E := rfl
/-
**Matroid.mapEmbedding_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {f : α ↪ β} {I : Set β},  
 (M.mapEmbedding f).Indep I ↔ M.Indep (⇑f ⁻¹' I) ∧ I ⊆ Set.range ⇑f
参数：M.mapEmbedding f；⇑f ⁻¹' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.mapEmbedding.eq_1`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid 
α) (f : α ↪ β), M.mapEmbedding f = M.map ⇑f ⋯
· 使用定理 `Matroid.map_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : 
Matroid α} {hf : Set.InjOn f M.E} {I : Set β},   (M.map f hf).Indep I ↔ ∃ I₀, M.
Indep I₀ ∧ …
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
-/
@[simp] lemma mapEmbedding_indep_iff {f : α ↪ β} {I : Set β} :
    (M.mapEmbedding f).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I ⊆ range f := by
  rw [mapEmbedding, map_indep_iff]
  refine ⟨?_, fun ⟨h,h'⟩ ↦ ⟨f ⁻¹' I, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, image_subset_range _ _⟩
/-
**Matroid.Indep.mapEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Matroid α},   M.Indep I →
 ∀ (f : α ↪ β), (M.mapEmbedding f).Indep (⇑f '' I)
参数：f : α ↪ β；M.mapEmbedding f；⇑f '' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma Indep.mapEmbedding (hI : M.Indep I) (f : α ↪ β) : (M.mapEmbedding f).Indep (f '' I) := by
  simpa [preimage_image_eq I f.injective]
/-
**Matroid.IsBase.mapEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {B : Set α},   M.IsBase B 
→ ∀ (f : α ↪ β), (M.mapEmbedding f).IsBase (⇑f '' B)
参数：f : α ↪ β；M.mapEmbedding f；⇑f '' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.mapEmbedding.eq_1`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid 
α) (f : α ↪ β), M.mapEmbedding f = M.map ⇑f ⋯
· 使用定理 `Matroid.map_isBase_iff`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) 
(f : α → β) (hf : Set.InjOn f M.E) {B : Set β},   (M.map f hf).IsBase B ↔ ∃ B₀, 
M.IsBase B₀ …
-/
lemma IsBase.mapEmbedding {B : Set α} (hB : M.IsBase B) (f : α ↪ β) :
    (M.mapEmbedding f).IsBase (f '' B) := by
  rw [Matroid.mapEmbedding, map_isBase_iff]
  exact ⟨B, hB, rfl⟩
/-
**Matroid.IsBasis.mapEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Matroid α} {X : Set α},  
 M.IsBasis I X → ∀ (f : α ↪ β), (M.mapEmbedding f).IsBasis (⇑f '' I) (⇑f '' X)
参数：f : α ↪ β；M.mapEmbedding f；⇑f '' I；⇑f '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Ma
troid α} {X : Set α},   M.IsBasis I X → ∀ {f : α → β} (hf : Set.InjOn f M.E), (M
.map f hf…
-/
lemma IsBasis.mapEmbedding {X : Set α} (hIX : M.IsBasis I X) (f : α ↪ β) :
    (M.mapEmbedding f).IsBasis (f '' I) (f '' X) := by
  apply hIX.map
/-
**Matroid.mapEmbedding_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {f : α ↪ β} {B : Set β},  
 (M.mapEmbedding f).IsBase B ↔ M.IsBase (⇑f ⁻¹' B) ∧ B ⊆ Set.range ⇑f
参数：M.mapEmbedding f；⇑f ⁻¹' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.mapEmbedding.eq_1`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid 
α) (f : α ↪ β), M.mapEmbedding f = M.map ⇑f ⋯
· 使用定理 `Matroid.map_isBase_iff`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) 
(f : α → β) (hf : Set.InjOn f M.E) {B : Set β},   (M.map f hf).IsBase B ↔ ∃ B₀, 
M.IsBase B₀ …
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
-/
@[simp] lemma mapEmbedding_isBase_iff {f : α ↪ β} {B : Set β} :
    (M.mapEmbedding f).IsBase B ↔ M.IsBase (f ⁻¹' B) ∧ B ⊆ range f := by
  rw [mapEmbedding, map_isBase_iff]
  refine ⟨?_, fun ⟨h,h'⟩ ↦ ⟨f ⁻¹' B, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨B, hB, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hB, image_subset_range _ _⟩
/-
**Matroid.mapEmbedding_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {f : α ↪ β} {I X : Set β},
   (M.mapEmbedding f).IsBasis I X ↔ M.IsBasis (⇑f ⁻¹' I) (⇑f ⁻¹' X) ∧ I ⊆ X ∧ X 
⊆ Set.range ⇑f
参数：M.mapEmbedding f；⇑f ⁻¹' I；⇑f ⁻¹' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.mapEmbedding.eq_1`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid 
α) (f : α ↪ β), M.mapEmbedding f = M.map ⇑f ⋯
· 使用引理 `Matroid.map_isBasis_iff'`：map_isBasis_iff' {I X : Set β} {hf} : (M.map f
 hf).IsBasis I X ↔ exists I₀ X₀, M.IsBasis I₀ X₀ ∧ I = f '' I₀ ∧ X = f '' X₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_range_iff_exists_image_eq`：subset_range_iff_exists_image_eq {
f : α -> β} {s : Set β} : s subseteq range f ↔ exists t, f '' t = s
· 使用定理 `Set.subset_image_iff`：subset_image_iff {t : Set β} : t subseteq f '' s ↔
 exists u, u subseteq s ∧ f '' u = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
@[simp] lemma mapEmbedding_isBasis_iff {f : α ↪ β} {I X : Set β} :
    (M.mapEmbedding f).IsBasis I X ↔ M.IsBasis (f ⁻¹' I) (f ⁻¹' X) ∧ I ⊆ X ∧ X ⊆ range f := by
  rw [mapEmbedding, map_isBasis_iff']
  refine ⟨?_, fun ⟨hb, hIX, hX⟩ ↦ ?_⟩
  · rintro ⟨I, X, hIX, rfl, rfl⟩
    simp [preimage_image_eq _ f.injective, image_mono hIX.subset, hIX]
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.1 hX
  obtain ⟨I, -, rfl⟩ := subset_image_iff.1 hIX
  exact ⟨I, X, by simpa [preimage_image_eq _ f.injective] using hb⟩
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Nonempty] {f : α ↪ β} : (M.mapEmbedding f).Nonempty :=
  inferInstanceAs (M.map f f.injective.injOn).Nonempty
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Finite] {f : α ↪ β} : (M.mapEmbedding f).Finite :=
  inferInstanceAs (M.map f f.injective.injOn).Finite
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Finitary] {f : α ↪ β} : (M.mapEmbedding f).Finitary :=
  inferInstanceAs (M.map f f.injective.injOn).Finitary
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.RankFinite] {f : α ↪ β} : (M.mapEmbedding f).RankFinite :=
  inferInstanceAs (M.map f f.injective.injOn).RankFinite
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.RankPos] {f : α ↪ β} : (M.mapEmbedding f).RankPos :=
  inferInstanceAs (M.map f f.injective.injOn).RankPos

end mapEmbedding

section mapEquiv

variable {f : α ≃ β}

/-- Map `M : Matroid α` across an equivalence `α ≃ β` -/
/-
**Matroid.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：mapEquiv (M : Matroid α) (f : α ≃ β) : Matroid β
参数：M : Matroid α；f : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map `M : Matroid α` across an equivalence `α ≃ β`
-/
def mapEquiv (M : Matroid α) (f : α ≃ β) : Matroid β := M.mapEmbedding f.toEmbedding
/-
**Matroid.mapEquiv_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) (f : α ≃ β), (M.mapEquiv f
).E = ⇑f '' M.E
参数：M : Matroid α；f : α ≃ β；M.mapEquiv f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapEquiv_ground_eq (M : Matroid α) (f : α ≃ β) :
    (M.mapEquiv f).E = f '' M.E := rfl
/-
**Matroid.mapEquiv_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mapEquiv_eq_map (f : α ≃ β) : M.mapEquiv f = M.map f f.injective.injOn
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapEquiv_eq_map (f : α ≃ β) : M.mapEquiv f = M.map f f.injective.injOn := rfl
/-
**Matroid.mapEquiv_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {f : α ≃ β} {I : Set β}, (
M.mapEquiv f).Indep I ↔ M.Indep (⇑f.symm '' I)
参数：M.mapEquiv f；⇑f.symm '' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.mapEquiv_eq_map`：mapEquiv_eq_map (f : α ≃ β) : M.mapEquiv f = M.
map f f.injective.injOn
· 使用定理 `Matroid.map_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {M : 
Matroid α} {hf : Set.InjOn f M.E} {I : Set β},   (M.map f hf).Indep I ↔ ∃ I₀, M.
Indep I₀ ∧ …
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.image_symm_image`：image_symm_image {α β} (e : α ≃ β) (s : Set β) :
 e '' e.symm '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapEquiv_indep_iff {I : Set β} : (M.mapEquiv f).Indep I ↔ M.Indep (f.symm '' I) := by
  rw [mapEquiv_eq_map, map_indep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩
/-
**Matroid.mapEquiv_dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {f : α ≃ β} {D : Set β}, (
M.mapEquiv f).Dep D ↔ M.Dep (⇑f.symm '' D)
参数：M.mapEquiv f；⇑f.symm '' D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.mapEquiv_eq_map`：mapEquiv_eq_map (f : α ≃ β) : M.mapEquiv f = M.
map f f.injective.injOn
· 使用引理 `Matroid.map_dep_iff`：map_dep_iff {hf} {D : Set β} : (M.map f hf).Dep D ↔
 exists D₀, M.Dep D₀ ∧ D = f '' D₀
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.image_symm_image`：image_symm_image {α β} (e : α ≃ β) (s : Set β) :
 e '' e.symm '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapEquiv_dep_iff {D : Set β} : (M.mapEquiv f).Dep D ↔ M.Dep (f.symm '' D) := by
  rw [mapEquiv_eq_map, map_dep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩
/-
**Matroid.mapEquiv_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {f : α ≃ β} {B : Set β},  
 (M.mapEquiv f).IsBase B ↔ M.IsBase (⇑f.symm '' B)
参数：M.mapEquiv f；⇑f.symm '' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.mapEquiv_eq_map`：mapEquiv_eq_map (f : α ≃ β) : M.mapEquiv f = M.
map f f.injective.injOn
· 使用定理 `Matroid.map_isBase_iff`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) 
(f : α → β) (hf : Set.InjOn f M.E) {B : Set β},   (M.map f hf).IsBase B ↔ ∃ B₀, 
M.IsBase B₀ …
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.image_symm_image`：image_symm_image {α β} (e : α ≃ β) (s : Set β) :
 e '' e.symm '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapEquiv_isBase_iff {B : Set β} :
    (M.mapEquiv f).IsBase B ↔ M.IsBase (f.symm '' B) := by
  rw [mapEquiv_eq_map, map_isBase_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩
/-
**Matroid.mapEquiv_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} {M : Matroid α} (f : α ≃ β) {I X : Set β},
   (M.mapEquiv f).IsBasis I X ↔ M.IsBasis (⇑f.symm '' I) (⇑f.symm '' X)
参数：f : α ≃ β；M.mapEquiv f；⇑f.symm '' I；⇑f.symm '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.mapEquiv_eq_map`：mapEquiv_eq_map (f : α ≃ β) : M.mapEquiv f = M.
map f f.injective.injOn
· 使用引理 `Matroid.map_isBasis_iff'`：map_isBasis_iff' {I X : Set β} {hf} : (M.map f
 hf).IsBasis I X ↔ exists I₀ X₀, M.IsBasis I₀ X₀ ∧ I = f '' I₀ ∧ X = f '' X₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.image_symm_image`：image_symm_image {α β} (e : α ≃ β) (s : Set β) :
 e '' e.symm '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapEquiv_isBasis_iff {α β : Type*} {M : Matroid α} (f : α ≃ β) {I X : Set β} :
    (M.mapEquiv f).IsBasis I X ↔ M.IsBasis (f.symm '' I) (f.symm '' X) := by
  rw [mapEquiv_eq_map, map_isBasis_iff']
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨_, _, h, by simp, by simp⟩⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := h
  simpa
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Nonempty] {f : α ≃ β} : (M.mapEquiv f).Nonempty :=
  inferInstanceAs (M.map f f.injective.injOn).Nonempty
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Finite] {f : α ≃ β} : (M.mapEquiv f).Finite :=
  inferInstanceAs (M.map f f.injective.injOn).Finite
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Finitary] {f : α ≃ β} : (M.mapEquiv f).Finitary :=
  inferInstanceAs (M.map f f.injective.injOn).Finitary
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.RankFinite] {f : α ≃ β} : (M.mapEquiv f).RankFinite :=
  inferInstanceAs (M.map f f.injective.injOn).RankFinite
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.RankPos] {f : α ≃ β} : (M.mapEquiv f).RankPos :=
  inferInstanceAs (M.map f f.injective.injOn).RankPos

end mapEquiv

section restrictSubtype

variable {E X I : Set α} {M : Matroid α}

/-- Given `M : Matroid α` and `X : Set α`, the restriction of `M` to `X`,
viewed as a matroid on type `X` with ground set `univ`.
Always isomorphic to `M ↾ X`. If `X = M.E`, then isomorphic to `M`. -/
/-
**Matroid.restrictSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：restrictSubtype (M : Matroid α) (X : Set α) : Matroid X
参数：M : Matroid α；X : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `M : Matroid α` and `X : Set α`, the restriction of `M` to `X`,
viewed as a matroid on type `X` with ground set `univ`.
Always isomorphic to `M ↾ X`. If `X = M.E`, then isomorphic to `M`.
-/
def restrictSubtype (M : Matroid α) (X : Set α) : Matroid X := (M ↾ X).comap (↑)
/-
**Matroid.restrictSubtype_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {X : Set α} {M : Matroid α}, (M.restrictSubtype X).E = Se
t.univ
参数：M.restrictSubtype X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma restrictSubtype_ground : (M.restrictSubtype X).E = univ := by
  simp [restrictSubtype]
/-
**Matroid.restrictSubtype_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {X : Set α} {M : Matroid α} {I : Set ↑X}, (M.restrictSubt
ype X).Indep I ↔ M.Indep (Subtype.val '' I)
参数：M.restrictSubtype X；Subtype.val '' I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma restrictSubtype_indep_iff {I : Set X} :
    (M.restrictSubtype X).Indep I ↔ M.Indep ((↑) '' I) := by
  simp [restrictSubtype, Subtype.val_injective.injOn]
/-
**Matroid.restrictSubtype_indep_iff_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Matroid
`。
形式化陈述：restrictSubtype_indep_iff_of_subset (hIX : I subseteq X) : (M.restrictSubt
ype X).Indep (X ↓inter I) ↔ M.Indep I
参数：hIX : I subseteq X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrictSubtype_indep_iff`：∀ {α : Type u_1} {X : Set α} {M : Mat
roid α} {I : Set ↑X}, (M.restrictSubtype X).Indep I ↔ M.Indep (Subtype.val '' I)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrictSubtype_indep_iff_of_subset (hIX : I ⊆ X) :
    (M.restrictSubtype X).Indep (X ↓∩ I) ↔ M.Indep I := by
  rw [restrictSubtype_indep_iff, image_preimage_eq_iff.2]; simpa
/-
**Matroid.restrictSubtype_inter_indep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrictSubtype_inter_indep_iff : (M.restrictSubtype X).Indep (X ↓inter I)
 ↔ M.Indep (X inter I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrictSubtype_inter_indep_iff :
    (M.restrictSubtype X).Indep (X ↓∩ I) ↔ M.Indep (X ∩ I) := by
  simp [restrictSubtype, Subtype.val_injective.injOn]
/-
**Matroid.restrictSubtype_isBasis_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrictSubtype_isBasis_iff {Y : Set α} {I X : Set Y} : (M.restrictSubtype
 Y).IsBasis I X ↔ M.IsBasis' I X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrictSubtype.eq_1`：∀ {α : Type u_1} (M : Matroid α) (X : Set 
α), M.restrictSubtype X = (M.restrict X).comap Subtype.val
· 使用定理 `Matroid.comap_isBasis_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
N : Matroid β} {I X : Set α},   (N.comap f).IsBasis I X ↔ N.IsBasis (f '' I) (f 
'' X) ∧ Set.Inj…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.isBasis_restrict_iff'`：isBasis_restrict_iff' : (M ↾ R).IsBasis I
 X ↔ M.IsBasis I (X inter M.E) ∧ X subseteq R
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrictSubtype_isBasis_iff {Y : Set α} {I X : Set Y} :
    (M.restrictSubtype Y).IsBasis I X ↔ M.IsBasis' I X := by
  rw [restrictSubtype, comap_isBasis_iff, and_iff_right Subtype.val_injective.injOn,
    and_iff_left_of_imp, isBasis_restrict_iff', isBasis'_iff_isBasis_inter_ground]
  · simp
  exact fun h ↦ (image_subset_image_iff Subtype.val_injective).1 h.subset
/-
**Matroid.restrictSubtype_isBase_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrictSubtype_isBase_iff {B : Set X} : (M.restrictSubtype X).IsBase B ↔ 
M.IsBasis' B X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrictSubtype.eq_1`：∀ {α : Type u_1} (M : Matroid α) (X : Set 
α), M.restrictSubtype X = (M.restrict X).comap Subtype.val
· 使用定理 `Matroid.comap_isBase_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {N
 : Matroid β} {B : Set α},   (N.comap f).IsBase B ↔ N.IsBasis (f '' B) (f '' f ⁻
¹' N.E) ∧ Set.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrictSubtype_isBase_iff {B : Set X} : (M.restrictSubtype X).IsBase B ↔ M.IsBasis' B X := by
  rw [restrictSubtype, comap_isBase_iff]
  simp [Subtype.val_injective.injOn, isBasis_restrict_iff',
    isBasis'_iff_isBasis_inter_ground]
/-
**Matroid.restrictSubtype_ground_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set ↑M.E}, (M.restrictSubtype M.E).I
sBase B ↔ M.IsBase (Subtype.val '' B)
参数：M.restrictSubtype M.E；Subtype.val '' B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.restrictSubtype_isBase_iff`：restrictSubtype_isBase_iff {B : Set 
X} : (M.restrictSubtype X).IsBase B ↔ M.IsBasis' B X
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma restrictSubtype_ground_isBase_iff {B : Set M.E} :
    (M.restrictSubtype M.E).IsBase B ↔ M.IsBase B := by
  rw [restrictSubtype_isBase_iff, isBasis'_iff_isBasis, isBasis_ground_iff]
/-
**Matroid.restrictSubtype_ground_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set ↑M.E},   (M.restrictSubtype M.
E).IsBasis I X ↔ M.IsBasis (Subtype.val '' I) (Subtype.val '' X)
参数：M.restrictSubtype M.E；Subtype.val '' I；Subtype.val '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.restrictSubtype_isBasis_iff`：restrictSubtype_isBasis_iff {Y : Se
t α} {I X : Set Y} : (M.restrictSubtype Y).IsBasis I X ↔ M.IsBasis' I X
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma restrictSubtype_ground_isBasis_iff {I X : Set M.E} :
    (M.restrictSubtype M.E).IsBasis I X ↔ M.IsBasis I X := by
  rw [restrictSubtype_isBasis_iff, isBasis'_iff_isBasis]
/-
**Matroid.eq_of_restrictSubtype_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eq_of_restrictSubtype_eq {N : Matroid α} (hM : M.E = E) (hN : N.E = E) (h 
: M.restrictSubtype E = N.restrictSubtype E) : M = N
参数：hM : M.E = E；hN : N.E = E；h : M.restrictSubtype E = N.restrictSubtype E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrictSubtype_indep_iff_of_subset`：restrictSubtype_indep_iff_o
f_subset (hIX : I subseteq X) : (M.restrictSubtype X).Indep (X ↓inter I) ↔ M.Ind
ep I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_of_restrictSubtype_eq {N : Matroid α} (hM : M.E = E) (hN : N.E = E)
    (h : M.restrictSubtype E = N.restrictSubtype E) : M = N := by
  subst hM
  refine ext_indep (by rw [hN]) (fun I hI ↦ ?_)
  rwa [← restrictSubtype_indep_iff_of_subset hI, h, restrictSubtype_indep_iff_of_subset]
/-
**Matroid.restrictSubtype_dual** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α}, (M.restrictSubtype M.E)✶ = M✶.restrictSu
btype M.E
参数：M.restrictSubtype M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrictSubtype.eq_1`：∀ {α : Type u_1} (M : Matroid α) (X : Set 
α), M.restrictSubtype X = (M.restrict X).comap Subtype.val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.comapOn_preimage_eq`：comapOn_preimage_eq (N : Matroid β) (f : α 
-> β) : N.comapOn (f ⁻¹' N.E) f = N.comap f
· 使用引理 `Matroid.comapOn_dual_eq_of_bijOn`：comapOn_dual_eq_of_bijOn (h : BijOn f 
E N.E) : (N.comapOn E f)✶ = N✶.comapOn E f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
-/
@[simp] lemma restrictSubtype_dual : (M.restrictSubtype M.E)✶ = M✶.restrictSubtype M.E := by
  rw [restrictSubtype, ← comapOn_preimage_eq, comapOn_dual_eq_of_bijOn, restrict_ground_eq_self,
    ← dual_ground, comapOn_preimage_eq, restrictSubtype, restrict_ground_eq_self]
  exact ⟨by simp [MapsTo], Subtype.val_injective.injOn, by simp [SurjOn]⟩
/-
**Matroid.restrictSubtype_dual'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrictSubtype_dual' (hM : M.E = E) : (M.restrictSubtype E)✶ = M✶.restric
tSubtype E
参数：hM : M.E = E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.restrictSubtype_dual`：∀ {α : Type u_1} {M : Matroid α}, (M.restr
ictSubtype M.E)✶ = M✶.restrictSubtype M.E
-/
lemma restrictSubtype_dual' (hM : M.E = E) : (M.restrictSubtype E)✶ = M✶.restrictSubtype E := by
  rw [← hM, restrictSubtype_dual]

set_option backward.isDefEq.respectTransparency false in
/-- `M.restrictSubtype X` is isomorphic to `M ↾ X`. -/
/-
**Matroid.map_val_restrictSubtype_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α) (X : Set α), (M.restrictSubtype X).map Su
btype.val ⋯ = M.restrict X
参数：M : Matroid α；X : Set α；M.restrictSubtype X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.map_comap`：map_comap {f : α -> β} (h_range : N.E subseteq range 
f) (hf : InjOn f (f ⁻¹' N.E)) : (N.comap f).map f hf = N
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`M.restrictSubtype X` is isomorphic to `M ↾ X`.
-/
@[simp] lemma map_val_restrictSubtype_eq (M : Matroid α) (X : Set α) :
    (M.restrictSubtype X).map (↑) Subtype.val_injective.injOn = M ↾ X := by
  simp [restrictSubtype, map_comap]

/-- `M.restrictSubtype M.E` is isomorphic to `M`. -/
/-
**Matroid.map_val_restrictSubtype_ground_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_val_restrictSubtype_ground_eq (M : Matroid α) : (M.restrictSubtype M.E
).map (↑) Subtype.val_injective.injOn = M
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.map_val_restrictSubtype_eq`：∀ {α : Type u_1} (M : Matroid α) (X 
: Set α), (M.restrictSubtype X).map Subtype.val ⋯ = M.restrict X
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`M.restrictSubtype M.E` is isomorphic to `M`.
-/
lemma map_val_restrictSubtype_ground_eq (M : Matroid α) :
    (M.restrictSubtype M.E).map (↑) Subtype.val_injective.injOn = M := by
  simp
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Finitary] {X : Set α} : (M.restrictSubtype X).Finitary := by
  rw [restrictSubtype]; infer_instance
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.RankFinite] {X : Set α} : (M.restrictSubtype X).RankFinite := by
  rw [restrictSubtype]; infer_instance
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Finite] : (M.restrictSubtype M.E).Finite :=
  have := M.ground_finite.to_subtype
  ⟨Finite.ground_finite⟩
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.Nonempty] : (M.restrictSubtype M.E).Nonempty :=
  have := M.ground_nonempty.coe_sort
  ⟨by simp⟩
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [M.RankPos] : (M.restrictSubtype M.E).RankPos := by
  obtain ⟨B, hB⟩ := (M.restrictSubtype M.E).exists_isBase
  have hB' : M.IsBase ↑B := by simpa using hB.map Subtype.val_injective.injOn
  exact hB.rankPos_of_nonempty <| by simpa using hB'.nonempty

end restrictSubtype

end Matroid

