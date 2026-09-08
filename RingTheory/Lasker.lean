/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Order.Irreducible
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Lasker ring

## Main declarations

- `IsLasker`: An `R`-module `M` satisfies `IsLasker R M` when any `N : Submodule R M` can be
  decomposed into finitely many primary submodules.
- `IsLasker.exists_isMinimalPrimaryDecomposition`: Any `N : Submodule R N` in an `R`-module `M`
  satisfying `IsLasker R M` can be decomposed into finitely many primary submodules `Nᵢ`, such
  that the decomposition is minimal: each `Nᵢ` is necessary, and the `√Ann(M/Nᵢ)` are distinct.
- `IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`: The first uniqueness theorem
  for primary decomposition, Theorem 4.5 in Atiyah-Macdonald: In any minimal primary decomposition
  `I = ⨅ i, q_i`, the ideals `radical (q_i.colon M)` are exactly the associated primes of `I`.
- `Submodule.isLasker`: Every Noetherian module is Lasker.

-/

@[expose] public section

section IsLasker

open Ideal

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- An `R`-module `M` satisfies `IsLasker R M` when any `N : Submodule R M` can be
  decomposed into finitely many primary submodules. -/
/-
**IsLasker** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLasker : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `M` satisfies `IsLasker R M` when any `N : Submodule R M` can be
  decomposed into finitely many primary submodules.
-/
def IsLasker : Prop :=
  ∀ N : Submodule R M, ∃ s : Finset (Submodule R M), s.inf id = N ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary

variable {R M}

namespace Submodule

/-
**Submodule.decomposition_erase_inf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：decomposition_erase_inf {N : Submodule R M} {s : Finset (Submodule R M)} (
hs : s.inf id = N) : exists t : Finset (Submodule R M), t subseteq s ∧ t.inf id 
= N ∧ forall ⦃J⦄, J in t -> ¬ (t.erase J).inf id <= J
参数：Submodule R M；hs : s.inf id = N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eraseInduction`：eraseInduction [DecidableEq α] {p : Finset α -> P
rop} (H : (S : Finset α) -> (forall s in S, p (S.erase s)) -> p S) (S : Finset α
) : p S
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma decomposition_erase_inf {N : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = N) :
    ∃ t : Finset (Submodule R M), t ⊆ s ∧ t.inf id = N ∧
      ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J := by
  induction s using Finset.eraseInduction with
  | H s IH =>
    by_cases! H : ∀ J ∈ s, ¬ (s.erase J).inf id ≤ J
    · exact ⟨s, Finset.Subset.rfl, hs, H⟩
    obtain ⟨J, hJ, hJ'⟩ := H
    refine (IH _ hJ ?_).imp
      fun t ↦ And.imp_left (fun ht ↦ ht.trans (Finset.erase_subset _ _))
    rw [← Finset.insert_erase hJ] at hs
    simp [← hs, hJ']

open scoped Function -- required for scoped `on` notation
/-
**Submodule.isPrimary_decomposition_pairwise_ne_radical** 是 Mathlib 中的一个引理，位于命名空
间 `Submodule`。
形式化陈述：isPrimary_decomposition_pairwise_ne_radical {N : Submodule R M} {s : Finse
t (Submodule R M)} (hs : s.inf id = N) (hs' : forall ⦃J⦄, J in s -> J.IsPrimary)
 : exists t : Finset (Submodule R M), t.inf id = N ∧ (forall ⦃J⦄, J in t -> J.Is
Primary) ∧ (t : Set (Submodule R M)).Pairwise ((· != ·) on fun J => (J.colon Set
.univ).radical)
参数：Submodule R M；hs : s.inf id = N；hs' : forall ⦃J⦄, J in s -> J.IsPrimary。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Submodule.isPrimary_finsetInf`：isPrimary_finsetInf {ι : Type*} {s : Fins
et ι} {f : ι -> Submodule R M} {i : ι} (hi : i in s) (hs : forall ⦃y⦄, y in s ->
 (f y).IsPrimary) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用引理 `Ideal.radical_finset_inf`：radical_finset_inf {ι} {s : Finset ι} {f : ι -
> Ideal R} {i : ι} (hi : i in s) (hs : forall ⦃y⦄, y in s -> (f y).radical = (f 
i).radical) : …
· 使用引理 `Submodule.colon_finsetInf`：colon_finsetInf {ι : Type*} (s : Finset ι) (f
 : ι -> Submodule R M) : (s.inf f).colon S = s.inf (fun i => (f i).colon S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isPrimary_decomposition_pairwise_ne_radical {N : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = N) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = N ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical) := by
  refine ⟨(s.image fun J ↦ {I ∈ s | (I.colon .univ).radical = (J.colon .univ).radical}).image
    fun t ↦ t.inf id, ?_, ?_, ?_⟩
  · ext
    grind [Finset.inf_image, Submodule.mem_finsetInf]
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro J hJ
    refine isPrimary_finsetInf (i := J) ?_ ?_ (by simp)
    · simp [hJ]
    · simp only [Finset.mem_filter, id_eq, and_imp]
      intro y hy
      simp [hs' hy]
  · intro I hI J hJ hIJ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and] at hI hJ
    obtain ⟨I', hI', hI⟩ := hI
    obtain ⟨J', hJ', hJ⟩ := hJ
    simp only [Function.onFun, ne_eq]
    contrapose hIJ
    suffices (I'.colon Set.univ).radical = (J'.colon Set.univ).radical by
      rw [← hI, ← hJ, this]
    · rw [← hI, colon_finsetInf,
        radical_finset_inf (i := I') (by simp [hI']) (by simp), id_eq] at hIJ
      rw [hIJ, ← hJ, colon_finsetInf,
        radical_finset_inf (i := J') (by simp [hJ']) (by simp), id_eq]
/-
**Submodule.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition** 
是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition {N : Sub
module R M} {s : Finset (Submodule R M)} (hs : s.inf id = N) (hs' : forall ⦃J⦄, 
J in s -> J.IsPrimary) : exists t : Finset (Submodule R M), t.inf id = N ∧ (fora
ll ⦃J⦄, J in t -> J.IsPrimary) ∧ ((t : Set (Submodule R M)).Pairwise ((· != ·) o
n fun J => (J.colon Set.univ).radical)) ∧ (forall ⦃J⦄, J in t -> ¬ (t.erase J).i
nf id <= J)
参数：Submodule R M；hs : s.inf id = N；hs' : forall ⦃J⦄, J in s -> J.IsPrimary。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.isPrimary_decomposition_pairwise_ne_radical`：isPrimary_decompo
sition_pairwise_ne_radical {N : Submodule R M} {s : Finset (Submodule R M)} (hs 
: s.inf id = N) (hs' : forall ⦃J⦄, J in s -…
· 使用引理 `Submodule.decomposition_erase_inf`：decomposition_erase_inf {N : Submodul
e R M} {s : Finset (Submodule R M)} (hs : s.inf id = N) : exists t : Finset (Sub
module R M), t subseteq…
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
-/
lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition
    {N : Submodule R M} {s : Finset (Submodule R M)}
    (hs : s.inf id = N) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = N ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      ((t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical)) ∧
      (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi ↦ ht' (hut hi), ht''.mono hut, hu'⟩

/-- A `Finset` of submodules is a minimal primary decomposition of `N` if the submodules `Nᵢ`
intersect to `N`, are primary, the `√Ann(M/Nᵢ)` are distinct, and each `Nᵢ` is necessary. -/
/-
**Submodule.IsMinimalPrimaryDecomposition** 是 Mathlib 中的一个归纳类型，位于命名空间 `Submodule
`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → Submodule R M → Finset
 (Submodule R M) → Prop
参数：Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Finset` of submodules is a minimal primary decomposition of `N` if the submod
ules `Nᵢ`
intersect to `N`, are primary, the `√Ann(M/Nᵢ)` are distinct, and each `Nᵢ` is n
ecessary.
-/
structure IsMinimalPrimaryDecomposition
    (N : Submodule R M) (t : Finset (Submodule R M)) where
  inf_eq : t.inf id = N
  primary : ∀ ⦃J⦄, J ∈ t → J.IsPrimary
  distinct : (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical)
  minimal : ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J
/-
**Submodule.IsLasker.exists_isMinimalPrimaryDecomposition** 是 Mathlib 中的一个定理，位于命
名空间 `Submodule.IsLasker`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M],   IsLasker R M → ∀ (N : Submodule R M), ∃
 t, N.IsMinimalPrimaryDecomposition t
参数：N : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposit
ion`：exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition {N : Subm
odule R M} {s : Finset (Submodule R M)} (hs : s.inf id = N) (hs' …
-/
lemma IsLasker.exists_isMinimalPrimaryDecomposition
    (h : IsLasker R M) (N : Submodule R M) :
    ∃ t : Finset (Submodule R M), N.IsMinimalPrimaryDecomposition t := by
  obtain ⟨s, hs1, hs2⟩ := h N
  obtain ⟨t, h1, h2, h3, h4⟩ :=
    exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs1 hs2
  exact ⟨t, h1, h2, h3, h4⟩

namespace IsMinimalPrimaryDecomposition

/-
**Submodule.IsMinimalPrimaryDecomposition.injOn** 是 Mathlib 中的一个引理，位于命名空间 `Submo
dule.IsMinimalPrimaryDecomposition`。
形式化陈述：injOn (N : Submodule R M) (t : Finset (Submodule R M)) (ht : N.IsMinimalPr
imaryDecomposition t) : Set.InjOn (fun J => (J.colon Set.univ).radical) (t : Set
 (Submodule R M))
参数：N : Submodule R M；t : Finset (Submodule R M)；ht : N.IsMinimalPrimaryDecomposi
tion t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.injOn_iff_pairwise_ne`：injOn_iff_pairwise_ne {s : Set ι} : InjOn f s
 ↔ s.Pairwise (f · != f ·)
· 使用定理 `Submodule.IsMinimalPrimaryDecomposition.distinct`：∀ {R : Type u_1} {M : 
Type u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Mo
dule R M]   {N : Submodule R M} {t : F…
-/
lemma injOn (N : Submodule R M)
    (t : Finset (Submodule R M)) (ht : N.IsMinimalPrimaryDecomposition t) :
    Set.InjOn (fun J ↦ (J.colon Set.univ).radical) (t : Set (Submodule R M)) :=
  Set.injOn_iff_pairwise_ne.mpr ht.distinct

/-- The first uniqueness theorem for primary decomposition, Theorem 4.5 in Atiyah-Macdonald:
In any minimal primary decomposition `I = ⨅ i, q_i`, the ideals `radical (q_i.colon M)` are exactly
the associated primes of `I`. -/
/-
**Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes** 是
 Mathlib 中的一个引理，位于命名空间 `Submodule.IsMinimalPrimaryDecomposition`。
形式化陈述：image_radical_eq_associated_primes {N : Submodule R M} {t : Finset (Submod
ule R M)} (ht : IsMinimalPrimaryDecomposition N t) : (fun J : Submodule R M => (
J.colon Set.univ).radical) '' t = N.associatedPrimes
参数：Submodule R M；ht : IsMinimalPrimaryDecomposition N t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsMinimalPrimaryDecomposition.inf_eq`：∀ {R : Type u_1} {M : Ty
pe u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modu
le R M]   {N : Submodule R M} {t : F…
· 使用引理 `Submodule.colon_finsetInf`：colon_finsetInf {ι : Type*} (s : Finset ι) (f
 : ι -> Submodule R M) : (s.inf f).colon S = s.inf (fun i => (f i).colon S)
· 使用定理 `map_finset_inf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeInf α] [inst_1 : OrderTop α]   [inst_2 : SemilatticeInf
 β] …
· 使用定理 `InfTopHom.instInfTopHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Mi
n α] [inst_1 : Top α] [inst_2 : Min β] [inst_3 : Top β],   InfTopHomClass (InfTo
pHom α β) α β
· 使用定理 `Finset.inf_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] [inst_1 : OrderTop α] {s₁ s₂ : Finset β} {f g : β → α},   s₁ = s₂ → (∀ a ∈ s
₂, f a…
· 使用定理 `Submodule.IsPrimary.radical_colon_singleton_eq_ite`：∀ {R : Type u_1} {M 
: Type u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.
Module R M]   {S : Submodule R M},   S.I…
· 使用定理 `Submodule.IsMinimalPrimaryDecomposition.primary`：∀ {R : Type u_1} {M : T
ype u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Mod
ule R M]   {N : Submodule R M} {t : F…
· 使用定理 `Finset.inf_ite`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α
] [inst_1 : OrderTop α] {s : Finset β} {f g : β → α}   (p : β → Prop) [inst_2 : 
Deci…
· 使用定理 `Finset.inf_top`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α
] [inst_1 : OrderTop α] (s : Finset β), (s.inf fun x => ⊤) = ⊤
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.not_le_iff_exists`：not_le_iff_exists : ¬p <= q ↔ exists x in p, 
x ∉ q
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.IsMinimalPrimaryDecomposition.minimal`：∀ {R : Type u_1} {M : T
ype u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Mod
ule R M]   {N : Submodule R M} {t : F…
· 使用定理 `Submodule.IsPrimary.isPrime_radical_colon`：∀ {R : Type u_1} {M : Type u_
2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R 
M]   {S : Submodule R M}, S.IsP…
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `Finset.le_inf_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {a : α},   a ≤ s.inf f ↔ ∀
 b ∈ s,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.eq_inf_of_isPrime_inf`：eq_inf_of_isPrime_inf {s : Finset ι} {f : ι
 -> Ideal R} (hp : IsPrime (s.inf f)) : exists i in s, f i = s.inf f
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The first uniqueness theorem for primary decomposition, Theorem 4.5 in Atiyah-Ma
cdonald:
In any minimal primary decomposition `I = ⨅ i, q_i`, the ideals `radical (q_i.co
lon M)` are exactly
the associated primes of `I`.
-/
lemma image_radical_eq_associated_primes
    {N : Submodule R M} {t : Finset (Submodule R M)} (ht : IsMinimalPrimaryDecomposition N t) :
    (fun J : Submodule R M ↦ (J.colon Set.univ).radical) '' t = N.associatedPrimes := by
  classical
  replace h x : radical (N.colon {x}) = (t.filter (x ∉ ·)).inf fun q ↦ radical (q.colon .univ) := by
    simp_rw [← ht.inf_eq, colon_finsetInf, ← radicalInfTopHom_apply, map_finset_inf,
      Function.comp_def, radicalInfTopHom_apply, id_eq]
    rw [Finset.inf_congr rfl (fun q hq ↦ (ht.primary hq).radical_colon_singleton_eq_ite x),
      Finset.inf_ite, Finset.inf_top, top_inf_eq]
  ext p
  constructor
  · rintro ⟨q, hqt, rfl⟩
    obtain ⟨x, hxt, hxq⟩ := SetLike.not_le_iff_exists.mp (ht.minimal hqt)
    use (ht.primary hqt).isPrime_radical_colon, x
    rw [h, ← Finset.insert_erase (Finset.mem_filter.mpr ⟨hqt, hxq⟩), Finset.inf_insert,
      eq_comm, inf_eq_left, Finset.le_inf_iff]
    simp only [mem_finsetInf, Finset.mem_erase] at hxt
    grind
  · rintro ⟨hp, x, rfl⟩
    rw [h] at hp ⊢
    obtain ⟨q, hq1, hq2⟩ := eq_inf_of_isPrime_inf hp
    exact ⟨q, Finset.mem_of_mem_filter q hq1, hq2⟩

@[deprecated (since := "2026-01-19")]
alias mem_image_radical_colon_iff := image_radical_eq_associated_primes
/-
**Submodule.IsMinimalPrimaryDecomposition.mem_associatedPrimes** 是 Mathlib 中的一个引
理，位于命名空间 `Submodule.IsMinimalPrimaryDecomposition`。
形式化陈述：mem_associatedPrimes {N : Submodule R M} {t : Finset (Submodule R M)} (ht 
: IsMinimalPrimaryDecomposition N t) {q : Submodule R M} (hq : q in t) : (q.colo
n Set.univ).radical in N.associatedPrimes
参数：Submodule R M；ht : IsMinimalPrimaryDecomposition N t；hq : q in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_prim
es`：image_radical_eq_associated_primes {N : Submodule R M} {t : Finset (Submodul
e R M)} (ht : IsMinimalPrimaryDecomposition N t) : (fun J : Subm…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma mem_associatedPrimes {N : Submodule R M} {t : Finset (Submodule R M)}
    (ht : IsMinimalPrimaryDecomposition N t) {q : Submodule R M} (hq : q ∈ t) :
    (q.colon Set.univ).radical ∈ N.associatedPrimes := by
  rw [← ht.image_radical_eq_associated_primes]
  exact Set.mem_image_of_mem _ hq

section CommRing

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M] {N : Submodule R M}

open LocalizedModule in
/-
**Submodule.IsMinimalPrimaryDecomposition.comap_localized** 是 Mathlib 中的一个引理，位于命
名空间 `Submodule.IsMinimalPrimaryDecomposition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_localized₀_eq_ite
    (s₀ : Finset N.associatedPrimes) (hs₀ : IsLowerSet (s₀ : Set N.associatedPrimes))
    (q : Submodule R M) (hqp : q.IsPrimary)
    (p : N.associatedPrimes) (hq : (q.colon Set.univ).radical = p) :
    letI S := ⨅ q ∈ s₀, q.1.primeCompl
    letI f := mkLinearMap S M
    (localized₀ S f q).comap f = if p ∈ s₀ then q else ⊤ := by
  set S := ⨅ q ∈ s₀, q.1.primeCompl
  set f := mkLinearMap S M
  split_ifs with hp
  · refine le_antisymm (fun x hx ↦ ?_) (map_le_iff_le_comap.mp (map_le_localized₀ S f q))
    obtain ⟨b, hb, a, ha⟩ := hx
    rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower] at ha
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S f).mp ha
    replace hb := q.smul_mem c hb
    rw [← Submonoid.smul_def, hc, smul_smul] at hb
    apply (hqp.mem_or_mem hb).resolve_right
    grind [Submonoid.mem_iInf, mem_primeCompl_iff]
  · replace hq : ¬ (q.colon Set.univ : Set R) ⊆ ⋃ r ∈ s₀, r := by
      contrapose hp
      obtain ⟨r, hrs, h⟩ := (subset_union_prime p p fun i _ _ _ ↦ i.2.1).mp hp
      rw [← r.2.1.radical_le_iff, hq] at h
      exact hs₀ h hrs
    obtain ⟨y, hy1, hy2⟩ := Set.not_subset_iff_exists_mem_notMem.mp hq
    replace hy2 : y ∈ S := by
      simp only [Submonoid.mem_iInf, Ideal.mem_primeCompl_iff, Subtype.forall, S]
      intro r hrI hrs
      contrapose hy2
      exact Set.mem_biUnion hrs hy2
    rw [eq_top_iff, ← map_le_iff_le_comap, map_top]
    rintro - ⟨x, rfl⟩
    simp_rw [mem_localized₀, IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower]
    exact ⟨y • x, hy1 (Set.smul_mem_smul_set (Set.mem_univ x)), ⟨y, hy2⟩, rfl⟩

open LocalizedModule Submodule.IsLocalizedModule in
/-- The second uniqueness theorem for primary decomposition, Theorem 4.10 in Atiyah-Macdonald. -/
/-
**Submodule.IsMinimalPrimaryDecomposition.comap_localized** 是 Mathlib 中的一个引理，位于命
名空间 `Submodule.IsMinimalPrimaryDecomposition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second uniqueness theorem for primary decomposition, Theorem 4.10 in Atiyah-
Macdonald.
-/
lemma comap_localized₀_eq_iInf
    {t : Finset (Submodule R M)} (ht : N.IsMinimalPrimaryDecomposition t)
    (s₀ : Finset N.associatedPrimes) (hs₀ : IsLowerSet (s₀ : Set N.associatedPrimes))
    (s : Finset (Submodule R M)) (hs : s ⊆ t)
    (hs' : (s.image fun q ↦ (q.colon Set.univ).radical) = s₀.image (↑)) :
    letI S := ⨅ q ∈ s₀, q.1.primeCompl
    letI f := mkLinearMap S M
    (N.localized₀ S f).comap f = ⨅ q ∈ s, q := by
  set S := ⨅ q ∈ s₀, q.1.primeCompl
  set f := mkLinearMap S M
  rw [← ht.inf_eq, ← localized₀FrameHom_apply, map_finset_inf, Submodule.comap_finsetInf]
  simp_rw [Function.comp_def, id_eq, localized₀FrameHom_apply]
  suffices ∀ q ∈ t, (localized₀ S f q).comap f = if q ∈ s then q else ⊤ by
    rw [Finset.inf_congr rfl this, Finset.inf_ite, Finset.inf_top, inf_top_eq,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hs, Finset.inf_eq_iInf]
  refine fun q hqt ↦ (IsMinimalPrimaryDecomposition.comap_localized₀_eq_ite s₀ hs₀ q
    (ht.primary hqt) ⟨(q.colon Set.univ).radical, ht.mem_associatedPrimes hqt⟩ rfl).trans
    (ite_cond_congr (Iff.trans ?_ (ht.injOn.mem_image_iff hs hqt)).eq)
  grind [Finset.mem_image_of_mem]

end CommRing

end Submodule.IsMinimalPrimaryDecomposition

/-
**Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical** 是 Mat
hlib 中的一个引理，位于命名空间 `Submodule.IsMinimalPrimaryDecomposition`。
形式化陈述：Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical {I 
: Ideal R} {t : Finset (Ideal R)} (ht : I.IsMinimalPrimaryDecomposition t) : I.m
inimalPrimes subseteq radical '' t
参数：Ideal R；ht : I.IsMinimalPrimaryDecomposition t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsPrime.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ideal
 R}, I.IsPrime → I.radical = I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Submodule.IsMinimalPrimaryDecomposition.inf_eq`：∀ {R : Type u_1} {M : Ty
pe u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modu
le R M]   {N : Submodule R M} {t : F…
· 使用引理 `Ideal.radicalInfTopHom_apply`：radicalInfTopHom_apply (I : Ideal R) : rad
icalInfTopHom I = radical I
· 使用定理 `map_finset_inf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeInf α] [inst_1 : OrderTop α]   [inst_2 : SemilatticeInf
 β] …
· 使用定理 `InfTopHom.instInfTopHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Mi
n α] [inst_1 : Top α] [inst_2 : Min β] [inst_3 : Top β],   InfTopHomClass (InfTo
pHom α β) α β
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ideal.radical_mono`：radical_mono (H : I <= J) : radical I <= radical J
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsPrime.inf_le'`：∀ {R : Type u} {ι : Type u_1} [inst : CommSemirin
g R] {s : Finset ι} {f : ι → Ideal R} {P : Ideal R},   P.IsPrime → (s.inf f ≤ P 
↔ ∃ i ∈ s, …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.isPrime_radical`：isPrime_radical {I : Ideal R} (hi : I.IsPrimary) 
: IsPrime (radical I)
· 使用定理 `Submodule.IsMinimalPrimaryDecomposition.primary`：∀ {R : Type u_1} {M : T
ype u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Mod
ule R M]   {N : Submodule R M} {t : F…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β},   b ∈ s → s.inf f ≤ f
 b
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
-/
lemma Ideal.IsMinimalPrimaryDecomposition.minimalPrimes_subset_image_radical
    {I : Ideal R} {t : Finset (Ideal R)} (ht : I.IsMinimalPrimaryDecomposition t) :
    I.minimalPrimes ⊆ radical '' t := by
  intro p hp
  have htp : t.inf radical ≤ p := by
    rw [← hp.1.1.radical]
    refine le_trans ?_ (radical_mono hp.1.2)
    rw [← ht.inf_eq, ← radicalInfTopHom_apply, map_finset_inf]
    rfl
  obtain ⟨q, hqt, hqp⟩ := (IsPrime.inf_le' hp.1.1).mp htp
  exact ⟨q, hqt, le_antisymm hqp (hp.2 ⟨isPrime_radical (ht.primary hqt),
    ht.inf_eq.symm.trans_le ((Finset.inf_le hqt).trans le_radical)⟩ hqp)⟩

@[deprecated (since := "2026-01-19")]
alias Ideal.decomposition_erase_inf := Submodule.decomposition_erase_inf

@[deprecated (since := "2026-01-19")]
alias Ideal.isPrimary_decomposition_pairwise_ne_radical :=
  Submodule.isPrimary_decomposition_pairwise_ne_radical

@[deprecated (since := "2026-01-19")]
alias Ideal.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition :=
  Submodule.exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsMinimalPrimaryDecomposition := Submodule.IsMinimalPrimaryDecomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsLasker.exists_isMinimalPrimaryDecomposition :=
  Submodule.IsLasker.exists_isMinimalPrimaryDecomposition

@[deprecated (since := "2026-01-19")]
alias Ideal.IsLasker.minimal := Submodule.IsLasker.exists_isMinimalPrimaryDecomposition

end IsLasker

namespace Submodule

section Noetherian

open scoped Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M]

/-
**Submodule._root_.InfIrred.isPrimary** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.InfIrred.isPrimary {N : Submodule R M} (h : InfIrred N) : N.IsPrimary := by
  rw [Submodule.IsPrimary]
  refine ⟨h.ne_top, fun {a b} hab ↦ ?_⟩
  let f : ℕ → Submodule R M := fun n ↦
  { carrier := {x | a ^ n • x ∈ N}
    add_mem' hx hy := by simp [N.add_mem hx hy]
    zero_mem' := by simp
    smul_mem' x y h := by simp [smul_comm _ x, N.smul_mem x h] }
  have hf : Monotone f := by
    intro n m hnm x hx
    simpa [hnm, smul_smul, ← pow_add] using! N.smul_mem (a ^ (m - n)) hx
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹_› ⟨f, hf⟩
  rcases h with ⟨-, h⟩
  specialize @h (f n) (N + a ^ n • ⊤) ?_
  · refine le_antisymm (fun r ⟨h1, h2⟩ ↦ ?_) (le_inf (fun x ↦ N.smul_mem (a ^ n)) (by simp))
    simp only [add_eq_sup, SetLike.mem_coe, mem_sup, mem_smul_pointwise_iff_exists] at h2
    obtain ⟨x, hx, -, ⟨y, -, rfl⟩, rfl⟩ := h2
    have h : (a ^ n • y ∈ N) = (a ^ (n + n) • y ∈ N) := congr_arg (y ∈ ·) (hn (n + n) le_add_self)
    rw [pow_add, mul_smul] at h
    rwa [N.add_mem_iff_right hx, h, ← N.add_mem_iff_right (N.smul_mem (a ^ n) hx), ← smul_add]
  rw [add_eq_sup, sup_eq_left] at h
  refine h.imp (fun h ↦ ?_) (fun h ↦ ⟨n, h⟩)
  replace hn : f n = f (n + 1) := hn (n + 1) n.le_succ
  rw [← h, hn]
  rw [← h] at hab
  simpa [f, pow_succ, mul_smul] using! hab

variable (R M) in
/-- The Lasker--Noether theorem: every submodule in a Noetherian module admits a decomposition into
  primary submodules. -/
/-
**Submodule.isLasker** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ (R : Type u_1) (M : Type u_2) [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   [IsNoetherian R M], IsLasker R M
参数：R : Type u_1；M : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `InfIrred.isPrimary`：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] 
[inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsNoetherian R M] {N :
 Submodu…
· 使用定理 `exists_infIrred_decomposition`：exists_infIrred_decomposition (a : α) : e
xists s : Finset α, s.inf id = a ∧ forall ⦃b⦄, b in s -> InfIrred b

--- 原说明 ---
The Lasker--Noether theorem: every submodule in a Noetherian module admits a dec
omposition into
  primary submodules.
-/
lemma isLasker : IsLasker R M := fun I ↦
  (exists_infIrred_decomposition I).imp fun _ h ↦ h.imp_right fun h' _ ht ↦ (h' ht).isPrimary

end Noetherian

end Submodule

@[deprecated (since := "2026-01-19")]
alias Ideal.isLasker := Submodule.isLasker

