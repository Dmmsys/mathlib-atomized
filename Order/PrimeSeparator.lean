/-
Copyright (c) 2024 Sam van Gool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool
-/
module

public import Mathlib.Order.PrimeIdeal
public import Mathlib.Order.Zorn

/-!
# Separating prime filters and ideals

In a distributive lattice, if $F$ is a filter, $I$ is an ideal, and $F$ and $I$ are
disjoint, then there exists a prime ideal $J$ containing $I$ with $J$ still disjoint from $F$.
This theorem is a crucial ingredient to [Stone's][Sto1938] duality for bounded distributive
lattices. The construction of the separator relies on Zorn's lemma.

## Tags

ideal, filter, prime, distributive lattice

## References

* [M. H. Stone, Topological representations of distributive lattices and Brouwerian logics
  (1938)][Sto1938]
-/

public section

universe u
variable {α : Type*}

open Order Ideal Set

/-
**Lattice.mem_ideal_sup_principal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Lattice.mem_ideal_sup_principal [Lattice α] (a b : α) (J : Ideal α) : b in
 J ⊔ principal a ↔ exists j in J, b <= j ⊔ a
参数：a b : α；J : Ideal α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma Lattice.mem_ideal_sup_principal [Lattice α] (a b : α) (J : Ideal α) :
    b ∈ J ⊔ principal a ↔ ∃ j ∈ J, b ≤ j ⊔ a :=
  ⟨fun ⟨j, ⟨jJ, _, ha', bja'⟩⟩ => ⟨j, jJ, le_trans bja' (sup_le_sup_left ha' j)⟩,
    fun ⟨j, hj, hbja⟩ => ⟨j, hj, a, le_refl a, hbja⟩⟩

@[deprecated (since := "2026-06-11")] alias DistribLattice.mem_ideal_sup_principal :=
  Lattice.mem_ideal_sup_principal
/-
**DistribLattice.prime_ideal_of_disjoint_filter_ideal** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：DistribLattice.prime_ideal_of_disjoint_filter_ideal [DistribLattice α] {F 
: PFilter α} {I : Ideal α} (hFI : Disjoint (F : Set α) (I : Set α)) : exists J :
 Ideal α, (IsPrime J) ∧ I <= J ∧ Disjoint (F : Set α) J
参数：hFI : Disjoint (F : Set α) (I : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.isIdeal`：∀ {P : Type u_1} [inst : LE P] (s : Order.Ideal P),
 Order.IsIdeal ↑s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.isIdeal_sUnion_of_isChain`：isIdeal_sUnion_of_isChain {C : Set (Set
 P)} (hidl : forall I in C, IsIdeal I) (hC : IsChain (· subseteq ·) C) (hNe : C.
Nonempty) : IsIdeal C…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `zorn_subset_nonempty`：zorn_subset_nonempty (S : Set (Set α)) (H : forall
 c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall 
s in c, s …
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Order.Ideal.isProper_of_notMem`：isProper_of_notMem {I : Ideal P} {p : P}
 (notMem : p ∉ I) : IsProper I
· 使用定理 `Order.PFilter.nonempty`：∀ {P : Type u_1} [inst : Preorder P] (F : Order.
PFilter P), (↑F).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Order.Ideal.isPrime_iff_mem_or_mem`：isPrime_iff_mem_or_mem [IsProper I] 
: IsPrime I ↔ forall {x y : P}, x ⊓ y in I -> x in I ∨ y in I
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `Order.Ideal.mem_principal_self`：mem_principal_self : x in principal x
· 使用定理 `ne_of_mem_of_not_mem'`：∀ {α : Type u_1} {β : Type u_2} [inst : Membershi
p α β] {s t : β} {a : α}, a ∈ s → a ∉ t → s ≠ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Maximal.eq_of_le`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Part
ialOrder α], Maximal P x → P y → x ≤ y → x = y
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用引理 `Lattice.mem_ideal_sup_principal`：Lattice.mem_ideal_sup_principal [Lattic
e α] (a b : α) (J : Ideal α) : b in J ⊔ principal a ↔ exists j in J, b <= j ⊔ a
（共 37 条，此处仅展示前 30 条）
-/
theorem DistribLattice.prime_ideal_of_disjoint_filter_ideal [DistribLattice α]
    {F : PFilter α} {I : Ideal α} (hFI : Disjoint (F : Set α) (I : Set α)) :
    ∃ J : Ideal α, (IsPrime J) ∧ I ≤ J ∧ Disjoint (F : Set α) J := by
  -- Let S be the set of ideals containing I and disjoint from F.
  set S : Set (Set α) := { J : Set α | IsIdeal J ∧ I ≤ J ∧ Disjoint (F : Set α) J }
  -- Then I is in S...
  have IinS : ↑I ∈ S := ⟨Order.Ideal.isIdeal I, by trivial⟩
  -- ...and S contains upper bounds for any non-empty chains.
  have chainub : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hcC hcNe
    use sUnion c
    refine ⟨?_, fun s hs ↦ le_sSup hs⟩
    simp only [mem_ofPred_eq, disjoint_sUnion_right, S]
    let ⟨J, hJ⟩ := hcNe
    refine ⟨Order.isIdeal_sUnion_of_isChain (fun _ hJ ↦ (hcS hJ).1) hcC hcNe,
            ⟨le_trans (hcS hJ).2.1 (le_sSup hJ), fun J hJ ↦ (hcS hJ).2.2⟩⟩
  -- Thus, by Zorn's lemma, we can pick a maximal ideal J in S.
  obtain ⟨Jset, _, hmax⟩ := zorn_subset_nonempty S chainub I IinS
  obtain ⟨Jidl, IJ, JF⟩ := hmax.prop
  set J := IsIdeal.toIdeal Jidl
  use J
  have IJ' : I ≤ J := IJ
  clear chainub IinS
  -- By construction, J contains I and is disjoint from F. It remains to prove that J is prime.
  refine ⟨?_, ⟨IJ, JF⟩⟩
  -- First note that J is proper: ⊤ ∈ F so ⊤ ∉ J because F and J are disjoint.
  have Jpr : IsProper J := isProper_of_notMem (Set.disjoint_left.1 JF F.nonempty.some_mem)
  -- Suppose that a₁ ∉ J, a₂ ∉ J. We need to prove that a₁ ⊔ a₂ ∉ J.
  rw [isPrime_iff_mem_or_mem]
  intro a₁ a₂
  contrapose!
  intro ⟨ha₁, ha₂⟩
  -- Consider the ideals J₁, J₂ generated by J ∪ {a₁} and J ∪ {a₂}, respectively.
  let J₁ := J ⊔ principal a₁
  let J₂ := J ⊔ principal a₂
  -- For each i, Jᵢ is an ideal that contains aᵢ, and is not equal to J.
  have a₁J₁ : a₁ ∈ J₁ := mem_of_subset_of_mem (le_sup_right : _ ≤ J ⊔ _) mem_principal_self
  have a₂J₂ : a₂ ∈ J₂ := mem_of_subset_of_mem (le_sup_right : _ ≤ J ⊔ _) mem_principal_self
  have J₁J : ↑J₁ ≠ Jset := ne_of_mem_of_not_mem' a₁J₁ ha₁
  have J₂J : ↑J₂ ≠ Jset := ne_of_mem_of_not_mem' a₂J₂ ha₂
  -- Therefore, since J is maximal, we must have Jᵢ ∉ S.
  have J₁S : ↑J₁ ∉ S := fun h => J₁J (hmax.eq_of_le h (le_sup_left : J ≤ J₁)).symm
  have J₂S : ↑J₂ ∉ S := fun h => J₂J (hmax.eq_of_le h (le_sup_left : J ≤ J₂)).symm
  -- Since Jᵢ is an ideal that contains I, we have that Jᵢ is not disjoint from F.
  have J₁F : ¬ (Disjoint (F : Set α) J₁) := by
    intro hdis
    apply J₁S
    simp only [mem_ofPred_eq, SetLike.coe_subset_coe, S]
    exact ⟨J₁.isIdeal, le_trans IJ' le_sup_left, hdis⟩
  have J₂F : ¬ (Disjoint (F : Set α) J₂) := by
    intro hdis
    apply J₂S
    simp only [mem_ofPred_eq, SetLike.coe_subset_coe, S]
    exact ⟨J₂.isIdeal, le_trans IJ' le_sup_left, hdis⟩
  -- Thus, pick cᵢ ∈ F ∩ Jᵢ.
  let ⟨c₁, ⟨c₁F, c₁J₁⟩⟩ := Set.not_disjoint_iff.1 J₁F
  let ⟨c₂, ⟨c₂F, c₂J₂⟩⟩ := Set.not_disjoint_iff.1 J₂F
  -- Using the definition of Jᵢ, we can pick bᵢ ∈ J such that cᵢ ≤ bᵢ ⊔ aᵢ.
  let ⟨b₁, ⟨b₁J, cba₁⟩⟩ := (Lattice.mem_ideal_sup_principal a₁ c₁ J).1 c₁J₁
  let ⟨b₂, ⟨b₂J, cba₂⟩⟩ := (Lattice.mem_ideal_sup_principal a₂ c₂ J).1 c₂J₂
  -- Since J is an ideal, we have b := b₁ ⊔ b₂ ∈ J.
  let b := b₁ ⊔ b₂
  have bJ : b ∈ J := sup_mem b₁J b₂J
  -- We now prove a key inequality, using crucially that the lattice is distributive.
  have ineq : c₁ ⊓ c₂ ≤ b ⊔ (a₁ ⊓ a₂) :=
  calc
    c₁ ⊓ c₂ ≤ (b₁ ⊔ a₁) ⊓ (b₂ ⊔ a₂) := inf_le_inf cba₁ cba₂
    _       ≤ (b ⊔ a₁) ⊓ (b ⊔ a₂) := by gcongr; exacts [le_sup_left, le_sup_right]
    _       = b ⊔ (a₁ ⊓ a₂) := (sup_inf_left b a₁ a₂).symm
  -- Note that c₁ ⊓ c₂ ∈ F, since c₁ and c₂ are both in F and F is a filter.
  -- Since F is an upper set, it now follows that b ⊔ (a₁ ⊓ a₂) ∈ F.
  have ba₁a₂F : b ⊔ (a₁ ⊓ a₂) ∈ F := PFilter.mem_of_le ineq (PFilter.inf_mem c₁F c₂F)
  -- Now, if we would have a₁ ⊓ a₂ ∈ J, then, since J is an ideal and b ∈ J, we would also get
  -- b ⊔ (a₁ ⊓ a₂) ∈ J. But this contradicts that J is disjoint from F.
  contrapose JF with ha₁a₂
  rw [Set.not_disjoint_iff]
  use b ⊔ (a₁ ⊓ a₂)
  exact ⟨ba₁a₂F, sup_mem bJ ha₁a₂⟩

-- TODO: Define prime filters in Mathlib so that the following corollary can be stated and proved.
-- theorem prime_filter_of_disjoint_filter_ideal (hFI : Disjoint (F : Set α) (I : Set α)) :
--     ∃ G : PFilter α, (IsPrime G) ∧ F ≤ G ∧ Disjoint (G : Set α) I := by sorry
