/-
Copyright (c) 2022 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Order.SupIndep

/-!
# Canonical homomorphism from a finite family of monoids

This file defines the construction of the canonical homomorphism from a family of monoids.

Given a family of morphisms `ϕ i : N i →* M` for each `i : ι` where elements in the
images of different morphisms commute, we obtain a canonical morphism
`MonoidHom.noncommPiCoprod : (Π i, N i) →* M` that coincides with `ϕ`

## Main definitions

* `MonoidHom.noncommPiCoprod : (Π i, N i) →* M` is the main homomorphism
* `Subgroup.noncommPiCoprod : (Π i, H i) →* G` is the specialization to `H i : Subgroup G`
  and the subgroup embedding.

## Main theorems

* `MonoidHom.noncommPiCoprod` coincides with `ϕ i` when restricted to `N i`
* `MonoidHom.noncommPiCoprod_mrange`: The range of `MonoidHom.noncommPiCoprod` is
  `⨆ (i : ι), (ϕ i).mrange`
* `MonoidHom.noncommPiCoprod_range`: The range of `MonoidHom.noncommPiCoprod` is
  `⨆ (i : ι), (ϕ i).range`
* `Subgroup.noncommPiCoprod_range`: The range of `Subgroup.noncommPiCoprod` is `⨆ (i : ι), H i`.
* `MonoidHom.injective_noncommPiCoprod_of_iSupIndep`: in the case of groups, `pi_hom.hom` is
  injective if the `ϕ` are injective and the ranges of the `ϕ` are independent.
* `MonoidHom.independent_range_of_coprime_order`: If the `N i` have coprime orders, then the ranges
  of the `ϕ` are independent.
* `Subgroup.independent_of_coprime_order`: If commuting normal subgroups `H i` have coprime orders,
  they are independent.

-/

@[expose] public section

assert_not_exists Field

namespace Subgroup

variable {G : Type*} [Group G]

/-- `Finset.noncommProd` is “injective” in `f` if `f` maps into independent subgroups.  This
generalizes (one direction of) `Subgroup.disjoint_iff_mul_eq_one`. -/
@[to_additive /-- `Finset.noncommSum` is “injective” in `f` if `f` maps into independent subgroups.
This generalizes (one direction of) `AddSubgroup.disjoint_iff_add_eq_zero`. -/]
/-
**Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 `
Subgroup`。
形式化陈述：eq_one_of_noncommProd_eq_one_of_iSupIndep {ι : Type*} (s : Finset ι) (f : 
ι -> G) (comm) (K : ι -> Subgroup G) (hind : iSupIndep K) (hmem : forall x in s,
 f x in K x) (heq1 : s.noncommProd f comm = 1) : forall i in s, f i = 1
参数：s : Finset ι；f : ι -> G；comm；K : ι -> Subgroup G；hind : iSupIndep K；hmem : fo
rall x in s, f x in K x；heq1 : s.noncommProd f comm = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Subgroup.noncommProd_mem`：noncommProd_mem (K : Subgroup G) {ι : Type*} {
t : Finset ι} {f : ι -> G} (comm) : (forall c in t, f c in K) -> t.noncommProd f
 comm in K
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.disjoint_iff_mul_eq_one`：disjoint_iff_mul_eq_one {H₁ H₂ : Subgr
oup G} : Disjoint H₁ H₂ ↔ forall {x y : G}, x in H₁ -> y in H₂ -> x * y = 1 -> x
 = 1 ∧ y = 1
· 使用定理 `iSupIndep.disjoint_biSup`：iSupIndep.disjoint_biSup {ι : Type*} {α : Type
*} [CompleteLattice α] {t : ι -> α} (ht : iSupIndep t) {x : ι} {y : Set ι} (hx :
 x ∉ y) : Disj…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.noncommProd_insert_of_notMem`：noncommProd_insert_of_notMem [Decid
ableEq α] (s : Finset α) (a : α) (f : α -> β) (comm) (ha : a ∉ s) : noncommProd 
(insert a s) f comm = f a…
-/
theorem eq_one_of_noncommProd_eq_one_of_iSupIndep {ι : Type*} (s : Finset ι) (f : ι → G) (comm)
    (K : ι → Subgroup G) (hind : iSupIndep K) (hmem : ∀ x ∈ s, f x ∈ K x)
    (heq1 : s.noncommProd f comm = 1) : ∀ i ∈ s, f i = 1 := by
  classical
    revert heq1
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hnotMem ih =>
      have hcomm := comm.mono (Finset.coe_subset.2 <| Finset.subset_insert _ _)
      simp only [Finset.forall_mem_insert] at hmem
      have hmem_bsupr : s.noncommProd f hcomm ∈ ⨆ i ∈ (s : Set ι), K i := by
        refine Subgroup.noncommProd_mem _ _ ?_
        intro x hx
        have : K x ≤ ⨆ i ∈ (s : Set ι), K i := le_iSup₂ (f := fun i _ => K i) x hx
        exact this (hmem.2 x hx)
      intro heq1
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hnotMem] at heq1
      have hnotMem' : i ∉ (s : Set ι) := by simpa
      obtain ⟨heq1i : f i = 1, heq1S : s.noncommProd f _ = 1⟩ :=
        Subgroup.disjoint_iff_mul_eq_one.mp (hind.disjoint_biSup hnotMem') hmem.1 hmem_bsupr heq1
      intro i h
      simp only [Finset.mem_insert] at h
      rcases h with (rfl | h)
      · exact heq1i
      · refine ih hcomm hmem.2 heq1S _ h

end Subgroup

section FamilyOfMonoids

variable {M : Type*} [Monoid M]

-- We have a family of monoids
-- The fintype assumption is not always used, but declared here, to keep things in order
variable {ι : Type*} [Fintype ι]
variable {N : ι → Type*} [∀ i, Monoid (N i)]

-- And morphisms ϕ into G
variable (ϕ : ∀ i : ι, N i →* M)

-- We assume that the elements of different morphism commute
variable (hcomm : Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y))

namespace MonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- The canonical homomorphism from a family of monoids. -/
@[to_additive /-- The canonical homomorphism from a family of additive monoids. See also
`LinearMap.lsum` for a linear version without the commutativity assumption. -/]
/-
**MonoidHom.noncommPiCoprod** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：noncommPiCoprod : (forall i : ι, N i) ->* M where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def noncommPiCoprod : (∀ i : ι, N i) →* M where
  toFun f := Finset.univ.noncommProd (fun i => ϕ i (f i)) fun _ _ _ _ h => hcomm h _ _
  map_one' := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ _ _).trans (one_pow _)
    simp
  map_mul' f g := by
    convert! @Finset.noncommProd_mul_distrib _ _ _ _ (fun i => ϕ i (f i)) (fun i => ϕ i (g i)) _ _ _
    · exact map_mul _ _ _
    · rintro i - j - h
      exact hcomm h _ _

variable {hcomm}

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidHom.noncommPiCoprod_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：noncommPiCoprod_mulSingle [DecidableEq ι] (i : ι) (y : N i) : noncommPiCop
rod ϕ hcomm (Pi.mulSingle i y) = ϕ i y
参数：i : ι；y : N i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.noncommProd_insert_of_notMem`：noncommProd_insert_of_notMem [Decid
ableEq α] (s : Finset α) (a : α) (f : α -> β) (comm) (ha : a ∉ s) : noncommProd 
(insert a s) f comm = f a…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `Finset.noncommProd_eq_pow_card`：noncommProd_eq_pow_card (s : Finset α) (
f : α -> β) (comm) (m : β) (h : forall x in s, f x = m) : s.noncommProd f comm =
 m ^ s.card
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem noncommPiCoprod_mulSingle [DecidableEq ι] (i : ι) (y : N i) :
    noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y := by
  change Finset.univ.noncommProd (fun j => ϕ j (Pi.mulSingle i y j)) (fun _ _ _ _ h => hcomm h _ _)
    = ϕ i y
  rw [← Finset.insert_erase (Finset.mem_univ i)]
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ (Finset.notMem_erase i _)]
  rw [Pi.mulSingle_eq_same]
  rw [Finset.noncommProd_eq_pow_card]
  · rw [one_pow]
    exact mul_one _
  · intro j hj
    simp only [Finset.mem_erase] at hj
    simp [hj]

/--
The universal property of `MonoidHom.noncommPiCoprod`

Given monoid morphisms `φᵢ : Nᵢ → M` whose images pairwise commute,
there exists a unique monoid morphism `φ : Πᵢ Nᵢ → M` that induces the `φᵢ`,
and it is given by `MonoidHom.noncommPiCoprod`. -/
@[to_additive /-- The universal property of `MonoidHom.noncommPiCoprod`

Given monoid morphisms `φᵢ : Nᵢ → M` whose images pairwise commute,
there exists a unique monoid morphism `φ : Πᵢ Nᵢ → M` that induces the `φᵢ`,
and it is given by `AddMonoidHom.noncommPiCoprod`. -/]
/-
**MonoidHom.noncommPiCoprodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：noncommPiCoprodEquiv [DecidableEq ι] : { ϕ : forall i, N i ->* M // Pairwi
se fun i j => forall x y, Commute (ϕ i x) (ϕ j y) } ≃ ((forall i, N i) ->* M) wh
ere toFun ϕ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def noncommPiCoprodEquiv [DecidableEq ι] :
    { ϕ : ∀ i, N i →* M // Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y) } ≃
      ((∀ i, N i) →* M) where
  toFun ϕ := noncommPiCoprod ϕ.1 ϕ.2
  invFun f :=
    ⟨fun i => f.comp (MonoidHom.mulSingle N i), fun _ _ hij x y =>
      Commute.map (Pi.mulSingle_commute hij x y) f⟩
  left_inv ϕ := by
    ext
    simp only [coe_comp, Function.comp_apply, mulSingle_apply, noncommPiCoprod_mulSingle]
  right_inv f := pi_ext fun i x => by
    simp only [noncommPiCoprod_mulSingle, coe_comp, Function.comp_apply, mulSingle_apply]

@[to_additive]
/-
**MonoidHom.noncommPiCoprod_mrange** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：noncommPiCoprod_mrange : MonoidHom.mrange (noncommPiCoprod ϕ hcomm) = ⨆ i 
: ι, MonoidHom.mrange (ϕ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submonoid.noncommProd_mem`：noncommProd_mem (S : Submonoid M) {ι : Type*}
 (t : Finset ι) (f : ι -> M) (comm) (h : forall c in t, f c in S) : t.noncommPro
d f comm in S
· 使用定理 `Submonoid.mem_sSup_of_mem`：mem_sSup_of_mem {S : Set (Submonoid M)} {s : 
Submonoid M} (hs : s in S) : forall {x : M}, x in s -> x in sSup S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MonoidHom.noncommPiCoprod_mulSingle`：noncommPiCoprod_mulSingle [Decidabl
eEq ι] (i : ι) (y : N i) : noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y
-/
theorem noncommPiCoprod_mrange :
    MonoidHom.mrange (noncommPiCoprod ϕ hcomm) = ⨆ i : ι, MonoidHom.mrange (ϕ i) := by
  let := Classical.decEq ι
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    refine Submonoid.noncommProd_mem _ _ _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => ?_)
    apply Submonoid.mem_sSup_of_mem
    · use i
    simp
  · refine iSup_le ?_
    rintro i x ⟨y, rfl⟩
    exact ⟨Pi.mulSingle i y, noncommPiCoprod_mulSingle _ _ _⟩

@[to_additive]
/-
**MonoidHom.commute_noncommPiCoprod** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：commute_noncommPiCoprod {m : M} (comm : forall i (x : N i), Commute m ((ϕ 
i x))) (h : (i : ι) -> N i) : Commute m (MonoidHom.noncommPiCoprod ϕ hcomm h)
参数：comm : forall i (x : N i), Commute m ((ϕ i x))；h : (i : ι) -> N i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.noncommProd_induction`：noncommProd_induction (s : Finset α) (f : 
α -> β) (comm) (p : β -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit
 : p 1) (base : fo…
· 使用定理 `Commute.mul_right`：mul_right (hab : Commute a b) (hac : Commute a c) : C
ommute a (b * c)
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
-/
lemma commute_noncommPiCoprod {m : M}
    (comm : ∀ i (x : N i), Commute m ((ϕ i x))) (h : (i : ι) → N i) :
    Commute m (MonoidHom.noncommPiCoprod ϕ hcomm h) := by
  dsimp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]
  apply Finset.noncommProd_induction
  · exact fun x y ↦ Commute.mul_right
  · exact Commute.one_right _
  · exact fun x _ ↦ comm x (h x)

@[to_additive]
/-
**MonoidHom.noncommPiCoprod_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：noncommPiCoprod_apply (h : (i : ι) -> N i) : MonoidHom.noncommPiCoprod ϕ h
comm h = Finset.noncommProd Finset.univ (fun i => ϕ i (h i)) (Pairwise.set_pairw
ise (fun ⦃i j⦄ a => hcomm a (h i) (h j)) _)
参数：h : (i : ι) -> N i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma noncommPiCoprod_apply (h : (i : ι) → N i) :
    MonoidHom.noncommPiCoprod ϕ hcomm h = Finset.noncommProd Finset.univ (fun i ↦ ϕ i (h i))
      (Pairwise.set_pairwise (fun ⦃i j⦄ a ↦ hcomm a (h i) (h j)) _) := by
  dsimp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in
/--
Given monoid morphisms `φᵢ : Nᵢ → M` and `f : M → P`, if we have sufficient commutativity, then
`f ∘ (∐ᵢ φᵢ) = ∐ᵢ (f ∘ φᵢ)` -/
@[to_additive]
/-
**MonoidHom.comp_noncommPiCoprod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comp_noncommPiCoprod {P : Type*} [Monoid P] {f : M ->* P} (hcomm' : Pairwi
se fun i j => forall x y, Commute (f.comp (ϕ i) x) (f.comp (ϕ j) y)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Set.Pairwise.of_refl`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} [S
td.Refl r], s.Pairwise r → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_noncommProd`：map_noncommProd [MonoidHomClass F β γ] (s : Fins
et α) (f : α -> β) (comm) (g : F) : g (s.noncommProd f comm) = s.noncommProd (fu
n i => g (f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.noncommProd_congr`：noncommProd_congr {s₁ s₂ : Finset α} {f g : α 
-> β} (h₁ : s₁ = s₂) (h₂ : forall x in s₂, f x = g x) (comm) : noncommProd s₁ f 
comm = noncomm…
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given monoid morphisms `φᵢ : Nᵢ → M` and `f : M → P`, if we have sufficient comm
utativity, then
`f ∘ (∐ᵢ φᵢ) = ∐ᵢ (f ∘ φᵢ)`
-/
theorem comp_noncommPiCoprod {P : Type*} [Monoid P] {f : M →* P}
    (hcomm' : Pairwise fun i j => ∀ x y, Commute (f.comp (ϕ i) x) (f.comp (ϕ j) y) :=
      Pairwise.mono hcomm (fun i j ↦ forall_imp (fun x h y ↦ by
        simp only [MonoidHom.coe_comp, Function.comp_apply, Commute.map (h y) f]))) :
    f.comp (MonoidHom.noncommPiCoprod ϕ hcomm) =
      MonoidHom.noncommPiCoprod (fun i ↦ f.comp (ϕ i)) hcomm' :=
  MonoidHom.ext fun _ ↦ by
    simp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk,
      Function.comp_apply, Finset.map_noncommProd]

end MonoidHom

end FamilyOfMonoids

section FamilyOfGroups

variable {G : Type*} [Group G]
variable {ι : Type*}
variable {H : ι → Type*} [∀ i, Group (H i)]
variable (ϕ : ∀ i : ι, H i →* G)

namespace MonoidHom
-- The subgroup version of `MonoidHom.noncommPiCoprod_mrange`
@[to_additive]
/-
**MonoidHom.noncommPiCoprod_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：noncommPiCoprod_range [Fintype ι] {hcomm : Pairwise fun i j : ι => forall 
(x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)} : (noncommPiCoprod ϕ hcomm).range 
= ⨆ i : ι, (ϕ i).range
参数：x : H i；y : H j；ϕ i x；ϕ j y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.noncommProd_mem`：noncommProd_mem (K : Subgroup G) {ι : Type*} {
t : Finset ι} {f : ι -> G} (comm) : (forall c in t, f c in K) -> t.noncommProd f
 comm in K
· 使用定理 `Subgroup.mem_sSup_of_mem`：mem_sSup_of_mem {S : Set (Subgroup G)} {s : Su
bgroup G} (hs : s in S) : forall {x : G}, x in s -> x in sSup S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MonoidHom.noncommPiCoprod_mulSingle`：noncommPiCoprod_mulSingle [Decidabl
eEq ι] (i : ι) (y : N i) : noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y
-/
theorem noncommPiCoprod_range [Fintype ι]
    {hcomm : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)} :
    (noncommPiCoprod ϕ hcomm).range = ⨆ i : ι, (ϕ i).range := by
  let := Classical.decEq ι
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    refine Subgroup.noncommProd_mem _ (fun _ _ _ _ h => hcomm h _ _) ?_
    intro i _hi
    apply Subgroup.mem_sSup_of_mem
    · use i
    simp
  · refine iSup_le ?_
    rintro i x ⟨y, rfl⟩
    exact ⟨Pi.mulSingle i y, noncommPiCoprod_mulSingle _ _ _⟩

@[to_additive]
/-
**MonoidHom.injective_noncommPiCoprod_of_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 `Mo
noidHom`。
形式化陈述：injective_noncommPiCoprod_of_iSupIndep [Fintype ι] {hcomm : Pairwise fun i
 j : ι => forall (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)} (hind : iSupIndep
 fun i => (ϕ i).range) (hinj : forall i, Function.Injective (ϕ i)) : Function.In
jective (noncommPiCoprod ϕ hcomm)
参数：x : H i；y : H j；ϕ i x；ϕ j y；hind : iSupIndep fun i => (ϕ i).range；hinj : fora
ll i, Function.Injective (ϕ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep`：eq_one_of_noncommPro
d_eq_one_of_iSupIndep {ι : Type*} (s : Finset ι) (f : ι -> G) (comm) (K : ι -> S
ubgroup G) (hind : iSupIndep K) (hmem : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem injective_noncommPiCoprod_of_iSupIndep [Fintype ι]
    {hcomm : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)}
    (hind : iSupIndep fun i => (ϕ i).range)
    (hinj : ∀ i, Function.Injective (ϕ i)) : Function.Injective (noncommPiCoprod ϕ hcomm) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [eq_bot_iff]
  intro f heq1
  have : ∀ i, i ∈ Finset.univ → ϕ i (f i) = 1 :=
    Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep _ _ (fun _ _ _ _ h => hcomm h _ _)
      _ hind (by simp) heq1
  ext i
  apply hinj
  simp [this i (Finset.mem_univ i)]

@[to_additive]
/-
**MonoidHom.independent_range_of_coprime_order** 是 Mathlib 中的一个定理，位于命名空间 `Monoid
Hom`。
形式化陈述：independent_range_of_coprime_order (hcomm : Pairwise fun i j : ι => forall
 (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)) [Finite ι] [forall i, Fintype (H 
i)] (hcoprime : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fintype.ca
rd (H j))) : iSupIndep fun i => (ϕ i).range
参数：hcomm : Pairwise fun i j : ι => forall (x : H i) (y : H j), Commute (ϕ i x) (
ϕ j y)；H i；hcoprime : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fint
ype.card (H j))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.noncommPiCoprod_range`：noncommPiCoprod_range [Fintype ι] {hcom
m : Pairwise fun i j : ι => forall (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)}
 : (noncommPiCoprod ϕ…
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `orderOf_map_dvd`：orderOf_map_dvd {H : Type*} [Monoid H] (ψ : G ->* H) (x
 : G) : orderOf (ψ x) ∣ orderOf x
· 使用定理 `orderOf_dvd_card`：orderOf_dvd_card : orderOf x ∣ Fintype.card G
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
· 使用定理 `Nat.coprime_iff_gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n ↔ m.gcd n = 1
· 使用定理 `Nat.coprime_fintype_prod_left_iff`：coprime_fintype_prod_left_iff [Fintyp
e ι] {s : ι -> Nat} {x : Nat} : Coprime (∏ i, s i) x ↔ forall i, Coprime (s i) x
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem independent_range_of_coprime_order
    (hcomm : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y))
    [Finite ι] [∀ i, Fintype (H i)]
    (hcoprime : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    iSupIndep fun i => (ϕ i).range := by
  cases nonempty_fintype ι
  let := Classical.decEq ι
  rintro i
  rw [disjoint_iff_inf_le]
  rintro f ⟨hxi, hxp⟩
  dsimp at hxi hxp
  rw [iSup_subtype', ← noncommPiCoprod_range] at hxp
  rotate_left
  · intro _ _ hj
    apply hcomm
    exact hj ∘ Subtype.ext
  obtain ⟨g, hgf⟩ := hxp
  obtain ⟨g', hg'f⟩ := hxi
  have hxi : orderOf f ∣ Fintype.card (H i) := by
    rw [← hg'f]
    exact (orderOf_map_dvd _ _).trans orderOf_dvd_card
  have hxp : orderOf f ∣ ∏ j : { j // j ≠ i }, Fintype.card (H j) := by
    rw [← hgf, ← Fintype.card_pi]
    exact (orderOf_map_dvd _ _).trans orderOf_dvd_card
  change f = 1
  rw [← pow_one f, ← orderOf_dvd_iff_pow_eq_one]
  obtain ⟨c, hc⟩ := Nat.dvd_gcd hxp hxi
  use c
  rw [← hc]
  symm
  rw [← Nat.coprime_iff_gcd_eq_one, Nat.coprime_fintype_prod_left_iff, Subtype.forall]
  intro j h
  exact hcoprime h

end MonoidHom

end FamilyOfGroups

namespace Subgroup

-- We have a family of subgroups
variable {G : Type*} [Group G]
variable {ι : Type*} {H : ι → Subgroup G}

section CommutingSubgroups

-- We assume that the elements of different subgroups commute
-- with `hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y`

@[to_additive]
/-
**Subgroup.commute_subtype_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：commute_subtype_of_commute (hcomm : Pairwise fun i j : ι => forall x y : G
, x in H i -> y in H j -> Commute x y) (i j : ι) (hne : i != j) : forall (x : H 
i) (y : H j), Commute ((H i).subtype x) ((H j).subtype y)
参数：hcomm : Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commu
te x y；i j : ι；hne : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commute_subtype_of_commute
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) (i j : ι)
    (hne : i ≠ j) :
    ∀ (x : H i) (y : H j), Commute ((H i).subtype x) ((H j).subtype y) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  exact hcomm hne x y hx hy

@[to_additive]
/-
**Subgroup.independent_of_coprime_order** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：independent_of_coprime_order (hcomm : Pairwise fun i j : ι => forall x y :
 G, x in H i -> y in H j -> Commute x y) [Finite ι] [forall i, Fintype (H i)] (h
coprime : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fintype.card (H 
j))) : iSupIndep H
参数：hcomm : Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commu
te x y；H i；hcoprime : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fint
ype.card (H j))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `MonoidHom.independent_range_of_coprime_order`：independent_range_of_copri
me_order (hcomm : Pairwise fun i j : ι => forall (x : H i) (y : H j), Commute (ϕ
 i x) (ϕ j y)) [Finite ι] [forall …
· 使用定理 `Subgroup.commute_subtype_of_commute`：commute_subtype_of_commute (hcomm :
 Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y) (i
 j : ι) (hne : i != j) : …
-/
theorem independent_of_coprime_order
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    [Finite ι] [∀ i, Fintype (H i)]
    (hcoprime : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    iSupIndep H := by
  simpa using
    MonoidHom.independent_range_of_coprime_order (fun i => (H i).subtype)
      (commute_subtype_of_commute hcomm) hcoprime

variable [Fintype ι]

/-- The canonical homomorphism from a family of subgroups where elements from different subgroups
commute -/
@[to_additive /-- The canonical homomorphism from a family of additive subgroups where elements from
different subgroups commute -/]
/-
**Subgroup.noncommPiCoprod** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：noncommPiCoprod (hcomm : Pairwise fun i j : ι => forall x y : G, x in H i 
-> y in H j -> Commute x y) : (forall i : ι, H i) ->* G
参数：hcomm : Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commu
te x y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.commute_subtype_of_commute`：commute_subtype_of_commute (hcomm :
 Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y) (i
 j : ι) (hne : i != j) : …
-/
def noncommPiCoprod (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) :
    (∀ i : ι, H i) →* G :=
  MonoidHom.noncommPiCoprod (fun i => (H i).subtype) (commute_subtype_of_commute hcomm)

@[to_additive (attr := simp)]
/-
**Subgroup.noncommPiCoprod_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：noncommPiCoprod_mulSingle [DecidableEq ι] {hcomm : Pairwise fun i j : ι =>
 forall x y : G, x in H i -> y in H j -> Commute x y} (i : ι) (y : H i) : noncom
mPiCoprod hcomm (Pi.mulSingle i y) = y
参数：i : ι；y : H i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.noncommPiCoprod_mulSingle`：noncommPiCoprod_mulSingle [Decidabl
eEq ι] (i : ι) (y : N i) : noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y
· 使用定理 `Subgroup.commute_subtype_of_commute`：commute_subtype_of_commute (hcomm :
 Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y) (i
 j : ι) (hne : i != j) : …
-/
theorem noncommPiCoprod_mulSingle [DecidableEq ι]
    {hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y} (i : ι) (y : H i) :
    noncommPiCoprod hcomm (Pi.mulSingle i y) = y := by apply MonoidHom.noncommPiCoprod_mulSingle

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**Subgroup.noncommPiCoprod_range** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：noncommPiCoprod_range {hcomm : Pairwise fun i j : ι => forall x y : G, x i
n H i -> y in H j -> Commute x y} : (noncommPiCoprod hcomm).range = ⨆ i : ι, H i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.commute_subtype_of_commute`：commute_subtype_of_commute (hcomm :
 Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y) (i
 j : ι) (hne : i != j) : …
· 使用定理 `MonoidHom.noncommPiCoprod_range`：noncommPiCoprod_range [Fintype ι] {hcom
m : Pairwise fun i j : ι => forall (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)}
 : (noncommPiCoprod ϕ…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem noncommPiCoprod_range
    {hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y} :
    (noncommPiCoprod hcomm).range = ⨆ i : ι, H i := by
  simp [noncommPiCoprod, MonoidHom.noncommPiCoprod_range]

@[to_additive]
/-
**Subgroup.injective_noncommPiCoprod_of_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group`。
形式化陈述：injective_noncommPiCoprod_of_iSupIndep {hcomm : Pairwise fun i j : ι => fo
rall x y : G, x in H i -> y in H j -> Commute x y} (hind : iSupIndep H) : Functi
on.Injective (noncommPiCoprod hcomm)
参数：hind : iSupIndep H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.injective_noncommPiCoprod_of_iSupIndep`：injective_noncommPiCop
rod_of_iSupIndep [Fintype ι] {hcomm : Pairwise fun i j : ι => forall (x : H i) (
y : H j), Commute (ϕ i x) (ϕ j y)} (hi…
· 使用定理 `Subgroup.commute_subtype_of_commute`：commute_subtype_of_commute (hcomm :
 Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y) (i
 j : ι) (hne : i != j) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem injective_noncommPiCoprod_of_iSupIndep
    {hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y}
    (hind : iSupIndep H) :
    Function.Injective (noncommPiCoprod hcomm) := by
  apply MonoidHom.injective_noncommPiCoprod_of_iSupIndep
  · simpa using hind
  · intro i
    exact Subtype.coe_injective

@[to_additive]
/-
**Subgroup.noncommPiCoprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：noncommPiCoprod_apply (comm) (u : (i : ι) -> H i) : Subgroup.noncommPiCopr
od comm u = Finset.noncommProd Finset.univ (fun i => u i) (fun i _ j _ h => comm
 h _ _ (u i).prop (u j).prop)
参数：comm；u : (i : ι) -> H i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subgroup.commute_subtype_of_commute`：commute_subtype_of_commute (hcomm :
 Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y) (i
 j : ι) (hne : i != j) : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem noncommPiCoprod_apply (comm) (u : (i : ι) → H i) :
    Subgroup.noncommPiCoprod comm u = Finset.noncommProd Finset.univ (fun i ↦ u i)
      (fun i _ j _ h ↦ comm h _ _ (u i).prop (u j).prop) := by
  simp only [Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod,
    coe_subtype, MonoidHom.coe_mk, OneHom.coe_mk]

end CommutingSubgroups

end Subgroup

