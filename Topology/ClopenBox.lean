/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Compactness.Bases
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Sets.Closeds

/-!
# Clopen subsets in Cartesian products

In general, a clopen subset in a Cartesian product of topological spaces
cannot be written as a union of "clopen boxes",
i.e. products of clopen subsets of the components (see [buzyakovaClopenBox] for counterexamples).

However, when one of the factors is compact, a clopen subset can be written as such a union.
Our argument in `TopologicalSpace.Clopens.exists_prod_subset`
follows the one given in [buzyakovaClopenBox].

We deduce that in a product of compact spaces, a clopen subset is a finite union of clopen boxes,
and use that to prove that the property of having countably many clopens is preserved by taking
Cartesian products of compact spaces (this is relevant to the theory of light profinite sets).

## References

- [buzyakovaClopenBox]: *On clopen sets in Cartesian products*, 2001.
- [engelking1989]: *General Topology*, 1989.

-/

public section

open Function Set Filter TopologicalSpace
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]

namespace TopologicalSpace.Clopens

/-
**TopologicalSpace.Clopens.exists_prod_subset** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.Clopens`。
形式化陈述：exists_prod_subset (W : Clopens (X × Y)) {a : X × Y} (h : a in W) : exists
 U : Clopens X, a.1 in U ∧ exists V : Clopens Y, a.2 in V ∧ U ×ˢ V <= W
参数：W : Clopens (X × Y)；h : a in W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `TopologicalSpace.Clopens.isClopen'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Clopens α), IsClopen self.carrier
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsClopen.preimage`：IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X
 -> Y} (hf : Continuous f) : IsClopen (f ⁻¹' s)
· 使用引理 `ContinuousMap.isClopen_setOfPred_mapsTo`：isClopen_setOfPred_mapsTo (hK :
 IsCompact K) (hU : IsClopen U) : IsClopen {f : C(X, Y) | MapsTo f K U}
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Clopens.mk.congr_simp`：∀ {α : Type u_4} [inst : Topolog
icalSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is
Clopen' : IsClopen carrier),…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem exists_prod_subset (W : Clopens (X × Y)) {a : X × Y} (h : a ∈ W) :
    ∃ U : Clopens X, a.1 ∈ U ∧ ∃ V : Clopens Y, a.2 ∈ V ∧ U ×ˢ V ≤ W := by
  have hp : Continuous (fun y : Y ↦ (a.1, y)) := .prodMk_right _
  let V : Set Y := {y | (a.1, y) ∈ W}
  have hV : IsCompact V := (W.2.1.preimage hp).isCompact
  let U : Set X := {x | MapsTo (Prod.mk x) V W}
  have hUV : U ×ˢ V ⊆ W := fun ⟨_, _⟩ hw ↦ hw.1 hw.2
  exact ⟨⟨U, (ContinuousMap.isClopen_setOfPred_mapsTo hV W.2).preimage
    (ContinuousMap.id (X × Y)).curry.2⟩, by simp [U, V, MapsTo], ⟨V, W.2.preimage hp⟩, h, hUV⟩

variable [CompactSpace X]

/-- Every clopen set in a product of two compact spaces
is a union of finitely many clopen boxes. -/
/-
**TopologicalSpace.Clopens.exists_finset_eq_sup_prod** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace.Clopens`。
形式化陈述：exists_finset_eq_sup_prod (W : Clopens (X × Y)) : exists (I : Finset (Clop
ens X × Clopens Y)), W = I.sup fun i => i.1 ×ˢ i.2
参数：W : Clopens (X × Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `instCompactSpaceProd`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [CompactSpace Y],   Compact
Space (X ×…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `TopologicalSpace.Clopens.isClopen'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Clopens α), IsClopen self.carrier
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `TopologicalSpace.Clopens.exists_prod_subset`：exists_prod_subset (W : Clo
pens (X × Y)) {a : X × Y} (h : a in W) : exists U : Clopens X, a.1 in U ∧ exists
 V : Clopens Y, a.2 in V ∧ U ×ˢ V…

--- 原说明 ---
Every clopen set in a product of two compact spaces
is a union of finitely many clopen boxes.
-/
theorem exists_finset_eq_sup_prod (W : Clopens (X × Y)) :
    ∃ (I : Finset (Clopens X × Clopens Y)), W = I.sup fun i ↦ i.1 ×ˢ i.2 := by
  choose! U hxU V hxV hUV using fun x ↦ W.exists_prod_subset (a := x)
  rcases W.2.1.isCompact.elim_nhds_subcover (fun x ↦ U x ×ˢ V x) (fun x hx ↦
    (U x ×ˢ V x).2.isOpen.mem_nhds ⟨hxU x hx, hxV x hx⟩) with ⟨I, hIW, hWI⟩
  classical
  use I.image fun x ↦ (U x, V x)
  rw [Finset.sup_image]
  refine le_antisymm (fun x hx ↦ ?_) (Finset.sup_le fun x hx ↦ ?_)
  · rcases Set.mem_iUnion₂.1 (hWI hx) with ⟨i, hi, hxi⟩
    exact SetLike.le_def.1 (Finset.le_sup hi) hxi
  · exact hUV _ <| hIW _ hx
/-
**TopologicalSpace.Clopens.surjective_finset_sup_prod** 是 Mathlib 中的一个引理，位于命名空间 
`TopologicalSpace.Clopens`。
形式化陈述：surjective_finset_sup_prod : Surjective fun I : Finset (Clopens X × Clopen
s Y) => I.sup fun i => i.1 ×ˢ i.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Clopens.exists_finset_eq_sup_prod`：exists_finset_eq_sup
_prod (W : Clopens (X × Y)) : exists (I : Finset (Clopens X × Clopens Y)), W = I
.sup fun i => i.1 ×ˢ i.2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma surjective_finset_sup_prod :
    Surjective fun I : Finset (Clopens X × Clopens Y) ↦ I.sup fun i ↦ i.1 ×ˢ i.2 := fun W ↦
  let ⟨I, hI⟩ := W.exists_finset_eq_sup_prod; ⟨I, hI.symm⟩
/-
**TopologicalSpace.Clopens.countable_prod** 是 Mathlib 中的一个实例，位于命名空间 `Topological
Space.Clopens`。
形式化陈述：countable_prod [Countable (Clopens X)] [Countable (Clopens Y)] : Countable
 (Clopens (X × Y))
参数：Clopens X；Clopens Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.countable`：∀ {α : Sort u} {β : Sort v} [Countable α]
 {f : α → β}, Function.Surjective f → Countable β
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用引理 `TopologicalSpace.Clopens.surjective_finset_sup_prod`：surjective_finset_s
up_prod : Surjective fun I : Finset (Clopens X × Clopens Y) => I.sup fun i => i.
1 ×ˢ i.2
-/
instance countable_prod [Countable (Clopens X)]
    [Countable (Clopens Y)] : Countable (Clopens (X × Y)) :=
  surjective_finset_sup_prod.countable
/-
**TopologicalSpace.Clopens.finite_prod** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.Clopens`。
形式化陈述：finite_prod [Finite (Clopens X)] [Finite (Clopens Y)] : Finite (Clopens (X
 × Y))
参数：Clopens X；Clopens Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `TopologicalSpace.Clopens.surjective_finset_sup_prod`：surjective_finset_s
up_prod : Surjective fun I : Finset (Clopens X × Clopens Y) => I.sup fun i => i.
1 ×ˢ i.2
-/
instance finite_prod [Finite (Clopens X)] [Finite (Clopens Y)] :
    Finite (Clopens (X × Y)) := by
  cases nonempty_fintype (Clopens X)
  cases nonempty_fintype (Clopens Y)
  exact .of_surjective _ surjective_finset_sup_prod
/-
**TopologicalSpace.Clopens.countable_iff_secondCountable** 是 Mathlib 中的一个引理，位于命名
空间 `TopologicalSpace.Clopens`。
形式化陈述：countable_iff_secondCountable [T2Space X] [TotallyDisconnectedSpace X] : C
ountable (Clopens X) ↔ SecondCountableTopology X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `Function.Injective.of_eq_imp_le`：Function.Injective.of_eq_imp_le [Partia
lOrder α] {f : α -> β} (h : forall {x y}, f x = f y -> x <= y) : f.Injective
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.eq_generateFrom`：∀ {α : Type u} [t :
 TopologicalSpace α] {s : Set (Set α)},   TopologicalSpace.IsTopologicalBasis s 
→ t = TopologicalSpace.generateFrom s
· 使用定理 `loc_compact_Haus_tot_disc_of_zero_dim`：loc_compact_Haus_tot_disc_of_zero
_dim [TotallyDisconnectedSpace H] : IsTopologicalBasis { s : Set H | IsClopen s 
}
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用引理 `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open`：eq_sUnion_fins
et_of_isTopologicalBasis_of_isCompact_open (b : Set (Set X)) (hb : IsTopological
Basis b) (U : Set X) (hUc : IsCompact U) (hUo …
· 使用定理 `TopologicalSpace.isBasis_countableBasis`：isBasis_countableBasis [SecondC
ountableTopology α] : IsTopologicalBasis (countableBasis α)
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `TopologicalSpace.Clopens.isClopen'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Clopens α), IsClopen self.carrier
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `TopologicalSpace.Clopens.ext`：∀ {α : Type u_2} [inst : TopologicalSpace 
α] {s t : TopologicalSpace.Clopens α}, ↑s = ↑t → s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
-/
lemma countable_iff_secondCountable [T2Space X]
    [TotallyDisconnectedSpace X] : Countable (Clopens X) ↔ SecondCountableTopology X := by
  refine ⟨fun h ↦ ⟨{s : Set X | IsClopen s}, ?_, ?_⟩, fun h ↦ ?_⟩
  · let f : {s : Set X | IsClopen s} → Clopens X := fun s ↦ ⟨s.1, s.2⟩
    exact Injective.of_eq_imp_le (f := f) (·.le) |>.countable
  · apply IsTopologicalBasis.eq_generateFrom
    exact loc_compact_Haus_tot_disc_of_zero_dim
  · have : ∀ (s : Clopens X), ∃ (t : Finset (countableBasis X)), s.1 = (SetLike.coe t).sUnion :=
      fun s ↦ eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _
        (isBasis_countableBasis X) s.1 s.2.1.isCompact s.2.2
    let f : Clopens X → Finset (countableBasis X) := fun s ↦ (this s).choose
    have hf : f.Injective := by
      intro s t (h : Exists.choose _ = Exists.choose _)
      ext1; change s.carrier = t.carrier
      rw [(this s).choose_spec, (this t).choose_spec, h]
    exact hf.countable

end TopologicalSpace.Clopens

