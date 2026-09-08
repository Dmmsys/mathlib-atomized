/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Data.Set.Subset
public import Mathlib.Order.Irreducible
public import Mathlib.Topology.Order.LowerUpperTopology
public import Mathlib.Topology.Sets.Closeds

/-!
# Hull-Kernel Topology

Let `α` be a `CompleteLattice` and let `T` be a subset of `α`. The pair of maps
`S → sInf (Subtype.val '' S)` and `a → T ↓∩ Ici a` are often referred to as the `kernel` and the
`hull` respectively. They form an antitone Galois connection between the subsets of `T` and `α`.
When `α` can be generated from `T` by taking infs, this becomes a Galois insertion and the relative
topology (`Topology.lower`) on `T` takes on a particularly simple form: the relative-open sets are
exactly the sets of the form `(hull T a)ᶜ` for some `a` in `α`. The topological closure coincides
with the closure arising from the Galois insertion. For this reason the relative lower topology on
`T` is often referred to as the "hull-kernel topology". The names "Jacobson topology" and "structure
topology" also occur in the literature.

## Main statements

- `PrimitiveSpectrum.isTopologicalBasis_relativeLower` - the sets `(hull a)ᶜ` form a basis for the
  relative lower topology on `T`.
- `PrimitiveSpectrum.isOpen_iff` - for a complete lattice, the sets `(hull a)ᶜ` are the relative
  topology.
- `PrimitiveSpectrum.gc` - the `kernel` and the `hull` form a Galois connection
- `PrimitiveSpectrum.gi` - when `T` generates `α`, the Galois connection becomes an insertion.

## Implementation notes

The antitone Galois connection from `Set T` to `α` is implemented as a monotone Galois connection
between `Set T` to `αᵒᵈ`.

## Motivation

The motivating example for the study of a set `T` of prime elements which generate `α` is the
primitive spectrum of the lattice of M-ideals of a Banach space.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Henriksen et al, *Joincompact spaces, continuous lattices and C⋆-algebras*][henriksen_et_al1997]

## Tags

lower topology, hull-kernel topology, Jacobson topology, structure topology, primitive spectrum

-/

@[expose] public section

variable {α}

open TopologicalSpace
open Topology
open Set
open Set.Notation

section SemilatticeInf

variable [SemilatticeInf α]
namespace PrimitiveSpectrum

/-- For `a` of type `α` the set of element of `T` which dominate `a` is the `hull` of `a` in `T`. -/
/-
**PrimitiveSpectrum.hull** 是 Mathlib 中的一个缩写定义，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：hull (T : Set α) (a : α)
参数：T : Set α；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `a` of type `α` the set of element of `T` which dominate `a` is the `hull` o
f `a` in `T`.
-/
abbrev hull (T : Set α) (a : α) := T ↓∩ Ici a

variable {T : Set α}

/-- The set of relative-closed sets of the form `hull T a` for some `a` in `α` is closed under
pairwise union. -/
/-
**PrimitiveSpectrum.hull_inf** 是 Mathlib 中的一个引理，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：hull_inf (hT : forall p in T, InfPrime p) (a b : α) : hull T (a ⊓ b) = hul
l T a union hull T b
参数：hT : forall p in T, InfPrime p；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of relative-closed sets of the form `hull T a` for some `a` in `α` is cl
osed under
pairwise union.
-/
lemma hull_inf (hT : ∀ p ∈ T, InfPrime p) (a b : α) :
    hull T (a ⊓ b) = hull T a ∪ hull T b := by
  grind [InfPrime.inf_le]

variable [OrderTop α]

open Finset in
/-- Every relative-closed set of the form `T ↓∩ (↑(upperClosure F))` for `F` finite is a
relative-closed set of the form `hull T a` where `a = ⨅ F`. -/
/-
**PrimitiveSpectrum.hull_finsetInf** 是 Mathlib 中的一个引理，位于命名空间 `PrimitiveSpectrum`
。
形式化陈述：hull_finsetInf (hT : forall p in T, InfPrime p) (F : Finset α) : hull T (i
nf F id) = T ↓inter upperClosure (F : Set α)
参数：hT : forall p in T, InfPrime p；F : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_upperClosure`：coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a
 in s, Ici a
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.inf_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] [inst_1 : OrderTop α] {f : β → α}, ∅.inf f = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isMax_iff_eq_top`：isMax_iff_eq_top : IsMax a ↔ a = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.inf_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf 
α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β}   (h : b ∉ s), (Fins
et.co…
· 使用引理 `PrimitiveSpectrum.hull_inf`：hull_inf (hT : forall p in T, InfPrime p) (a
 b : α) : hull T (a ⊓ b) = hull T a union hull T b
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Every relative-closed set of the form `T ↓∩ (↑(upperClosure F))` for `F` finite 
is a
relative-closed set of the form `hull T a` where `a = ⨅ F`.
-/
lemma hull_finsetInf (hT : ∀ p ∈ T, InfPrime p) (F : Finset α) :
    hull T (inf F id) = T ↓∩ upperClosure (F : Set α) := by
  rw [coe_upperClosure]
  induction F using Finset.cons_induction with
  | empty =>
    simp only [coe_empty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.preimage_empty,
      inf_empty]
    by_contra hf
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hf
    obtain ⟨x, hx⟩ := hf
    exact (hT x (Subtype.coe_prop x)).1 (isMax_iff_eq_top.mpr (eq_top_iff.mpr hx))
  | cons a F' _ I4 => simp [hull_inf hT, I4]

open Finset in
/-- Every relative-open set of the form `T ↓∩ (↑(upperClosure F))ᶜ` for `F` finite
is a relative-open set of the form `(hull T a)ᶜ` where `a = ⨅ F`. -/
/-
**PrimitiveSpectrum.preimage_upperClosure_compl_finset** 是 Mathlib 中的一个引理，位于命名空间
 `PrimitiveSpectrum`。
形式化陈述：preimage_upperClosure_compl_finset (hT : forall p in T, InfPrime p) (F : F
inset α) : T ↓inter (upperClosure (F : Set α))ᶜ = (hull T (inf F id))ᶜ
参数：hT : forall p in T, InfPrime p；F : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用引理 `PrimitiveSpectrum.hull_finsetInf`：hull_finsetInf (hT : forall p in T, In
fPrime p) (F : Finset α) : hull T (inf F id) = T ↓inter upperClosure (F : Set α)

--- 原说明 ---
Every relative-open set of the form `T ↓∩ (↑(upperClosure F))ᶜ` for `F` finite
is a relative-open set of the form `(hull T a)ᶜ` where `a = ⨅ F`.
-/
lemma preimage_upperClosure_compl_finset (hT : ∀ p ∈ T, InfPrime p) (F : Finset α) :
    T ↓∩ (upperClosure (F : Set α))ᶜ = (hull T (inf F id))ᶜ := by
  rw [Set.preimage_compl, (hull_finsetInf hT)]

variable [TopologicalSpace α] [IsLower α]

/--
The relative-open sets of the form `(hull T a)ᶜ` for `a` in `α` form a basis for the relative
Lower topology.
-/
/-
**PrimitiveSpectrum.isTopologicalBasis_relativeLower** 是 Mathlib 中的一个引理，位于命名空间 `
PrimitiveSpectrum`。
形式化陈述：isTopologicalBasis_relativeLower (hT : forall p in T, InfPrime p) : IsTopo
logicalBasis { S : Set T | exists (a : α), (hull T a)ᶜ = S }
参数：hT : forall p in T, InfPrime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `upperClosure_singleton`：upperClosure_singleton (a : α) : upperClosure ({
a} : Set α) = UpperSet.Ici a
· 使用引理 `Set.image_val_compl`：image_val_compl : ↑(Dᶜ) = A \ ↑D
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `PrimitiveSpectrum.hull_finsetInf`：hull_finsetInf (hT : forall p in T, In
fPrime p) (F : Finset α) : hull T (inf F id) = T ↓inter upperClosure (F : Set α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `isTopologicalBasis_subtype`：isTopologicalBasis_subtype {α : Type*} [Topo
logicalSpace α] {B : Set (Set α)} (h : TopologicalSpace.IsTopologicalBasis B) (p
 : α -> Prop) : …
· 使用定理 `Topology.IsLower.isTopologicalBasis`：∀ {α : Type u_1} [inst : Preorder α
] [inst_1 : TopologicalSpace α] [Topology.IsLower α],   TopologicalSpace.IsTopol
ogicalBasis (Topology.IsL…

--- 原说明 ---
The relative-open sets of the form `(hull T a)ᶜ` for `a` in `α` form a basis for
 the relative
Lower topology.
-/
lemma isTopologicalBasis_relativeLower (hT : ∀ p ∈ T, InfPrime p) :
    IsTopologicalBasis { S : Set T | ∃ (a : α), (hull T a)ᶜ = S } := by
  convert! isTopologicalBasis_subtype Topology.IsLower.isTopologicalBasis (· ∈ T)
  ext R
  simp only [preimage_compl, mem_ofPred_eq, IsLower.lowerBasis, mem_image, exists_exists_and_eq_and]
  constructor <;> intro ha
  · obtain ⟨a, ha'⟩ := ha
    use {a}
    rw [← (Function.Injective.preimage_image Subtype.val_injective R), ← ha']
    simp only [finite_singleton, upperClosure_singleton, UpperSet.coe_Ici, image_val_compl,
      Subtype.image_preimage_coe, sdiff_self_inter, preimage_sdiff, Subtype.coe_preimage_self,
      true_and]
    exact compl_eq_univ_sdiff (Subtype.val ⁻¹' Ici a)
  · obtain ⟨F, hF⟩ := ha
    lift F to Finset α using hF.1
    use Finset.inf F id
    ext
    simp [hull_finsetInf hT, ← hF.2]

end PrimitiveSpectrum

end SemilatticeInf

namespace PrimitiveSpectrum
variable [CompleteLattice α] {T : Set α}

universe v

/-
**PrimitiveSpectrum.hull_iSup** 是 Mathlib 中的一个引理，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：hull_iSup {ι : Sort v} (s : ι -> α) : hull T (iSup s) = ⋂ i, hull T (s i)
参数：s : ι -> α。
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
lemma hull_iSup {ι : Sort v} (s : ι → α) : hull T (iSup s) = ⋂ i, hull T (s i) := by aesop
/-
**PrimitiveSpectrum.hull_sSup** 是 Mathlib 中的一个引理，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：hull_sSup (S : Set α) : hull T (sSup S) = ⋂₀ { hull T a | a in S }
参数：S : Set α。
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
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hull_sSup (S : Set α) : hull T (sSup S) = ⋂₀ { hull T a | a ∈ S } := by aesop

/-- When `α` is complete, a set is Lower topology relative-open if and only if it is of the form
`(hull T a)ᶜ` for some `a` in `α`. -/
/-
**PrimitiveSpectrum.isOpen_iff** 是 Mathlib 中的一个引理，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：isOpen_iff [TopologicalSpace α] [IsLower α] (hT : forall p in T, InfPrime 
p) (S : Set T) : IsOpen S ↔ exists (a : α), S = (hull T a)ᶜ
参数：hT : forall p in T, InfPrime p；S : Set T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'`：∀ {α : Type u} [t :
 TopologicalSpace α] {B : Set (Set α)},   TopologicalSpace.IsTopologicalBasis B 
→ ∀ {u : Set α}, IsOpen u → u = ⋃₀ {s | s…
· 使用引理 `PrimitiveSpectrum.isTopologicalBasis_relativeLower`：isTopologicalBasis_r
elativeLower (hT : forall p in T, InfPrime p) : IsTopologicalBasis { S : Set T |
 exists (a : α), (hull T a)ᶜ = S }
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `Topology.IsLower.instClosedIciTopology`：∀ {α : Type u_1} [inst : Preorde
r α] [inst_1 : TopologicalSpace α] [Topology.IsLower α], ClosedIciTopology α

--- 原说明 ---
When `α` is complete, a set is Lower topology relative-open if and only if it is
 of the form
`(hull T a)ᶜ` for some `a` in `α`.
-/
lemma isOpen_iff [TopologicalSpace α] [IsLower α] (hT : ∀ p ∈ T, InfPrime p)
    (S : Set T) : IsOpen S ↔ ∃ (a : α), S = (hull T a)ᶜ := by
  constructor <;> intro h
  · let R := {a : α | (hull T a)ᶜ ⊆ S}
    use sSup R
    rw [IsTopologicalBasis.open_eq_sUnion' (isTopologicalBasis_relativeLower hT) h]
    aesop
  · obtain ⟨a, ha⟩ := h
    exact ⟨(Ici a)ᶜ, isClosed_Ici.isOpen_compl, ha.symm⟩

/-- When `α` is complete, a set is closed in the relative lower topology if and only if it is of the
form `hull T a` for some `a` in `α`. -/
/-
**PrimitiveSpectrum.isClosed_iff** 是 Mathlib 中的一个引理，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：isClosed_iff [TopologicalSpace α] [IsLower α] (hT : forall p in T, InfPrim
e p) {S : Set T} : IsClosed S ↔ exists (a : α), S = hull T a
参数：hT : forall p in T, InfPrime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimitiveSpectrum.isOpen_iff`：isOpen_iff [TopologicalSpace α] [IsLower α
] (hT : forall p in T, InfPrime p) (S : Set T) : IsOpen S ↔ exists (a : α), S = 
(hull T a)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
When `α` is complete, a set is closed in the relative lower topology if and only
 if it is of the
form `hull T a` for some `a` in `α`.
-/
lemma isClosed_iff [TopologicalSpace α] [IsLower α] (hT : ∀ p ∈ T, InfPrime p)
    {S : Set T} : IsClosed S ↔ ∃ (a : α), S = hull T a := by
  simp only [← isOpen_compl_iff, isOpen_iff hT, compl_inj_iff]

/-- For a subset `S` of `T`, `kernel S` is the infimum of `S` (considered as a set of `α`) -/
/-
**PrimitiveSpectrum.kernel** 是 Mathlib 中的一个缩写定义，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：kernel (S : Set T)
参数：S : Set T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a subset `S` of `T`, `kernel S` is the infimum of `S` (considered as a set o
f `α`)
-/
abbrev kernel (S : Set T) := sInf (Subtype.val '' S)

open OrderDual in
/-- The pair of maps `kernel` and `hull` form an antitone Galois connection between the
subsets of `T` and `α`. -/
/-
**PrimitiveSpectrum.gc** 是 Mathlib 中的一个定理，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：gc : GaloisConnection (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The pair of maps `kernel` and `hull` form an antitone Galois connection between 
the
subsets of `T` and `α`.
-/
theorem gc : GaloisConnection (α := Set T) (β := αᵒᵈ)
    (fun S => toDual (kernel S)) (fun a => hull T (ofDual a)) := fun S a => by
  simp [Set.subset_def]
/-
**PrimitiveSpectrum.gc_closureOperator** 是 Mathlib 中的一个引理，位于命名空间 `PrimitiveSpect
rum`。
形式化陈述：gc_closureOperator (S : Set T) : gc.closureOperator S = hull T (kernel S)
参数：S : Set T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimitiveSpectrum.gc`：gc : GaloisConnection (α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaloisConnection.closureOperator_apply`：∀ {α : Type u_1} {β : Type u_4} 
[inst : PartialOrder α] [inst_1 : Preorder β] {l : α → β} {u : β → α}   (gc : Ga
loisConnection l u) (x : α),…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `OrderDual.toDual_symm_eq`：∀ {α : Type u_1}, OrderDual.toDual.symm = Orde
rDual.ofDual
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Set.preimage_id_eq`：preimage_id_eq : preimage (id : α -> α) = id
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
-/
lemma gc_closureOperator (S : Set T) : gc.closureOperator S = hull T (kernel S) := by
  simp only [toDual_sInf, GaloisConnection.closureOperator_apply, ofDual_sSup]
  rw [← preimage_comp, ← OrderDual.toDual_symm_eq, Equiv.symm_comp_self, preimage_id_eq, id_eq]

variable (T)

/-- `T` order generates `α` if, for every `a` in `α`, there exists a subset of `T` such that `a` is
the `kernel` of `S`. -/
/-
**PrimitiveSpectrum.OrderGenerates** 是 Mathlib 中的一个定义，位于命名空间 `PrimitiveSpectrum`
。
形式化陈述：OrderGenerates
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`T` order generates `α` if, for every `a` in `α`, there exists a subset of `T` s
uch that `a` is
the `kernel` of `S`.
-/
def OrderGenerates := ∀ (a : α), ∃ (S : Set T), a = kernel S

variable {T}

set_option backward.isDefEq.respectTransparency false in
/--
When `T` is order generating, the `kernel` and the `hull` form a Galois insertion
-/
/-
**PrimitiveSpectrum.gi** 是 Mathlib 中的一个定义，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：gi (hG : OrderGenerates T) : GaloisInsertion (α
参数：hG : OrderGenerates T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimitiveSpectrum.gc`：gc : GaloisConnection (α

--- 原说明 ---
When `T` is order generating, the `kernel` and the `hull` form a Galois insertio
n
-/
def gi (hG : OrderGenerates T) : GaloisInsertion (α := Set T) (β := αᵒᵈ)
    (OrderDual.toDual ∘ kernel)
    (hull T ∘ OrderDual.ofDual) :=
  gc.toGaloisInsertion fun a ↦ by
    obtain ⟨S, rfl⟩ := hG a
    rw [OrderDual.le_toDual, kernel, kernel]
    exact sInf_le_sInf <| image_val_mono fun c hcS => by
      rw [hull, mem_preimage, mem_Ici]
      exact sInf_le (mem_image_of_mem Subtype.val hcS)
/-
**PrimitiveSpectrum.kernel_hull** 是 Mathlib 中的一个引理，位于命名空间 `PrimitiveSpectrum`。
形式化陈述：kernel_hull (hG : OrderGenerates T) (a : α) : kernel (hull T a) = a
参数：hG : OrderGenerates T；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderDual.ofDual_toDual`：∀ {α : Type u_1} (a : α), OrderDual.ofDual (Ord
erDual.toDual a) = a
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
lemma kernel_hull (hG : OrderGenerates T) (a : α) : kernel (hull T a) = a := by
  conv_rhs => rw [← OrderDual.ofDual_toDual a, ← (gi hG).l_u_eq a]
  rfl
/-
**PrimitiveSpectrum.hull_kernel_of_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Primitive
Spectrum`。
形式化陈述：hull_kernel_of_isClosed [TopologicalSpace α] [IsLower α] (hT : forall p in
 T, InfPrime p) (hG : OrderGenerates T) {C : Set T} (h : IsClosed C) : hull T (k
ernel C) = C
参数：hT : forall p in T, InfPrime p；hG : OrderGenerates T；h : IsClosed C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `PrimitiveSpectrum.isClosed_iff`：isClosed_iff [TopologicalSpace α] [IsLow
er α] (hT : forall p in T, InfPrime p) {S : Set T} : IsClosed S ↔ exists (a : α)
, S = hull T a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PrimitiveSpectrum.kernel_hull`：kernel_hull (hG : OrderGenerates T) (a : 
α) : kernel (hull T a) = a
-/
lemma hull_kernel_of_isClosed [TopologicalSpace α] [IsLower α]
    (hT : ∀ p ∈ T, InfPrime p) (hG : OrderGenerates T) {C : Set T} (h : IsClosed C) :
    hull T (kernel C) = C := by
  obtain ⟨a, ha⟩ := (isClosed_iff hT).mp h
  rw [ha, kernel_hull hG]
/-
**PrimitiveSpectrum.closedsGC_closureOperator** 是 Mathlib 中的一个引理，位于命名空间 `Primiti
veSpectrum`。
形式化陈述：closedsGC_closureOperator [TopologicalSpace α] [IsLower α] (hT : forall p 
in T, InfPrime p) (hG : OrderGenerates T) (S : Set T) : (TopologicalSpace.Closed
s.gc (α
参数：hT : forall p in T, InfPrime p；hG : OrderGenerates T；S : Set T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Closeds.gc`：gc : GaloisConnection Closeds.closure ((↑) 
: Closeds α -> Set α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaloisConnection.closureOperator_apply`：∀ {α : Type u_1} {β : Type u_4} 
[inst : PartialOrder α] [inst_1 : Preorder β] {l : α → β} {u : β → α}   (gc : Ga
loisConnection l u) (x : α),…
· 使用定理 `TopologicalSpace.Closeds.coe_closure`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (s : Set α), ↑(TopologicalSpace.Closeds.closure s) = closure s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PrimitiveSpectrum.isClosed_iff`：isClosed_iff [TopologicalSpace α] [IsLow
er α] (hT : forall p in T, InfPrime p) {S : Set T} : IsClosed S ↔ exists (a : α)
, S = hull T a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimitiveSpectrum.hull_kernel_of_isClosed`：hull_kernel_of_isClosed [Topo
logicalSpace α] [IsLower α] (hT : forall p in T, InfPrime p) (hG : OrderGenerate
s T) {C : Set T} (h : IsClosed …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PrimitiveSpectrum.gc`：gc : GaloisConnection (α
· 使用引理 `PrimitiveSpectrum.gc_closureOperator`：gc_closureOperator (S : Set T) : g
c.closureOperator S = hull T (kernel S)
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma closedsGC_closureOperator [TopologicalSpace α] [IsLower α]
    (hT : ∀ p ∈ T, InfPrime p) (hG : OrderGenerates T) (S : Set T) :
    (TopologicalSpace.Closeds.gc (α := T)).closureOperator S = hull T (kernel S) := by
  simp only [GaloisConnection.closureOperator_apply, Closeds.coe_closure, closure, le_antisymm_iff]
  constructor
  · exact fun ⦃a⦄ a ↦ a (hull T (kernel S)) ⟨(isClosed_iff hT).mpr ⟨kernel S, rfl⟩,
      image_subset_iff.mp (fun _ hbS => sInf_le hbS)⟩
  · simp_rw [subset_sInter_iff]
    intro R hR
    rw [← (hull_kernel_of_isClosed hT hG hR.1), ← gc_closureOperator]
    exact ClosureOperator.monotone _ hR.2

end PrimitiveSpectrum

