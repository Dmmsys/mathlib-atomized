/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Disjointed
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sets.OpenCover

/-!
# Disjoint covers of profinite spaces

We prove various results about covering profinite spaces by disjoint clopens, including

* `TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`: any open cover of a
  profinite space can be refined to a finite cover by pairwise disjoint nonempty clopens.

* `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal`: if `f : X → V` is continuous
  with `X` profinite, and `S` is a neighbourhood of the diagonal in `V × V`, then `f` can be
  `S`-approximated by a function factoring through `Fin n` for some `n`.
-/

public section

open Set TopologicalSpace

open scoped Function Finset Topology

namespace TopologicalSpace.IsOpenCover

variable {ι X : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X] {U : ι → Opens X}

/-- Any open cover of a profinite space can be refined to a finite cover by clopens. -/
/-
**TopologicalSpace.IsOpenCover.exists_finite_clopen_cover** 是 Mathlib 中的一个引理，位于命
名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：exists_finite_clopen_cover (hU : IsOpenCover U) : exists (n : Nat) (V : Fi
n n -> Clopens X), (forall j, exists i, (V j : Set X) subseteq U i) ∧ univ subse
teq ⋃ j, (V j : Set X)
参数：hU : IsOpenCover U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `TopologicalSpace.Clopens.mk.congr_simp`：∀ {α : Type u_4} [inst : Topolog
icalSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is
Clopen' : IsClopen carrier),…
· 使用定理 `compact_exists_isClopen_in_isOpen`：compact_exists_isClopen_in_isOpen {x 
: X} {U : Set X} (is_open : IsOpen U) (memU : x in U) : exists V : Set X, IsClop
en V ∧ x in V ∧ V subse…
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `TopologicalSpace.IsOpenCover.exists_mem`：exists_mem (hu : IsOpenCover u)
 (a : X) : exists i, a in u i

--- 原说明 ---
Any open cover of a profinite space can be refined to a finite cover by clopens.
-/
lemma exists_finite_clopen_cover (hU : IsOpenCover U) : ∃ (n : ℕ) (V : Fin n → Clopens X),
    (∀ j, ∃ i, (V j : Set X) ⊆ U i) ∧ univ ⊆ ⋃ j, (V j : Set X) := by
  -- Choose an index `r x` for each point in `X` such that `∀ x, x ∈ U (r x)`.
  choose r hr using hU.exists_mem
  -- Choose a clopen neighbourhood `V x` of each `x` contained in `U (r x)`.
  choose V hV hVx hVU using fun x ↦ compact_exists_isClopen_in_isOpen (U _).isOpen (hr x)
  -- Apply compactness to extract a finite subset of the `V`s which covers `X`.
  obtain ⟨t, ht⟩ : ∃ t, univ ⊆ ⋃ i ∈ t, V i :=
    isCompact_univ.elim_finite_subcover V (fun x ↦ (hV x).2) (fun x _ ↦ mem_iUnion.mpr ⟨x, hVx x⟩)
  -- Biject it noncanonically with `Fin n` for some `n`.
  refine ⟨_, fun j ↦ ⟨_, hV (t.equivFin.symm j)⟩, fun j ↦ ⟨_, hVU _⟩, fun x hx ↦ ?_⟩
  obtain ⟨m, hm, hm'⟩ := mem_iUnion₂.mp (ht hx)
  exact Set.mem_iUnion_of_mem (t.equivFin ⟨m, hm⟩) (by simpa)

/-- Any open cover of a profinite space can be refined to a finite cover by pairwise disjoint
nonempty clopens. -/
/-
**TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover** 是 
Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.IsOpenCover`。
形式化陈述：exists_finite_nonempty_disjoint_clopen_cover (hU : IsOpenCover U) : exists
 (n : Nat) (W : Fin n -> Clopens X), (forall j, W j != ⊥ ∧ exists i, (W j : Set 
X) subseteq U i) ∧ (univ : Set X) subseteq ⋃ j, ↑(W j) ∧ Pairwise (Disjoint on W
)
参数：hU : IsOpenCover U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.IsOpenCover.exists_finite_clopen_cover`：exists_finite_c
lopen_cover (hU : IsOpenCover U) : exists (n : Nat) (V : Fin n -> Clopens X), (f
orall j, exists i, (V j : Set X) subseteq U i…
· 使用引理 `Fintype.exists_disjointed_le`：Fintype.exists_disjointed_le {ι : Type*} [
Fintype ι] (f : ι -> α) : exists g, g <= f ∧ univ.sup g = univ.sup f ∧ Pairwise 
(Disjoint on g)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TopologicalSpace.Clopens.coe_finset_sup`：coe_finset_sup (s : Finset ι) (
U : ι -> Clopens α) : (↑(s.sup U) : Set α) = ⋃ i in s, U i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `Pairwise.comp_of_injective`：Pairwise.comp_of_injective (hr : Pairwise r)
 {f : β -> α} (hf : Injective f) : Pairwise (r on f)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Any open cover of a profinite space can be refined to a finite cover by pairwise
 disjoint
nonempty clopens.
-/
lemma exists_finite_nonempty_disjoint_clopen_cover (hU : IsOpenCover U) :
    ∃ (n : ℕ) (W : Fin n → Clopens X), (∀ j, W j ≠ ⊥ ∧ ∃ i, (W j : Set X) ⊆ U i)
    ∧ (univ : Set X) ⊆ ⋃ j, ↑(W j) ∧ Pairwise (Disjoint on W) := by
  classical
  obtain ⟨n, V, hVle, hVun⟩ := hU.exists_finite_clopen_cover
  obtain ⟨W, hWle, hWun, hWd⟩ := Fintype.exists_disjointed_le V
  simp only [← SetLike.coe_set_eq, Clopens.coe_finset_sup, Finset.mem_univ, iUnion_true] at hWun
  let t : Finset (Fin n) := {j | W j ≠ ⊥}
  refine ⟨#t, fun k ↦ W (t.equivFin.symm k), fun k ↦ ⟨?_, ?_⟩, fun x hx ↦ ?_, ?_⟩
  · exact (Finset.mem_filter.mp (t.equivFin.symm k).2).2
  · exact match hVle (t.equivFin.symm k) with | ⟨i, hi⟩ => ⟨i, subset_trans (hWle _) hi⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp <| (hWun ▸ hVun) hx
    have : W j ≠ ⊥ := by simpa [← SetLike.coe_ne_coe, ← Set.nonempty_iff_ne_empty] using ⟨x, hj⟩
    exact mem_iUnion.mpr ⟨t.equivFin ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩⟩, by simpa⟩
  · exact hWd.comp_of_injective <| Subtype.val_injective.comp t.equivFin.symm.injective

end TopologicalSpace.IsOpenCover

namespace TopologicalSpace
variable {X : Type*} [TopologicalSpace X] {S : Set (X × X)}

/-- If `S` is any neighbourhood of the diagonal in a topological space `X`, any point of `X` has an
open neighbourhood `U` such that `U ×ˢ U ⊆ S`. -/
/-
**TopologicalSpace.exists_open_prod_subset_of_mem_nhds_diagonal** 是 Mathlib 中的一个
引理，位于命名空间 `TopologicalSpace`。
形式化陈述：exists_open_prod_subset_of_mem_nhds_diagonal (hS : S in nhdsSet (diagonal 
X)) (x : X) : exists U : Set X, IsOpen U ∧ x in U ∧ U ×ˢ U subseteq S
参数：hS : S in nhdsSet (diagonal X)；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_prod_iff'`：mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)}
 : s in 𝓝 (x, y) ↔ exists u v, IsOpen u ∧ x in u ∧ IsOpen v ∧ y in v ∧ u ×ˢ v su
bseteq s
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `S` is any neighbourhood of the diagonal in a topological space `X`, any poin
t of `X` has an
open neighbourhood `U` such that `U ×ˢ U ⊆ S`.
-/
lemma exists_open_prod_subset_of_mem_nhds_diagonal (hS : S ∈ nhdsSet (diagonal X)) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ S := by
  have : S ∈ 𝓝 (x, x) := mem_nhdsSet_iff_forall.mp hS _ rfl
  obtain ⟨u, v, huo, hux, hvo, hvx, H⟩ := by rwa [mem_nhds_prod_iff'] at this
  exact ⟨_, huo.inter hvo, ⟨hux, hvx⟩, fun p hp ↦ H ⟨hp.1.1, hp.2.2⟩⟩

variable [CompactSpace X]

/-- If `S` is any neighbourhood of the diagonal in a compact topological space `X`, then there
exists a finite cover of `X` by opens `U i` such that `U i ×ˢ U i ⊆ S` for all `i`.

That the indexing set is a finset of `X` is an artifact of the proof; it could be any finite type.
-/
/-
**TopologicalSpace.exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_
compact** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace`。
形式化陈述：exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact (hS :
 S in nhdsSet (diagonal X)) : exists (t : Finset X) (U : t -> Opens X), IsOpenCo
ver U ∧ forall i, (U i : Set X) ×ˢ U i subseteq S
参数：hS : S in nhdsSet (diagonal X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `TopologicalSpace.IsOpenCover.of_sets`：of_sets {v : ι -> Set X} (h_open :
 forall i, IsOpen (v i)) (h_iUnion : ⋃ i, v i = univ) : IsOpenCover (fun i => ⟨v
 i, h_open i⟩)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `TopologicalSpace.exists_open_prod_subset_of_mem_nhds_diagonal`：exists_op
en_prod_subset_of_mem_nhds_diagonal (hS : S in nhdsSet (diagonal X)) (x : X) : e
xists U : Set X, IsOpen U ∧ x in U ∧ U ×ˢ U subsete…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `S` is any neighbourhood of the diagonal in a compact topological space `X`, 
then there
exists a finite cover of `X` by opens `U i` such that `U i ×ˢ U i ⊆ S` for all `
i`.

That the indexing set is a finset of `X` is an artifact of the proof; it could b
e any finite type.
-/
lemma exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact
    (hS : S ∈ nhdsSet (diagonal X)) :
    ∃ (t : Finset X) (U : t → Opens X), IsOpenCover U ∧ ∀ i, (U i : Set X) ×ˢ U i ⊆ S := by
  choose U hUo hUx hUp using exists_open_prod_subset_of_mem_nhds_diagonal hS
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hUo (fun x _ ↦ mem_iUnion.mpr ⟨_, hUx x⟩)
  refine ⟨t, fun i ↦ ⟨_, hUo i⟩, .of_sets _ ?_, (hUp ·)⟩
  simpa [iUnion_subtype, ← univ_subset_iff] using ht

variable [TotallyDisconnectedSpace X] [T2Space X]

/-- If `S` is any neighbourhood of the diagonal in a profinite topological space `X`, then there
exists a finite cover of `X` by disjoint nonempty clopens `U i` with `U i ×ˢ U i ⊆ S` for all `i`.
-/
/-
**TopologicalSpace.exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diag
onal_of_profinite** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is any neighbourhood of the diagonal in a profinite topological space `X`
, then there
exists a finite cover of `X` by disjoint nonempty clopens `U i` with `U i ×ˢ U i
 ⊆ S` for all `i`.
-/
private lemma exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite
    (hS : S ∈ nhdsSet (diagonal X)) :
    ∃ (n : ℕ) (D : Fin n → Clopens X), (∀ i, D i ≠ ⊥) ∧ (∀ i, ∀ y ∈ D i, ∀ z ∈ D i, (y, z) ∈ S)
    ∧ (univ : Set X) ⊆ ⋃ i, D i ∧ Pairwise (Disjoint on D) := by
  obtain ⟨t, U, hUc, hUS⟩ := exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact hS
  -- Now refine it to a disjoint covering.
  obtain ⟨n, W, hW₁, hW₂, hW₃⟩ := hUc.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, fun j ↦ (hW₁ j).1, fun j y hy z hz ↦ ?_, hW₂, hW₃⟩
  exact match (hW₁ j).2 with | ⟨i, hi⟩ => hUS i ⟨hi hy, hi hz⟩

end TopologicalSpace

namespace ContinuousMap

variable {X V : Type*} [TopologicalSpace X] [TopologicalSpace V] [TotallyDisconnectedSpace X]
  [T2Space X] [CompactSpace X] {S : Set (V × V)} (f : C(X, V))

/--
For any continuous function `f : X → V`, with `X` profinite, and `S` a neighbourhood of the
diagonal in `V × V`, there exists a finite cover of `X` by pairwise-disjoint nonempty clopens, on
each of which `f` varies within `S`.
-/
/-
**ContinuousMap.exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal** 是 M
athlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal (hS : S in nhds
Set (diagonal V)) : exists (n : Nat) (D : Fin n -> Clopens X), (forall i, D i !=
 ⊥) ∧ (forall i, forall y in D i, forall z in D i, (f y, f z) in S) ∧ (univ : Se
t X) subseteq ⋃ i, D i ∧ Pairwise (Disjoint on D)
参数：hS : S in nhdsSet (diagonal V)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhdsSet_iff_forall`：mem_nhdsSet_iff_forall : s in 𝓝ˢ t ↔ forall x : 
X, x in t -> s in 𝓝 x
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `_private.Mathlib.Topology.Separation.DisjointCover.0.TopologicalSpace.ex
ists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite`：∀ 
{X : Type u_1} [inst : TopologicalSpace X] {S : Set (X × X)} [CompactSpace X] [T
otallyDisconnectedSpace X]   [T2Space X],   S ∈ nhdsSet (S…

--- 原说明 ---
For any continuous function `f : X → V`, with `X` profinite, and `S` a neighbour
hood of the
diagonal in `V × V`, there exists a finite cover of `X` by pairwise-disjoint non
empty clopens, on
each of which `f` varies within `S`.
-/
lemma exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal (hS : S ∈ nhdsSet (diagonal V)) :
    ∃ (n : ℕ) (D : Fin n → Clopens X), (∀ i, D i ≠ ⊥) ∧ (∀ i, ∀ y ∈ D i, ∀ z ∈ D i, (f y, f z) ∈ S)
    ∧ (univ : Set X) ⊆ ⋃ i, D i ∧ Pairwise (Disjoint on D) := by
  have : (f.prodMap f) ⁻¹' S ∈ nhdsSet (diagonal X) := by
    rw [mem_nhdsSet_iff_forall] at hS ⊢
    rintro ⟨x, y⟩ (rfl : x = y)
    exact (map_continuous _).continuousAt.preimage_mem_nhds (hS _ rfl)
  exact exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite this

/--
For any continuous function `f : X → V`, with `X` profinite, and `S` a neighbourhood of the
diagonal in `V × V`, the function `f` can be `S`-approximated by a function factoring through
`Fin n`, for some `n`. -/
/-
**ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal** 是 Mathlib 中的一
个引理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_finite_approximation_of_mem_nhds_diagonal (hS : S in nhdsSet (diago
nal V)) : exists (n : Nat) (g : X -> Fin n) (h : Fin n -> V), Continuous g ∧ for
all x, (f x, h (g x)) in S
参数：hS : S in nhdsSet (diagonal V)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMap.exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal
`：exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal (hS : S in nhdsSet 
(diagonal V)) : exists (n : Nat) (D : Fin n -> Clopens X), (fo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {a b : α}, Pairwise r →
 ¬r a b → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_discrete_rng`：continuous_discrete_rng {α} [TopologicalSpace α
] [TopologicalSpace β] [DiscreteTopology β] {f : α -> β} : Continuous f ↔ forall
 b : β, IsOpe…
· 使用定理 `instDiscreteTopologyFin`：∀ {n : ℕ}, DiscreteTopology (Fin n)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `TopologicalSpace.Clopens.isOpen`：isOpen (s : Clopens α) : IsOpen (s : Se
t α)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
For any continuous function `f : X → V`, with `X` profinite, and `S` a neighbour
hood of the
diagonal in `V × V`, the function `f` can be `S`-approximated by a function fact
oring through
`Fin n`, for some `n`.
-/
lemma exists_finite_approximation_of_mem_nhds_diagonal (hS : S ∈ nhdsSet (diagonal V)) :
    ∃ (n : ℕ) (g : X → Fin n) (h : Fin n → V), Continuous g ∧ ∀ x, (f x, h (g x)) ∈ S := by
  obtain ⟨n, E, hEne, hES, hEuniv, hEdis⟩ :=
    exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal f hS
  have h_uniq (x) : ∃! i, x ∈ E i := by
    refine match mem_iUnion.mp (hEuniv <| mem_univ x) with
      | ⟨i, hi⟩ => ⟨i, hi, fun j hj ↦ hEdis.eq ?_⟩
    simpa [← Clopens.coe_disjoint, not_disjoint_iff] using! ⟨x, hj, hi⟩
  choose g hg hg' using h_uniq -- for each `x`, `g x` is the unique `i` such that `x ∈ E i`
  have h_ex (i) : ∃ x, x ∈ E i := by
    simpa [← SetLike.coe_set_eq, ← nonempty_iff_ne_empty] using! hEne i
  choose r hr using h_ex -- for each `i`, choose an `r i ∈ E i`
  refine ⟨n, g, f ∘ r, continuous_discrete_rng.mpr fun j ↦ ?_, fun x ↦ (hES _) _ (hg _) _ (hr _)⟩
  convert! (E j).isOpen
  exact Set.ext fun x ↦ ⟨fun hj ↦ hj ▸ hg x, fun hx ↦ (hg' _ _ hx).symm⟩

/--
If `f` is a continuous map from a profinite space to a topological space with a commutative monoid
structure, then we can approximate `f` by finite products of indicator functions of clopen sets.

(Note no compatibility is assumed between the monoid structure on `V` and the topology.)
-/
@[to_additive /-- If `f` is a continuous map from a profinite space to a topological space with a
commutative additive monoid structure, then we can approximate `f` by finite sums of indicator
functions of clopen sets.

(Note no compatibility is assumed between the monoid structure on `V` and the topology.) -/]
/-
**ContinuousMap.exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_d
iagonal** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal [C
ommMonoid V] (hS : S in nhdsSet (diagonal V)) : exists (n : Nat) (U : Fin n -> C
lopens X) (v : Fin n -> V), forall x, (f x, ∏ n, mulIndicator (U n) (fun _ => v 
n) x) in S
参数：hS : S in nhdsSet (diagonal V)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal`：exists_f
inite_approximation_of_mem_nhds_diagonal (hS : S in nhdsSet (diagonal V)) : exis
ts (n : Nat) (g : X -> Fin n) (h : Fin n -> V), Cont…
· 使用定理 `IsClopen.preimage`：IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X
 -> Y} (hf : Continuous f) : IsClopen (f ⁻¹' s)
· 使用定理 `isClopen_discrete`：isClopen_discrete [DiscreteTopology X] (s : Set X) : 
IsClopen s
· 使用定理 `instDiscreteTopologyFin`：∀ {n : ℕ}, DiscreteTopology (Fin n)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.prod_eq_single`：prod_eq_single {f : α -> M} (a : α) (h : forall 
x != a, f x = 1) : ∏ x, f x = f a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
-/
lemma exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal [CommMonoid V]
    (hS : S ∈ nhdsSet (diagonal V)) :
    ∃ (n : ℕ) (U : Fin n → Clopens X) (v : Fin n → V),
    ∀ x, (f x, ∏ n, mulIndicator (U n) (fun _ ↦ v n) x) ∈ S := by
  obtain ⟨n, g, h, hg, hgh⟩ := exists_finite_approximation_of_mem_nhds_diagonal f hS
  refine ⟨n, fun i ↦ ⟨_, (isClopen_discrete {i}).preimage hg⟩, h, fun x ↦ ?_⟩
  convert! hgh x
  exact (Fintype.prod_eq_single _ fun i hi ↦ mulIndicator_of_notMem hi.symm _).trans
    (mulIndicator_of_mem rfl _)

end ContinuousMap

