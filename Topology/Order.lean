/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Induced

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion.  That is, for topologies `t₁` and
`t₂` on `α`, we write `t₁ ≤ t₂` if every set open in `t₂` is also open in `t₁`.  (One also calls
`t₁` *finer* than `t₂`, and `t₂` *coarser* than `t₁`.)

Any function `f : α → β` induces

* `TopologicalSpace.induced f : TopologicalSpace β → TopologicalSpace α`;
* `TopologicalSpace.coinduced f : TopologicalSpace α → TopologicalSpace β`.

Continuity, the ordering on topologies and (co)induced topologies are related as follows:

* The identity map `(α, t₁) → (α, t₂)` is continuous iff `t₁ ≤ t₂`.
* A map `f : (α, t) → (β, u)` is continuous
  * iff `t ≤ TopologicalSpace.induced f u` (`continuous_iff_le_induced`)
  * iff `TopologicalSpace.coinduced f t ≤ u` (`continuous_iff_coinduced_le`).

Topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the indiscrete
topology.

For a function `f : α → β`, `(TopologicalSpace.coinduced f, TopologicalSpace.induced f)` is a Galois
connection between topologies on `α` and topologies on `β`.

## Implementation notes

There is a Galois insertion between topologies on `α` (with the inclusion ordering) and all
collections of sets in `α`. The complete lattice structure on topologies on `α` is defined as the
reverse of the one obtained via this Galois insertion. More precisely, we use the corresponding
Galois coinsertion between topologies on `α` (with the reversed inclusion ordering) and collections
of sets in `α` (with the reversed inclusion ordering).

## Tags

finer, coarser, induced topology, coinduced topology
-/

@[expose] public section

open Function Set Filter Topology

universe u v w

namespace TopologicalSpace

variable {α : Type u}

/-- The open sets of the least topology containing a collection of basic sets. -/
/-
**TopologicalSpace.GenerateOpen** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpace`。
形式化陈述：{α : Type u} → Set (Set α) → Set α → Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open sets of the least topology containing a collection of basic sets.
-/
inductive GenerateOpen (g : Set (Set α)) : Set α → Prop
  | basic : ∀ s ∈ g, GenerateOpen g s
  | univ : GenerateOpen g univ
  | inter : ∀ s t, GenerateOpen g s → GenerateOpen g t → GenerateOpen g (s ∩ t)
  | sUnion : ∀ S : Set (Set α), (∀ s ∈ S, GenerateOpen g s) → GenerateOpen g (⋃₀ S)

/-- The smallest topological space containing the collection `g` of basic sets -/
@[instance_reducible]
/-
**TopologicalSpace.generateFrom** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：generateFrom (g : Set (Set α)) : TopologicalSpace α where IsOpen
参数：g : Set (Set α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest topological space containing the collection `g` of basic sets
-/
def generateFrom (g : Set (Set α)) : TopologicalSpace α where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion
/-
**TopologicalSpace.isOpen_generateFrom_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace`。
形式化陈述：isOpen_generateFrom_of_mem {g : Set (Set α)} {s : Set α} (hs : s in g) : I
sOpen[generateFrom g] s
参数：Set α；hs : s in g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isOpen_generateFrom_of_mem {g : Set (Set α)} {s : Set α} (hs : s ∈ g) :
    IsOpen[generateFrom g] s :=
  GenerateOpen.basic s hs
/-
**TopologicalSpace.nhds_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
`。
形式化陈述：nhds_generateFrom {g : Set (Set α)} {a : α} : @nhds α (generateFrom g) a =
 ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_def`：∀ {X : Type u_3} [inst : TopologicalSpace X] (x : X), nhds x =
 ⨅ s ∈ {s | x ∈ s ∧ IsOpen s}, Filter.principal s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `biInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α} {p q : ι → Prop},   (∀ (i : ι), p i → q i) → ⨅ i, ⨅ (_ : q i), f i ≤ 
…
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem nhds_generateFrom {g : Set (Set α)} {a : α} :
    @nhds α (generateFrom g) a = ⨅ s ∈ { s | a ∈ s ∧ s ∈ g }, 𝓟 s := by
  let := generateFrom g
  rw [nhds_def]
  refine le_antisymm (biInf_mono fun s ⟨as, sg⟩ => ⟨as, .basic _ sg⟩) <| le_iInf₂ ?_
  rintro s ⟨ha, hs⟩
  induction hs with
  | basic _ hs => exact iInf₂_le _ ⟨ha, hs⟩
  | univ => exact le_top.trans_eq principal_univ.symm
  | inter _ _ _ _ hs ht => exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal
  | sUnion _ _ hS =>
    let ⟨t, htS, hat⟩ := ha
    exact (hS t htS hat).trans (principal_mono.2 <| subset_sUnion_of_mem htS)
/-
**TopologicalSpace.tendsto_nhds_generateFrom_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topo
logicalSpace`。
形式化陈述：tendsto_nhds_generateFrom_iff {β : Type*} {m : α -> β} {f : Filter α} {g :
 Set (Set β)} {b : β} : Tendsto m f (@nhds β (generateFrom g) b) ↔ forall s in g
, b in s -> m ⁻¹' s in f
参数：Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma tendsto_nhds_generateFrom_iff {β : Type*} {m : α → β} {f : Filter α} {g : Set (Set β)}
    {b : β} : Tendsto m f (@nhds β (generateFrom g) b) ↔ ∀ s ∈ g, b ∈ s → m ⁻¹' s ∈ f := by
  simp only [nhds_generateFrom, @forall_comm (b ∈ _), tendsto_iInf, mem_ofPred_eq, and_imp,
    tendsto_principal]; rfl

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
@[instance_reducible]
/-
**TopologicalSpace.mkOfNhds** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：{α : Type u} → (α → Filter α) → TopologicalSpace α
参数：α → Filter α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a topology on α given the filter of neighborhoods of each point of α.
-/
protected def mkOfNhds (n : α → Filter α) : TopologicalSpace α where
  IsOpen s := ∀ a ∈ s, s ∈ n a
  isOpen_univ _ _ := univ_mem
  isOpen_inter := fun _s _t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  isOpen_sUnion := fun _s hs _a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (subset_sUnion_of_mem hx)
/-
**TopologicalSpace.nhds_mkOfNhds_of_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace`。
形式化陈述：nhds_mkOfNhds_of_hasBasis {n : α -> Filter α} {ι : α -> Sort*} {p : forall
 a, ι a -> Prop} {s : forall a, ι a -> Set α} (hb : forall a, (n a).HasBasis (p 
a) (s a)) (hpure : forall a i, p a i -> a in s a i) (hopen : forall a i, p a i -
> forallᶠ x in n a, s a i in n x) (a : α) : @nhds α (.mkOfNhds n) a = n a
参数：hb : forall a, (n a).HasBasis (p a) (s a)；hpure : forall a i, p a i -> a in s
 a i；hopen : forall a i, p a i -> forallᶠ x in n a, s a i in n x；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
-/
theorem nhds_mkOfNhds_of_hasBasis {n : α → Filter α} {ι : α → Sort*} {p : ∀ a, ι a → Prop}
    {s : ∀ a, ι a → Set α} (hb : ∀ a, (n a).HasBasis (p a) (s a))
    (hpure : ∀ a i, p a i → a ∈ s a i) (hopen : ∀ a i, p a i → ∀ᶠ x in n a, s a i ∈ n x) (a : α) :
    @nhds α (.mkOfNhds n) a = n a := by
  let t : TopologicalSpace α := .mkOfNhds n
  apply le_antisymm
  · intro U hU
    replace hpure : pure ≤ n := fun x ↦ (hb x).ge_iff.2 (hpure x)
    refine mem_nhds_iff.2 ⟨{x | U ∈ n x}, fun x hx ↦ hpure x hx, fun x hx ↦ ?_, hU⟩
    rcases (hb x).mem_iff.1 hx with ⟨i, hpi, hi⟩
    exact (hopen x i hpi).mono fun y ↦ by gcongr
  · exact (nhds_basis_opens a).ge_iff.2 fun U ⟨haU, hUo⟩ ↦ hUo a haU
/-
**TopologicalSpace.nhds_mkOfNhds** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace`。
形式化陈述：nhds_mkOfNhds (n : α -> Filter α) (a : α) (h₀ : pure <= n) (h₁ : forall a,
 forall s in n a, forallᶠ y in n a, s in n y) : @nhds α (TopologicalSpace.mkOfNh
ds n) a = n a
参数：n : α -> Filter α；a : α；h₀ : pure <= n；h₁ : forall a, forall s in n a, forall
ᶠ y in n a, s in n y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.nhds_mkOfNhds_of_hasBasis`：nhds_mkOfNhds_of_hasBasis {n
 : α -> Filter α} {ι : α -> Sort*} {p : forall a, ι a -> Prop} {s : forall a, ι 
a -> Set α} (hb : forall a, (n a…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem nhds_mkOfNhds (n : α → Filter α) (a : α) (h₀ : pure ≤ n)
    (h₁ : ∀ a, ∀ s ∈ n a, ∀ᶠ y in n a, s ∈ n y) :
    @nhds α (TopologicalSpace.mkOfNhds n) a = n a :=
  nhds_mkOfNhds_of_hasBasis (fun a ↦ (n a).basis_sets) h₀ h₁ _
/-
**TopologicalSpace.nhds_mkOfNhds_single** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace`。
形式化陈述：nhds_mkOfNhds_single [DecidableEq α] {a₀ : α} {l : Filter α} (h : pure a₀ 
<= l) (b : α) : @nhds α (TopologicalSpace.mkOfNhds (update pure a₀ l)) b = (upda
te pure a₀ l : α -> Filter α) b
参数：h : pure a₀ <= l；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.nhds_mkOfNhds`：nhds_mkOfNhds (n : α -> Filter α) (a : α
) (h₀ : pure <= n) (h₁ : forall a, forall s in n a, forallᶠ y in n a, s in n y) 
: @nhds α (Topologic…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_update_iff`：le_update_iff : x <= Function.update y i a ↔ x i <= a ∧ f
orall (j) (_ : j != i), x j <= y j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem nhds_mkOfNhds_single [DecidableEq α] {a₀ : α} {l : Filter α} (h : pure a₀ ≤ l) (b : α) :
    @nhds α (TopologicalSpace.mkOfNhds (update pure a₀ l)) b =
      (update pure a₀ l : α → Filter α) b := by
  refine nhds_mkOfNhds _ _ (le_update_iff.mpr ⟨h, fun _ _ => le_rfl⟩) fun a s hs => ?_
  rcases eq_or_ne a a₀ with (rfl | ha)
  · filter_upwards [hs] with b hb
    rcases eq_or_ne b a with (rfl | hb)
    · exact hs
    · rwa [update_of_ne hb]
  · simpa only [update_of_ne ha, mem_pure, eventually_pure] using hs
/-
**TopologicalSpace.nhds_mkOfNhds_filterBasis** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace`。
形式化陈述：nhds_mkOfNhds_filterBasis (B : α -> FilterBasis α) (a : α) (h₀ : forall x,
 forall n in B x, x in n) (h₁ : forall x, forall n in B x, exists n₁ in B x, for
all x' in n₁, exists n₂ in B x', n₂ subseteq n) : @nhds α (TopologicalSpace.mkOf
Nhds fun x => (B x).filter) a = (B a).filter
参数：B : α -> FilterBasis α；a : α；h₀ : forall x, forall n in B x, x in n；h₁ : fora
ll x, forall n in B x, exists n₁ in B x, forall x' in n₁, exists n₂ in B x', n₂ 
subseteq n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.nhds_mkOfNhds_of_hasBasis`：nhds_mkOfNhds_of_hasBasis {n
 : α -> Filter α} {ι : α -> Sort*} {p : forall a, ι a -> Prop} {s : forall a, ι 
a -> Set α} (hb : forall a, (n a…
· 使用定理 `FilterBasis.hasBasis`：∀ {α : Type u_1} (B : FilterBasis α), B.filter.Has
Basis (fun s => s ∈ B) id
-/
theorem nhds_mkOfNhds_filterBasis (B : α → FilterBasis α) (a : α) (h₀ : ∀ x, ∀ n ∈ B x, x ∈ n)
    (h₁ : ∀ x, ∀ n ∈ B x, ∃ n₁ ∈ B x, ∀ x' ∈ n₁, ∃ n₂ ∈ B x', n₂ ⊆ n) :
    @nhds α (TopologicalSpace.mkOfNhds fun x => (B x).filter) a = (B a).filter :=
  nhds_mkOfNhds_of_hasBasis (fun a ↦ (B a).hasBasis) h₀ h₁ a

section Lattice

variable {α : Type u} {β : Type v}

/-- The ordering on topologies on the type `α`. `t ≤ s` if every set open in `s` is also open in `t`
(`t` is finer than `s`). -/
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordering on topologies on the type `α`. `t ≤ s` if every set open in `s` is 
also open in `t`
(`t` is finer than `s`).
-/
instance : PartialOrder (TopologicalSpace α) :=
  { PartialOrder.lift (fun t => OrderDual.toDual IsOpen[t]) (fun _ _ => TopologicalSpace.ext) with
    le := fun s t => ∀ U, IsOpen[t] U → IsOpen[s] U }
/-
**TopologicalSpace.le_def** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace`。
形式化陈述：∀ {α : Type u_1} {t s : TopologicalSpace α}, t ≤ s ↔ IsOpen ≤ IsOpen
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem le_def {α} {t s : TopologicalSpace α} : t ≤ s ↔ IsOpen[s] ≤ IsOpen[t] :=
  Iff.rfl
/-
**TopologicalSpace.le_generateFrom_iff_subset_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace`。
形式化陈述：le_generateFrom_iff_subset_isOpen {g : Set (Set α)} {t : TopologicalSpace 
α} : t <= generateFrom g ↔ g subseteq { s | IsOpen[t] s }
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
-/
theorem le_generateFrom_iff_subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} :
    t ≤ generateFrom g ↔ g ⊆ { s | IsOpen[t] s } :=
  ⟨fun ht s hs => ht _ <| .basic s hs, fun hg _s hs =>
    hs.recOn (fun _ h => hg h) isOpen_univ (fun _ _ _ _ => IsOpen.inter) fun _ _ => isOpen_sUnion⟩

/-- If `s` equals the collection of open sets in the topology it generates, then `s` defines a
topology. -/
@[instance_reducible]
/-
**TopologicalSpace.mkOfClosure** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：{α : Type u} → (s : Set (Set α)) → {u | TopologicalSpace.GenerateOpen s u}
 = s → TopologicalSpace α
参数：s : Set (Set α)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` equals the collection of open sets in the topology it generates, then `s`
 defines a
topology.
-/
protected def mkOfClosure (s : Set (Set α)) (hs : { u | GenerateOpen s u } = s) :
    TopologicalSpace α where
  IsOpen u := u ∈ s
  isOpen_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  isOpen_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  isOpen_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion
/-
**TopologicalSpace.mkOfClosure_sets** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace`
。
形式化陈述：mkOfClosure_sets {s : Set (Set α)} {hs : {u | GenerateOpen s u} = s} : Top
ologicalSpace.mkOfClosure s hs = generateFrom s
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mkOfClosure_sets {s : Set (Set α)} {hs : {u | GenerateOpen s u} = s} :
    TopologicalSpace.mkOfClosure s hs = generateFrom s :=
  TopologicalSpace.ext (by ext U; exact Set.ext_iff.mp hs.symm U)
/-
**TopologicalSpace.gc_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace`。
形式化陈述：gc_generateFrom (α) : GaloisConnection (fun t : TopologicalSpace α => Orde
rDual.toDual { s | IsOpen[t] s }) (generateFrom ∘ OrderDual.ofDual)
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `TopologicalSpace.le_generateFrom_iff_subset_isOpen`：le_generateFrom_iff_
subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} : t <= generateFrom g ↔
 g subseteq { s | IsOpen[t] s }
-/
theorem gc_generateFrom (α) :
    GaloisConnection (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s })
      (generateFrom ∘ OrderDual.ofDual) := fun _ _ =>
  le_generateFrom_iff_subset_isOpen.symm

/-- The Galois coinsertion between `TopologicalSpace α` and `(Set (Set α))ᵒᵈ` whose lower part sends
  a topology to its collection of open subsets, and whose upper part sends a collection of subsets
  of `α` to the topology they generate. -/
/-
**TopologicalSpace.gciGenerateFrom** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace`。
形式化陈述：gciGenerateFrom (α : Type*) : GaloisCoinsertion (fun t : TopologicalSpace 
α => OrderDual.toDual { s | IsOpen[t] s }) (generateFrom ∘ OrderDual.ofDual) whe
re gc
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.gc_generateFrom`：gc_generateFrom (α) : GaloisConnection
 (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s }) (generateF
rom ∘ OrderDual.ofDual…

--- 原说明 ---
The Galois coinsertion between `TopologicalSpace α` and `(Set (Set α))ᵒᵈ` whose 
lower part sends
  a topology to its collection of open subsets, and whose upper part sends a col
lection of subsets
  of `α` to the topology they generate.
-/
def gciGenerateFrom (α : Type*) :
    GaloisCoinsertion (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s })
      (generateFrom ∘ OrderDual.ofDual) where
  gc := gc_generateFrom α
  u_l_le _ s hs := TopologicalSpace.GenerateOpen.basic s hs
  choice g hg := TopologicalSpace.mkOfClosure g
    (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection
.
-/
instance : CompleteLattice (TopologicalSpace α) := (gciGenerateFrom α).liftCompleteLattice

@[mono, gcongr]
/-
**TopologicalSpace.generateFrom_anti** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
`。
形式化陈述：generateFrom_anti {α} {g₁ g₂ : Set (Set α)} (h : g₁ subseteq g₂) : generat
eFrom g₂ <= generateFrom g₁
参数：Set α；h : g₁ subseteq g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `TopologicalSpace.gc_generateFrom`：gc_generateFrom (α) : GaloisConnection
 (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s }) (generateF
rom ∘ OrderDual.ofDual…
-/
theorem generateFrom_anti {α} {g₁ g₂ : Set (Set α)} (h : g₁ ⊆ g₂) :
    generateFrom g₂ ≤ generateFrom g₁ :=
  (gc_generateFrom _).monotone_u h
/-
**TopologicalSpace.generateFrom_setOfPred_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace`。
形式化陈述：generateFrom_setOfPred_isOpen (t : TopologicalSpace α) : generateFrom { s 
| IsOpen[t] s } = t
参数：t : TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
theorem generateFrom_setOfPred_isOpen (t : TopologicalSpace α) :
    generateFrom { s | IsOpen[t] s } = t :=
  (gciGenerateFrom α).u_l_eq t

@[deprecated (since := "2026-07-09")]
alias generateFrom_setOf_isOpen := generateFrom_setOfPred_isOpen
/-
**TopologicalSpace.leftInverse_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `Topologic
alSpace`。
形式化陈述：leftInverse_generateFrom : LeftInverse generateFrom fun t : TopologicalSpa
ce α => { s | IsOpen[t] s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.leftInverse_u_l`：∀ {α : Type u} {β : Type v} {u : α → 
β} {l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoins
ertion l u), Function.L…
-/
theorem leftInverse_generateFrom :
    LeftInverse generateFrom fun t : TopologicalSpace α => { s | IsOpen[t] s } :=
  (gciGenerateFrom α).leftInverse_u_l
/-
**TopologicalSpace.generateFrom_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace`。
形式化陈述：generateFrom_surjective : Surjective (generateFrom : Set (Set α) -> Topolo
gicalSpace α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_surjective`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsert
ion l u), Function.S…
-/
theorem generateFrom_surjective : Surjective (generateFrom : Set (Set α) → TopologicalSpace α) :=
  (gciGenerateFrom α).u_surjective
/-
**TopologicalSpace.setOfPred_isOpen_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace`。
形式化陈述：setOfPred_isOpen_injective : Injective fun t : TopologicalSpace α => { s |
 IsOpen[t] s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_injective`：∀ {α : Type u} {β : Type v} {u : α → β} {
l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinserti
on l u), Function.I…
-/
theorem setOfPred_isOpen_injective : Injective fun t : TopologicalSpace α => { s | IsOpen[t] s } :=
  (gciGenerateFrom α).l_injective

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_injective := setOfPred_isOpen_injective

end Lattice

end TopologicalSpace

section Lattice

variable {α : Type*} {t t₁ t₂ : TopologicalSpace α} {s : Set α}

/-
**IsOpen.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.mono (hs : IsOpen[t₂] s) (h : t₁ <= t₂) : IsOpen[t₁] s
参数：hs : IsOpen[t₂] s；h : t₁ <= t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsOpen.mono (hs : IsOpen[t₂] s) (h : t₁ ≤ t₂) : IsOpen[t₁] s := h s hs
/-
**IsClosed.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ <= t₂) : IsClosed[t₁] s
参数：hs : IsClosed[t₂] s；h : t₁ <= t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `IsOpen.mono`：IsOpen.mono (hs : IsOpen[t₂] s) (h : t₁ <= t₂) : IsOpen[t₁]
 s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
theorem IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ ≤ t₂) : IsClosed[t₁] s :=
  (@isOpen_compl_iff α s t₁).mp <| hs.isOpen_compl.mono h
/-
**closure.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure.mono (h : t₁ <= t₂) : closure[t₁] s subseteq closure[t₂] s
参数：h : t₁ <= t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsClosed.mono`：IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ <= t₂) : IsCl
osed[t₁] s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem closure.mono (h : t₁ ≤ t₂) : closure[t₁] s ⊆ closure[t₂] s :=
  @closure_minimal _ t₁ s (@closure _ t₂ s) subset_closure (IsClosed.mono isClosed_closure h)
/-
**isOpen_implies_isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_implies_isOpen_iff : (forall s, IsOpen[t₁] s -> IsOpen[t₂] s) ↔ t₂ 
<= t₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_implies_isOpen_iff : (∀ s, IsOpen[t₁] s → IsOpen[t₂] s) ↔ t₂ ≤ t₁ :=
  Iff.rfl

section nontriviality

/-- A topological space is indiscrete if the only open sets are the empty set and the whole space,
that is that its topology equals the indiscrete topology `⊤`.

This can also go by the name "trivial topology" or "codiscrete topology". -/
@[mk_iff]
/-
**IndiscreteTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is indiscrete if the only open sets are the empty set and th
e whole space,
that is that its topology equals the indiscrete topology `⊤`.

This can also go by the name "trivial topology" or "codiscrete topology".
-/
class IndiscreteTopology (α) [TopologicalSpace α] where
  eq_top (α) : ‹TopologicalSpace α› = ⊤
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @IndiscreteTopology α ⊤ := @IndiscreteTopology.mk _ ⊤ rfl


/-- A topological space is nontrivial if it is not the indiscrete topology. -/
@[mk_iff]
/-
**NontrivialTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is nontrivial if it is not the indiscrete topology.
-/
class NontrivialTopology (α) [TopologicalSpace α] where
  ne_top (α) : ‹TopologicalSpace α› ≠ ⊤
/-
**TopologicalSpace.indiscrete_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.indiscrete_or_nontrivial (α) [TopologicalSpace α] : Indis
creteTopology α ∨ NontrivialTopology α
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
-/
theorem TopologicalSpace.indiscrete_or_nontrivial (α) [TopologicalSpace α] :
    IndiscreteTopology α ∨ NontrivialTopology α :=
  (eq_or_ne ‹TopologicalSpace α› ⊤).imp .mk .mk

@[simp, push]
/-
**TopologicalSpace.not_indiscrete_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.not_indiscrete_iff [TopologicalSpace α] : ¬IndiscreteTopo
logy α ↔ NontrivialTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NontrivialTopology.ne_top`：∀ (α : Type u_2) {inst : TopologicalSpace α} 
[self : NontrivialTopology α], inst ≠ ⊤
· 使用定理 `IndiscreteTopology.eq_top`：∀ (α : Type u_2) {inst : TopologicalSpace α} 
[self : IndiscreteTopology α], inst = ⊤
-/
theorem TopologicalSpace.not_indiscrete_iff [TopologicalSpace α] :
    ¬IndiscreteTopology α ↔ NontrivialTopology α :=
  ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h x => h.ne_top x.eq_top⟩

@[simp, push]
/-
**TopologicalSpace.not_nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.not_nontrivial_iff [TopologicalSpace α] : ¬NontrivialTopo
logy α ↔ IndiscreteTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `TopologicalSpace.not_indiscrete_iff`：TopologicalSpace.not_indiscrete_iff
 [TopologicalSpace α] : ¬IndiscreteTopology α ↔ NontrivialTopology α
-/
theorem TopologicalSpace.not_nontrivial_iff [TopologicalSpace α] :
    ¬NontrivialTopology α ↔ IndiscreteTopology α :=
  TopologicalSpace.not_indiscrete_iff.not_right.symm

end nontriviality

/-- The only open sets in the indiscrete topology are the empty set and the whole space. -/
/-
**IndiscreteTopology.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IndiscreteTopology.isOpen_iff [IndiscreteTopology α] (U : Set α) : IsOpen 
U ↔ U = ∅ ∨ U = univ
参数：U : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IndiscreteTopology.eq_top`：∀ (α : Type u_2) {inst : TopologicalSpace α} 
[self : IndiscreteTopology α], inst = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Set.sUnion_mem_empty_univ`：sUnion_mem_empty_univ {S : Set (Set α)} (h : 
S subseteq {∅, univ}) : ⋃₀ S in ({∅, univ} : Set (Set α))
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
The only open sets in the indiscrete topology are the empty set and the whole sp
ace.
-/
theorem IndiscreteTopology.isOpen_iff [IndiscreteTopology α] (U : Set α) :
    IsOpen U ↔ U = ∅ ∨ U = univ := by
  cases IndiscreteTopology.eq_top α
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | basic _ h => exact False.elim h
    | univ => exact .inr rfl
    | inter _ _ _ _ h₁ h₂ =>
      rcases h₁ with (rfl | rfl) <;> rcases h₂ with (rfl | rfl) <;> simp
    | sUnion _ _ ih => exact sUnion_mem_empty_univ ih
  · rintro (rfl | rfl)
    exacts [@isOpen_empty _ ⊤, @isOpen_univ _ ⊤]
/-
**TopologicalSpace.isOpen_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.isOpen_top_iff {α} (U : Set α) : IsOpen[⊤] U ↔ U = ∅ ∨ U 
= univ
参数：U : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IndiscreteTopology.isOpen_iff`：IndiscreteTopology.isOpen_iff [Indiscrete
Topology α] (U : Set α) : IsOpen U ↔ U = ∅ ∨ U = univ
· 使用定理 `instIndiscreteTopology`：∀ {α : Type u_1}, IndiscreteTopology α
-/
theorem TopologicalSpace.isOpen_top_iff {α} (U : Set α) : IsOpen[⊤] U ↔ U = ∅ ∨ U = univ :=
  letI : TopologicalSpace α := ⊤; IndiscreteTopology.isOpen_iff _
/-
**IndiscreteTopology.isClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IndiscreteTopology.isClosed_iff [IndiscreteTopology α] (C : Set α) : IsClo
sed C ↔ C = ∅ ∨ C = Set.univ
参数：C : Set α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IndiscreteTopology.isClosed_iff [IndiscreteTopology α] (C : Set α) :
    IsClosed C ↔ C = ∅ ∨ C = Set.univ := by
  simp [← isOpen_compl_iff, IndiscreteTopology.isOpen_iff, Or.comm]
/-
**dense_indiscrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_indiscrete [IndiscreteTopology α] {s : Set α} (h : s.Nonempty) : Den
se s
参数：h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem dense_indiscrete [IndiscreteTopology α] {s : Set α} (h : s.Nonempty) : Dense s := by
  simp [dense_iff_inter_open, IndiscreteTopology.isOpen_iff, h]
/-
**closure_indiscrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_indiscrete [IndiscreteTopology α] {s : Set α} (h : s.Nonempty) : c
losure s = Set.univ
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `dense_indiscrete`：dense_indiscrete [IndiscreteTopology α] {s : Set α} (h
 : s.Nonempty) : Dense s
-/
theorem closure_indiscrete [IndiscreteTopology α] {s : Set α} (h : s.Nonempty) :
    closure s = Set.univ := Dense.closure_eq (dense_indiscrete h)

/-- Every function to the indiscrete topology is continuous -/
@[fun_prop]
/-
**continuous_of_indiscreteTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_indiscreteTopology {β} [TopologicalSpace β] [IndiscreteTopol
ogy β] {f : α -> β} : Continuous f where isOpen_preimage
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Every function to the indiscrete topology is continuous
-/
theorem continuous_of_indiscreteTopology {β} [TopologicalSpace β] [IndiscreteTopology β]
    {f : α → β} : Continuous f where
  isOpen_preimage := by simp [IndiscreteTopology.isOpen_iff]

/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
/-
**DiscreteTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [t : TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`.
-/
class DiscreteTopology (α : Type*) [t : TopologicalSpace α] : Prop where
  /-- The `TopologicalSpace` structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥
/-
**discreteTopology_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_bot (α : Type*) : @DiscreteTopology α ⊥
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem discreteTopology_bot (α : Type*) : @DiscreteTopology α ⊥ :=
  @DiscreteTopology.mk α ⊥ rfl

section DiscreteTopology

variable [TopologicalSpace α] [DiscreteTopology α] {β : Type*}

@[simp]
/-
**isOpen_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_discrete (s : Set α) : IsOpen s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteTopology.eq_bot`：∀ {α : Type u_2} {t : TopologicalSpace α} [self
 : DiscreteTopology α], t = ⊥
-/
theorem isOpen_discrete (s : Set α) : IsOpen s := (@DiscreteTopology.eq_bot α _).symm ▸ trivial
/-
**isClosed_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [DiscreteTopology α] (s : Set
 α), IsClosed s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
-/
@[simp] theorem isClosed_discrete (s : Set α) : IsClosed s := ⟨isOpen_discrete _⟩
/-
**closure_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_discrete (s : Set α) : closure s = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Discret
eTopology α] (s : Set α), IsClosed s
-/
theorem closure_discrete (s : Set α) : closure s = s := (isClosed_discrete _).closure_eq
/-
**dense_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [DiscreteTopology α] {s : Set
 α}, Dense s ↔ s = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem dense_discrete {s : Set α} : Dense s ↔ s = univ := by simp [dense_iff_closure_eq]

@[simp]
/-
**denseRange_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_discrete {ι : Type*} {f : ι -> α} : DenseRange f ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DenseRange.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] {α : Type u_
1} (f : α → X), DenseRange f = Dense (Set.range f)
· 使用定理 `dense_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [DiscreteTo
pology α] {s : Set α}, Dense s ↔ s = Set.univ
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem denseRange_discrete {ι : Type*} {f : ι → α} : DenseRange f ↔ Surjective f := by
  rw [DenseRange, dense_discrete, range_eq_univ]

@[nontriviality, continuity, fun_prop]
/-
**continuous_of_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_discreteTopology [TopologicalSpace β] {f : α -> β} : Continu
ous f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
-/
theorem continuous_of_discreteTopology [TopologicalSpace β] {f : α → β} : Continuous f :=
  continuous_def.2 fun _ _ => isOpen_discrete _

/-- A function to a discrete topological space is continuous if and only if the preimage of every
singleton is open. -/
/-
**continuous_discrete_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_discrete_rng {α} [TopologicalSpace α] [TopologicalSpace β] [Dis
creteTopology β] {f : α -> β} : Continuous f ↔ forall b : β, IsOpen (f ⁻¹' {b})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Set.preimage_iUnion₂`：preimage_iUnion₂ {f : α -> β} {s : forall i, κ i -
> Set β} : (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)

--- 原说明 ---
A function to a discrete topological space is continuous if and only if the prei
mage of every
singleton is open.
-/
theorem continuous_discrete_rng {α} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopology β]
    {f : α → β} : Continuous f ↔ ∀ b : β, IsOpen (f ⁻¹' {b}) :=
  ⟨fun h _ => (isOpen_discrete _).preimage h, fun h => ⟨fun s _ => by
    rw [← biUnion_of_singleton s, preimage_iUnion₂]
    exact isOpen_biUnion fun _ _ => h _⟩⟩

@[simp]
/-
**nhds_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteTopology α] : @nhd
s α _ = pure
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteTopology α] : @nhds α _ = pure :=
  le_antisymm (fun _ s hs => (isOpen_discrete s).mem_nhds hs) pure_le_nhds
/-
**mem_nhds_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_discrete {x : α} {s : Set α} : s in 𝓝 x ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `Filter.mem_pure`：mem_pure {a : α} {s : Set α} : s in (pure a : Filter α)
 ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nhds_discrete {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ x ∈ s := by rw [nhds_discrete, mem_pure]

end DiscreteTopology

/-
**le_of_nhds_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_nhds_le_nhds (h : forall x, @nhds α t₁ x <= @nhds α t₂ x) : t₁ <= t₂
参数：h : forall x, @nhds α t₁ x <= @nhds α t₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
-/
theorem le_of_nhds_le_nhds (h : ∀ x, @nhds α t₁ x ≤ @nhds α t₂ x) : t₁ ≤ t₂ := fun s => by
  rw [@isOpen_iff_mem_nhds _ t₁, @isOpen_iff_mem_nhds _ t₂]
  exact fun hs a ha => h _ (hs _ ha)
/-
**eq_bot_of_singletons_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_bot_of_singletons_open {t : TopologicalSpace α} (h : forall x, IsOpen[t
] {x}) : t = ⊥
参数：h : forall x, IsOpen[t] {x}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
-/
theorem eq_bot_of_singletons_open {t : TopologicalSpace α} (h : ∀ x, IsOpen[t] {x}) : t = ⊥ :=
  bot_unique fun s _ => biUnion_of_singleton s ▸ isOpen_biUnion fun x _ => h x
/-
**discreteTopology_iff_forall_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_forall_isOpen [TopologicalSpace α] : DiscreteTopology
 α ↔ forall s : Set α, IsOpen s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `eq_bot_of_singletons_open`：eq_bot_of_singletons_open {t : TopologicalSpa
ce α} (h : forall x, IsOpen[t] {x}) : t = ⊥
-/
theorem discreteTopology_iff_forall_isOpen [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ s : Set α, IsOpen s :=
  ⟨@isOpen_discrete _ _, fun h ↦ ⟨eq_bot_of_singletons_open fun _ ↦ h _⟩⟩
/-
**discreteTopology_iff_forall_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_forall_isClosed [TopologicalSpace α] : DiscreteTopolo
gy α ↔ forall s : Set α, IsClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `discreteTopology_iff_forall_isOpen`：discreteTopology_iff_forall_isOpen [
TopologicalSpace α] : DiscreteTopology α ↔ forall s : Set α, IsOpen s
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
-/
theorem discreteTopology_iff_forall_isClosed [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ s : Set α, IsClosed s :=
  discreteTopology_iff_forall_isOpen.trans <| compl_surjective.forall.trans <| forall_congr' fun _ ↦
    isOpen_compl_iff
/-
**discreteTopology_iff_isOpen_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_isOpen_singleton [TopologicalSpace α] : DiscreteTopol
ogy α ↔ (forall a : α, IsOpen ({a} : Set α))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `eq_bot_of_singletons_open`：eq_bot_of_singletons_open {t : TopologicalSpa
ce α} (h : forall x, IsOpen[t] {x}) : t = ⊥
-/
theorem discreteTopology_iff_isOpen_singleton [TopologicalSpace α] :
    DiscreteTopology α ↔ (∀ a : α, IsOpen ({a} : Set α)) :=
  ⟨fun _ _ ↦ isOpen_discrete _, fun h ↦ ⟨eq_bot_of_singletons_open h⟩⟩
/-
**DiscreteTopology.of_finite_of_isClosed_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiscreteTopology.of_finite_of_isClosed_singleton [TopologicalSpace α] [Fin
ite α] (h : forall a : α, IsClosed {a}) : DiscreteTopology α
参数：h : forall a : α, IsClosed {a}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_forall_isClosed`：discreteTopology_iff_forall_isClos
ed [TopologicalSpace α] : DiscreteTopology α ↔ forall s : Set α, IsClosed s
· 使用定理 `isClosed_iUnion_of_finite`：isClosed_iUnion_of_finite [Finite ι] {s : ι -
> Set X} (h : forall i, IsClosed (s i)) : IsClosed (⋃ i, s i)
· 使用定理 `Set.iUnion_of_singleton_coe`：iUnion_of_singleton_coe (s : Set α) : ⋃ i :
 s, ({(i : α)} : Set α) = s
-/
theorem DiscreteTopology.of_finite_of_isClosed_singleton [TopologicalSpace α] [Finite α]
    (h : ∀ a : α, IsClosed {a}) : DiscreteTopology α :=
  discreteTopology_iff_forall_isClosed.mpr fun s ↦
    s.iUnion_of_singleton_coe ▸ isClosed_iUnion_of_finite fun _ ↦ h _
/-
**discreteTopology_iff_singleton_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_singleton_mem_nhds [TopologicalSpace α] : DiscreteTop
ology α ↔ forall x : α, {x} in 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem discreteTopology_iff_singleton_mem_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, {x} ∈ 𝓝 x := by
  simp only [discreteTopology_iff_isOpen_singleton,
    isOpen_iff_mem_nhds, mem_singleton_iff, forall_eq]

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
/-
**discreteTopology_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_nhds [TopologicalSpace α] : DiscreteTopology α ↔ fora
ll x : α, 𝓝 x = pure x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
This lemma characterizes discrete topological spaces as those whose singletons a
re
neighbourhoods.
-/
theorem discreteTopology_iff_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝 x = pure x := by
  simp only [discreteTopology_iff_singleton_mem_nhds]
  apply forall_congr' (fun x ↦ ?_)
  simp [le_antisymm_iff, pure_le_nhds x]
/-
**discreteTopology_iff_nhds_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_iff_nhds_ne [TopologicalSpace α] : DiscreteTopology α ↔ f
orall x : α, 𝓝[!=] x = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem discreteTopology_iff_nhds_ne [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝[≠] x = ⊥ := by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhdsWithin, inf_principal_eq_bot, compl_compl]

/-- If the codomain of a continuous injective function has discrete topology,
then so does the domain.

See also `Embedding.discreteTopology` for an important special case. -/
/-
**DiscreteTopology.of_continuous_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiscreteTopology.of_continuous_injective {β : Type*} [TopologicalSpace α] 
[TopologicalSpace β] [DiscreteTopology β] {f : α -> β} (hc : Continuous f) (hinj
 : Injective f) : DiscreteTopology α
参数：hc : Continuous f；hinj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_forall_isOpen`：discreteTopology_iff_forall_isOpen [
TopologicalSpace α] : DiscreteTopology α ↔ forall s : Set α, IsOpen s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s

--- 原说明 ---
If the codomain of a continuous injective function has discrete topology,
then so does the domain.

See also `Embedding.discreteTopology` for an important special case.
-/
theorem DiscreteTopology.of_continuous_injective
    {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopology β] {f : α → β}
    (hc : Continuous f) (hinj : Injective f) : DiscreteTopology α :=
  discreteTopology_iff_forall_isOpen.2 fun s ↦
    hinj.preimage_image s ▸ (isOpen_discrete _).preimage hc

end Lattice

section GaloisConnection

variable {α β γ : Type*}

/-
**isOpen_induced_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α -> β} : IsO
pen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    IsOpen[t.induced f] s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl
/-
**isClosed_induced_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α -> β} : I
sClosed[t.induced f] s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    IsClosed[t.induced f] s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by
  let := t.induced f
  simp only [← isOpen_compl_iff, isOpen_induced_iff]
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])
/-
**isOpen_coinduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} {f : α -> β} : IsOpe
n[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
    IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl
/-
**isClosed_coinduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_coinduced {t : TopologicalSpace α} {s : Set β} {f : α -> β} : IsC
losed[t.coinduced f] s ↔ IsClosed (f ⁻¹' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
    IsClosed[t.coinduced f] s ↔ IsClosed (f ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_coinduced (f := f), preimage_compl]
/-
**preimage_nhds_coinduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_nhds_coinduced [TopologicalSpace α] {π : α -> β} {s : Set β} {a :
 α} (hs : s in @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s in 𝓝 
a
参数：hs : s in @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem preimage_nhds_coinduced [TopologicalSpace α] {π : α → β} {s : Set β} {a : α}
    (hs : s ∈ @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a := by
  let := TopologicalSpace.coinduced π ‹_›
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩

variable {t t₁ t₂ : TopologicalSpace α} {t' : TopologicalSpace β} {f : α → β} {g : β → α}
/-
**Continuous.coinduced_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.coinduced_le (h : Continuous[t, t'] f) : t.coinduced f <= t'
参数：h : Continuous[t, t'] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
-/
theorem Continuous.coinduced_le (h : Continuous[t, t'] f) : t.coinduced f ≤ t' :=
  (@continuous_def α β t t').1 h
/-
**coinduced_le_iff_le_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_le_iff_le_induced {f : α -> β} {tα : TopologicalSpace α} {tβ : T
opologicalSpace β} : tα.coinduced f <= tβ ↔ tα <= tβ.induced f
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coinduced_le_iff_le_induced {f : α → β} {tα : TopologicalSpace α}
    {tβ : TopologicalSpace β} : tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
  ⟨fun h _s ⟨_t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩
/-
**Continuous.le_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.le_induced (h : Continuous[t, t'] f) : t <= t'.induced f
参数：h : Continuous[t, t'] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `coinduced_le_iff_le_induced`：coinduced_le_iff_le_induced {f : α -> β} {t
α : TopologicalSpace α} {tβ : TopologicalSpace β} : tα.coinduced f <= tβ ↔ tα <=
 tβ.induced f
· 使用定理 `Continuous.coinduced_le`：Continuous.coinduced_le (h : Continuous[t, t'] 
f) : t.coinduced f <= t'
-/
theorem Continuous.le_induced (h : Continuous[t, t'] f) : t ≤ t'.induced f :=
  coinduced_le_iff_le_induced.1 h.coinduced_le
/-
**gc_coinduced_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gc_coinduced_induced (f : α -> β) : GaloisConnection (TopologicalSpace.coi
nduced f) (TopologicalSpace.induced f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `coinduced_le_iff_le_induced`：coinduced_le_iff_le_induced {f : α -> β} {t
α : TopologicalSpace α} {tβ : TopologicalSpace β} : tα.coinduced f <= tβ ↔ tα <=
 tβ.induced f
-/
theorem gc_coinduced_induced (f : α → β) :
    GaloisConnection (TopologicalSpace.coinduced f) (TopologicalSpace.induced f) := fun _ _ =>
  coinduced_le_iff_le_induced

@[gcongr]
/-
**induced_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_mono (h : t₁ <= t₂) : t₁.induced g <= t₂.induced g
参数：h : t₁ <= t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
  (gc_coinduced_induced g).monotone_u h

@[gcongr]
/-
**coinduced_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_mono (h : t₁ <= t₂) : t₁.coinduced f <= t₂.coinduced f
参数：h : t₁ <= t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
  (gc_coinduced_induced f).monotone_l h

@[simp]
/-
**induced_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_top : (⊤ : TopologicalSpace α).induced g = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem induced_top : (⊤ : TopologicalSpace α).induced g = ⊤ :=
  (gc_coinduced_induced g).u_top

@[simp]
/-
**induced_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g :=
  (gc_coinduced_induced g).u_inf

@[simp]
/-
**induced_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_iInf {ι : Sort w} {t : ι -> TopologicalSpace α} : (⨅ i, t i).induc
ed g = ⨅ i, (t i).induced g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem induced_iInf {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨅ i, t i).induced g = ⨅ i, (t i).induced g :=
  (gc_coinduced_induced g).u_iInf

@[simp]
/-
**induced_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_sInf {s : Set (TopologicalSpace α)} : TopologicalSpace.induced g (
sInf s) = sInf (TopologicalSpace.induced g '' s)
参数：TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `sInf_image'`：∀ {α : Type u_1} {β : Type u_2} [inst : InfSet α] {s : Set 
β} {f : β → α}, sInf (f '' s) = ⨅ a, f ↑a
· 使用定理 `induced_iInf`：induced_iInf {ι : Sort w} {t : ι -> TopologicalSpace α} : 
(⨅ i, t i).induced g = ⨅ i, (t i).induced g
-/
theorem induced_sInf {s : Set (TopologicalSpace α)} :
    TopologicalSpace.induced g (sInf s) = sInf (TopologicalSpace.induced g '' s) := by
  rw [sInf_eq_iInf', sInf_image', induced_iInf]

@[simp]
/-
**coinduced_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥ :=
  (gc_coinduced_induced f).l_bot

@[simp]
/-
**coinduced_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f :=
  (gc_coinduced_induced f).l_sup

@[simp]
/-
**coinduced_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_iSup {ι : Sort w} {t : ι -> TopologicalSpace α} : (⨆ i, t i).coi
nduced f = ⨆ i, (t i).coinduced f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem coinduced_iSup {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f :=
  (gc_coinduced_induced f).l_iSup

@[simp]
/-
**coinduced_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_sSup {s : Set (TopologicalSpace α)} : TopologicalSpace.coinduced
 f (sSup s) = sSup ((TopologicalSpace.coinduced f) '' s)
参数：TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
· 使用定理 `coinduced_iSup`：coinduced_iSup {ι : Sort w} {t : ι -> TopologicalSpace α
} : (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f
-/
theorem coinduced_sSup {s : Set (TopologicalSpace α)} :
    TopologicalSpace.coinduced f (sSup s) = sSup ((TopologicalSpace.coinduced f) '' s) := by
  rw [sSup_eq_iSup', sSup_image', coinduced_iSup]
/-
**induced_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_id [t : TopologicalSpace α] : t.induced id = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem induced_id [t : TopologicalSpace α] : t.induced id = t :=
  TopologicalSpace.ext <|
    funext fun s => propext <| ⟨fun ⟨_, hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩
/-
**induced_fun_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_fun_id {t : TopologicalSpace α} : t.induced (·) = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `induced_id`：induced_id [t : TopologicalSpace α] : t.induced id = t
-/
theorem induced_fun_id {t : TopologicalSpace α} : t.induced (·) = t := induced_id
/-
**induced_compose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} {g : β -> γ} : (tγ.
induced g).induced f = tγ.induced (g ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem induced_compose {tγ : TopologicalSpace γ} {f : α → β} {g : β → γ} :
    (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
  TopologicalSpace.ext <|
    funext fun _ => propext
      ⟨fun ⟨_, ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
        fun ⟨s, hs, h⟩ => ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩
/-
**induced_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun _ : β => x
) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Continuous.le_induced`：Continuous.le_induced (h : Continuous[t, t'] f) :
 t <= t'.induced f
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun _ : β => x) = ⊤ :=
  le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced
/-
**coinduced_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_id [t : TopologicalSpace α] : t.coinduced id = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
-/
theorem coinduced_id [t : TopologicalSpace α] : t.coinduced id = t :=
  TopologicalSpace.ext rfl
/-
**coinduced_compose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_compose [tα : TopologicalSpace α] {f : α -> β} {g : β -> γ} : (t
α.coinduced f).coinduced g = tα.coinduced (g ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
-/
theorem coinduced_compose [tα : TopologicalSpace α] {f : α → β} {g : β → γ} :
    (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
  TopologicalSpace.ext rfl
/-
**Equiv.induced_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.induced_symm {α β : Type*} (e : α ≃ β) : TopologicalSpace.induced e.
symm = TopologicalSpace.coinduced e
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_induced_iff`：isOpen_induced_iff [t : TopologicalSpace β] {s : Set
 α} {f : α -> β} : IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {α β} (e : α ≃ 
β) (s t) : e ⁻¹' s = t ↔ s = e '' t
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Equiv.induced_symm {α β : Type*} (e : α ≃ β) :
    TopologicalSpace.induced e.symm = TopologicalSpace.coinduced e := by
  ext t U
  rw [isOpen_induced_iff, isOpen_coinduced]
  simp only [e.symm.preimage_eq_iff_eq_image, exists_eq_right, Equiv.image_symm_eq_preimage]
/-
**Equiv.coinduced_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.coinduced_symm {α β : Type*} (e : α ≃ β) : TopologicalSpace.coinduce
d e.symm = TopologicalSpace.induced e
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.induced_symm`：Equiv.induced_symm {α β : Type*} (e : α ≃ β) : Topol
ogicalSpace.induced e.symm = TopologicalSpace.coinduced e
-/
theorem Equiv.coinduced_symm {α β : Type*} (e : α ≃ β) :
    TopologicalSpace.coinduced e.symm = TopologicalSpace.induced e :=
  e.symm.induced_symm.symm
/-
**WithTopology.topology_eq_induced** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithTopology.topology_eq_induced {X : Type*} (t : TopologicalSpace X) : in
stTopologicalSpace X t = .induced ofTopology t
参数：t : TopologicalSpace X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.coinduced_symm`：Equiv.coinduced_symm {α β : Type*} (e : α ≃ β) : T
opologicalSpace.coinduced e.symm = TopologicalSpace.induced e
-/
lemma WithTopology.topology_eq_induced {X : Type*} (t : TopologicalSpace X) :
    instTopologicalSpace X t = .induced ofTopology t :=
  congrFun (WithTopology.equiv X t).coinduced_symm t

end GaloisConnection

-- constructions using the complete lattice structure
section Constructions

open TopologicalSpace

variable {α : Type u} {β : Type v}

/-
**inhabitedTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α) :=
  ⟨⊥⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Subsingleton.uniqueTopologicalSpace [Subsingleton α] :
    Unique (TopologicalSpace α) where
  default := ⊥
  uniq t :=
    eq_bot_of_singletons_open fun x =>
      Subsingleton.set_cases (@isOpen_empty _ t) (@isOpen_univ _ t) ({x} : Set α)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Subsingleton.discreteTopology [t : TopologicalSpace α] [Subsingleton α] :
    DiscreteTopology α :=
  ⟨Unique.eq_default t⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [Subsingleton α] : IndiscreteTopology α where
  eq_top := Subsingleton.elim _ _

variable (α) in
/-
**Nontrivial.of_nontrivialTopology** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nontrivial.of_nontrivialTopology [TopologicalSpace α] [h : NontrivialTopol
ogy α] : Nontrivial α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
-/
lemma Nontrivial.of_nontrivialTopology [TopologicalSpace α] [h : NontrivialTopology α] :
    Nontrivial α := by contrapose! h; infer_instance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace Empty := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology Empty := ⟨rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IndiscreteTopology Empty := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace PEmpty := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology PEmpty := ⟨rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IndiscreteTopology PEmpty := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace PUnit := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology PUnit := ⟨rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IndiscreteTopology PUnit := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace Bool := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology Bool := ⟨rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace ℕ := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology ℕ := ⟨rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace ℤ := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology ℤ := ⟨rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} : TopologicalSpace (Fin n) := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} : DiscreteTopology (Fin n) := ⟨rfl⟩

/-- A copy of a type equipped with the discrete topology. -/
/-
**WithDiscreteTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：WithDiscreteTopology (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of a type equipped with the discrete topology.
-/
abbrev WithDiscreteTopology (α : Type*) := WithTopology α ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology (WithDiscreteTopology α) where
  eq_bot := coinduced_bot
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IndiscreteTopology (WithTopology α ⊤) where
  eq_top := by rw [WithTopology.topology_eq_induced, induced_top]
/-
**WithTopology.nontrivialTopology_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithTopology`。
形式化陈述：∀ {α : Type u} {t : TopologicalSpace α}, NontrivialTopology (WithTopology 
α t) ↔ t ≠ ⊤
参数：WithTopology α t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithTopology.topology_eq_induced`：WithTopology.topology_eq_induced {X : 
Type*} (t : TopologicalSpace X) : instTopologicalSpace X t = .induced ofTopology
 t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `induced_fun_id`：induced_fun_id {t : TopologicalSpace α} : t.induced (·) 
= t
· 使用定理 `induced_top`：induced_top : (⊤ : TopologicalSpace α).induced g = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem WithTopology.nontrivialTopology_iff {t : TopologicalSpace α} :
    NontrivialTopology (WithTopology α t) ↔ t ≠ ⊤ := by
  simp_rw [nontrivialTopology_iff, topology_eq_induced, ne_eq, not_iff_not]
  constructor
  · intro h
    simpa [induced_compose, comp_def, induced_fun_id] using congr(induced (toTopology t) $h)
  · simp +contextual
/-
**Nat.cast_continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.cast_continuous {R : Type*} [NatCast R] [TopologicalSpace R] : Continu
ous (Nat.cast (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
-/
lemma Nat.cast_continuous {R : Type*} [NatCast R] [TopologicalSpace R] :
    Continuous (Nat.cast (R := R)) :=
  continuous_of_discreteTopology
/-
**Int.cast_continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.cast_continuous {R : Type*} [IntCast R] [TopologicalSpace R] : Continu
ous (Int.cast (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
-/
lemma Int.cast_continuous {R : Type*} [IntCast R] [TopologicalSpace R] :
    Continuous (Int.cast (R := R)) :=
  continuous_of_discreteTopology
/-
**sierpinskiSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：sierpinskiSpace : TopologicalSpace Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sierpinskiSpace : TopologicalSpace Prop :=
  generateFrom {{True}}

/-- See also `continuous_of_discreteTopology`, which works for `IsEmpty α`. -/
/-
**continuous_empty_function** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_empty_function [TopologicalSpace α] [TopologicalSpace β] [IsEmp
ty β] (f : α -> β) : Continuous f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α

--- 原说明 ---
See also `continuous_of_discreteTopology`, which works for `IsEmpty α`.
-/
theorem continuous_empty_function [TopologicalSpace α] [TopologicalSpace β] [IsEmpty β]
    (f : α → β) : Continuous f :=
  letI := Function.isEmpty f
  continuous_of_discreteTopology
/-
**le_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_generateFrom {t : TopologicalSpace α} {g : Set (Set α)} (h : forall s i
n g, IsOpen s) : t <= generateFrom g
参数：Set α；h : forall s in g, IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.le_generateFrom_iff_subset_isOpen`：le_generateFrom_iff_
subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} : t <= generateFrom g ↔
 g subseteq { s | IsOpen[t] s }
-/
theorem le_generateFrom {t : TopologicalSpace α} {g : Set (Set α)} (h : ∀ s ∈ g, IsOpen s) :
    t ≤ generateFrom g :=
  le_generateFrom_iff_subset_isOpen.2 h
/-
**induced_generateFrom_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_generateFrom_eq {α β} {b : Set (Set β)} {f : α -> β} : (generateFr
om b).induced f = generateFrom (preimage f '' b)
参数：Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_generateFrom`：le_generateFrom {t : TopologicalSpace α} {g : Set (Set 
α)} (h : forall s in g, IsOpen s) : t <= generateFrom g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `coinduced_le_iff_le_induced`：coinduced_le_iff_le_induced {f : α -> β} {t
α : TopologicalSpace α} {tβ : TopologicalSpace β} : tα.coinduced f <= tβ ↔ tα <=
 tβ.induced f
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem induced_generateFrom_eq {α β} {b : Set (Set β)} {f : α → β} :
    (generateFrom b).induced f = generateFrom (preimage f '' b) :=
  le_antisymm (le_generateFrom <| forall_mem_image.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <| le_generateFrom fun _s hs => .basic _ (mem_image_of_mem _ hs))
/-
**le_induced_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_induced_generateFrom {α β} [t : TopologicalSpace α] {b : Set (Set β)} {
f : α -> β} (h : forall a : Set β, a in b -> IsOpen (f ⁻¹' a)) : t <= induced f 
(generateFrom b)
参数：Set β；h : forall a : Set β, a in b -> IsOpen (f ⁻¹' a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `induced_generateFrom_eq`：induced_generateFrom_eq {α β} {b : Set (Set β)}
 {f : α -> β} : (generateFrom b).induced f = generateFrom (preimage f '' b)
· 使用定理 `le_generateFrom`：le_generateFrom {t : TopologicalSpace α} {g : Set (Set 
α)} (h : forall s in g, IsOpen s) : t <= generateFrom g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem le_induced_generateFrom {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α → β}
    (h : ∀ a : Set β, a ∈ b → IsOpen (f ⁻¹' a)) : t ≤ induced f (generateFrom b) := by
  rw [induced_generateFrom_eq]
  apply le_generateFrom
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp]
  exact h
/-
**generateFrom_insert_of_generateOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：generateFrom_insert_of_generateOpen {α : Type*} {s : Set (Set α)} {t : Set
 α} (ht : GenerateOpen s t) : generateFrom (insert t s) = generateFrom s
参数：Set α；ht : GenerateOpen s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `TopologicalSpace.generateFrom_anti`：generateFrom_anti {α} {g₁ g₂ : Set (
Set α)} (h : g₁ subseteq g₂) : generateFrom g₂ <= generateFrom g₁
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `le_generateFrom`：le_generateFrom {t : TopologicalSpace α} {g : Set (Set 
α)} (h : forall s in g, IsOpen s) : t <= generateFrom g
· 使用定理 `TopologicalSpace.isOpen_generateFrom_of_mem`：isOpen_generateFrom_of_mem 
{g : Set (Set α)} {s : Set α} (hs : s in g) : IsOpen[generateFrom g] s
-/
lemma generateFrom_insert_of_generateOpen {α : Type*} {s : Set (Set α)} {t : Set α}
    (ht : GenerateOpen s t) : generateFrom (insert t s) = generateFrom s := by
  refine le_antisymm (generateFrom_anti <| subset_insert t s) (le_generateFrom ?_)
  rintro t (rfl | h)
  · exact ht
  · exact isOpen_generateFrom_of_mem h

@[simp]
/-
**generateFrom_insert_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：generateFrom_insert_univ {α : Type*} {s : Set (Set α)} : generateFrom (ins
ert univ s) = generateFrom s
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `generateFrom_insert_of_generateOpen`：generateFrom_insert_of_generateOpen
 {α : Type*} {s : Set (Set α)} {t : Set α} (ht : GenerateOpen s t) : generateFro
m (insert t s) = generate…
-/
lemma generateFrom_insert_univ {α : Type*} {s : Set (Set α)} :
    generateFrom (insert univ s) = generateFrom s :=
  generateFrom_insert_of_generateOpen .univ

@[simp]
/-
**generateFrom_insert_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：generateFrom_insert_empty {α : Type*} {s : Set (Set α)} : generateFrom (in
sert ∅ s) = generateFrom s
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用引理 `generateFrom_insert_of_generateOpen`：generateFrom_insert_of_generateOpen
 {α : Type*} {s : Set (Set α)} {t : Set α} (ht : GenerateOpen s t) : generateFro
m (insert t s) = generate…
-/
lemma generateFrom_insert_empty {α : Type*} {s : Set (Set α)} :
    generateFrom (insert ∅ s) = generateFrom s := by
  rw [← sUnion_empty]
  exact generateFrom_insert_of_generateOpen (.sUnion ∅ (fun s_1 a ↦ False.elim a))

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
@[instance_reducible]
/-
**nhdsAdjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α where IsOpen s
参数：a : α；f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`.
-/
def nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α where
  IsOpen s := a ∈ s → s ∈ f
  isOpen_univ _ := univ_mem
  isOpen_inter := fun _s _t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  isOpen_sUnion := fun _k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)
/-
**gc_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_nhds_iff`：le_nhds_iff {f} : f <= 𝓝 x ↔ forall s : Set X, x in s -> Is
Open s -> s in f
-/
theorem gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a := fun f t => by
  rw [le_nhds_iff]
  exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩
/-
**nhds_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂) : @nhds α t₁
 a <= @nhds α t₂ a
参数：h : t₁ <= t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `gc_nhds`：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nh
ds α t a
-/
theorem nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ ≤ t₂) :
    @nhds α t₁ a ≤ @nhds α t₂ a :=
  (gc_nhds a).monotone_u h
/-
**le_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_nhds {α : Type*} (t t' : TopologicalSpace α) : t <= t' ↔ forall x, 
@nhds α t x <= @nhds α t' x
参数：t t' : TopologicalSpace α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_mono`：nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂)
 : @nhds α t₁ a <= @nhds α t₂ a
· 使用定理 `le_of_nhds_le_nhds`：le_of_nhds_le_nhds (h : forall x, @nhds α t₁ x <= @n
hds α t₂ x) : t₁ <= t₂
-/
theorem le_iff_nhds {α : Type*} (t t' : TopologicalSpace α) :
    t ≤ t' ↔ ∀ x, @nhds α t x ≤ @nhds α t' x :=
  ⟨fun h _ => nhds_mono h, le_of_nhds_le_nhds⟩
/-
**isOpen_singleton_nhdsAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_singleton_nhdsAdjoint {α : Type*} {a b : α} (f : Filter α) (hb : b 
!= a) : IsOpen[nhdsAdjoint a f] {b}
参数：f : Filter α；hb : b != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem isOpen_singleton_nhdsAdjoint {α : Type*} {a b : α} (f : Filter α) (hb : b ≠ a) :
    IsOpen[nhdsAdjoint a f] {b} := fun h ↦
  absurd h hb.symm
/-
**nhds_nhdsAdjoint_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_nhdsAdjoint_same (a : α) (f : Filter α) : @nhds α (nhdsAdjoint a f) a
 = pure a ⊔ f
参数：a : α；f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `gc_nhds`：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nh
ds α t a
-/
theorem nhds_nhdsAdjoint_same (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) a = pure a ⊔ f := by
  let _ := nhdsAdjoint a f
  apply le_antisymm
  · rintro t ⟨hat : a ∈ t, htf : t ∈ f⟩
    exact IsOpen.mem_nhds (fun _ ↦ htf) hat
  · exact sup_le (pure_le_nhds _) ((gc_nhds a).le_u_l f)
/-
**nhds_nhdsAdjoint_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_nhdsAdjoint_of_ne {a b : α} (f : Filter α) (h : b != a) : @nhds α (nh
dsAdjoint a f) b = pure b
参数：f : Filter α；h : b != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_singleton_iff_nhds_eq_pure`：isOpen_singleton_iff_nhds_eq_pure (x 
: X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x
· 使用定理 `isOpen_singleton_nhdsAdjoint`：isOpen_singleton_nhdsAdjoint {α : Type*} {
a b : α} (f : Filter α) (hb : b != a) : IsOpen[nhdsAdjoint a f] {b}
-/
theorem nhds_nhdsAdjoint_of_ne {a b : α} (f : Filter α) (h : b ≠ a) :
    @nhds α (nhdsAdjoint a f) b = pure b :=
  let _ := nhdsAdjoint a f
  (isOpen_singleton_iff_nhds_eq_pure _).1 <| isOpen_singleton_nhdsAdjoint f h
/-
**nhds_nhdsAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_nhdsAdjoint [DecidableEq α] (a : α) (f : Filter α) : @nhds α (nhdsAdj
oint a f) = update pure a (pure a ⊔ f)
参数：a : α；f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.eq_update_iff`：eq_update_iff {a : α} {b : β a} {f g : forall a,
 β a} : g = update f a b ↔ g a = b ∧ forall x != a, g x = f x
· 使用定理 `nhds_nhdsAdjoint_same`：nhds_nhdsAdjoint_same (a : α) (f : Filter α) : @n
hds α (nhdsAdjoint a f) a = pure a ⊔ f
· 使用定理 `nhds_nhdsAdjoint_of_ne`：nhds_nhdsAdjoint_of_ne {a b : α} (f : Filter α) 
(h : b != a) : @nhds α (nhdsAdjoint a f) b = pure b
-/
theorem nhds_nhdsAdjoint [DecidableEq α] (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) = update pure a (pure a ⊔ f) :=
  eq_update_iff.2 ⟨nhds_nhdsAdjoint_same .., fun _ ↦ nhds_nhdsAdjoint_of_ne _⟩
/-
**le_nhdsAdjoint_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhdsAdjoint_iff' {a : α} {f : Filter α} {t : TopologicalSpace α} : t <=
 nhdsAdjoint a f ↔ @nhds α t a <= pure a ⊔ f ∧ forall b != a, @nhds α t b = pure
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_nhdsAdjoint`：nhds_nhdsAdjoint [DecidableEq α] (a : α) (f : Filter α
) : @nhds α (nhdsAdjoint a f) = update pure a (pure a ⊔ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_nhdsAdjoint_iff' {a : α} {f : Filter α} {t : TopologicalSpace α} :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b ≠ a, @nhds α t b = pure b := by
  classical
  simp_rw [le_iff_nhds, nhds_nhdsAdjoint, forall_update_iff, (pure_le_nhds _).ge_iff_eq']
/-
**le_nhdsAdjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nhdsAdjoint_iff {α : Type*} (a : α) (f : Filter α) (t : TopologicalSpac
e α) : t <= nhdsAdjoint a f ↔ @nhds α t a <= pure a ⊔ f ∧ forall b != a, IsOpen[
t] {b}
参数：a : α；f : Filter α；t : TopologicalSpace α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `isOpen_singleton_iff_nhds_eq_pure`：isOpen_singleton_iff_nhds_eq_pure (x 
: X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_nhdsAdjoint_iff {α : Type*} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b ≠ a, IsOpen[t] {b} := by
  simp only [le_nhdsAdjoint_iff', @isOpen_singleton_iff_nhds_eq_pure α t]
/-
**nhds_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} : @nhds α (iIn
f t) a = ⨅ i, @nhds α (t i) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `gc_nhds`：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nh
ds α t a
-/
theorem nhds_iInf {ι : Sort*} {t : ι → TopologicalSpace α} {a : α} :
    @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a :=
  (gc_nhds a).u_iInf
/-
**nhds_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_sInf {s : Set (TopologicalSpace α)} {a : α} : @nhds α (sInf s) a = ⨅ 
t in s, @nhds α t a
参数：TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用定理 `gc_nhds`：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nh
ds α t a
-/
theorem nhds_sInf {s : Set (TopologicalSpace α)} {a : α} :
    @nhds α (sInf s) a = ⨅ t ∈ s, @nhds α t a :=
  (gc_nhds a).u_sInf

-- Porting note: type error without `b₁ := t₁`
/-
**nhds_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} : @nhds α (t₁ ⊓ t₂) a = @nhd
s α t₁ a ⊓ @nhds α t₂ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `gc_nhds`：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nh
ds α t a
-/
theorem nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} :
    @nhds α (t₁ ⊓ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a :=
  (gc_nhds a).u_inf (b₁ := t₁)
/-
**nhds_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_top {a : α} : @nhds α ⊤ a = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `gc_nhds`：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nh
ds α t a
-/
theorem nhds_top {a : α} : @nhds α ⊤ a = ⊤ :=
  (gc_nhds a).u_top
/-
**isOpen_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_sup {t₁ t₂ : TopologicalSpace α} {s : Set α} : IsOpen[t₁ ⊔ t₂] s ↔ 
IsOpen[t₁] s ∧ IsOpen[t₂] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_sup {t₁ t₂ : TopologicalSpace α} {s : Set α} :
    IsOpen[t₁ ⊔ t₂] s ↔ IsOpen[t₁] s ∧ IsOpen[t₂] s :=
  Iff.rfl
/-
**IndiscreteTopology.nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IndiscreteTopology.nhds_eq [TopologicalSpace α] [IndiscreteTopology α] (a 
: α) : nhds a = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IndiscreteTopology.eq_top`：∀ (α : Type u_2) {inst : TopologicalSpace α} 
[self : IndiscreteTopology α], inst = ⊤
· 使用定理 `nhds_top`：nhds_top {a : α} : @nhds α ⊤ a = ⊤
-/
theorem IndiscreteTopology.nhds_eq [TopologicalSpace α] [IndiscreteTopology α] (a : α) :
    nhds a = ⊤ := by
  cases IndiscreteTopology.eq_top α
  exact nhds_top
/-
**clusterPt_of_indiscreteTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_of_indiscreteTopology [TopologicalSpace α] [IndiscreteTopology α
] {x : α} {f : Filter α} [f.NeBot] : ClusterPt x f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IndiscreteTopology.nhds_eq`：IndiscreteTopology.nhds_eq [TopologicalSpace
 α] [IndiscreteTopology α] (a : α) : nhds a = ⊤
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem clusterPt_of_indiscreteTopology [TopologicalSpace α] [IndiscreteTopology α]
    {x : α} {f : Filter α} [f.NeBot] : ClusterPt x f := by
  simpa [ClusterPt, IndiscreteTopology.nhds_eq]

/-- In the indiscrete topology no points are separable.

The corresponding `bot` lemma is handled more generally by `inseparable_iff_eq`. -/
@[simp]
/-
**Inseparable.all** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.all [TopologicalSpace α] [IndiscreteTopology α] (x y : α) : In
separable x y
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IndiscreteTopology.nhds_eq`：IndiscreteTopology.nhds_eq [TopologicalSpace
 α] [IndiscreteTopology α] (a : α) : nhds a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In the indiscrete topology no points are separable.

The corresponding `bot` lemma is handled more generally by `inseparable_iff_eq`.
-/
theorem Inseparable.all [TopologicalSpace α] [IndiscreteTopology α] (x y : α) :
    Inseparable x y :=
  (IndiscreteTopology.nhds_eq _).trans (IndiscreteTopology.nhds_eq _).symm
/-
**IndiscreteTopology.of_forall_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IndiscreteTopology.of_forall_inseparable [TopologicalSpace α] (h : forall 
x y : α, Inseparable x y) : IndiscreteTopology α where eq_top
参数：h : forall x y : α, Inseparable x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext_nhds`：∀ {X : Type u_2} {t t' : TopologicalSpace X},
 (∀ (x : X), nhds x = nhds x) → t = t'
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_top`：nhds_top {a : α} : @nhds α ⊤ a = ⊤
-/
theorem IndiscreteTopology.of_forall_inseparable [TopologicalSpace α]
    (h : ∀ x y : α, Inseparable x y) : IndiscreteTopology α where
  eq_top := ext_nhds fun x => nhds_top ▸ top_unique fun _ hs a => mem_of_mem_nhds <| h x a ▸ hs
/-
**TopologicalSpace.indiscrete_iff_forall_inseparable** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：TopologicalSpace.indiscrete_iff_forall_inseparable {t : TopologicalSpace α
} : IndiscreteTopology α ↔ (forall x y : α, Inseparable x y) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.all`：Inseparable.all [TopologicalSpace α] [IndiscreteTopolog
y α] (x y : α) : Inseparable x y
· 使用定理 `IndiscreteTopology.of_forall_inseparable`：IndiscreteTopology.of_forall_i
nseparable [TopologicalSpace α] (h : forall x y : α, Inseparable x y) : Indiscre
teTopology α where eq_top
-/
theorem TopologicalSpace.indiscrete_iff_forall_inseparable {t : TopologicalSpace α} :
    IndiscreteTopology α ↔ (∀ x y : α, Inseparable x y) where
  mp _ := Inseparable.all
  mpr := .of_forall_inseparable
/-
**TopologicalSpace.nontrivial_iff_exists_not_inseparable** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：TopologicalSpace.nontrivial_iff_exists_not_inseparable {t : TopologicalSpa
ce α} : NontrivialTopology α ↔ exists x y : α, ¬Inseparable x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `TopologicalSpace.indiscrete_iff_forall_inseparable`：TopologicalSpace.ind
iscrete_iff_forall_inseparable {t : TopologicalSpace α} : IndiscreteTopology α ↔
 (forall x y : α, Inseparable x y) where…
-/
theorem TopologicalSpace.nontrivial_iff_exists_not_inseparable {t : TopologicalSpace α} :
    NontrivialTopology α ↔ ∃ x y : α, ¬Inseparable x y := by
  simpa using indiscrete_iff_forall_inseparable.not

alias ⟨NontrivialTopology.exists_not_inseparable, NontrivialTopology.of_exists_not_inseparable⟩ :=
  TopologicalSpace.nontrivial_iff_exists_not_inseparable

@[deprecated Inseparable.all (since := "2026-01-21")]
/-
**inseparable_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_top (x y : α) : @Inseparable α ⊤ x y
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.all`：Inseparable.all [TopologicalSpace α] [IndiscreteTopolog
y α] (x y : α) : Inseparable x y
· 使用定理 `instIndiscreteTopology`：∀ {α : Type u_1}, IndiscreteTopology α
-/
theorem inseparable_top (x y : α) : @Inseparable α ⊤ x y :=
  @Inseparable.all _ ⊤ _ x y

@[deprecated TopologicalSpace.indiscrete_iff_forall_inseparable (since := "2026-01-21")]
/-
**TopologicalSpace.eq_top_iff_forall_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.eq_top_iff_forall_inseparable {t : TopologicalSpace α} : 
t = ⊤ ↔ (forall x y : α, Inseparable x y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.indiscrete_iff_forall_inseparable`：TopologicalSpace.ind
iscrete_iff_forall_inseparable {t : TopologicalSpace α} : IndiscreteTopology α ↔
 (forall x y : α, Inseparable x y) where…
· 使用定理 `indiscreteTopology_iff`：∀ (α : Type u_2) [inst : TopologicalSpace α], In
discreteTopology α ↔ inst = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem TopologicalSpace.eq_top_iff_forall_inseparable {t : TopologicalSpace α} :
    t = ⊤ ↔ (∀ x y : α, Inseparable x y) := by
  rw [← TopologicalSpace.indiscrete_iff_forall_inseparable, indiscreteTopology_iff]

@[deprecated TopologicalSpace.nontrivial_iff_exists_not_inseparable (since := "2026-01-21")]
/-
**TopologicalSpace.ne_top_iff_exists_not_inseparable** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：TopologicalSpace.ne_top_iff_exists_not_inseparable {t : TopologicalSpace α
} : t != ⊤ ↔ exists x y : α, ¬Inseparable x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.nontrivial_iff_exists_not_inseparable`：TopologicalSpace
.nontrivial_iff_exists_not_inseparable {t : TopologicalSpace α} : NontrivialTopo
logy α ↔ exists x y : α, ¬Inseparable x y
· 使用定理 `nontrivialTopology_iff`：∀ (α : Type u_2) [inst : TopologicalSpace α], No
ntrivialTopology α ↔ inst ≠ ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem TopologicalSpace.ne_top_iff_exists_not_inseparable {t : TopologicalSpace α} :
    t ≠ ⊤ ↔ ∃ x y : α, ¬Inseparable x y := by
  rw [← TopologicalSpace.nontrivial_iff_exists_not_inseparable, nontrivialTopology_iff]

open TopologicalSpace

variable {γ : Type*} {f : α → β} {ι : Sort*}
/-
**continuous_iff_coinduced_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iff_coinduced_le {t₁ : TopologicalSpace α} {t₂ : TopologicalSpa
ce β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= t₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
-/
theorem continuous_iff_coinduced_le {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f ↔ coinduced f t₁ ≤ t₂ :=
  continuous_def
/-
**continuous_iff_le_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iff_le_induced {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace
 β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用定理 `gc_coinduced_induced`：gc_coinduced_induced (f : α -> β) : GaloisConnecti
on (TopologicalSpace.coinduced f) (TopologicalSpace.induced f)
-/
theorem continuous_iff_le_induced {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f ↔ t₁ ≤ induced f t₂ :=
  Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)
/-
**continuous_generateFrom_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_generateFrom_iff {t : TopologicalSpace α} {b : Set (Set β)} : C
ontinuous[t, generateFrom b] f ↔ forall s in b, IsOpen (f ⁻¹' s)
参数：Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用定理 `TopologicalSpace.le_generateFrom_iff_subset_isOpen`：le_generateFrom_iff_
subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} : t <= generateFrom g ↔
 g subseteq { s | IsOpen[t] s }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuous_generateFrom_iff {t : TopologicalSpace α} {b : Set (Set β)} :
    Continuous[t, generateFrom b] f ↔ ∀ s ∈ b, IsOpen (f ⁻¹' s) := by
  rw [continuous_iff_coinduced_le, le_generateFrom_iff_subset_isOpen]
  simp only [isOpen_coinduced, subset_def, mem_ofPred_eq]

@[continuity, fun_prop]
/-
**continuous_induced_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_induced_dom {t : TopologicalSpace β} : Continuous[induced f t, 
t] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem continuous_induced_dom {t : TopologicalSpace β} : Continuous[induced f t, t] f :=
  continuous_iff_le_induced.2 le_rfl
/-
**continuous_induced_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_induced_rng {g : γ -> α} {t₂ : TopologicalSpace β} {t₁ : Topolo
gicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Continuous[t₁, t₂] (f ∘ g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_induced_rng {g : γ → α} {t₂ : TopologicalSpace β} {t₁ : TopologicalSpace γ} :
    Continuous[t₁, induced f t₂] g ↔ Continuous[t₁, t₂] (f ∘ g) := by
  simp only [continuous_iff_le_induced, induced_compose]
/-
**continuous_coinduced_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_coinduced_rng {t : TopologicalSpace α} : Continuous[t, coinduce
d f t] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem continuous_coinduced_rng {t : TopologicalSpace α} :
    Continuous[t, coinduced f t] f :=
  continuous_iff_coinduced_le.2 le_rfl
/-
**continuous_coinduced_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_coinduced_dom {g : β -> γ} {t₁ : TopologicalSpace α} {t₂ : Topo
logicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔ Continuous[t₁, t₂] (g ∘ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `coinduced_compose`：coinduced_compose [tα : TopologicalSpace α] {f : α ->
 β} {g : β -> γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_coinduced_dom {g : β → γ} {t₁ : TopologicalSpace α} {t₂ : TopologicalSpace γ} :
    Continuous[coinduced f t₁, t₂] g ↔ Continuous[t₁, t₂] (g ∘ f) := by
  simp only [continuous_iff_coinduced_le, coinduced_compose]
/-
**continuous_le_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} (
h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂, t₃] f
参数：h₁ : t₂ <= t₁；h₂ : Continuous[t₁, t₃] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} (h₁ : t₂ ≤ t₁)
    (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂, t₃] f := by
  rw [continuous_iff_le_induced] at h₂ ⊢
  exact le_trans h₁ h₂
/-
**continuous_le_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_le_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} (
h₁ : t₂ <= t₃) (h₂ : Continuous[t₁, t₂] f) : Continuous[t₁, t₃] f
参数：h₁ : t₂ <= t₃；h₂ : Continuous[t₁, t₂] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem continuous_le_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} (h₁ : t₂ ≤ t₃)
    (h₂ : Continuous[t₁, t₂] f) : Continuous[t₁, t₃] f := by
  rw [continuous_iff_coinduced_le] at h₂ ⊢
  exact le_trans h₂ h₁
/-
**continuous_sup_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sup_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} 
: Continuous[t₁ ⊔ t₂, t₃] f ↔ Continuous[t₁, t₃] f ∧ Continuous[t₂, t₃] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_sup_dom {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₁ ⊔ t₂, t₃] f ↔ Continuous[t₁, t₃] f ∧ Continuous[t₂, t₃] f := by
  simp only [continuous_iff_le_induced, sup_le_iff]
/-
**continuous_sup_rng_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sup_rng_left {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpac
e β} : Continuous[t₁, t₂] f -> Continuous[t₁, t₂ ⊔ t₃] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_rng`：continuous_le_rng {t₁ : TopologicalSpace α} {t₂ t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₃) (h₂ : Continuous[t₁, t₂] f) : Continuous[t₁,
 t₃] f
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem continuous_sup_rng_left {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β} :
    Continuous[t₁, t₂] f → Continuous[t₁, t₂ ⊔ t₃] f :=
  continuous_le_rng le_sup_left
/-
**continuous_sup_rng_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sup_rng_right {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpa
ce β} : Continuous[t₁, t₃] f -> Continuous[t₁, t₂ ⊔ t₃] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_rng`：continuous_le_rng {t₁ : TopologicalSpace α} {t₂ t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₃) (h₂ : Continuous[t₁, t₂] f) : Continuous[t₁,
 t₃] f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem continuous_sup_rng_right {t₁ : TopologicalSpace α} {t₃ t₂ : TopologicalSpace β} :
    Continuous[t₁, t₃] f → Continuous[t₁, t₂ ⊔ t₃] f :=
  continuous_le_rng le_sup_right
/-
**continuous_sSup_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sSup_dom {T : Set (TopologicalSpace α)} {t₂ : TopologicalSpace 
β} : Continuous[sSup T, t₂] f ↔ forall t in T, Continuous[t, t₂] f
参数：TopologicalSpace α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_sSup_dom {T : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β} :
    Continuous[sSup T, t₂] f ↔ ∀ t ∈ T, Continuous[t, t₂] f := by
  simp only [continuous_iff_le_induced, sSup_le_iff]
/-
**continuous_sSup_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sSup_rng {t₁ : TopologicalSpace α} {t₂ : Set (TopologicalSpace 
β)} {t : TopologicalSpace β} (h₁ : t in t₂) (hf : Continuous[t₁, t] f) : Continu
ous[t₁, sSup t₂] f
参数：TopologicalSpace β；h₁ : t in t₂；hf : Continuous[t₁, t] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用定理 `le_sSup_of_le`：le_sSup_of_le (hb : b in s) (h : a <= b) : a <= sSup s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem continuous_sSup_rng {t₁ : TopologicalSpace α} {t₂ : Set (TopologicalSpace β)}
    {t : TopologicalSpace β} (h₁ : t ∈ t₂) (hf : Continuous[t₁, t] f) :
    Continuous[t₁, sSup t₂] f :=
  continuous_iff_coinduced_le.2 <| le_sSup_of_le h₁ <| continuous_iff_coinduced_le.1 hf
/-
**continuous_iSup_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iSup_dom {t₁ : ι -> TopologicalSpace α} {t₂ : TopologicalSpace 
β} : Continuous[iSup t₁, t₂] f ↔ forall i, Continuous[t₁ i, t₂] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem continuous_iSup_dom {t₁ : ι → TopologicalSpace α} {t₂ : TopologicalSpace β} :
    Continuous[iSup t₁, t₂] f ↔ ∀ i, Continuous[t₁ i, t₂] f := by
  simp only [continuous_iff_le_induced, iSup_le_iff]
/-
**continuous_iSup_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iSup_rng {t₁ : TopologicalSpace α} {t₂ : ι -> TopologicalSpace 
β} {i : ι} (h : Continuous[t₁, t₂ i] f) : Continuous[t₁, iSup t₂] f
参数：h : Continuous[t₁, t₂ i] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_sSup_rng`：continuous_sSup_rng {t₁ : TopologicalSpace α} {t₂ :
 Set (TopologicalSpace β)} {t : TopologicalSpace β} (h₁ : t in t₂) (hf : Continu
ous[t₁, t…
-/
theorem continuous_iSup_rng {t₁ : TopologicalSpace α} {t₂ : ι → TopologicalSpace β} {i : ι}
    (h : Continuous[t₁, t₂ i] f) : Continuous[t₁, iSup t₂] f :=
  continuous_sSup_rng ⟨i, rfl⟩ h
/-
**continuous_inf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inf_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} 
: Continuous[t₁, t₂ ⊓ t₃] f ↔ Continuous[t₁, t₂] f ∧ Continuous[t₁, t₃] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_inf_rng {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} :
    Continuous[t₁, t₂ ⊓ t₃] f ↔ Continuous[t₁, t₂] f ∧ Continuous[t₁, t₃] f := by
  simp only [continuous_iff_coinduced_le, le_inf_iff]
/-
**continuous_inf_dom_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inf_dom_left {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpac
e β} : Continuous[t₁, t₃] f -> Continuous[t₁ ⊓ t₂, t₃] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_dom`：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂,
 t₃] f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem continuous_inf_dom_left {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₁, t₃] f → Continuous[t₁ ⊓ t₂, t₃] f :=
  continuous_le_dom inf_le_left
/-
**continuous_inf_dom_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inf_dom_right {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpa
ce β} : Continuous[t₂, t₃] f -> Continuous[t₁ ⊓ t₂, t₃] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_dom`：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂,
 t₃] f
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem continuous_inf_dom_right {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} :
    Continuous[t₂, t₃] f → Continuous[t₁ ⊓ t₂, t₃] f :=
  continuous_le_dom inf_le_right
/-
**continuous_sInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sInf_dom {t₁ : Set (TopologicalSpace α)} {t₂ : TopologicalSpace
 β} {t : TopologicalSpace α} (h₁ : t in t₁) : Continuous[t, t₂] f -> Continuous[
sInf t₁, t₂] f
参数：TopologicalSpace α；h₁ : t in t₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_dom`：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂,
 t₃] f
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem continuous_sInf_dom {t₁ : Set (TopologicalSpace α)} {t₂ : TopologicalSpace β}
    {t : TopologicalSpace α} (h₁ : t ∈ t₁) :
    Continuous[t, t₂] f → Continuous[sInf t₁, t₂] f :=
  continuous_le_dom <| sInf_le h₁
/-
**continuous_sInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_sInf_rng {t₁ : TopologicalSpace α} {T : Set (TopologicalSpace β
)} : Continuous[t₁, sInf T] f ↔ forall t in T, Continuous[t₁, t] f
参数：TopologicalSpace β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_sInf_rng {t₁ : TopologicalSpace α} {T : Set (TopologicalSpace β)} :
    Continuous[t₁, sInf T] f ↔ ∀ t ∈ T, Continuous[t₁, t] f := by
  simp only [continuous_iff_coinduced_le, le_sInf_iff]
/-
**continuous_iInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iInf_dom {t₁ : ι -> TopologicalSpace α} {t₂ : TopologicalSpace 
β} {i : ι} : Continuous[t₁ i, t₂] f -> Continuous[iInf t₁, t₂] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_dom`：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂,
 t₃] f
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem continuous_iInf_dom {t₁ : ι → TopologicalSpace α} {t₂ : TopologicalSpace β} {i : ι} :
    Continuous[t₁ i, t₂] f → Continuous[iInf t₁, t₂] f :=
  continuous_le_dom <| iInf_le _ _
/-
**continuous_iInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iInf_rng {t₁ : TopologicalSpace α} {t₂ : ι -> TopologicalSpace 
β} : Continuous[t₁, iInf t₂] f ↔ forall i, Continuous[t₁, t₂ i] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem continuous_iInf_rng {t₁ : TopologicalSpace α} {t₂ : ι → TopologicalSpace β} :
    Continuous[t₁, iInf t₂] f ↔ ∀ i, Continuous[t₁, t₂ i] f := by
  simp only [continuous_iff_coinduced_le, le_iInf_iff]

@[continuity, fun_prop]
/-
**continuous_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_bot {t : TopologicalSpace β} : Continuous[⊥, t] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem continuous_bot {t : TopologicalSpace β} : Continuous[⊥, t] f :=
  continuous_iff_le_induced.2 bot_le

@[continuity, fun_prop]
/-
**continuous_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_top {t : TopologicalSpace α} : Continuous[t, ⊤] f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem continuous_top {t : TopologicalSpace α} : Continuous[t, ⊤] f :=
  continuous_iff_coinduced_le.2 le_top
/-
**continuous_id_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_id_iff_le {t t' : TopologicalSpace α} : Continuous[t, t'] id ↔ 
t <= t'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
-/
theorem continuous_id_iff_le {t t' : TopologicalSpace α} : Continuous[t, t'] id ↔ t ≤ t' :=
  @continuous_def _ _ t t' id
/-
**continuous_id_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_id_of_le {t t' : TopologicalSpace α} (h : t <= t') : Continuous
[t, t'] id
参数：h : t <= t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_id_iff_le`：continuous_id_iff_le {t t' : TopologicalSpace α} :
 Continuous[t, t'] id ↔ t <= t'
-/
theorem continuous_id_of_le {t t' : TopologicalSpace α} (h : t ≤ t') : Continuous[t, t'] id :=
  continuous_id_iff_le.2 h

-- 𝓝 in the induced topology
/-
**mem_nhds_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β) (s : Set β)
 : s in @nhds β (TopologicalSpace.induced f T) a ↔ exists u in 𝓝 (f a), f ⁻¹' u 
subseteq s
参数：f : β -> α；a : β；s : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem mem_nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) (s : Set β) :
    s ∈ @nhds β (TopologicalSpace.induced f T) a ↔ ∃ u ∈ 𝓝 (f a), f ⁻¹' u ⊆ s := by
  let := T.induced f
  simp_rw [mem_nhds_iff, isOpen_induced_iff]
  constructor
  · rintro ⟨u, usub, ⟨v, openv, rfl⟩, au⟩
    exact ⟨v, ⟨v, Subset.rfl, openv, au⟩, usub⟩
  · rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
    exact ⟨f ⁻¹' v, (Set.preimage_mono vsubu).trans finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩
/-
**nhds_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β) : @nhds β (Topo
logicalSpace.induced f T) a = comap f (𝓝 (f a))
参数：f : β -> α；a : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_induced`：mem_nhds_induced [T : TopologicalSpace α] (f : β -> α)
 (a : β) (s : Set β) : s in @nhds β (TopologicalSpace.induced f T) a ↔ exists u 
in 𝓝 (…
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) :
    @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a)) := by
  ext s
  rw [mem_nhds_induced, mem_comap]
/-
**induced_iff_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f
 : β -> α) : tβ = tα.induced f ↔ forall b, 𝓝 b = comap f (𝓝 <| f b)
参数：f : β -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β → α) :
    tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝 <| f b) := by
  simp only [ext_iff_nhds, nhds_induced]
/-
**map_nhds_induced_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β -> α} (hf :
 Surjective f) (a : β) : map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f
 a)
参数：hf : Surjective f；a : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
-/
theorem map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β → α} (hf : Surjective f)
    (a : β) : map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f a) := by
  rw [nhds_induced, map_comap_of_surjective hf]
/-
**continuous_nhdsAdjoint_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_nhdsAdjoint_dom [TopologicalSpace β] {f : α -> β} {a : α} {l : 
Filter α} : Continuous[nhdsAdjoint a l, _] f ↔ Tendsto f l (𝓝 (f a))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gc_nhds`：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nh
ds α t a
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_nhdsAdjoint_dom [TopologicalSpace β] {f : α → β} {a : α} {l : Filter α} :
    Continuous[nhdsAdjoint a l, _] f ↔ Tendsto f l (𝓝 (f a)) := by
  simp_rw [continuous_iff_le_induced, gc_nhds _ _, nhds_induced, tendsto_iff_comap]
/-
**coinduced_nhdsAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coinduced_nhdsAdjoint (f : α -> β) (a : α) (l : Filter α) : coinduced f (n
hdsAdjoint a l) = nhdsAdjoint (f a) (map f l)
参数：f : α -> β；a : α；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gc_nhds`：gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nh
ds α t a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
· 使用定理 `continuous_nhdsAdjoint_dom`：continuous_nhdsAdjoint_dom [TopologicalSpace
 β] {f : α -> β} {a : α} {l : Filter α} : Continuous[nhdsAdjoint a l, _] f ↔ Ten
dsto f l (𝓝 (f a…
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coinduced_nhdsAdjoint (f : α → β) (a : α) (l : Filter α) :
    coinduced f (nhdsAdjoint a l) = nhdsAdjoint (f a) (map f l) :=
  eq_of_forall_ge_iff fun _ ↦ by
    rw [gc_nhds, ← continuous_iff_coinduced_le, continuous_nhdsAdjoint_dom, Tendsto]

end Constructions

section Induced

open TopologicalSpace

variable {α : Type*} {β : Type*}
variable [t : TopologicalSpace β] {f : α → β}

/-
**isOpen_induced_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_induced_eq {s : Set α} : IsOpen[induced f t] s ↔ s in preimage f ''
 { s | IsOpen s }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_induced_eq {s : Set α} :
    IsOpen[induced f t] s ↔ s ∈ preimage f '' { s | IsOpen s } :=
  Iff.rfl
/-
**isOpen_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induced f t] (f ⁻¹' s)
参数：h : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induced f t] (f ⁻¹' s) :=
  ⟨s, h, rfl⟩
/-
**isClosed_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_induced {s : Set β} (h : IsClosed s) : IsClosed[induced f t] (f ⁻
¹' s)
参数：h : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
theorem isClosed_induced {s : Set β} (h : IsClosed s) : IsClosed[induced f t] (f ⁻¹' s) := by
  simp_rw [← isOpen_compl_iff]
  exact isOpen_induced h.isOpen_compl
/-
**map_nhds_induced_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f]
 f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
-/
theorem map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] f a := by
  rw [nhds_induced, Filter.map_comap, nhdsWithin]
/-
**map_nhds_induced_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nhds_induced_of_mem {a : α} (h : range f in 𝓝 (f a)) : map f (@nhds α 
(induced f t) a) = 𝓝 (f a)
参数：h : range f in 𝓝 (f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
-/
theorem map_nhds_induced_of_mem {a : α} (h : range f ∈ 𝓝 (f a)) :
    map f (@nhds α (induced f t) a) = 𝓝 (f a) := by rw [nhds_induced, Filter.map_comap_of_mem h]
/-
**closure_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_induced {f : α -> β} {a : α} {s : Set α} : a in @closure α (t.indu
ced f) s ↔ f a in closure (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closure_induced {f : α → β} {a : α} {s : Set α} :
    a ∈ @closure α (t.induced f) s ↔ f a ∈ closure (f '' s) := by
  simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm]
/-
**isClosed_induced_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_induced_iff' {f : α -> β} {s : Set α} : IsClosed[t.induced f] s ↔
 forall a, f a in closure (f '' s) -> a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_induced_iff' {f : α → β} {s : Set α} :
    IsClosed[t.induced f] s ↔ ∀ a, f a ∈ closure (f '' s) → a ∈ s := by
  simp only [← closure_subset_iff_isClosed, subset_def, closure_induced]

end Induced

section Sierpinski

variable {α : Type*}

@[simp]
/-
**isOpen_singleton_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_singleton_true : IsOpen ({True} : Set Prop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem isOpen_singleton_true : IsOpen ({True} : Set Prop) :=
  TopologicalSpace.GenerateOpen.basic _ (mem_singleton _)

@[simp]
/-
**nhds_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_true : 𝓝 True = pure True
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_pure_iff`：le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {
a} in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_singleton_true`：isOpen_singleton_true : IsOpen ({True} : Set Prop
)
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
theorem nhds_true : 𝓝 True = pure True :=
  le_antisymm (le_pure_iff.2 <| isOpen_singleton_true.mem_nhds <| mem_singleton _) (pure_le_nhds _)

@[simp]
/-
**nhds_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_false : 𝓝 False = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem nhds_false : 𝓝 False = ⊤ :=
  TopologicalSpace.nhds_generateFrom.trans <| by simp [@and_comm (_ ∈ _)]
/-
**tendsto_nhds_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_true {l : Filter α} {p : α -> Prop} : Tendsto p l (𝓝 True) ↔ 
forallᶠ x in l, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_true`：nhds_true : 𝓝 True = pure True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhds_true {l : Filter α} {p : α → Prop} :
    Tendsto p l (𝓝 True) ↔ ∀ᶠ x in l, p x := by simp
/-
**tendsto_nhds_Prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_Prop {l : Filter α} {p : α -> Prop} {q : Prop} : Tendsto p l 
(𝓝 q) ↔ (q -> forallᶠ x in l, p x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `nhds_true`：nhds_true : 𝓝 True = pure True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `nhds_false`：nhds_false : 𝓝 False = ⊤
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem tendsto_nhds_Prop {l : Filter α} {p : α → Prop} {q : Prop} :
    Tendsto p l (𝓝 q) ↔ (q → ∀ᶠ x in l, p x) := by
  by_cases q <;> simp [*]

variable [TopologicalSpace α]
/-
**continuous_Prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_Prop {p : α -> Prop} : Continuous p ↔ IsOpen { x | p x }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuous_Prop {p : α → Prop} : Continuous p ↔ IsOpen { x | p x } := by
  simp only [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_Prop, isOpen_iff_mem_nhds]; rfl
/-
**isOpen_iff_continuous_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous (· in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `continuous_Prop`：continuous_Prop {p : α -> Prop} : Continuous p ↔ IsOpen
 { x | p x }
-/
theorem isOpen_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous (· ∈ s) :=
  continuous_Prop.symm

end Sierpinski

section iInf

open TopologicalSpace

variable {α : Type u} {ι : Sort v}

/-
**generateFrom_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generateFrom_union (a₁ a₂ : Set (Set α)) : generateFrom (a₁ union a₂) = ge
nerateFrom a₁ ⊓ generateFrom a₂
参数：a₁ a₂ : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `TopologicalSpace.gc_generateFrom`：gc_generateFrom (α) : GaloisConnection
 (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s }) (generateF
rom ∘ OrderDual.ofDual…
-/
theorem generateFrom_union (a₁ a₂ : Set (Set α)) :
    generateFrom (a₁ ∪ a₂) = generateFrom a₁ ⊓ generateFrom a₂ :=
  (gc_generateFrom α).u_inf
/-
**setOfPred_isOpen_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_isOpen_sup (t₁ t₂ : TopologicalSpace α) : { s | IsOpen[t₁ ⊔ t₂] 
s } = { s | IsOpen[t₁] s } inter { s | IsOpen[t₂] s }
参数：t₁ t₂ : TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem setOfPred_isOpen_sup (t₁ t₂ : TopologicalSpace α) :
    { s | IsOpen[t₁ ⊔ t₂] s } = { s | IsOpen[t₁] s } ∩ { s | IsOpen[t₂] s } :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_sup := setOfPred_isOpen_sup
/-
**generateFrom_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generateFrom_iUnion {f : ι -> Set (Set α)} : generateFrom (⋃ i, f i) = ⨅ i
, generateFrom (f i)
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `TopologicalSpace.gc_generateFrom`：gc_generateFrom (α) : GaloisConnection
 (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s }) (generateF
rom ∘ OrderDual.ofDual…
-/
theorem generateFrom_iUnion {f : ι → Set (Set α)} :
    generateFrom (⋃ i, f i) = ⨅ i, generateFrom (f i) :=
  (gc_generateFrom α).u_iInf
/-
**setOfPred_isOpen_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_isOpen_iSup {t : ι -> TopologicalSpace α} : { s | IsOpen[⨆ i, t 
i] s } = ⋂ i, { s | IsOpen[t i] s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `TopologicalSpace.gc_generateFrom`：gc_generateFrom (α) : GaloisConnection
 (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s }) (generateF
rom ∘ OrderDual.ofDual…
-/
theorem setOfPred_isOpen_iSup {t : ι → TopologicalSpace α} :
    { s | IsOpen[⨆ i, t i] s } = ⋂ i, { s | IsOpen[t i] s } :=
  (gc_generateFrom α).l_iSup

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_iSup := setOfPred_isOpen_iSup
/-
**generateFrom_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generateFrom_sUnion {S : Set (Set (Set α))} : generateFrom (⋃₀ S) = ⨅ s in
 S, generateFrom s
参数：Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用定理 `TopologicalSpace.gc_generateFrom`：gc_generateFrom (α) : GaloisConnection
 (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s }) (generateF
rom ∘ OrderDual.ofDual…
-/
theorem generateFrom_sUnion {S : Set (Set (Set α))} :
    generateFrom (⋃₀ S) = ⨅ s ∈ S, generateFrom s :=
  (gc_generateFrom α).u_sInf
/-
**setOfPred_isOpen_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_isOpen_sSup {T : Set (TopologicalSpace α)} : { s | IsOpen[sSup T
] s } = ⋂ t in T, { s | IsOpen[t] s }
参数：TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `TopologicalSpace.gc_generateFrom`：gc_generateFrom (α) : GaloisConnection
 (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s }) (generateF
rom ∘ OrderDual.ofDual…
-/
theorem setOfPred_isOpen_sSup {T : Set (TopologicalSpace α)} :
    { s | IsOpen[sSup T] s } = ⋂ t ∈ T, { s | IsOpen[t] s } :=
  (gc_generateFrom α).l_sSup

@[deprecated (since := "2026-07-09")] alias setOf_isOpen_sSup := setOfPred_isOpen_sSup
/-
**generateFrom_union_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generateFrom_union_isOpen (a b : TopologicalSpace α) : generateFrom ({ s |
 IsOpen[a] s } union { s | IsOpen[b] s }) = a ⊓ b
参数：a b : TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_inf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem generateFrom_union_isOpen (a b : TopologicalSpace α) :
    generateFrom ({ s | IsOpen[a] s } ∪ { s | IsOpen[b] s }) = a ⊓ b :=
  (gciGenerateFrom α).u_inf_l _ _
/-
**generateFrom_iUnion_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generateFrom_iUnion_isOpen (f : ι -> TopologicalSpace α) : generateFrom (⋃
 i, { s | IsOpen[f i] s }) = ⨅ i, f i
参数：f : ι -> TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iInf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem generateFrom_iUnion_isOpen (f : ι → TopologicalSpace α) :
    generateFrom (⋃ i, { s | IsOpen[f i] s }) = ⨅ i, f i :=
  (gciGenerateFrom α).u_iInf_l _
/-
**generateFrom_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generateFrom_inter (a b : TopologicalSpace α) : generateFrom ({ s | IsOpen
[a] s } inter { s | IsOpen[b] s }) = a ⊔ b
参数：a b : TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_sup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem generateFrom_inter (a b : TopologicalSpace α) :
    generateFrom ({ s | IsOpen[a] s } ∩ { s | IsOpen[b] s }) = a ⊔ b :=
  (gciGenerateFrom α).u_sup_l _ _
/-
**generateFrom_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generateFrom_iInter (f : ι -> TopologicalSpace α) : generateFrom (⋂ i, { s
 | IsOpen[f i] s }) = ⨆ i, f i
参数：f : ι -> TopologicalSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iSup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem generateFrom_iInter (f : ι → TopologicalSpace α) :
    generateFrom (⋂ i, { s | IsOpen[f i] s }) = ⨆ i, f i :=
  (gciGenerateFrom α).u_iSup_l _
/-
**generateFrom_iInter_of_generateFrom_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generateFrom_iInter_of_generateFrom_eq_self (f : ι -> Set (Set α)) (hf : f
orall i, { s | IsOpen[generateFrom (f i)] s } = f i) : generateFrom (⋂ i, f i) =
 ⨆ i, generateFrom (f i)
参数：f : ι -> Set (Set α)；hf : forall i, { s | IsOpen[generateFrom (f i)] s } = f 
i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iSup_of_l_u_eq_self`：∀ {α : Type u} {β : Type v} {u 
: α → β} {l : β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (
gi : GaloisCoinsertion l u) {…
-/
theorem generateFrom_iInter_of_generateFrom_eq_self (f : ι → Set (Set α))
    (hf : ∀ i, { s | IsOpen[generateFrom (f i)] s } = f i) :
    generateFrom (⋂ i, f i) = ⨆ i, generateFrom (f i) :=
  (gciGenerateFrom α).u_iSup_of_l_u_eq_self f hf

variable {t : ι → TopologicalSpace α}
/-
**isOpen_iSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ forall i, IsOpen[t i] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `setOfPred_isOpen_iSup`：setOfPred_isOpen_iSup {t : ι -> TopologicalSpace 
α} : { s | IsOpen[⨆ i, t i] s } = ⋂ i, { s | IsOpen[t i] s }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iSup_iff {s : Set α} : IsOpen[⨆ i, t i] s ↔ ∀ i, IsOpen[t i] s :=
  show s ∈ {s | IsOpen[iSup t] s} ↔ s ∈ { x : Set α | ∀ i : ι, IsOpen[t i] x } by
    simp [setOfPred_isOpen_iSup]
/-
**isOpen_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_sSup_iff {s : Set α} {T : Set (TopologicalSpace α)} : IsOpen[sSup T
] s ↔ forall t in T, IsOpen[t] s
参数：TopologicalSpace α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_sSup_iff {s : Set α} {T : Set (TopologicalSpace α)} :
    IsOpen[sSup T] s ↔ ∀ t ∈ T, IsOpen[t] s := by
  simp +instances only [sSup_eq_iSup, isOpen_iSup_iff]
/-
**isClosed_iSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_iSup_iff {s : Set α} : IsClosed[⨆ i, t i] s ↔ forall i, IsClosed[
t i] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_iSup_iff {s : Set α} : IsClosed[⨆ i, t i] s ↔ ∀ i, IsClosed[t i] s := by
  simp only [← @isOpen_compl_iff _ _ (⨆ i, t i), ← @isOpen_compl_iff _ _ (t _), isOpen_iSup_iff]
/-
**isClosed_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_sSup_iff {s : Set α} {T : Set (TopologicalSpace α)} : IsClosed[sS
up T] s ↔ forall t in T, IsClosed[t] s
参数：TopologicalSpace α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_sSup_iff {s : Set α} {T : Set (TopologicalSpace α)} :
    IsClosed[sSup T] s ↔ ∀ t ∈ T, IsClosed[t] s := by
  simp +instances only [sSup_eq_iSup, isClosed_iSup_iff]

end iInf

