/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular, normal, T₃, T₄ and T₅ spaces

This file continues the study of separation properties of topological spaces, focusing
on conditions strictly stronger than T₂.

## Main definitions

* `RegularSpace`: A regular space is one where, given any closed `C` and `x ∉ C`,
  there are disjoint open sets containing `x` and `C` respectively. Such a space is not necessarily
  Hausdorff.
* `T3Space`: A T₃ space is a regular T₀ space. T₃ implies T₂.₅.
* `NormalSpace`: A normal space, is one where given two disjoint closed sets,
  we can find two open sets that separate them. Such a space is not necessarily Hausdorff, even if
  it is T₀.
* `T4Space`: A T₄ space is a normal T₁ space. T₄ implies T₃.
* `CompletelyNormalSpace`: A completely normal space is one in which for any two sets `s`, `t`
  such that if both `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`,
  then there exist disjoint neighbourhoods of `s` and `t`. `Embedding.completelyNormalSpace` allows
  us to conclude that this is equivalent to all subspaces being normal. Such a space is not
  necessarily Hausdorff or regular, even if it is T₀.
* `T5Space`: A T₅ space is a completely normal T₁ space. T₅ implies T₄.

See `Mathlib/Topology/Separation/GDelta.lean` for the definitions of `PerfectlyNormalSpace` and
`T6Space`.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### Regular spaces

If the space is also Lindelöf:

* `NormalSpace.of_regularSpace_lindelofSpace`: every regular Lindelöf space is normal.

### T₃ spaces

* `disjoint_nested_nhds`: Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and
  `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* <https://en.wikipedia.org/wiki/Normal_space>
* [Willard's *General Topology*][zbMATH02107988]

-/

public section

assert_not_exists UniformSpace

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section RegularSpace

/-- A topological space is called a *regular space* if for any closed set `s` and `a ∉ s`, there
exist disjoint open sets `U ⊇ s` and `V ∋ a`. We formulate this condition in terms of `Disjoint`ness
of filters `𝓝ˢ s` and `𝓝 a`. -/
@[mk_iff]
/-
**RegularSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is called a *regular space* if for any closed set `s` and `a
 ∉ s`, there
exist disjoint open sets `U ⊇ s` and `V ∋ a`. We formulate this condition in ter
ms of `Disjoint`ness
of filters `𝓝ˢ s` and `𝓝 a`.
-/
class RegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `a` is a point that does not belong to a closed set `s`, then `a` and `s` admit disjoint
  neighborhoods. -/
  regular : ∀ {s : Set X} {a}, IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a)
/-
**regularSpace_TFAE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：regularSpace_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE [RegularSp
ace X, forall (s : Set X) x, x ∉ closure s -> Disjoint (𝓝ˢ s) (𝓝 x), forall (x :
 X) (s : Set X), Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s, forall (x : X) (s : Set 
X), s in 𝓝 x -> exists t in 𝓝 x, IsClosed t ∧ t subseteq s, forall x : X, (𝓝 x).
lift' closure <= 𝓝 x, forall x : X, (𝓝 x).lift' closure = 𝓝 x]
参数：X : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `regularSpace_iff`：∀ (X : Type u) [inst : TopologicalSpace X],   RegularS
pace X ↔ ∀ {s : Set X} {a : X}, IsClosed s → a ∉ s → Disjoint (nhdsSet s) (nhds 
a)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.disjoint_iff_right`：∀ {α : Type u_1} {ι : Sort u_4} {l l
' : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l' l 
↔ ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s →
 (l.lift' closure).…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.le_lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X] (l :
 Filter X), l ≤ l.lift' closure
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
（共 44 条，此处仅展示前 30 条）
-/
theorem regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
    List.TFAE [RegularSpace X,
      ∀ (s : Set X) x, x ∉ closure s → Disjoint (𝓝ˢ s) (𝓝 x),
      ∀ (x : X) (s : Set X), Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s,
      ∀ (x : X) (s : Set X), s ∈ 𝓝 x → ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s,
      ∀ x : X, (𝓝 x).lift' closure ≤ 𝓝 x,
      ∀ x : X, (𝓝 x).lift' closure = 𝓝 x] := by
  tfae_have 1 ↔ 5 := by
    rw [regularSpace_iff, (@compl_surjective (Set X) _).forall, forall_comm]
    simp only [isClosed_compl_iff, mem_compl_iff, Classical.not_not, @and_comm (_ ∈ _),
      (nhds_basis_opens _).lift'_closure.le_basis_iff (nhds_basis_opens _), and_imp,
      (nhds_basis_opens _).disjoint_iff_right, ← subset_interior_iff_mem_nhdsSet,
      interior_compl, compl_subset_compl]
  tfae_have 5 → 6 := fun h a => (h a).antisymm (𝓝 _).le_lift'_closure
  tfae_have 6 → 4
  | H, a, s, hs => by
    rw [← H] at hs
    rcases (𝓝 a).basis_sets.lift'_closure.mem_iff.mp hs with ⟨U, hU, hUs⟩
    exact ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, hUs⟩
  tfae_have 4 → 2
  | H, s, a, ha => by
    have ha' : sᶜ ∈ 𝓝 a := by rwa [← mem_interior_iff_mem_nhds, interior_compl]
    rcases H _ _ ha' with ⟨U, hU, hUc, hUs⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ hU
    rwa [← subset_interior_iff_mem_nhdsSet, hUc.isOpen_compl.interior_eq, subset_compl_comm]
  tfae_have 2 → 3 := by
    refine fun H a s => ⟨fun hd has => mem_closure_iff_nhds_ne_bot.mp has ?_, H s a⟩
    exact (hd.symm.mono_right <| @principal_le_nhdsSet _ _ s).eq_bot
  tfae_have 3 → 1 := fun H => ⟨fun hs ha => (H _ _).mpr <| hs.closure_eq.symm ▸ ha⟩
  tfae_finish
/-
**RegularSpace.of_lift'_closure_le** 是 Mathlib 中的一个定理，位于命名空间 `RegularSpace`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], (∀ (x : X), (nhds x).lift' c
losure ≤ nhds x) → RegularSpace X
参数：∀ (x : X), (nhds x).lift' closure ≤ nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `regularSpace_TFAE`：regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
 List.TFAE [RegularSpace X, forall (s : Set X) x, x ∉ closure s -> Disjoint (𝓝ˢ 
s) (𝓝 x…
-/
theorem RegularSpace.of_lift'_closure_le (h : ∀ x : X, (𝓝 x).lift' closure ≤ 𝓝 x) :
    RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 4) h
/-
**RegularSpace.of_lift'_closure** 是 Mathlib 中的一个定理，位于命名空间 `RegularSpace`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], (∀ (x : X), (nhds x).lift' c
losure = nhds x) → RegularSpace X
参数：∀ (x : X), (nhds x).lift' closure = nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `regularSpace_TFAE`：regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
 List.TFAE [RegularSpace X, forall (s : Set X) x, x ∉ closure s -> Disjoint (𝓝ˢ 
s) (𝓝 x…
-/
theorem RegularSpace.of_lift'_closure (h : ∀ x : X, (𝓝 x).lift' closure = 𝓝 x) : RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 5) h
/-
**RegularSpace.of_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RegularSpace.of_hasBasis {ι : X -> Sort*} {p : forall a, ι a -> Prop} {s :
 forall a, ι a -> Set X} (h₁ : forall a, (𝓝 a).HasBasis (p a) (s a)) (h₂ : foral
l a i, p a i -> IsClosed (s a i)) : RegularSpace X
参数：h₁ : forall a, (𝓝 a).HasBasis (p a) (s a)；h₂ : forall a i, p a i -> IsClosed 
(s a i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularSpace.of_lift'_closure`：∀ {X : Type u_1} [inst : TopologicalSpace
 X], (∀ (x : X), (nhds x).lift' closure = nhds x) → RegularSpace X
· 使用定理 `Filter.HasBasis.lift'_closure_eq_self`：∀ {X : Type u} [inst : Topologica
lSpace X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBas
is p s → (∀ (i : ι), p i → …
-/
theorem RegularSpace.of_hasBasis {ι : X → Sort*} {p : ∀ a, ι a → Prop} {s : ∀ a, ι a → Set X}
    (h₁ : ∀ a, (𝓝 a).HasBasis (p a) (s a)) (h₂ : ∀ a i, p a i → IsClosed (s a i)) :
    RegularSpace X :=
  .of_lift'_closure fun a => (h₁ a).lift'_closure_eq_self (h₂ a)
/-
**RegularSpace.of_exists_mem_nhds_isClosed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RegularSpace.of_exists_mem_nhds_isClosed_subset (h : forall (x : X), foral
l s in 𝓝 x, exists t in 𝓝 x, IsClosed t ∧ t subseteq s) : RegularSpace X
参数：h : forall (x : X), forall s in 𝓝 x, exists t in 𝓝 x, IsClosed t ∧ t subseteq
 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `regularSpace_TFAE`：regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
 List.TFAE [RegularSpace X, forall (s : Set X) x, x ∉ closure s -> Disjoint (𝓝ˢ 
s) (𝓝 x…
-/
theorem RegularSpace.of_exists_mem_nhds_isClosed_subset
    (h : ∀ (x : X), ∀ s ∈ 𝓝 x, ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s) : RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 3) h

/-- A weakly locally compact R₁ space is regular. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weakly locally compact R₁ space is regular.
-/
instance (priority := 100) [WeaklyLocallyCompactSpace X] [R1Space X] : RegularSpace X :=
  .of_hasBasis isCompact_isClosed_basis_nhds fun _ _ ⟨_, _, h⟩ ↦ h

/-- Given a subbasis `s`, it is enough to check the condition of regularity for complements of sets
in `s`. -/
/-
**regularSpace_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：regularSpace_generateFrom {s : Set (Set X)} (h : ‹_› = generateFrom s) : R
egularSpace X ↔ forall t in s, forall a in t, Disjoint (𝓝ˢ tᶜ) (𝓝 a)
参数：Set X；h : ‹_› = generateFrom s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularSpace.regular`：∀ {X : Type u} {inst : TopologicalSpace X} [self :
 RegularSpace X] {s : Set X} {a : X},   IsClosed s → a ∉ s → Disjoint (nhdsSet s
) (nhds a)
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `TopologicalSpace.isOpen_generateFrom_of_mem`：isOpen_generateFrom_of_mem 
{g : Set (Set α)} {s : Set α} (hs : s in g) : IsOpen[generateFrom g] s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `nhdsSet_empty`：nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥
· 使用定理 `Set.compl_sUnion`：compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '
' S)
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s

--- 原说明 ---
Given a subbasis `s`, it is enough to check the condition of regularity for comp
lements of sets
in `s`.
-/
theorem regularSpace_generateFrom {s : Set (Set X)} (h : ‹_› = generateFrom s) :
    RegularSpace X ↔ ∀ t ∈ s, ∀ a ∈ t, Disjoint (𝓝ˢ tᶜ) (𝓝 a) := by
  refine ⟨fun _ t ht a ha => RegularSpace.regular
    (h ▸ isOpen_generateFrom_of_mem ht).isClosed_compl
    (Set.notMem_compl_iff.mpr ha), fun h' => ⟨fun {t a} ht ha => ?_⟩⟩
  obtain ⟨t, rfl⟩ := compl_involutive.surjective t
  rw [isClosed_compl_iff, h] at ht
  rw [Set.notMem_compl_iff] at ha
  induction ht with
  | basic t ht => exact h' t ht a ha
  | univ => simp
  | inter t₁ t₂ _ _ ih₁ ih₂ => grind [compl_inter, nhdsSet_union, disjoint_sup_left]
  | sUnion S _ ih =>
    obtain ⟨t, ht, ha⟩ := ha
    grw [compl_sUnion, sInter_image, iInter₂_subset t ht]
    exact ih t ht ha

section
variable [RegularSpace X] {x : X} {s : Set X}

/-
**disjoint_nhdsSet_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhdsSet_nhds : Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `regularSpace_TFAE`：regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
 List.TFAE [RegularSpace X, forall (s : Set X) x, x ∉ closure s -> Disjoint (𝓝ˢ 
s) (𝓝 x…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem disjoint_nhdsSet_nhds : Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s := by
  have h := (regularSpace_TFAE X).out 0 2
  exact h.mp ‹_› _ _
/-
**disjoint_nhds_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhds_nhdsSet : Disjoint (𝓝 x) (𝓝ˢ s) ↔ x ∉ closure s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `disjoint_nhdsSet_nhds`：disjoint_nhdsSet_nhds : Disjoint (𝓝ˢ s) (𝓝 x) ↔ x
 ∉ closure s
-/
theorem disjoint_nhds_nhdsSet : Disjoint (𝓝 x) (𝓝ˢ s) ↔ x ∉ closure s :=
  disjoint_comm.trans disjoint_nhdsSet_nhds

/-- A regular space is R₁. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular space is R₁.
-/
instance (priority := 100) : R1Space X where
  specializes_or_disjoint_nhds _ _ := or_iff_not_imp_left.2 fun h ↦ by
    rwa [← nhdsSet_singleton, disjoint_nhdsSet_nhds, ← specializes_iff_mem_closure]
/-
**exists_mem_nhds_isClosed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_nhds_isClosed_subset {x : X} {s : Set X} (h : s in 𝓝 x) : exist
s t in 𝓝 x, IsClosed t ∧ t subseteq s
参数：h : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `regularSpace_TFAE`：regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
 List.TFAE [RegularSpace X, forall (s : Set X) x, x ∉ closure s -> Disjoint (𝓝ˢ 
s) (𝓝 x…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem exists_mem_nhds_isClosed_subset {x : X} {s : Set X} (h : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s := by
  have h' := (regularSpace_TFAE X).out 0 3
  exact h'.mp ‹_› _ _ h
/-
**closed_nhds_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : Set X => s in 𝓝 x ∧ Is
Closed s) id
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `exists_mem_nhds_isClosed_subset`：exists_mem_nhds_isClosed_subset {x : X}
 {s : Set X} (h : s in 𝓝 x) : exists t in 𝓝 x, IsClosed t ∧ t subseteq s
-/
theorem closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsClosed s) id :=
  hasBasis_self.2 fun _ => exists_mem_nhds_isClosed_subset
/-
**lift'_nhds_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace X] (x : X), (nh
ds x).lift' closure = nhds x
参数：x : X；nhds x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.lift'_closure_eq_self`：∀ {X : Type u} [inst : Topologica
lSpace X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBas
is p s → (∀ (i : ι), p i → …
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem lift'_nhds_closure (x : X) : (𝓝 x).lift' closure = 𝓝 x :=
  (closed_nhds_basis x).lift'_closure_eq_self fun _ => And.right
/-
**Filter.HasBasis.nhds_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.nhds_closure {ι : Sort*} {x : X} {p : ι -> Prop} {s : ι ->
 Set X} (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p fun i => closure (s i)
参数：h : (𝓝 x).HasBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s →
 (l.lift' closure).…
· 使用定理 `lift'_nhds_closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Regula
rSpace X] (x : X), (nhds x).lift' closure = nhds x
-/
theorem Filter.HasBasis.nhds_closure {ι : Sort*} {x : X} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p fun i => closure (s i) :=
  lift'_nhds_closure x ▸ h.lift'_closure
/-
**hasBasis_nhds_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_nhds_closure (x : X) : (𝓝 x).HasBasis (fun s => s in 𝓝 x) closure
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.nhds_closure`：Filter.HasBasis.nhds_closure {ι : Sort*} {
x : X} {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasi
s p fun i => closu…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem hasBasis_nhds_closure (x : X) : (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x) closure :=
  (𝓝 x).basis_sets.nhds_closure
/-
**hasBasis_opens_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_opens_closure (x : X) : (𝓝 x).HasBasis (fun s => x in s ∧ IsOpen 
s) closure
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.nhds_closure`：Filter.HasBasis.nhds_closure {ι : Sort*} {
x : X} {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasi
s p fun i => closu…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
-/
theorem hasBasis_opens_closure (x : X) : (𝓝 x).HasBasis (fun s => x ∈ s ∧ IsOpen s) closure :=
  (nhds_basis_opens x).nhds_closure
/-
**IsCompact.exists_isOpen_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isOpen_closure_subset {K U : Set X} (hK : IsCompact K) (h
U : U in 𝓝ˢ K) : exists V, IsOpen V ∧ K subseteq V ∧ closure V subseteq U
参数：hK : IsCompact K；hU : U in 𝓝ˢ K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCompact.disjoint_nhdsSet_left`：IsCompact.disjoint_nhdsSet_left {l : Fi
lter X} (hs : IsCompact s) : Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
-/
theorem IsCompact.exists_isOpen_closure_subset {K U : Set X} (hK : IsCompact K) (hU : U ∈ 𝓝ˢ K) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U := by
  have hd : Disjoint (𝓝ˢ K) (𝓝ˢ Uᶜ) := by
    simpa [hK.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
      ← subset_interior_iff_mem_nhdsSet] using! hU
  rcases ((hasBasis_nhdsSet _).disjoint_iff (hasBasis_nhdsSet _)).1 hd
    with ⟨V, ⟨hVo, hKV⟩, W, ⟨hW, hUW⟩, hVW⟩
  refine ⟨V, hVo, hKV, Subset.trans ?_ (compl_subset_comm.1 hUW)⟩
  exact closure_minimal hVW.subset_compl_right hW.isClosed_compl
/-
**IsCompact.lift'_closure_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace X] {K : Set X},
   IsCompact K → (nhdsSet K).lift' closure = nhdsSet K
参数：nhdsSet K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `IsCompact.exists_isOpen_closure_subset`：IsCompact.exists_isOpen_closure_
subset {K U : Set X} (hK : IsCompact K) (hU : U in 𝓝ˢ K) : exists V, IsOpen V ∧ 
K subseteq V ∧ closure V sub…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `Filter.le_lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X] (l :
 Filter X), l ≤ l.lift' closure
-/
theorem IsCompact.lift'_closure_nhdsSet {K : Set X} (hK : IsCompact K) :
    (𝓝ˢ K).lift' closure = 𝓝ˢ K := by
  refine le_antisymm (fun U hU ↦ ?_) (le_lift'_closure _)
  rcases hK.exists_isOpen_closure_subset hU with ⟨V, hVo, hKV, hVU⟩
  exact mem_of_superset (mem_lift' <| hVo.mem_nhdsSet.2 hKV) hVU
/-
**TopologicalSpace.IsTopologicalBasis.nhds_basis_closure** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：TopologicalSpace.IsTopologicalBasis.nhds_basis_closure {B : Set (Set X)} (
hB : IsTopologicalBasis B) (x : X) : (𝓝 x).HasBasis (fun s : Set X => x in s ∧ s
 in B) closure
参数：Set X；hB : IsTopologicalBasis B；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.nhds_closure`：Filter.HasBasis.nhds_closure {ι : Sort*} {
x : X} {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasi
s p fun i => closu…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.nhds_hasBasis`：∀ {α : Type u} [t : T
opologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis b → 
∀ {a : α}, (nhds a).HasBasis (fun t => …
-/
theorem TopologicalSpace.IsTopologicalBasis.nhds_basis_closure {B : Set (Set X)}
    (hB : IsTopologicalBasis B) (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ s ∈ B) closure := by
  simpa only [and_comm] using hB.nhds_hasBasis.nhds_closure
/-
**TopologicalSpace.IsTopologicalBasis.exists_closure_subset** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：TopologicalSpace.IsTopologicalBasis.exists_closure_subset {B : Set (Set X)
} (hB : IsTopologicalBasis B) {x : X} {s : Set X} (h : s in 𝓝 x) : exists t in B
, x in t ∧ closure t subseteq s
参数：Set X；hB : IsTopologicalBasis B；h : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.nhds_closure`：Filter.HasBasis.nhds_closure {ι : Sort*} {
x : X} {p : ι -> Prop} {s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasi
s p fun i => closu…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.nhds_hasBasis`：∀ {α : Type u} [t : T
opologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis b → 
∀ {a : α}, (nhds a).HasBasis (fun t => …
-/
theorem TopologicalSpace.IsTopologicalBasis.exists_closure_subset {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {x : X} {s : Set X} (h : s ∈ 𝓝 x) :
    ∃ t ∈ B, x ∈ t ∧ closure t ⊆ s := by
  simpa only [exists_prop, and_assoc] using hB.nhds_hasBasis.nhds_closure.mem_iff.mp h
/-
**Topology.IsInducing.regularSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducin
g`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [RegularSpace 
X] [inst_2 : TopologicalSpace Y] {f : Y → X},   Topology.IsInducing f → RegularS
pace Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularSpace.of_hasBasis`：RegularSpace.of_hasBasis {ι : X -> Sort*} {p :
 forall a, ι a -> Prop} {s : forall a, ι a -> Set X} (h₁ : forall a, (𝓝 a).HasBa
sis (p a) (s a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem Topology.IsInducing.regularSpace [TopologicalSpace Y] {f : Y → X}
    (hf : IsInducing f) : RegularSpace Y :=
  .of_hasBasis
    (fun b => by rw [hf.nhds_eq_comap b]; exact (closed_nhds_basis _).comap _)
    fun b s hs => by exact hs.2.preimage hf.continuous
/-
**regularSpace_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：regularSpace_induced (f : Y -> X) : @RegularSpace Y (induced f ‹_›)
参数：f : Y -> X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.regularSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [RegularSpace X] [inst_2 : TopologicalSpace Y] {f : Y → X}
,   Topology.IsInducin…
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f
-/
theorem regularSpace_induced (f : Y → X) : @RegularSpace Y (induced f ‹_›) :=
  letI := induced f ‹_›
  (IsInducing.induced f).regularSpace
/-
**regularSpace_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：regularSpace_sInf {X} {T : Set (TopologicalSpace X)} (h : forall t in T, @
RegularSpace X t) : @RegularSpace X (sInf T)
参数：TopologicalSpace X；h : forall t in T, @RegularSpace X t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_sInf`：nhds_sInf {s : Set (TopologicalSpace α)} {a : α} : @nhds α (s
Inf s) a = ⨅ t in s, @nhds α t a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_subtype''`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_
8} (s : Set ι) (f : ι → α), ⨅ i, f ↑i = ⨅ t ∈ s, f t
· 使用定理 `Filter.HasBasis.iInf`：∀ {α : Type u_1} {ι : Type u_6} {ι' : ι → Type u_7
} {l : ι → Filter α} {p : (i : ι) → ι' i → Prop}   {s : (i : ι) → ι' i → Set α},
   (∀ (i :…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `RegularSpace.of_hasBasis`：RegularSpace.of_hasBasis {ι : X -> Sort*} {p :
 forall a, ι a -> Prop} {s : forall a, ι a -> Set X} (h₁ : forall a, (𝓝 a).HasBa
sis (p a) (s a…
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `IsClosed.mono`：IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ <= t₂) : IsCl
osed[t₁] s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem regularSpace_sInf {X} {T : Set (TopologicalSpace X)} (h : ∀ t ∈ T, @RegularSpace X t) :
    @RegularSpace X (sInf T) := by
  let _ := sInf T
  have : ∀ a, (𝓝 a).HasBasis
      (fun If : Σ I : Set T, I → Set X =>
        If.1.Finite ∧ ∀ i : If.1, If.2 i ∈ @nhds X i a ∧ @IsClosed X i (If.2 i))
      fun If => ⋂ i : If.1, If.snd i := fun a ↦ by
    rw [nhds_sInf, ← iInf_subtype'']
    exact .iInf fun t : T => @closed_nhds_basis X t (h t t.2) a
  refine .of_hasBasis this fun a If hIf => isClosed_iInter fun i => ?_
  exact (hIf.2 i).2.mono (sInf_le (i : T).2)
/-
**regularSpace_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：regularSpace_iInf {ι X} {t : ι -> TopologicalSpace X} (h : forall i, @Regu
larSpace X (t i)) : @RegularSpace X (iInf t)
参数：h : forall i, @RegularSpace X (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `regularSpace_sInf`：regularSpace_sInf {X} {T : Set (TopologicalSpace X)} 
(h : forall t in T, @RegularSpace X t) : @RegularSpace X (sInf T)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem regularSpace_iInf {ι X} {t : ι → TopologicalSpace X} (h : ∀ i, @RegularSpace X (t i)) :
    @RegularSpace X (iInf t) :=
  regularSpace_sInf <| forall_mem_range.mpr h
/-
**RegularSpace.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RegularSpace.inf {X} {t₁ t₂ : TopologicalSpace X} (h₁ : @RegularSpace X t₁
) (h₂ : @RegularSpace X t₂) : @RegularSpace X (t₁ ⊓ t₂)
参数：h₁ : @RegularSpace X t₁；h₂ : @RegularSpace X t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用定理 `regularSpace_iInf`：regularSpace_iInf {ι X} {t : ι -> TopologicalSpace X}
 (h : forall i, @RegularSpace X (t i)) : @RegularSpace X (iInf t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.forall_bool`：∀ {p : Bool → Prop}, (∀ (b : Bool), p b) ↔ p false ∧ p
 true
-/
theorem RegularSpace.inf {X} {t₁ t₂ : TopologicalSpace X} (h₁ : @RegularSpace X t₁)
    (h₂ : @RegularSpace X t₂) : @RegularSpace X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  exact regularSpace_iInf (Bool.forall_bool.2 ⟨h₂, h₁⟩)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : X → Prop} : RegularSpace (Subtype p) :=
  IsEmbedding.subtypeVal.isInducing.regularSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace Y] [RegularSpace Y] : RegularSpace (X × Y) :=
  (regularSpace_induced (@Prod.fst X Y)).inf (regularSpace_induced (@Prod.snd X Y))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, RegularSpace (X i)] :
    RegularSpace (∀ i, X i) :=
  regularSpace_iInf fun _ => regularSpace_induced _

/-- In a regular space, if a compact set and a closed set are disjoint, then they have disjoint
neighborhoods. -/
/-
**SeparatedNhds.of_isCompact_isClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SeparatedNhds.of_isCompact_isClosed {s t : Set X} (hs : IsCompact s) (ht :
 IsClosed t) (hst : Disjoint s t) : SeparatedNhds s t
参数：hs : IsCompact s；ht : IsClosed t；hst : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCompact.disjoint_nhdsSet_left`：IsCompact.disjoint_nhdsSet_left {l : Fi
lter X} (hs : IsCompact s) : Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
In a regular space, if a compact set and a closed set are disjoint, then they ha
ve disjoint
neighborhoods.
-/
lemma SeparatedNhds.of_isCompact_isClosed {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) : SeparatedNhds s t := by
  simpa only [separatedNhds_iff_disjoint, hs.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
    ht.closure_eq, disjoint_left] using hst

end

/-- This technique to witness `HasSeparatingCover` in regular Lindelöf topological spaces
will be used to prove regular Lindelöf spaces are normal. -/
/-
**IsClosed.HasSeparatingCover** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.HasSeparatingCover {s t : Set X} [LindelofSpace X] [RegularSpace 
X] (s_cl : IsClosed s) (t_cl : IsClosed t) (st_dis : Disjoint s t) : HasSeparati
ngCover s t
参数：s_cl : IsClosed s；t_cl : IsClosed t；st_dis : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_eq_empty`：subset_eq_empty {s t : Set α} (h : t subseteq s) (e
 : s = ∅) : t = ∅
· 使用定理 `trivial`：True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty 
α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `hasSeparatingCovers_iff_separatedNhds`：hasSeparatingCovers_iff_separated
Nhds {s t : Set X} : HasSeparatingCover s t ∧ HasSeparatingCover t s ↔ Separated
Nhds s t
· 使用定理 `SeparatedNhds.empty_left`：∀ {X : Type u_1} [inst : TopologicalSpace X] (
s : Set X), SeparatedNhds ∅ s
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `regularSpace_TFAE`：regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
 List.TFAE [RegularSpace X, forall (s : Set X) x, x ∉ closure s -> Disjoint (𝓝ˢ 
s) (𝓝 x…
· 使用定理 `IsClosed.compl_mem_nhds`：IsClosed.compl_mem_nhds (hs : IsClosed s) (hx :
 x ∉ s) : sᶜ in 𝓝 x
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `SeparatedNhds.disjoint_closure_left`：disjoint_closure_left (h : Separate
dNhds s t) : Disjoint (closure s) t
· 使用定理 `IsLindelof.indexed_countable_subcover`：IsLindelof.indexed_countable_subc
over {ι : Type v} [Nonempty ι] (hs : IsLindelof s) (U : ι -> Set X) (hUo : foral
l i, IsOpen (U i)) (hsU : s…
· 使用定理 `IsClosed.isLindelof`：IsClosed.isLindelof [LindelofSpace X] (h : IsClosed
 s) : IsLindelof s
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
This technique to witness `HasSeparatingCover` in regular Lindelöf topological s
paces
will be used to prove regular Lindelöf spaces are normal.
-/
lemma IsClosed.HasSeparatingCover {s t : Set X} [LindelofSpace X] [RegularSpace X]
    (s_cl : IsClosed s) (t_cl : IsClosed t) (st_dis : Disjoint s t) : HasSeparatingCover s t := by
  -- `IsLindelof.indexed_countable_subcover` requires the space be Nonempty
  rcases isEmpty_or_nonempty X with empty_X | nonempty_X
  · rw [subset_eq_empty (t := s) (fun ⦃_⦄ _ ↦ trivial) (univ_eq_empty_iff.mpr empty_X)]
    exact hasSeparatingCovers_iff_separatedNhds.mpr (SeparatedNhds.empty_left t) |>.1
  -- This is almost `HasSeparatingCover`, but is not countable. We define for all `a : X` for use
  -- with `IsLindelof.indexed_countable_subcover` momentarily.
  have (a : X) : ∃ n : Set X, IsOpen n ∧ Disjoint (closure n) t ∧ (a ∈ s → a ∈ n) := by
    wlog ains : a ∈ s
    · exact ⟨∅, isOpen_empty, SeparatedNhds.empty_left t |>.disjoint_closure_left, fun a ↦ ains a⟩
    obtain ⟨n, nna, ncl, nsubkc⟩ := ((regularSpace_TFAE X).out 0 3 :).mp ‹RegularSpace X› a tᶜ <|
      t_cl.compl_mem_nhds (disjoint_left.mp st_dis ains)
    exact
      ⟨interior n,
       isOpen_interior,
       disjoint_left.mpr fun ⦃_⦄ ain ↦
         nsubkc <| (IsClosed.closure_subset_iff ncl).mpr interior_subset ain,
       fun _ ↦ mem_interior_iff_mem_nhds.mpr nna⟩
  -- By Lindelöf, we may obtain a countable subcover witnessing `HasSeparatingCover`
  choose u u_open u_dis u_nhds using this
  obtain ⟨f, f_cov⟩ := s_cl.isLindelof.indexed_countable_subcover
    u u_open (fun a ainh ↦ mem_iUnion.mpr ⟨a, u_nhds a ainh⟩)
  exact ⟨u ∘ f, f_cov, fun n ↦ ⟨u_open (f n), u_dis (f n)⟩⟩

/-- Given two separable points `x` and `y`, we can find neighbourhoods
`x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open,
such that the `Uₖ` are disjoint. -/
/-
**disjoint_nested_nhds_of_not_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nested_nhds_of_not_inseparable [RegularSpace X] {x y : X} (h : ¬I
nseparable x y) : exists U₁ in 𝓝 x, exists V₁ in 𝓝 x, exists U₂ in 𝓝 y, exists V
₂ in 𝓝 y, IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ subseteq U₁ ∧ V
₂ subseteq U₂ ∧ Disjoint U₁ U₂
参数：h : ¬Inseparable x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `r1_separation`：r1_separation {x y : X} (h : ¬Inseparable x y) : exists u
 v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `exists_mem_nhds_isClosed_subset`：exists_mem_nhds_isClosed_subset {x : X}
 {s : Set X} (h : s in 𝓝 x) : exists t in 𝓝 x, IsClosed t ∧ t subseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f

--- 原说明 ---
Given two separable points `x` and `y`, we can find neighbourhoods
`x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open,
such that the `Uₖ` are disjoint.
-/
theorem disjoint_nested_nhds_of_not_inseparable [RegularSpace X] {x y : X} (h : ¬Inseparable x y) :
    ∃ U₁ ∈ 𝓝 x, ∃ V₁ ∈ 𝓝 x, ∃ U₂ ∈ 𝓝 y, ∃ V₂ ∈ 𝓝 y,
      IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ Disjoint U₁ U₂ := by
  rcases r1_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩
  rcases exists_mem_nhds_isClosed_subset (U₁_op.mem_nhds x_in) with ⟨V₁, V₁_in, V₁_closed, h₁⟩
  rcases exists_mem_nhds_isClosed_subset (U₂_op.mem_nhds y_in) with ⟨V₂, V₂_in, V₂_closed, h₂⟩
  exact ⟨U₁, mem_of_superset V₁_in h₁, V₁, V₁_in, U₂, mem_of_superset V₂_in h₂, V₂, V₂_in,
    V₁_closed, V₂_closed, U₁_op, U₂_op, h₁, h₂, H⟩

end RegularSpace

section LocallyCompactRegularSpace

/-- In a (possibly non-Hausdorff) locally compact regular space, for every containment `K ⊆ U` of
  a compact set `K` in an open set `U`, there is a compact closed neighborhood `L`
  such that `K ⊆ L ⊆ U`: equivalently, there is a compact closed set `L` such
  that `K ⊆ interior L` and `L ⊆ U`. -/
/-
**exists_compact_closed_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_compact_closed_between [LocallyCompactSpace X] [RegularSpace X] {K 
U : Set X} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K subseteq U) : exists L, 
IsCompact L ∧ IsClosed L ∧ K subseteq interior L ∧ L subseteq U
参数：hK : IsCompact K；hU : IsOpen U；h_KU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_compact_between`：exists_compact_between [LocallyCompactSpace X] {
K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K subseteq U) : exists L
, IsCompact …
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsCompact.closure_subset_of_isOpen`：IsCompact.closure_subset_of_isOpen {
K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) :
 closure K subseteq U

--- 原说明 ---
In a (possibly non-Hausdorff) locally compact regular space, for every containme
nt `K ⊆ U` of
  a compact set `K` in an open set `U`, there is a compact closed neighborhood `
L`
  such that `K ⊆ L ⊆ U`: equivalently, there is a compact closed set `L` such
  that `K ⊆ interior L` and `L ⊆ U`.
-/
theorem exists_compact_closed_between [LocallyCompactSpace X] [RegularSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K ⊆ U) :
    ∃ L, IsCompact L ∧ IsClosed L ∧ K ⊆ interior L ∧ L ⊆ U :=
  let ⟨L, L_comp, KL, LU⟩ := exists_compact_between hK hU h_KU
  ⟨closure L, L_comp.closure, isClosed_closure, KL.trans <| interior_mono subset_closure,
    L_comp.closure_subset_of_isOpen hU LU⟩

/-- In a (possibly non-Hausdorff) locally compact regular space, for every compact set `K`,
`𝓝ˢ K` has a basis consisting of closed compact sets. -/
/-
**IsCompact.nhdsSet_basis_isCompact_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nhdsSet_basis_isCompact_isClosed [LocallyCompactSpace X] [Regula
rSpace X] {K : Set X} (hK : IsCompact K) : (𝓝ˢ K).HasBasis (fun L => L in 𝓝ˢ K ∧
 IsCompact L ∧ IsClosed L) id
参数：hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `Filter.HasBasis.forall_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {P : Set α → Prop}, 
(∀ ⦃s t : Set α⦄…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `exists_compact_closed_between`：exists_compact_closed_between [LocallyCom
pactSpace X] [RegularSpace X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (
h_KU : K subseteq U…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s

--- 原说明 ---
In a (possibly non-Hausdorff) locally compact regular space, for every compact s
et `K`,
`𝓝ˢ K` has a basis consisting of closed compact sets.
-/
theorem IsCompact.nhdsSet_basis_isCompact_isClosed
    [LocallyCompactSpace X] [RegularSpace X] {K : Set X} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun L ↦ L ∈ 𝓝ˢ K ∧ IsCompact L ∧ IsClosed L) id := by
  rw [hasBasis_self, (hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hL', hKL, hLU⟩ := exists_compact_closed_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], ⟨hL, hL'⟩, hLU⟩

/-- In a locally compact regular space, given a compact set `K` inside an open set `U`, we can find
an open set `V` between these sets with compact closure: `K ⊆ V` and the closure of `V` is
inside `U`. -/
/-
**exists_open_between_and_isCompact_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_open_between_and_isCompact_closure [LocallyCompactSpace X] [Regular
Space X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) :
 exists V, IsOpen V ∧ K subseteq V ∧ closure V subseteq U ∧ IsCompact (closure V
)
参数：hK : IsCompact K；hU : IsOpen U；hKU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_compact_closed_between`：exists_compact_closed_between [LocallyCom
pactSpace X] [RegularSpace X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (
h_KU : K subseteq U…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X

--- 原说明 ---
In a locally compact regular space, given a compact set `K` inside an open set `
U`, we can find
an open set `V` between these sets with compact closure: `K ⊆ V` and the closure
 of `V` is
inside `U`.
-/
theorem exists_open_between_and_isCompact_closure [LocallyCompactSpace X] [RegularSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧ IsCompact (closure V) := by
  rcases exists_compact_closed_between hK hU hKU with ⟨L, L_compact, L_closed, KL, LU⟩
  have A : closure (interior L) ⊆ L := by
    apply (closure_mono interior_subset).trans (le_of_eq L_closed.closure_eq)
  refine ⟨interior L, isOpen_interior, KL, A.trans LU, ?_⟩
  exact L_compact.closure_of_subset interior_subset
/-
**IsCompact.closure_eq_nhdsKer** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.closure_eq_nhdsKer [RegularSpace X] {s : Set X} (hs : IsCompact 
s) : closure s = nhdsKer s
参数：hs : IsCompact s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsKer.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X), 
nhdsKer s = (nhdsSet s).ker
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.lift'_closure_nhdsSet`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] [RegularSpace X] {K : Set X},   IsCompact K → (nhdsSet K).lift' closure = 
nhdsSet K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.ker_iInf`：∀ {ι : Sort u_1} {α : Type u_2} (f : ι → Filter α), (⨅ 
i, f i).ker = ⋂ i, (f i).ker
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Filter.ker_principal`：∀ {α : Type u_2} (s : Set α), (Filter.principal s)
.ker = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Filter.disjoint_iff`：∀ {α : Type u} {f g : Filter α}, Disjoint f g ↔ ∃ s
 ∈ f, ∃ t ∈ g, Disjoint s t
· 使用定理 `disjoint_nhdsSet_nhds`：disjoint_nhdsSet_nhds : Disjoint (𝓝ˢ s) (𝓝 x) ↔ x
 ∉ closure s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
lemma IsCompact.closure_eq_nhdsKer [RegularSpace X] {s : Set X} (hs : IsCompact s) :
    closure s = nhdsKer s := by
  apply subset_antisymm
  · rw [nhdsKer, ← hs.lift'_closure_nhdsSet]
    simp +contextual [Filter.lift', Filter.lift, closure_mono, subset_of_mem_nhdsSet]
  · intro y hy
    by_contra! hy'
    rw [← _root_.disjoint_nhdsSet_nhds, Filter.disjoint_iff] at hy'
    obtain ⟨t, hts, t', ht'y, H⟩ := hy'
    exact Set.disjoint_iff.mp H ⟨hy t hts, mem_of_mem_nhds ht'y⟩

end LocallyCompactRegularSpace

section T25

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of closures
  empty, one containing `x` and the other `y` . -/
/-
**T25Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection o
f closures
  empty, one containing `x` and the other `y` .
-/
class T25Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Given two distinct points in a T₂.₅ space, their filters of closed neighborhoods are
  disjoint. -/
  t2_5 : ∀ ⦃x y : X⦄, x ≠ y → Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure)

@[simp]
/-
**disjoint_lift'_closure_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space X] {x y : X},   Dis
joint ((nhds x).lift' closure) ((nhds y).lift' closure) ↔ x ≠ y
参数：(nhds x).lift' closure；(nhds y).lift' closure。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `T25Space.t2_5`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T25Spa
ce X] ⦃x y : X⦄,   x ≠ y → Disjoint ((nhds x).lift' closure) ((nhds y).lift' clo
sur…
-/
theorem disjoint_lift'_closure_nhds [T25Space X] {x y : X} :
    Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure) ↔ x ≠ y :=
  ⟨fun h hxy => by simp [hxy, nhds_neBot.ne] at h, fun h => T25Space.t2_5 h⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) T25Space.t2Space [T25Space X] : T2Space X :=
  t2Space_iff_disjoint_nhds.2 fun _ _ hne =>
    (disjoint_lift'_closure_nhds.2 hne).mono (le_lift'_closure _) (le_lift'_closure _)
/-
**exists_nhds_disjoint_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nhds_disjoint_closure [T25Space X] {x y : X} (h : x != y) : exists 
s in 𝓝 x, exists t in 𝓝 y, Disjoint (closure s) (closure t)
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `Filter.HasBasis.lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s →
 (l.lift' closure).…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_lift'_closure_nhds`：∀ {X : Type u_1} [inst : TopologicalSpace X
] [T25Space X] {x y : X},   Disjoint ((nhds x).lift' closure) ((nhds y).lift' cl
osure) ↔ x ≠ y
-/
theorem exists_nhds_disjoint_closure [T25Space X] {x y : X} (h : x ≠ y) :
    ∃ s ∈ 𝓝 x, ∃ t ∈ 𝓝 y, Disjoint (closure s) (closure t) :=
  ((𝓝 x).basis_sets.lift'_closure.disjoint_iff (𝓝 y).basis_sets.lift'_closure).1 <|
    disjoint_lift'_closure_nhds.2 h
/-
**exists_open_nhds_disjoint_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_open_nhds_disjoint_closure [T25Space X] {x y : X} (h : x != y) : ex
ists u : Set X, x in u ∧ IsOpen u ∧ exists v : Set X, y in v ∧ IsOpen v ∧ Disjoi
nt (closure u) (closure v)
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `Filter.HasBasis.lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s →
 (l.lift' closure).…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_lift'_closure_nhds`：∀ {X : Type u_1} [inst : TopologicalSpace X
] [T25Space X] {x y : X},   Disjoint ((nhds x).lift' closure) ((nhds y).lift' cl
osure) ↔ x ≠ y
-/
theorem exists_open_nhds_disjoint_closure [T25Space X] {x y : X} (h : x ≠ y) :
    ∃ u : Set X,
      x ∈ u ∧ IsOpen u ∧ ∃ v : Set X, y ∈ v ∧ IsOpen v ∧ Disjoint (closure u) (closure v) := by
  simpa only [exists_prop, and_assoc] using
    ((nhds_basis_opens x).lift'_closure.disjoint_iff (nhds_basis_opens y).lift'_closure).1
      (disjoint_lift'_closure_nhds.2 h)
/-
**T25Space.of_injective_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：T25Space.of_injective_continuous [TopologicalSpace Y] [T25Space Y] {f : X 
-> Y} (hinj : Injective f) (hcont : Continuous f) : T25Space X where t2_5 x y hn
e
参数：hinj : Injective f；hcont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.disjoint`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {la
₁ la₂ : Filter α} {lb₁ lb₂ : Filter β},   Filter.Tendsto f la₁ lb₁ → Disjoint lb
₁ lb₂ → Filte…
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `tendsto_lift'_closure_nhds`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (x
 : X), Filter.Te…
· 使用定理 `T25Space.t2_5`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T25Spa
ce X] ⦃x y : X⦄,   x ≠ y → Disjoint ((nhds x).lift' closure) ((nhds y).lift' clo
sur…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem T25Space.of_injective_continuous [TopologicalSpace Y] [T25Space Y] {f : X → Y}
    (hinj : Injective f) (hcont : Continuous f) : T25Space X where
  t2_5 x y hne := (tendsto_lift'_closure_nhds hcont x).disjoint (t2_5 <| hinj.ne hne)
    (tendsto_lift'_closure_nhds hcont y)
/-
**Topology.IsEmbedding.t25Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.t25Space [TopologicalSpace Y] [T25Space Y] {f : X -> 
Y} (hf : IsEmbedding f) : T25Space X
参数：hf : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T25Space.of_injective_continuous`：T25Space.of_injective_continuous [Topo
logicalSpace Y] [T25Space Y] {f : X -> Y} (hinj : Injective f) (hcont : Continuo
us f) : T25Space X whe…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
-/
theorem Topology.IsEmbedding.t25Space [TopologicalSpace Y] [T25Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T25Space X :=
  .of_injective_continuous hf.injective hf.continuous
/-
**Homeomorph.t25Space** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T25Space X] (h : X ≃ₜ Y),   T25Space Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t25Space`：Topology.IsEmbedding.t25Space [Topologica
lSpace Y] [T25Space Y] {f : X -> Y} (hf : IsEmbedding f) : T25Space X
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
protected theorem Homeomorph.t25Space [TopologicalSpace Y] [T25Space X] (h : X ≃ₜ Y) : T25Space Y :=
  h.symm.isEmbedding.t25Space
/-
**Subtype.instT25Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.instT25Space [T25Space X] {p : X -> Prop} : T25Space {x // p x}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t25Space`：Topology.IsEmbedding.t25Space [Topologica
lSpace Y] [T25Space Y] {f : X -> Y} (hf : IsEmbedding f) : T25Space X
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
instance Subtype.instT25Space [T25Space X] {p : X → Prop} : T25Space {x // p x} :=
  IsEmbedding.subtypeVal.t25Space

end T25

section T3

/-- A T₃ space is a T₀ space which is a regular space. Any T₃ space is a T₁ space, a T₂ space, and
a T₂.₅ space. -/
/-
**T3Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₃ space is a T₀ space which is a regular space. Any T₃ space is a T₁ space, a
 T₂ space, and
a T₂.₅ space.
-/
class T3Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, RegularSpace X
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) instT3Space [T0Space X] [RegularSpace X] : T3Space X := ⟨⟩
/-
**RegularSpace.t3Space_iff_t0Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RegularSpace.t3Space_iff_t0Space [RegularSpace X] : T3Space X ↔ T0Space X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
-/
theorem RegularSpace.t3Space_iff_t0Space [RegularSpace X] : T3Space X ↔ T0Space X := by
  constructor <;> intro <;> infer_instance

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) T3Space.t25Space [T3Space X] : T25Space X := by
  refine ⟨fun x y hne => ?_⟩
  rw [lift'_nhds_closure, lift'_nhds_closure]
  have : x ∉ closure {y} ∨ y ∉ closure {x} :=
    (t0Space_iff_or_notMem_closure X).mp inferInstance hne
  simp only [← disjoint_nhds_nhdsSet, nhdsSet_singleton] at this
  exact this.elim id fun h => h.symm
/-
**Topology.IsEmbedding.t3Space** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T3Space Y] {f : X → Y},   Topology.IsEmbedding f → T3Space X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `Topology.IsInducing.regularSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [RegularSpace X] [inst_2 : TopologicalSpace Y] {f : Y → X}
,   Topology.IsInducin…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
protected theorem Topology.IsEmbedding.t3Space [TopologicalSpace Y] [T3Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T3Space X :=
  { toT0Space := hf.t0Space
    toRegularSpace := hf.isInducing.regularSpace }
/-
**Homeomorph.t3Space** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T3Space X] (h : X ≃ₜ Y),   T3Space Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t3Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T3Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
protected theorem Homeomorph.t3Space [TopologicalSpace Y] [T3Space X] (h : X ≃ₜ Y) : T3Space Y :=
  h.symm.isEmbedding.t3Space
/-
**Subtype.t3Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.t3Space [T3Space X] {p : X -> Prop} : T3Space (Subtype p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t3Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T3Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
instance Subtype.t3Space [T3Space X] {p : X → Prop} : T3Space (Subtype p) :=
  IsEmbedding.subtypeVal.t3Space
/-
**ULift.instT3Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instT3Space [T3Space X] : T3Space (ULift X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t3Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T3Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用引理 `Topology.IsEmbedding.uliftDown`：Topology.IsEmbedding.uliftDown [Topologi
calSpace X] : IsEmbedding (ULift.down : ULift.{v, u} X -> X)
-/
instance ULift.instT3Space [T3Space X] : T3Space (ULift X) :=
  IsEmbedding.uliftDown.t3Space
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace Y] [T3Space X] [T3Space Y] : T3Space (X × Y) := ⟨⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T3Space (X i)] :
    T3Space (∀ i, X i) := ⟨⟩

/-- Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`,
with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint. -/
/-
**disjoint_nested_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nested_nhds [T3Space X] {x y : X} (h : x != y) : exists U₁ in 𝓝 x
, exists V₁ in 𝓝 x, exists U₂ in 𝓝 y, exists V₂ in 𝓝 y, IsClosed V₁ ∧ IsClosed V
₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ subseteq U₁ ∧ V₂ subseteq U₂ ∧ Disjoint U₁ U₂
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_nested_nhds_of_not_inseparable`：disjoint_nested_nhds_of_not_ins
eparable [RegularSpace X] {x y : X} (h : ¬Inseparable x y) : exists U₁ in 𝓝 x, e
xists V₁ in 𝓝 x, exists U₂ in…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X

--- 原说明 ---
Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆
 U₂`,
with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.
-/
theorem disjoint_nested_nhds [T3Space X] {x y : X} (h : x ≠ y) :
    ∃ U₁ ∈ 𝓝 x, ∃ V₁ ∈ 𝓝 x, ∃ U₂ ∈ 𝓝 y, ∃ V₂ ∈ 𝓝 y,
      IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ Disjoint U₁ U₂ :=
  disjoint_nested_nhds_of_not_inseparable (mt Inseparable.eq h)

open SeparationQuotient

/-- The `SeparationQuotient` of a regular space is a T₃ space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SeparationQuotient` of a regular space is a T₃ space.
-/
instance [RegularSpace X] : T3Space (SeparationQuotient X) where
  regular {s a} hs ha := by
    rcases surjective_mk a with ⟨a, rfl⟩
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhds_mk, comap_mk_nhdsSet]
    exact RegularSpace.regular (hs.preimage continuous_mk) ha

end T3

section NormalSpace

/-- A topological space is said to be a *normal space* if any two disjoint closed sets
have disjoint open neighborhoods. -/
/-
**NormalSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is said to be a *normal space* if any two disjoint closed se
ts
have disjoint open neighborhoods.
-/
class NormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two disjoint sets in a normal space admit disjoint neighbourhoods. -/
  normal : ∀ s t : Set X, IsClosed s → IsClosed t → Disjoint s t → SeparatedNhds s t
/-
**normal_separation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：normal_separation [NormalSpace X] {s t : Set X} (H1 : IsClosed s) (H2 : Is
Closed t) (H3 : Disjoint s t) : SeparatedNhds s t
参数：H1 : IsClosed s；H2 : IsClosed t；H3 : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormalSpace.normal`：∀ {X : Type u} {inst : TopologicalSpace X} [self : N
ormalSpace X] (s t : Set X),   IsClosed s → IsClosed t → Disjoint s t → Separate
dNhds s …
-/
theorem normal_separation [NormalSpace X] {s t : Set X} (H1 : IsClosed s) (H2 : IsClosed t)
    (H3 : Disjoint s t) : SeparatedNhds s t :=
  NormalSpace.normal s t H1 H2 H3
/-
**disjoint_nhdsSet_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhdsSet_nhdsSet [NormalSpace X] {s t : Set X} (hs : IsClosed s) (
ht : IsClosed t) (hd : Disjoint s t) : Disjoint (𝓝ˢ s) (𝓝ˢ t)
参数：hs : IsClosed s；ht : IsClosed t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatedNhds.disjoint_nhdsSet`：∀ {X : Type u_1} [inst : TopologicalSpac
e X] {s t : Set X}, SeparatedNhds s t → Disjoint (nhdsSet s) (nhdsSet t)
· 使用定理 `normal_separation`：normal_separation [NormalSpace X] {s t : Set X} (H1 :
 IsClosed s) (H2 : IsClosed t) (H3 : Disjoint s t) : SeparatedNhds s t
-/
theorem disjoint_nhdsSet_nhdsSet [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : Disjoint (𝓝ˢ s) (𝓝ˢ t) :=
  (normal_separation hs ht hd).disjoint_nhdsSet
/-
**normal_exists_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：normal_exists_closure_subset [NormalSpace X] {s t : Set X} (hs : IsClosed 
s) (ht : IsOpen t) (hst : s subseteq t) : exists u, IsOpen u ∧ s subseteq u ∧ cl
osure u subseteq t
参数：hs : IsClosed s；ht : IsOpen t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `normal_separation`：normal_separation [NormalSpace X] {s t : Set X} (H1 :
 IsClosed s) (H2 : IsClosed t) (H3 : Disjoint s t) : SeparatedNhds s t
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
-/
theorem normal_exists_closure_subset [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t)
    (hst : s ⊆ t) : ∃ u, IsOpen u ∧ s ⊆ u ∧ closure u ⊆ t := by
  have : Disjoint s tᶜ := Set.disjoint_left.mpr fun x hxs hxt => hxt (hst hxs)
  rcases normal_separation hs (isClosed_compl_iff.2 ht) this with
    ⟨s', t', hs', ht', hss', htt', hs't'⟩
  refine ⟨s', hs', hss', Subset.trans (closure_minimal ?_ (isClosed_compl_iff.2 ht'))
    (compl_subset_comm.1 htt')⟩
  exact fun x hxs hxt => hs't'.le_bot ⟨hxs, hxt⟩
/-
**exists_mem_nhdsSet_isClosed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_nhdsSet_isClosed_subset [NormalSpace X] {u s : Set X} (h : s in
 𝓝ˢ u) (hu : IsClosed u) : exists t in 𝓝ˢ u, IsClosed t ∧ t subseteq s
参数：h : s in 𝓝ˢ u；hu : IsClosed u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsSet_iff_exists`：mem_nhdsSet_iff_exists : s in 𝓝ˢ t ↔ exists U : 
Set X, IsOpen U ∧ t subseteq U ∧ U subseteq s
· 使用定理 `normal_exists_closure_subset`：normal_exists_closure_subset [NormalSpace 
X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t) (hst : s subseteq t) : exists
 u, IsOpen u ∧ s s…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem exists_mem_nhdsSet_isClosed_subset [NormalSpace X] {u s : Set X} (h : s ∈ 𝓝ˢ u)
    (hu : IsClosed u) : ∃ t ∈ 𝓝ˢ u, IsClosed t ∧ t ⊆ s := by
  obtain ⟨o, ho_open, huo, hos⟩ := mem_nhdsSet_iff_exists.mp h
  obtain ⟨v, hv_open, huv, hcvo⟩ := normal_exists_closure_subset hu ho_open huo
  refine ⟨closure v, ?_, isClosed_closure, hcvo.trans hos⟩
  exact mem_of_superset (mem_nhdsSet_iff_exists.mpr ⟨v, hv_open, huv, subset_rfl⟩) subset_closure
/-
**closed_nhdsSet_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closed_nhdsSet_basis [NormalSpace X] (u : Set X) (hu : IsClosed u) : (𝓝ˢ u
).HasBasis (fun s : Set X => s in 𝓝ˢ u ∧ IsClosed s) id
参数：u : Set X；hu : IsClosed u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `exists_mem_nhdsSet_isClosed_subset`：exists_mem_nhdsSet_isClosed_subset [
NormalSpace X] {u s : Set X} (h : s in 𝓝ˢ u) (hu : IsClosed u) : exists t in 𝓝ˢ 
u, IsClosed t ∧ t subset…
-/
theorem closed_nhdsSet_basis [NormalSpace X] (u : Set X) (hu : IsClosed u) : (𝓝ˢ u).HasBasis
    (fun s : Set X ↦ s ∈ 𝓝ˢ u ∧ IsClosed s) id := by
  refine hasBasis_self.2 fun _ ht ↦ exists_mem_nhdsSet_isClosed_subset ht hu
/-
**lift'_nhdsSet_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [NormalSpace X] (u : Set X), 
  IsClosed u → (nhdsSet u).lift' closure = nhdsSet u
参数：u : Set X；nhdsSet u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.lift'_closure_eq_self`：∀ {X : Type u} [inst : Topologica
lSpace X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBas
is p s → (∀ (i : ι), p i → …
· 使用定理 `closed_nhdsSet_basis`：closed_nhdsSet_basis [NormalSpace X] (u : Set X) (
hu : IsClosed u) : (𝓝ˢ u).HasBasis (fun s : Set X => s in 𝓝ˢ u ∧ IsClosed s) id
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem lift'_nhdsSet_closure [NormalSpace X] (u : Set X) (hu : IsClosed u) :
    (𝓝ˢ u).lift' closure = 𝓝ˢ u :=
  (closed_nhdsSet_basis u hu).lift'_closure_eq_self fun _ ↦ And.right
/-
**Filter.HasBasis.nhdsSet_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.nhdsSet_closure [NormalSpace X] {ι : Sort*} {u : Set X} {p
 : ι -> Prop} {s : ι -> Set X} (hu : IsClosed u) (h : (𝓝ˢ u).HasBasis p s) : (𝓝ˢ
 u).HasBasis p fun i => closure (s i)
参数：hu : IsClosed u；h : (𝓝ˢ u).HasBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s →
 (l.lift' closure).…
· 使用定理 `lift'_nhdsSet_closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Nor
malSpace X] (u : Set X),   IsClosed u → (nhdsSet u).lift' closure = nhdsSet u
-/
theorem Filter.HasBasis.nhdsSet_closure [NormalSpace X] {ι : Sort*} {u : Set X} {p : ι → Prop}
    {s : ι → Set X} (hu : IsClosed u) (h : (𝓝ˢ u).HasBasis p s) :
    (𝓝ˢ u).HasBasis p fun i ↦ closure (s i) :=
  lift'_nhdsSet_closure u hu ▸ h.lift'_closure
/-
**hasBasis_nhdsSet_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_nhdsSet_closure [NormalSpace X] (u : Set X) (hu : IsClosed u) : (
𝓝ˢ u).HasBasis (fun s => s in 𝓝ˢ u) closure
参数：u : Set X；hu : IsClosed u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.nhdsSet_closure`：Filter.HasBasis.nhdsSet_closure [Normal
Space X] {ι : Sort*} {u : Set X} {p : ι -> Prop} {s : ι -> Set X} (hu : IsClosed
 u) (h : (𝓝ˢ u).HasBa…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem hasBasis_nhdsSet_closure [NormalSpace X] (u : Set X) (hu : IsClosed u) :
    (𝓝ˢ u).HasBasis (fun s => s ∈ 𝓝ˢ u) closure :=
  (𝓝ˢ u).basis_sets.nhdsSet_closure hu

/-- If the codomain of a closed embedding is a normal space, then so is the domain. -/
/-
**Topology.IsClosedEmbedding.normalSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsC
losedEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [NormalSpace Y] {f : X → Y},   Topology.IsClosedEmbedding f → No
rmalSpace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormalSpace.normal`：∀ {X : Type u} {inst : TopologicalSpace X} [self : N
ormalSpace X] (s t : Set X),   IsClosed s → IsClosed t → Disjoint s t → Separate
dNhds s …
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `Set.disjoint_image_of_injective`：disjoint_image_of_injective (hf : Injec
tive f) {s t : Set α} (hd : Disjoint s t) : Disjoint (f '' s) (f '' t)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `SeparatedNhds.mono`：mono (h : SeparatedNhds s₂ t₂) (hs : s₁ subseteq s₂)
 (ht : t₁ subseteq t₂) : SeparatedNhds s₁ t₁
· 使用定理 `SeparatedNhds.preimage`：preimage [TopologicalSpace Y] {f : X -> Y} {s t 
: Set Y} (h : SeparatedNhds s t) (hf : Continuous f) : SeparatedNhds (f ⁻¹' s) (
f ⁻¹' t)
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
If the codomain of a closed embedding is a normal space, then so is the domain.
-/
protected theorem Topology.IsClosedEmbedding.normalSpace [TopologicalSpace Y] [NormalSpace Y]
    {f : X → Y} (hf : IsClosedEmbedding f) : NormalSpace X where
  normal s t hs ht hst := by
    have H : SeparatedNhds (f '' s) (f '' t) :=
      NormalSpace.normal (f '' s) (f '' t) (hf.isClosedMap s hs) (hf.isClosedMap t ht)
        (disjoint_image_of_injective hf.injective hst)
    exact (H.preimage hf.continuous).mono (subset_preimage_image _ _) (subset_preimage_image _ _)
/-
**Homeomorph.normalSpace** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [NormalSpace X] (h : X ≃ₜ Y),   NormalSpace Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.normalSpace`：∀ {X : Type u_1} {Y : Type u_2} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [NormalSpace Y] {f : X
 → Y},   Topology.IsClosedEm…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
protected theorem Homeomorph.normalSpace [TopologicalSpace Y] [NormalSpace X] (h : X ≃ₜ Y) :
    NormalSpace Y :=
  h.symm.isClosedEmbedding.normalSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormalSpace.of_compactSpace_r1Space [CompactSpace X] [R1Space X] :
    NormalSpace X where
  normal _s _t hs ht := .of_isCompact_isCompact_isClosed hs.isCompact ht.isCompact ht

/-- A regular topological space with a Lindelöf topology is a normal space. A consequence of e.g.
Corollaries 20.8 and 20.10 of [Willard's *General Topology*][zbMATH02107988] (without the
assumption of Hausdorff). -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular topological space with a Lindelöf topology is a normal space. A conseq
uence of e.g.
Corollaries 20.8 and 20.10 of [Willard's *General Topology*][zbMATH02107988] (wi
thout the
assumption of Hausdorff).
-/
instance (priority := 100) NormalSpace.of_regularSpace_lindelofSpace
    [RegularSpace X] [LindelofSpace X] : NormalSpace X where
  normal _ _ hcl kcl hkdis :=
    hasSeparatingCovers_iff_separatedNhds.mp
    ⟨hcl.HasSeparatingCover kcl hkdis, kcl.HasSeparatingCover hcl (Disjoint.symm hkdis)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormalSpace.of_regularSpace_secondCountableTopology
    [RegularSpace X] [SecondCountableTopology X] : NormalSpace X :=
  of_regularSpace_lindelofSpace

end NormalSpace

section Normality

/-- A T₄ space is a normal T₁ space. -/
/-
**T4Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₄ space is a normal T₁ space.
-/
class T4Space (X : Type u) [TopologicalSpace X] : Prop extends T1Space X, NormalSpace X
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [T1Space X] [NormalSpace X] : T4Space X := ⟨⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) T4Space.t3Space [T4Space X] : T3Space X where
  regular hs hxs := by simpa only [nhdsSet_singleton] using (normal_separation hs isClosed_singleton
    (disjoint_singleton_right.mpr hxs)).disjoint_nhdsSet

/-- If the codomain of a closed embedding is a T₄ space, then so is the domain. -/
/-
**Topology.IsClosedEmbedding.t4Space** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsClose
dEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T4Space Y] {f : X → Y},   Topology.IsClosedEmbedding f → T4Spac
e X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T1Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `T4Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T4
Space X], T1Space X
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `Topology.IsClosedEmbedding.normalSpace`：∀ {X : Type u_1} {Y : Type u_2} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [NormalSpace Y] {f : X
 → Y},   Topology.IsClosedEm…
· 使用定理 `T4Space.toNormalSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self 
: T4Space X], NormalSpace X

--- 原说明 ---
If the codomain of a closed embedding is a T₄ space, then so is the domain.
-/
protected theorem Topology.IsClosedEmbedding.t4Space [TopologicalSpace Y] [T4Space Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : T4Space X where
  toT1Space := hf.isEmbedding.t1Space
  toNormalSpace := hf.normalSpace
/-
**Homeomorph.t4Space** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T4Space X] (h : X ≃ₜ Y),   T4Space Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.t4Space`：∀ {X : Type u_1} {Y : Type u_2} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [T4Space Y] {f : X → Y},  
 Topology.IsClosedEmbedd…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
protected theorem Homeomorph.t4Space [TopologicalSpace Y] [T4Space X] (h : X ≃ₜ Y) : T4Space Y :=
  h.symm.isClosedEmbedding.t4Space
/-
**ULift.instT4Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instT4Space [T4Space X] : T4Space (ULift X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.t4Space`：∀ {X : Type u_1} {Y : Type u_2} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [T4Space Y] {f : X → Y},  
 Topology.IsClosedEmbedd…
· 使用引理 `Topology.IsClosedEmbedding.uliftDown`：Topology.IsClosedEmbedding.uliftDo
wn [TopologicalSpace X] : IsClosedEmbedding (ULift.down : ULift.{v, u} X -> X)
-/
instance ULift.instT4Space [T4Space X] : T4Space (ULift X) := IsClosedEmbedding.uliftDown.t4Space

namespace SeparationQuotient

/-- The `SeparationQuotient` of a normal space is a normal space. -/
/-
**SeparationQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `SeparationQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SeparationQuotient` of a normal space is a normal space.
-/
instance [NormalSpace X] : NormalSpace (SeparationQuotient X) where
  normal s t hs ht hd := separatedNhds_iff_disjoint.2 <| by
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhdsSet, comap_mk_nhdsSet]
    exact disjoint_nhdsSet_nhdsSet (hs.preimage continuous_mk) (ht.preimage continuous_mk)
      (hd.preimage mk)

end SeparationQuotient

end Normality

section CompletelyNormal

/-- A topological space `X` is a *completely normal space* provided that for any two sets `s`, `t`
such that if both `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`,
then there exist disjoint neighbourhoods of `s` and `t`. -/
/-
**CompletelyNormalSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space `X` is a *completely normal space* provided that for any two
 sets `s`, `t`
such that if both `closure s` is disjoint with `t`, and `s` is disjoint with `cl
osure t`,
then there exist disjoint neighbourhoods of `s` and `t`.
-/
class CompletelyNormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`, then `s` and `t`
  admit disjoint neighbourhoods. -/
  completely_normal :
    ∀ ⦃s t : Set X⦄, Disjoint (closure s) t → Disjoint s (closure t) → Disjoint (𝓝ˢ s) (𝓝ˢ t)

export CompletelyNormalSpace (completely_normal)

-- see Note [lower instance priority]
/-- A completely normal space is a normal space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A completely normal space is a normal space.
-/
instance (priority := 100) CompletelyNormalSpace.toNormalSpace
    [CompletelyNormalSpace X] : NormalSpace X where
  normal s t hs ht hd := separatedNhds_iff_disjoint.2 <|
    completely_normal (by rwa [hs.closure_eq]) (by rwa [ht.closure_eq])
/-
**Topology.IsInducing.completelyNormalSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.completelyNormalSpace [TopologicalSpace Y] [Completely
NormalSpace Y] {e : X -> Y} (he : IsInducing e) : CompletelyNormalSpace X
参数：he : IsInducing e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.nhdsSet_eq_comap`：nhdsSet_eq_comap (hf : IsInducing 
f) (s : Set X) : 𝓝ˢ s = comap f (𝓝ˢ (f '' s))
· 使用定理 `Filter.disjoint_comap`：disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (c
omap m g₁) (comap m g₂)
· 使用定理 `CompletelyNormalSpace.completely_normal`：∀ {X : Type u} {inst : Topologi
calSpace X} [self : CompletelyNormalSpace X] ⦃s t : Set X⦄,   Disjoint (closure 
s) t → Disjoint s (closure t)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.subset_compl_iff_disjoint_left`：subset_compl_iff_disjoint_left : s s
ubseteq tᶜ ↔ Disjoint t s
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
-/
theorem Topology.IsInducing.completelyNormalSpace [TopologicalSpace Y] [CompletelyNormalSpace Y]
    {e : X → Y} (he : IsInducing e) : CompletelyNormalSpace X := by
  refine ⟨fun s t hd₁ hd₂ => ?_⟩
  simp only [he.nhdsSet_eq_comap]
  refine disjoint_comap (completely_normal ?_ ?_)
  · rwa [← subset_compl_iff_disjoint_left, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_left]
  · rwa [← subset_compl_iff_disjoint_right, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_right]

/-- A subspace of a completely normal space is a completely normal space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subspace of a completely normal space is a completely normal space.
-/
instance [CompletelyNormalSpace X] {p : X → Prop} : CompletelyNormalSpace { x // p x } :=
  IsEmbedding.subtypeVal.completelyNormalSpace
/-
**ULift.instCompletelyNormalSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instCompletelyNormalSpace [CompletelyNormalSpace X] : CompletelyNorm
alSpace (ULift X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.completelyNormalSpace`：Topology.IsInducing.completel
yNormalSpace [TopologicalSpace Y] [CompletelyNormalSpace Y] {e : X -> Y} (he : I
sInducing e) : CompletelyNormal…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用引理 `Topology.IsEmbedding.uliftDown`：Topology.IsEmbedding.uliftDown [Topologi
calSpace X] : IsEmbedding (ULift.down : ULift.{v, u} X -> X)
-/
instance ULift.instCompletelyNormalSpace [CompletelyNormalSpace X] :
    CompletelyNormalSpace (ULift X) :=
  IsEmbedding.uliftDown.completelyNormalSpace

/--
A space is completely normal iff all open subspaces are normal.
-/
/-
**completelyNormalSpace_iff_forall_isOpen_normalSpace** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：completelyNormalSpace_iff_forall_isOpen_normalSpace : CompletelyNormalSpac
e X ↔ forall s : Set X, IsOpen s -> NormalSpace s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `instCompletelyNormalSpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSp
ace X] [CompletelyNormalSpace X] {p : X → Prop},   CompletelyNormalSpace { x // 
p x }
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `normal_separation`：normal_separation [NormalSpace X] {s t : Set X} (H1 :
 IsClosed s) (H2 : IsClosed t) (H3 : Disjoint s t) : SeparatedNhds s t
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `separatedNhds_iff_disjoint`：separatedNhds_iff_disjoint {s t : Set X} : S
eparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t)
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `Subtype.preimage_val_subset_preimage_val_iff`：preimage_val_subset_preima
ge_val_iff (s t u : Set α) : (Subtype.val ⁻¹' t : Set s) subseteq Subtype.val ⁻¹
' u ↔ s inter t subseteq s inter u
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Disjoint.notMem_of_mem_left`：∀ {α : Type u} {s t : Set α}, Disjoint s t 
→ ∀ ⦃a : α⦄, a ∈ s → a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A space is completely normal iff all open subspaces are normal.
-/
theorem completelyNormalSpace_iff_forall_isOpen_normalSpace :
    CompletelyNormalSpace X ↔ ∀ s : Set X, IsOpen s → NormalSpace s := by
  refine ⟨fun _ _ _ => inferInstance, fun h => ⟨fun s t hSt hsT => ?_⟩⟩
  let e := (closure s ∩ closure t)ᶜ
  have he : IsOpen e := (isClosed_closure.inter isClosed_closure).isOpen_compl
  specialize h e he
  have hst : Disjoint (((↑) : e → X) ⁻¹' closure s) (((↑) : e → X) ⁻¹' closure t) := by
    rw [disjoint_left]
    intro x hxs hxt
    exact x.2 ⟨hxs, hxt⟩
  obtain ⟨U, V, hU, hV, hsU, htV, hUV⟩ := normal_separation
    (isClosed_closure.preimage continuous_subtype_val)
    (isClosed_closure.preimage continuous_subtype_val) hst
  rw [Topology.IsInducing.subtypeVal.isOpen_iff] at hU hV
  obtain ⟨U, hU, rfl⟩ := hU
  obtain ⟨V, hV, rfl⟩ := hV
  rw [← separatedNhds_iff_disjoint]
  rw [Subtype.preimage_val_subset_preimage_val_iff, inter_comm e, inter_comm e] at hsU htV
  refine ⟨U ∩ e, V ∩ e, hU.inter he, hV.inter he, ?_, ?_, ?_⟩
  · intro x hx
    exact hsU ⟨subset_closure hx, fun h => hsT.notMem_of_mem_left hx h.2⟩
  · intro x hx
    exact htV ⟨subset_closure hx, fun h => hSt.notMem_of_mem_left h.1 hx⟩
  · rw [disjoint_left] at hUV ⊢
    intro x hxU hxV
    exact @hUV ⟨x, hxU.2⟩ hxU.1 hxV.1

/--
A space is completely normal iff it is hereditarily normal.
-/
/-
**completelyNormalSpace_iff_forall_normalSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completelyNormalSpace_iff_forall_normalSpace : CompletelyNormalSpace X ↔ f
orall s : Set X, NormalSpace s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `instCompletelyNormalSpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSp
ace X] [CompletelyNormalSpace X] {p : X → Prop},   CompletelyNormalSpace { x // 
p x }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `completelyNormalSpace_iff_forall_isOpen_normalSpace`：completelyNormalSpa
ce_iff_forall_isOpen_normalSpace : CompletelyNormalSpace X ↔ forall s : Set X, I
sOpen s -> NormalSpace s

--- 原说明 ---
A space is completely normal iff it is hereditarily normal.
-/
theorem completelyNormalSpace_iff_forall_normalSpace :
    CompletelyNormalSpace X ↔ ∀ s : Set X, NormalSpace s :=
  ⟨fun _ _ => inferInstance, fun h =>
    completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s _ => h s⟩

alias ⟨_, CompletelyNormalSpace.of_forall_isOpen_normalSpace⟩ :=
  completelyNormalSpace_iff_forall_isOpen_normalSpace
alias ⟨_, CompletelyNormalSpace.of_forall_normalSpace⟩ :=
  completelyNormalSpace_iff_forall_normalSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompletelyNormalSpace.of_regularSpace_secondCountableTopology
    [RegularSpace X] [SecondCountableTopology X] : CompletelyNormalSpace X :=
  .of_forall_normalSpace fun _ => .of_regularSpace_secondCountableTopology

/-- A T₅ space is a completely normal T₁ space. -/
/-
**T5Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₅ space is a completely normal T₁ space.
-/
class T5Space (X : Type u) [TopologicalSpace X] : Prop extends T1Space X, CompletelyNormalSpace X
/-
**Topology.IsEmbedding.t5Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.t5Space [TopologicalSpace Y] [T5Space Y] {e : X -> Y}
 (he : IsEmbedding e) : T5Space X where toCompletelyNormalSpace
参数：he : IsEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T1Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `Topology.IsInducing.completelyNormalSpace`：Topology.IsInducing.completel
yNormalSpace [TopologicalSpace Y] [CompletelyNormalSpace Y] {e : X -> Y} (he : I
sInducing e) : CompletelyNormal…
· 使用定理 `T5Space.toCompletelyNormalSpace`：∀ {X : Type u} {inst : TopologicalSpace
 X} [self : T5Space X], CompletelyNormalSpace X
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
-/
theorem Topology.IsEmbedding.t5Space [TopologicalSpace Y] [T5Space Y] {e : X → Y}
    (he : IsEmbedding e) : T5Space X where
  toCompletelyNormalSpace := he.completelyNormalSpace
  toT1Space := he.t1Space
/-
**Homeomorph.t5Space** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T5Space X] (h : X ≃ₜ Y),   T5Space Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t5Space`：Topology.IsEmbedding.t5Space [TopologicalS
pace Y] [T5Space Y] {e : X -> Y} (he : IsEmbedding e) : T5Space X where toComple
telyNormalSpace
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
protected theorem Homeomorph.t5Space [TopologicalSpace Y] [T5Space X] (h : X ≃ₜ Y) : T5Space Y :=
  h.symm.isClosedEmbedding.t5Space

-- see Note [lower instance priority]
/-- A `T₅` space is a `T₄` space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `T₅` space is a `T₄` space.
-/
instance (priority := 100) T5Space.toT4Space [T5Space X] : T4Space X where
  -- follows from type-class inference

/-- A subspace of a T₅ space is a T₅ space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subspace of a T₅ space is a T₅ space.
-/
instance [T5Space X] {p : X → Prop} : T5Space { x // p x } :=
  IsEmbedding.subtypeVal.t5Space
/-
**ULift.instT5Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instT5Space [T5Space X] : T5Space (ULift X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t5Space`：Topology.IsEmbedding.t5Space [TopologicalS
pace Y] [T5Space Y] {e : X -> Y} (he : IsEmbedding e) : T5Space X where toComple
telyNormalSpace
· 使用引理 `Topology.IsEmbedding.uliftDown`：Topology.IsEmbedding.uliftDown [Topologi
calSpace X] : IsEmbedding (ULift.down : ULift.{v, u} X -> X)
-/
instance ULift.instT5Space [T5Space X] : T5Space (ULift X) :=
  IsEmbedding.uliftDown.t5Space

/--
A space is a `T5Space` iff all its open subspaces are `T4Space`.
-/
/-
**t5Space_iff_forall_isOpen_t4Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t5Space_iff_forall_isOpen_t4Space : T5Space X ↔ forall s : Set X, IsOpen s
 -> T4Space s where mp _ _ _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `instT5SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Spac
e X] {p : X → Prop}, T5Space { x // p x }
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `t1Space_of_injective_of_continuous`：t1Space_of_injective_of_continuous [
TopologicalSpace Y] {f : X -> Y} (hf : Function.Injective f) (hf' : Continuous f
) [T1Space Y] : T1Space …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `T4Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T4
Space X], T1Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `completelyNormalSpace_iff_forall_isOpen_normalSpace`：completelyNormalSpa
ce_iff_forall_isOpen_normalSpace : CompletelyNormalSpace X ↔ forall s : Set X, I
sOpen s -> NormalSpace s
· 使用定理 `T4Space.toNormalSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self 
: T4Space X], NormalSpace X

--- 原说明 ---
A space is a `T5Space` iff all its open subspaces are `T4Space`.
-/
theorem t5Space_iff_forall_isOpen_t4Space :
    T5Space X ↔ ∀ s : Set X, IsOpen s → T4Space s where
  mp _ _ _ := inferInstance
  mpr h :=
    { toCompletelyNormalSpace :=
        completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s hs => (h s hs).toNormalSpace
      toT1Space :=
        have := h univ isOpen_univ
        t1Space_of_injective_of_continuous
          (fun _ _ => congrArg Subtype.val) (continuous_id.subtype_mk mem_univ) }

/--
A space is `T5Space` iff it is hereditarily `T4Space`.
-/
/-
**t5Space_iff_forall_t4Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t5Space_iff_forall_t4Space : T5Space X ↔ forall s : Set X, T4Space s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `instT5SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Spac
e X] {p : X → Prop}, T5Space { x // p x }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `t5Space_iff_forall_isOpen_t4Space`：t5Space_iff_forall_isOpen_t4Space : T
5Space X ↔ forall s : Set X, IsOpen s -> T4Space s where mp _ _ _

--- 原说明 ---
A space is `T5Space` iff it is hereditarily `T4Space`.
-/
theorem t5Space_iff_forall_t4Space :
    T5Space X ↔ ∀ s : Set X, T4Space s :=
  ⟨fun _ _ => inferInstance, fun h => t5Space_iff_forall_isOpen_t4Space.2 fun s _ => h s⟩

alias ⟨_, T5Space.of_forall_isOpen_t4Space⟩ := t5Space_iff_forall_isOpen_t4Space
alias ⟨_, T5Space.of_forall_t4Space⟩ := t5Space_iff_forall_t4Space

open SeparationQuotient

/-- The `SeparationQuotient` of a completely normal R₀ space is a T₅ space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SeparationQuotient` of a completely normal R₀ space is a T₅ space.
-/
instance [CompletelyNormalSpace X] [R0Space X] : T5Space (SeparationQuotient X) where
  t1 := by
    rwa [((t1Space_TFAE (SeparationQuotient X)).out 1 0 :), SeparationQuotient.t1Space_iff]
  completely_normal s t hd₁ hd₂ := by
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhdsSet, comap_mk_nhdsSet]
    apply completely_normal <;> rw [← preimage_mk_closure]
    exacts [hd₁.preimage mk, hd₂.preimage mk]

end CompletelyNormal

/-- In a compact T₂ space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
/-
**connectedComponent_eq_iInter_isClopen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_eq_iInter_isClopen [T2Space X] [CompactSpace X] (x : X)
 : connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x in s }, s
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `connectedComponent_subset_iInter_isClopen`：connectedComponent_subset_iIn
ter_isClopen {x : α} : connectedComponent x subseteq ⋂ Z : { Z : Set α // IsClop
en Z ∧ x in Z }, Z
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPreconnected_iff_subset_of_fully_disjoint_closed`：isPreconnected_iff_s
ubset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) : IsPreconnected s 
↔ forall u v, IsClosed u -> IsClosed v -…
· 使用定理 `normal_separation`：normal_separation [NormalSpace X] {s t : Set X} (H1 :
 IsClosed s) (H2 : IsClosed t) (H3 : Disjoint s t) : SeparatedNhds s t
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `IsCompact.inter_iInter_nonempty`：IsCompact.inter_iInter_nonempty {ι : Ty
pe v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst 
: forall u : Finset ι…
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_compl_left_iff_subset`：disjoint_compl_left_iff_subset : Dis
joint sᶜ t ↔ t subseteq s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `isClopen_biInter_finset`：isClopen_biInter_finset {Y} {s : Finset Y} {f :
 Y -> Set X} (h : forall i in s, IsClopen (f i)) : IsClopen (⋂ i in s, f i)
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
In a compact T₂ space, the connected component of a point equals the intersectio
n of all
its clopen neighbourhoods.
-/
theorem connectedComponent_eq_iInter_isClopen [T2Space X] [CompactSpace X] (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s := by
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  -- Reduce to showing that the clopen intersection is connected.
  refine IsPreconnected.subset_connectedComponent ?_ (mem_iInter.2 fun s => s.2.2)
  -- We do this by showing that any disjoint cover by two closed sets implies
  -- that one of these closed sets must contain our whole thing.
  -- To reduce to the case where the cover is disjoint on all of `X` we need that `s` is closed
  have hs : @IsClosed X _ (⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s) :=
    isClosed_iInter fun s => s.2.1.1
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hs]
  intro a b ha hb hab ab_disj
  -- Since our space is normal, we get two larger disjoint open sets containing the disjoint
  -- closed sets. If we can show that our intersection is a subset of any of these we can then
  -- "descend" this to show that it is a subset of either a or b.
  rcases normal_separation ha hb ab_disj with ⟨u, v, hu, hv, hau, hbv, huv⟩
  obtain ⟨s, H⟩ : ∃ s : Set X, IsClopen s ∧ x ∈ s ∧ s ⊆ u ∪ v := by
    /- Now we find a clopen set `s` around `x`, contained in `u ∪ v`. We utilize the fact that
    `X \ u ∪ v` will be compact, so there must be some finite intersection of clopen neighbourhoods
    of `X` disjoint to it, but a finite intersection of clopen sets is clopen,
    so we let this be our `s`. -/
    have H1 := (hu.union hv).isClosed_compl.isCompact.inter_iInter_nonempty
      (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s) fun s => s.2.1.1
    rw [← not_disjoint_iff_nonempty_inter, imp_not_comm, not_forall] at H1
    obtain ⟨si, H2⟩ :=
      H1 (disjoint_compl_left_iff_subset.2 <| hab.trans <| union_subset_union hau hbv)
    refine ⟨⋂ U ∈ si, Subtype.val U, ?_, ?_, ?_⟩
    · exact isClopen_biInter_finset fun s _ => s.2.1
    · exact mem_iInter₂.2 fun s _ => s.2.2
    · rwa [← disjoint_compl_left_iff_subset, disjoint_iff_inter_eq_empty,
        ← not_nonempty_iff_eq_empty]
  -- So, we get a disjoint decomposition `s = s ∩ u ∪ s ∩ v` of clopen sets. The intersection of all
  -- clopen neighbourhoods will then lie in whichever of u or v x lies in and hence will be a subset
  -- of either a or b.
  · have H1 := isClopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv
    rw [union_comm] at H
    have H2 := isClopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu huv.symm
    by_cases hxu : x ∈ u <;> [left; right]
    -- The x ∈ u case.
    · suffices ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, ↑s ⊆ u
        from Disjoint.left_le_of_le_sup_right hab (huv.mono this hbv)
      · apply Subset.trans _ s.inter_subset_right
        exact iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s.1)
          ⟨s ∩ u, H1, mem_inter H.2.1 hxu⟩
    -- If x ∉ u, we get x ∈ v since x ∈ u ∪ v. The rest is then like the x ∈ u case.
    · have h1 : x ∈ v :=
        (hab.trans (union_subset_union hau hbv) (mem_iInter.2 fun i => i.2.2)).resolve_left hxu
      suffices ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, ↑s ⊆ v
        from (huv.symm.mono this hau).left_le_of_le_sup_left hab
      · refine Subset.trans ?_ s.inter_subset_right
        exact iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s.1)
          ⟨s ∩ v, H2, mem_inter H.2.1 h1⟩

/-- `ConnectedComponents X` is Hausdorff when `X` is Hausdorff and compact -/
@[stacks 0900 "The Stacks entry proves profiniteness."]
/-
**ConnectedComponents.t2** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ConnectedComponents.t2 [T2Space X] [CompactSpace X] : T2Space (ConnectedCo
mponents X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₂`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f → ∀ {p : β → β → Prop}, (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (
x₁ x₂ : α), p (f …
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
· 使用定理 `connectedComponent_disjoint`：connectedComponent_disjoint {x y : α} (h : 
connectedComponent x != connectedComponent y) : Disjoint (connectedComponent x) 
(connectedCompone…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConnectedComponents.coe_ne_coe`：coe_ne_coe {x y : α} : (x : ConnectedCom
ponents α) != y ↔ connectedComponent x != connectedComponent y
· 使用定理 `IsCompact.elim_finite_subfamily_closed`：IsCompact.elim_finite_subfamily_
closed {ι : Type v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClose
d (t i)) (hst : (s inter ⋂ i…
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `isClosed_connectedComponent`：isClosed_connectedComponent {x : α} : IsClo
sed (connectedComponent x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `connectedComponent_eq_iInter_isClopen`：connectedComponent_eq_iInter_isCl
open [T2Space X] [CompactSpace X] (x : X) : connectedComponent x = ⋂ s : { s : S
et X // IsClopen s ∧ x in s…
· 使用定理 `isClopen_biInter_finset`：isClopen_biInter_finset {Y} {s : Finset Y} {f :
 Y -> Set X} (h : forall i in s, IsClopen (f i)) : IsClopen (⋂ i in s, f i)
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用定理 `IsClopen.connectedComponent_subset`：IsClopen.connectedComponent_subset {
x} (hs : IsClopen s) (hx : x in s) : connectedComponent x subseteq s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsClopen.biUnion_connectedComponent_eq`：IsClopen.biUnion_connectedCompon
ent_eq {Z : Set α} (h : IsClopen Z) : ⋃ x in Z, connectedComponent x = Z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `connectedComponents_preimage_image`：connectedComponents_preimage_image (
U : Set α) : (↑) ⁻¹' ((↑) '' U : Set (ConnectedComponents α)) = ⋃ x in U, connec
tedComponent x
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
· 使用定理 `Topology.IsQuotientMap.isClopen_preimage`：∀ {X : Type u} {Y : Type v} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.
IsQuotientMap f → ∀ {s : Set Y…
· 使用定理 `ConnectedComponents.isQuotientMap_coe`：isQuotientMap_coe : IsQuotientMap
 (mk : α -> ConnectedComponents α)
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a

--- 原说明 ---
`ConnectedComponents X` is Hausdorff when `X` is Hausdorff and compact
-/
instance ConnectedComponents.t2 [T2Space X] [CompactSpace X] : T2Space (ConnectedComponents X) := by
  -- Fix 2 distinct connected components, with points a and b
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b ne => ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at ne
  have h := connectedComponent_disjoint ne
  -- write ↑b as the intersection of all clopen subsets containing it
  rw [connectedComponent_eq_iInter_isClopen b, disjoint_iff_inter_eq_empty] at h
  -- Now we show that this can be reduced to some clopen containing `↑b` being disjoint to `↑a`
  obtain ⟨U, V, hU, ha, hb, rfl⟩ : ∃ (U : Set X) (V : Set (ConnectedComponents X)),
      IsClopen U ∧ connectedComponent a ∩ U = ∅ ∧ connectedComponent b ⊆ U ∧ (↑) ⁻¹' V = U := by
    have h :=
      (isClosed_connectedComponent (α := X)).isCompact.elim_finite_subfamily_closed
        _ (fun s : { s : Set X // IsClopen s ∧ b ∈ s } => s.2.1.1) h
    obtain ⟨fin_a, ha⟩ := h
    -- This clopen and its complement will separate the connected components of `a` and `b`
    set U : Set X := ⋂ (i : { s // IsClopen s ∧ b ∈ s }) (_ : i ∈ fin_a), i
    have hU : IsClopen U := isClopen_biInter_finset fun i _ => i.2.1
    exact ⟨U, (↑) '' U, hU, ha, subset_iInter₂ fun s _ => s.2.1.connectedComponent_subset s.2.2,
      (connectedComponents_preimage_image U).symm ▸ hU.biUnion_connectedComponent_eq⟩
  rw [ConnectedComponents.isQuotientMap_coe.isClopen_preimage] at hU
  refine ⟨Vᶜ, V, hU.compl.isOpen, hU.isOpen, ?_, hb mem_connectedComponent, disjoint_compl_left⟩
  exact fun h => flip Set.Nonempty.ne_empty ha ⟨a, mem_connectedComponent, h⟩
