/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Compactification.StoneCech

/-!
# Extremally disconnected spaces

An extremally disconnected topological space is a space in which the closure of every open set is
open. Such spaces are also called Stonean spaces. They are the projective objects in the category of
compact Hausdorff spaces.

## Main declarations

* `ExtremallyDisconnected`: Predicate for a space to be extremally disconnected.
* `CompactT2.Projective`: Predicate for a topological space to be a projective object in the
  category of compact Hausdorff spaces.
* `CompactT2.Projective.extremallyDisconnected`: Compact Hausdorff spaces that are projective are
  extremally disconnected.
* `CompactT2.ExtremallyDisconnected.projective`: Extremally disconnected spaces are projective
  objects in the category of compact Hausdorff spaces.

## References

[Gleason, *Projective topological spaces*][gleason1958]
-/

@[expose] public section

noncomputable section

open Function Set

universe u

variable (X : Type u) [TopologicalSpace X]

/-- An extremally disconnected topological space is a space
in which the closure of every open set is open. -/
/-
**ExtremallyDisconnected** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An extremally disconnected topological space is a space
in which the closure of every open set is open.
-/
class ExtremallyDisconnected : Prop where
  /-- The closure of every open set is open. -/
  open_closure : ∀ U : Set X, IsOpen U → IsOpen (closure U)
/-
**extremallyDisconnected_of_homeo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremallyDisconnected_of_homeo {X Y : Type*} [TopologicalSpace X] [Topolo
gicalSpace Y] [ExtremallyDisconnected X] (e : X ≃ₜ Y) : ExtremallyDisconnected Y
 where open_closure U hU
参数：e : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `Homeomorph.isOpen_preimage`：isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : I
sOpen (h ⁻¹' s) ↔ IsOpen s
· 使用定理 `ExtremallyDisconnected.open_closure`：∀ {X : Type u} {inst : TopologicalS
pace X} [self : ExtremallyDisconnected X] (U : Set X), IsOpen U → IsOpen (closur
e U)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isOpen_image`：isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen 
(h '' s) ↔ IsOpen s
-/
theorem extremallyDisconnected_of_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ExtremallyDisconnected X] (e : X ≃ₜ Y) : ExtremallyDisconnected Y where
  open_closure U hU := by
    rw [e.symm.isInducing.closure_eq_preimage_closure_image, Homeomorph.isOpen_preimage]
    exact ExtremallyDisconnected.open_closure _ (e.symm.isOpen_image.mpr hU)

section TotallySeparated

/-- Extremally disconnected spaces are totally separated. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extremally disconnected spaces are totally separated.
-/
instance [ExtremallyDisconnected X] [T2Space X] : TotallySeparatedSpace X :=
{ isTotallySeparated_univ := by
    intro x _ y _ hxy
    obtain ⟨U, V, hUV⟩ := T2Space.t2 hxy
    refine ⟨closure U, (closure U)ᶜ, ExtremallyDisconnected.open_closure U hUV.1,
      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_,
      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩
    rw [Set.mem_compl_iff, mem_closure_iff]
    push Not
    refine ⟨V, ⟨hUV.2.1, hUV.2.2.2.1, ?_⟩⟩
    rw [← Set.disjoint_iff_inter_eq_empty, disjoint_comm]
    exact hUV.2.2.2.2 }

end TotallySeparated

section

/-- The assertion `CompactT2.Projective` states that given continuous maps
`f : X → Z` and `g : Y → Z` with `g` surjective between `t_2`, compact topological spaces,
there exists a continuous lift `h : X → Y`, such that `f = g ∘ h`. -/
/-
**CompactT2.Projective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompactT2.Projective : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The assertion `CompactT2.Projective` states that given continuous maps
`f : X → Z` and `g : Y → Z` with `g` surjective between `t_2`, compact topologic
al spaces,
there exists a continuous lift `h : X → Y`, such that `f = g ∘ h`.
-/
def CompactT2.Projective : Prop :=
  ∀ {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z],
    ∀ [CompactSpace Y] [T2Space Y] [CompactSpace Z] [T2Space Z],
      ∀ {f : X → Z} {g : Y → Z} (_ : Continuous f) (_ : Continuous g) (_ : Surjective g),
        ∃ h : X → Y, Continuous h ∧ g ∘ h = f

variable {X}
/-
**StoneCech.projective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StoneCech.projective [DiscreteTopology X] : CompactT2.Projective (StoneCec
h X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `continuous_stoneCechExtend`：continuous_stoneCechExtend : Continuous (sto
neCechExtend hg)
· 使用定理 `DenseRange.equalizer`：DenseRange.equalizer (hfd : DenseRange f) {g h : β
 -> γ} (hg : Continuous g) (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h
· 使用定理 `denseRange_stoneCechUnit`：denseRange_stoneCechUnit : DenseRange (stoneCe
chUnit : α -> StoneCech α)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用引理 `stoneCechExtend_extends`：stoneCechExtend_extends : stoneCechExtend hg ∘ 
stoneCechUnit = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
theorem StoneCech.projective [DiscreteTopology X] : CompactT2.Projective (StoneCech X) := by
  intro Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur
  let s : Z → Y := fun z => Classical.choose <| g_sur z
  have hs : g ∘ s = id := funext fun z => Classical.choose_spec (g_sur z)
  let t := s ∘ f ∘ stoneCechUnit
  have ht : Continuous t := continuous_of_discreteTopology
  let h : StoneCech X → Y := stoneCechExtend ht
  have hh : Continuous h := continuous_stoneCechExtend ht
  refine ⟨h, hh, denseRange_stoneCechUnit.equalizer (hg.comp hh) hf ?_⟩
  rw [comp_assoc, stoneCechExtend_extends ht, ← comp_assoc, hs, id_comp]
/-
**CompactT2.Projective.extremallyDisconnected** 是 Mathlib 中的一个定理，位于命名空间 `Compact
T2.Projective`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] [CompactSpace X] [T2Space X],  
 CompactT2.Projective X → ExtremallyDisconnected X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `IsClosed.prod`：IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁
) (h₂ : IsClosed s₂) : IsClosed (s₁ ×ˢ s₂)
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `T4Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T4
Space X], T1Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `NormalSpace.of_compactSpace_r1Space`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompactSpace X] [R1Space X], NormalSpace X
· 使用定理 `Finite.compactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Finite 
X], CompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `instCompactSpaceProd`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [CompactSpace Y],   Compact
Space (X ×…
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
（共 44 条，此处仅展示前 30 条）
-/
protected theorem CompactT2.Projective.extremallyDisconnected [CompactSpace X] [T2Space X]
    (h : CompactT2.Projective X) : ExtremallyDisconnected X := by
  refine { open_closure := fun U hU => ?_ }
  let Z₁ : Set (X × Bool) := Uᶜ ×ˢ {true}
  let Z₂ : Set (X × Bool) := closure U ×ˢ {false}
  let Z : Set (X × Bool) := Z₁ ∪ Z₂
  have hZ₁₂ : Disjoint Z₁ Z₂ := disjoint_left.2 fun x hx₁ hx₂ => by cases hx₁.2.symm.trans hx₂.2
  have hZ₁ : IsClosed Z₁ := hU.isClosed_compl.prod (T1Space.t1 _)
  have hZ₂ : IsClosed Z₂ := isClosed_closure.prod (T1Space.t1 false)
  have hZ : IsClosed Z := hZ₁.union hZ₂
  let f : Z → X := Prod.fst ∘ Subtype.val
  have f_cont : Continuous f := continuous_fst.comp continuous_subtype_val
  have f_sur : Surjective f := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨⟨(x, false), Or.inr ⟨subset_closure hx, mem_singleton _⟩⟩, rfl⟩
    · exact ⟨⟨(x, true), Or.inl ⟨hx, mem_singleton _⟩⟩, rfl⟩
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  obtain ⟨g, hg, g_sec⟩ := h continuous_id f_cont f_sur
  let φ := Subtype.val ∘ g
  have hφ : Continuous φ := continuous_subtype_val.comp hg
  have hφ₁ : ∀ x, (φ x).1 = x := congr_fun g_sec
  suffices closure U = φ ⁻¹' Z₂ by
    rw [this, preimage_comp, ← isClosed_compl_iff, ← preimage_compl,
      ← preimage_subtype_coe_eq_compl Subset.rfl]
    · exact hZ₁.preimage hφ
    · rw [hZ₁₂.inter_eq, inter_empty]
  refine (closure_minimal ?_ <| hZ₂.preimage hφ).antisymm fun x hx => ?_
  · intro x hx
    have : φ x ∈ Z₁ ∪ Z₂ := (g x).2
    rcases this with hφ | hφ
    · exact ((hφ₁ x ▸ hφ.1) hx).elim
    · exact hφ
  · rw [← hφ₁ x]
    exact hx.1

end

section

variable {A D E : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace E]

/-- Lemma 2.4 in [Gleason, *Projective topological spaces*][gleason1958]:
a continuous surjection $\pi$ from a compact space $D$ to a Fréchet space $A$ restricts to
a compact subset $E$ of $D$, such that $\pi$ maps $E$ onto $A$ and satisfies the
"Zorn subset condition", where $\pi(E_0) \ne A$ for any proper closed subset $E_0 \subsetneq E$. -/
/-
**exists_compact_surjective_zorn_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_compact_surjective_zorn_subset [T1Space A] [CompactSpace D] {X : D 
-> A} (X_cont : Continuous X) (X_surj : X.Surjective) : exists E : Set D, Compac
tSpace E ∧ X '' E = univ ∧ forall E₀ : Set E, E₀ != univ -> IsClosed E₀ -> E.dom
Restrict X '' E₀ != univ
参数：X_cont : Continuous X；X_surj : X.Surjective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.inter_nonempty_iff_exists_left`：inter_nonempty_iff_exists_left : (s 
inter t).Nonempty ↔ exists x in s, x in t
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `IsChain.symm`：IsChain.symm (h : IsChain r s) : IsChain (flip r) s
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `instReflGe`：∀ {α : Type u} [inst : Preorder α], Std.Refl fun x1 x2 => x2
 ≤ x1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inter_nonempty_iff`：image_inter_nonempty_iff {f : α -> β} {s :
 Set α} {t : Set β} : (f '' s inter t).Nonempty ↔ (s inter f ⁻¹' t).Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `Set.iInter_inter`：iInter_inter [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (⋂ i, t i) inter s = ⋂ i, t i inter s
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `zorn_superset`：zorn_superset (S : Set (Set α)) (h : forall c subseteq S,
 IsChain (· subseteq ·) c -> exists lb in S, forall s in c, lb subseteq s) : exi
sts…
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Lemma 2.4 in [Gleason, *Projective topological spaces*][gleason1958]:
a continuous surjection $\pi$ from a compact space $D$ to a Fréchet space $A$ re
stricts to
a compact subset $E$ of $D$, such that $\pi$ maps $E$ onto $A$ and satisfies the
"Zorn subset condition", where $\pi(E_0) \ne A$ for any proper closed subset $E_
0 \subsetneq E$.
-/
lemma exists_compact_surjective_zorn_subset [T1Space A] [CompactSpace D] {X : D → A}
    (X_cont : Continuous X) (X_surj : X.Surjective) : ∃ E : Set D, CompactSpace E ∧ X '' E = univ ∧
    ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → E.domRestrict X '' E₀ ≠ univ := by
  -- suffices to apply Zorn's lemma on the subsets of $D$ that are closed and mapped onto $A$
  let S : Set <| Set D := {E : Set D | IsClosed E ∧ X '' E = univ}
  suffices ∀ (C : Set <| Set D) (_ : C ⊆ S) (_ : IsChain (· ⊆ ·) C), ∃ s ∈ S, ∀ c ∈ C, s ⊆ c by
    rcases zorn_superset S this with ⟨E, E_min⟩
    obtain ⟨E_closed, E_surj⟩ := E_min.prop
    refine ⟨E, isCompact_iff_compactSpace.mp E_closed.isCompact, E_surj, ?_⟩
    intro E₀ E₀_min E₀_closed
    contrapose E₀_min
    exact eq_univ_of_image_val_eq <|
      E_min.eq_of_subset ⟨E₀_closed.trans E_closed, image_image_val_eq_domRestrict_image ▸ E₀_min⟩
        image_val_subset
  -- suffices to prove intersection of chain is minimal
  intro C C_sub C_chain
  -- prove intersection of chain is closed
  refine ⟨iInter (fun c : C => c), ⟨isClosed_iInter fun ⟨_, h⟩ => (C_sub h).left, ?_⟩,
    fun c hc _ h => mem_iInter.mp h ⟨c, hc⟩⟩
  -- prove intersection of chain is mapped onto $A$
  by_cases hC : Nonempty C
  · refine eq_univ_of_forall fun a => inter_nonempty_iff_exists_left.mp ?_
    -- apply Cantor's intersection theorem
    refine iInter_inter (ι := C) (X ⁻¹' {a}) _ ▸
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
      ?_ (fun c => ?_) (fun c => IsClosed.isCompact ?_) (fun c => ?_)
    · replace C_chain : IsChain (· ⊇ ·) C := C_chain.symm
      exact (directedOn_iff_directed.mp C_chain.directedOn).mono_comp (g := (· ∩ X ⁻¹' {a})) _
        fun _ _ => inter_subset_inter_left _
    · rw [← image_inter_nonempty_iff, (C_sub c.mem).right, univ_inter]
      exact singleton_nonempty a
    all_goals exact (C_sub c.mem).left.inter <| (T1Space.t1 a).preimage X_cont
  · rw [@iInter_of_empty _ _ <| not_nonempty_iff.mp hC, image_univ_of_surjective X_surj]

/-- Lemma 2.1 in [Gleason, *Projective topological spaces*][gleason1958]:
if $\rho$ is a continuous surjection from a topological space $E$ to a topological space $A$
satisfying the "Zorn subset condition", then $\rho(G)$ is contained in
the closure of $A \setminus \rho(E \setminus G)$ for any open set $G$ of $E$. -/
/-
**image_subset_closure_compl_image_compl_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：image_subset_closure_compl_image_compl_of_isOpen {ρ : E -> A} (ρ_cont : Co
ntinuous ρ) (ρ_surj : ρ.Surjective) (zorn_subset : forall E₀ : Set E, E₀ != univ
 -> IsClosed E₀ -> ρ '' E₀ != univ) {G : Set E} (hG : IsOpen G) : ρ '' G subsete
q closure ((ρ '' Gᶜ)ᶜ)
参数：ρ_cont : Continuous ρ；ρ_surj : ρ.Surjective；zorn_subset : forall E₀ : Set E, 
E₀ != univ -> IsClosed E₀ -> ρ '' E₀ != univ；hG : IsOpen G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Set.compl_ne_univ`：compl_ne_univ : sᶜ != univ ↔ s.Nonempty
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `Set.nonempty_compl`：nonempty_compl : sᶜ.Nonempty ↔ s != univ
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b

--- 原说明 ---
Lemma 2.1 in [Gleason, *Projective topological spaces*][gleason1958]:
if $\rho$ is a continuous surjection from a topological space $E$ to a topologic
al space $A$
satisfying the "Zorn subset condition", then $\rho(G)$ is contained in
the closure of $A \setminus \rho(E \setminus G)$ for any open set $G$ of $E$.
-/
lemma image_subset_closure_compl_image_compl_of_isOpen {ρ : E → A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ)
    {G : Set E} (hG : IsOpen G) : ρ '' G ⊆ closure ((ρ '' Gᶜ)ᶜ) := by
  -- suffices to prove for nonempty $G$
  by_cases G_empty : G = ∅
  · simpa only [G_empty, image_empty] using empty_subset _
  · -- let $a \in \rho(G)$
    intro a ha
    rw [mem_closure_iff]
    -- let $N$ be a neighbourhood of $a$
    intro N N_open hN
    -- get $x \in A$ from nonempty open $G \cap \rho^{-1}(N)$
    rcases (G.mem_image ρ a).mp ha with ⟨e, he, rfl⟩
    have nonempty : (G ∩ ρ ⁻¹' N).Nonempty := ⟨e, mem_inter he <| mem_preimage.mpr hN⟩
    have is_open : IsOpen <| G ∩ ρ ⁻¹' N := hG.inter <| N_open.preimage ρ_cont
    have ne_univ : ρ '' (G ∩ ρ ⁻¹' N)ᶜ ≠ univ :=
      zorn_subset _ (compl_ne_univ.mpr nonempty) is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_univ with ⟨x, hx⟩
    -- prove $x \in N \cap (A \setminus \rho(E \setminus G))$
    have hx' : x ∈ (ρ '' Gᶜ)ᶜ := fun h => hx <| image_mono (by simp) h
    rcases ρ_surj x with ⟨y, rfl⟩
    have hy : y ∈ G ∩ ρ ⁻¹' N := by simpa using mt (mem_image_of_mem ρ) <| mem_compl hx
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩

/-- Lemma 2.2 in [Gleason, *Projective topological spaces*][gleason1958]:
in an extremally disconnected space, if $U_1$ and $U_2$ are disjoint open sets,
then $\overline{U_1}$ and $\overline{U_2}$ are also disjoint. -/
/-
**ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen [ExtremallyDisc
onnected A] {U₁ U₂ : Set A} (h : Disjoint U₁ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen
 U₂) : Disjoint (closure U₁) (closure U₂)
参数：h : Disjoint U₁ U₂；hU₁ : IsOpen U₁；hU₂ : IsOpen U₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.closure_left`：Disjoint.closure_left (hd : Disjoint s t) (ht : I
sOpen t) : Disjoint (closure s) t
· 使用定理 `Disjoint.closure_right`：Disjoint.closure_right (hd : Disjoint s t) (hs :
 IsOpen s) : Disjoint s (closure t)
· 使用定理 `ExtremallyDisconnected.open_closure`：∀ {X : Type u} {inst : TopologicalS
pace X} [self : ExtremallyDisconnected X] (U : Set X), IsOpen U → IsOpen (closur
e U)

--- 原说明 ---
Lemma 2.2 in [Gleason, *Projective topological spaces*][gleason1958]:
in an extremally disconnected space, if $U_1$ and $U_2$ are disjoint open sets,
then $\overline{U_1}$ and $\overline{U_2}$ are also disjoint.
-/
lemma ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen [ExtremallyDisconnected A]
    {U₁ U₂ : Set A} (h : Disjoint U₁ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) :
    Disjoint (closure U₁) (closure U₂) :=
  (h.closure_right hU₁).closure_left <| open_closure U₂ hU₂

set_option backward.privateInPublic true in
/-
**ExtremallyDisconnected.homeoCompactToT2_injective** 是 Mathlib 中的一个引理，位于命名空间 ``
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ExtremallyDisconnected.homeoCompactToT2_injective [ExtremallyDisconnected A]
    [T2Space A] [T2Space E] [CompactSpace E] {ρ : E → A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ) :
    ρ.Injective := by
  -- let $x_1, x_2 \in E$ be distinct points such that $\rho(x_1) = \rho(x_2)$
  intro x₁ x₂ hρx
  by_contra hx
  -- let $G_1$ and $G_2$ be disjoint open neighbourhoods of $x_1$ and $x_2$ respectively
  rcases t2_separation hx with ⟨G₁, G₂, G₁_open, G₂_open, hx₁, hx₂, disj⟩
  -- prove $A \setminus \rho(E - G_1)$ and $A \setminus \rho(E - G_2)$ are disjoint
  have G₁_comp : IsCompact G₁ᶜ := IsClosed.isCompact G₁_open.isClosed_compl
  have G₂_comp : IsCompact G₂ᶜ := IsClosed.isCompact G₂_open.isClosed_compl
  have G₁_open' : IsOpen (ρ '' G₁ᶜ)ᶜ := (G₁_comp.image ρ_cont).isClosed.isOpen_compl
  have G₂_open' : IsOpen (ρ '' G₂ᶜ)ᶜ := (G₂_comp.image ρ_cont).isClosed.isOpen_compl
  have disj' : Disjoint (ρ '' G₁ᶜ)ᶜ (ρ '' G₂ᶜ)ᶜ := by
    rw [disjoint_iff_inter_eq_empty, ← compl_union, ← image_union, ← compl_inter,
      disjoint_iff_inter_eq_empty.mp disj, compl_empty, compl_empty_iff,
      image_univ_of_surjective ρ_surj]
  -- apply Lemma 2.2 to prove their closures are disjoint
  have disj'' : Disjoint (closure (ρ '' G₁ᶜ)ᶜ) (closure (ρ '' G₂ᶜ)ᶜ) :=
    disjoint_closure_of_disjoint_isOpen disj' G₁_open' G₂_open'
  -- apply Lemma 2.1 to prove $\rho(x_1) = \rho(x_2)$ lies in their intersection
  have hx₁' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₁_open <|
    mem_image_of_mem ρ hx₁
  have hx₂' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₂_open <|
    mem_image_of_mem ρ hx₂
  exact disj''.ne_of_mem hx₁' hx₂' hρx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Lemma 2.3 in [Gleason, *Projective topological spaces*][gleason1958]:
a continuous surjection from a compact Hausdorff space to an extremally disconnected Hausdorff space
satisfying the "Zorn subset condition" is a homeomorphism. -/
/-
**ExtremallyDisconnected.homeoCompactToT2** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ExtremallyDisconnected.homeoCompactToT2 [ExtremallyDisconnected A] [T2Spac
e A] [T2Space E] [CompactSpace E] {ρ : E -> A} (ρ_cont : Continuous ρ) (ρ_surj :
 ρ.Surjective) (zorn_subset : forall E₀ : Set E, E₀ != univ -> IsClosed E₀ -> ρ 
'' E₀ != univ) : E ≃ₜ A
参数：ρ_cont : Continuous ρ；ρ_surj : ρ.Surjective；zorn_subset : forall E₀ : Set E, 
E₀ != univ -> IsClosed E₀ -> ρ '' E₀ != univ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lemma 2.3 in [Gleason, *Projective topological spaces*][gleason1958]:
a continuous surjection from a compact Hausdorff space to an extremally disconne
cted Hausdorff space
satisfying the "Zorn subset condition" is a homeomorphism.
-/
noncomputable def ExtremallyDisconnected.homeoCompactToT2 [ExtremallyDisconnected A] [T2Space A]
    [T2Space E] [CompactSpace E] {ρ : E → A} (ρ_cont : Continuous ρ) (ρ_surj : ρ.Surjective)
    (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ) : E ≃ₜ A :=
  ρ_cont.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ρ ⟨homeoCompactToT2_injective ρ_cont ρ_surj zorn_subset, ρ_surj⟩)

/-- Theorem 2.5 in [Gleason, *Projective topological spaces*][gleason1958]:
in the category of compact spaces and continuous maps,
the projective spaces are precisely the extremally disconnected spaces. -/
/-
**CompactT2.ExtremallyDisconnected.projective** 是 Mathlib 中的一个定理，位于命名空间 `Compact
T2.ExtremallyDisconnected`。
形式化陈述：∀ {A : Type u} [inst : TopologicalSpace A] [ExtremallyDisconnected A] [Com
pactSpace A] [T2Space A],   CompactT2.Projective A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `instCompactSpaceProd`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [CompactSpace Y],   Compact
Space (X ×…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `exists_compact_surjective_zorn_subset`：exists_compact_surjective_zorn_su
bset [T1Space A] [CompactSpace D] {X : D -> A} (X_cont : Continuous X) (X_surj :
 X.Surjective) : exists E :…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Homeomorph.self_comp_symm`：self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f

--- 原说明 ---
Theorem 2.5 in [Gleason, *Projective topological spaces*][gleason1958]:
in the category of compact spaces and continuous maps,
the projective spaces are precisely the extremally disconnected spaces.
-/
protected theorem CompactT2.ExtremallyDisconnected.projective [ExtremallyDisconnected A]
    [CompactSpace A] [T2Space A] : CompactT2.Projective A := by
  -- let $B$ and $C$ be compact; let $f : B \twoheadrightarrow C$ and $\phi : A \to C$ be continuous
  intro B C _ _ _ _ _ _ φ f φ_cont f_cont f_surj
  -- let $D := \{(a, b) : \phi(a) = f(b)\}$ with projections $\pi_1 : D \to A$ and $\pi_2 : D \to B$
  let D : Set <| A × B := {x | φ x.fst = f x.snd}
  have D_comp : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_eq (φ_cont.comp continuous_fst) (f_cont.comp continuous_snd)).isCompact
  -- apply Lemma 2.4 to get closed $E$ satisfying "Zorn subset condition"
  let X₁ : D → A := Prod.fst ∘ Subtype.val
  have X₁_cont : Continuous X₁ := continuous_fst.comp continuous_subtype_val
  have X₁_surj : X₁.Surjective := fun a => ⟨⟨⟨a, _⟩, (f_surj <| φ a).choose_spec.symm⟩, rfl⟩
  rcases exists_compact_surjective_zorn_subset X₁_cont X₁_surj with ⟨E, _, E_onto, E_min⟩
  -- apply Lemma 2.3 to get homeomorphism $\pi_1|_E : E \to A$
  let ρ : E → A := E.domRestrict X₁
  have ρ_cont : Continuous ρ := X₁_cont.continuousOn.domRestrict
  have ρ_surj : ρ.Surjective := fun a => by
    rcases (E_onto ▸ mem_univ a : a ∈ X₁ '' E) with ⟨d, ⟨hd, rfl⟩⟩; exact ⟨⟨d, hd⟩, rfl⟩
  let ρ' := ExtremallyDisconnected.homeoCompactToT2 ρ_cont ρ_surj E_min
  -- prove $\rho := \pi_2|_E \circ \pi_1|_E^{-1}$ satisfies $\phi = f \circ \rho$
  let X₂ : D → B := Prod.snd ∘ Subtype.val
  have X₂_cont : Continuous X₂ := continuous_snd.comp continuous_subtype_val
  refine ⟨E.domRestrict X₂ ∘ ρ'.symm,
    ⟨X₂_cont.continuousOn.domRestrict.comp ρ'.symm.continuous, ?_⟩⟩
  suffices f ∘ E.domRestrict X₂ = φ ∘ ρ' by
    rw [← comp_assoc, this, comp_assoc, Homeomorph.self_comp_symm, comp_id]
  ext x
  exact x.val.mem.symm
/-
**CompactT2.projective_iff_extremallyDisconnected** 是 Mathlib 中的一个定理，位于命名空间 `Com
pactT2`。
形式化陈述：∀ {A : Type u} [inst : TopologicalSpace A] [CompactSpace A] [T2Space A],  
 CompactT2.Projective A ↔ ExtremallyDisconnected A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactT2.Projective.extremallyDisconnected`：∀ {X : Type u} [inst : Topo
logicalSpace X] [CompactSpace X] [T2Space X],   CompactT2.Projective X → Extrema
llyDisconnected X
· 使用定理 `CompactT2.ExtremallyDisconnected.projective`：∀ {A : Type u} [inst : Topo
logicalSpace A] [ExtremallyDisconnected A] [CompactSpace A] [T2Space A],   Compa
ctT2.Projective A
-/
protected theorem CompactT2.projective_iff_extremallyDisconnected [CompactSpace A] [T2Space A] :
    Projective A ↔ ExtremallyDisconnected A :=
  ⟨Projective.extremallyDisconnected, fun _ => ExtremallyDisconnected.projective⟩

end

-- Note: It might be possible to use Gleason for this instead
/-- The sigma-type of extremally disconnected spaces is extremally disconnected. -/
/-
**instExtremallyDisconnected** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instExtremallyDisconnected {ι : Type*} {X : ι -> Type*} [forall i, Topolog
icalSpace (X i)] [h₀ : forall i, ExtremallyDisconnected (X i)] : ExtremallyDisco
nnected (Σ i, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_sigma_iff`：isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ fora
ll i, IsOpen (Sigma.mk i ⁻¹' s)
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sigma_mk_preimage_image_eq_self`：sigma_mk_preimage_image_eq_self : Sigma
.mk i ⁻¹' Sigma.mk i '' s = s
· 使用引理 `sigma_mk_preimage_image'`：sigma_mk_preimage_image' (h : i != j) : Sigma.
mk j ⁻¹' Sigma.mk i '' s = ∅
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)

--- 原说明 ---
The sigma-type of extremally disconnected spaces is extremally disconnected.
-/
instance instExtremallyDisconnected {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [h₀ : ∀ i, ExtremallyDisconnected (X i)] : ExtremallyDisconnected (Σ i, X i) := by
  constructor
  intro s hs
  rw [isOpen_sigma_iff] at hs ⊢
  intro i
  rcases h₀ i with ⟨h₀⟩
  suffices h : Sigma.mk i ⁻¹' closure s = closure (Sigma.mk i ⁻¹' s) by
    rw [h]
    exact h₀ _ (hs i)
  apply IsOpenMap.preimage_closure_eq_closure_preimage
  · intro U _
    rw [isOpen_sigma_iff]
    intro j
    by_cases ij : i = j
    · rwa [← ij, sigma_mk_preimage_image_eq_self]
    · rw [sigma_mk_preimage_image' ij]
      exact isOpen_empty
  · fun_prop

variable {X}

/-- A preirreducible space is extremally disconnected. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preirreducible space is extremally disconnected.
-/
instance (priority := 100) [h : PreirreducibleSpace X] : ExtremallyDisconnected X where
  open_closure U hU := by
    by_cases! Un : U = ∅
    · simp_all
    · exact ((preirreducibleSpace_iff_open_dense X).mp h hU Un).closure_eq ▸ isOpen_univ

/-- A (pre-)connected, extremally disconnected space is preirreducible. -/
/-
**ExtremallyDisconnected.toPreirreducibleSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExtremallyDisconnected.toPreirreducibleSpace [h : ExtremallyDisconnected X
] [h' : PreconnectedSpace X] : PreirreducibleSpace X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `preirreducibleSpace_iff_open_dense`：preirreducibleSpace_iff_open_dense (
X : Type*) [TopologicalSpace X] : PreirreducibleSpace X ↔ forall ⦃U : Set X⦄, Is
Open U -> U.Nonempty -> …
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `preconnectedSpace_iff_clopen`：preconnectedSpace_iff_clopen : Preconnecte
dSpace α ↔ forall s : Set α, IsClopen s -> s = ∅ ∨ s = Set.univ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `ExtremallyDisconnected.open_closure`：∀ {X : Type u} {inst : TopologicalS
pace X} [self : ExtremallyDisconnected X] (U : Set X), IsOpen U → IsOpen (closur
e U)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
A (pre-)connected, extremally disconnected space is preirreducible.
-/
theorem ExtremallyDisconnected.toPreirreducibleSpace [h : ExtremallyDisconnected X]
    [h' : PreconnectedSpace X] :
    PreirreducibleSpace X := by
  apply (preirreducibleSpace_iff_open_dense X).mpr (fun s hs sn ↦ ?_)
  apply dense_iff_closure_eq.mpr
  cases preconnectedSpace_iff_clopen.mp h' (closure s) ⟨isClosed_closure, h.open_closure s hs⟩
  · simp_all
  · assumption

end

