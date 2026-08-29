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

/--
Definition of `ExtremallyDisconnected` / `ExtremallyDisconnected` 的定义

English:
class ExtremallyDisconnected
  parameters: : Prop where
  axioms and operations (1):
    - open_closure : forall U : Set X, IsOpen U -> IsOpen (closure U)

中文:
类 ExtremallyDisconnected
  参数: : 命题 where
  公理与运算 (1 个):
    - open_closure : 对任意 U : 集合 X, 是开集 U -> 是开集 (closure U)
-/
class ExtremallyDisconnected : Prop where
  /-- The closure of every open set is open. -/
  open_closure : forall U : Set X, IsOpen U -> IsOpen (closure U)

/--
theorem `extremallyDisconnected_of_homeo` / 定理 `extremallyDisconnected_of_homeo`

English:
theorem extremallyDisconnected_of_homeo
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: by
    rw [e.symm.isInducing.closure_eq_preimage_closure_image]; rw [Homeomorph.isOpen_preimage]
    exact ExtremallyDisconnected.open_closure _ (e.symm.isOpen_image.mpr hU)

中文:
定理 extremallyDisconnected_of_homeo
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y]
  证明: by
    rw [e.symm.isInducing.closure_eq_preimage_closure_image]; rw [Homeomorph.isOpen_preimage]
    exact ExtremallyDisconnected.open_closure _ (e.symm.isOpen_image.mpr hU)

Depends on / 依赖: ExtremallyDisconnected, ExtremallyDisconnected.open_closure, Homeomorph, Homeomorph.isOpen_preimage, closure_eq_preimage_closure_image, e.symm.isInducing.closure_eq_preimage_closure_image, e.symm.isOpen_image.mpr, isInducing, isOpen_image, isOpen_preimage, open_closure
-/
theorem extremallyDisconnected_of_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ExtremallyDisconnected X] (e : X ≃ₜ Y) : ExtremallyDisconnected Y where
  open_closure U hU := by
    rw [e.symm.isInducing.closure_eq_preimage_closure_image]; rw [Homeomorph.isOpen_preimage]
    exact ExtremallyDisconnected.open_closure _ (e.symm.isOpen_image.mpr hU)

section TotallySeparated

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ExtremallyDisconnected
  signature: X] [T2Space X] : TotallySeparatedSpace X
  body: { isTotallySeparated_univ := by
    intro x _ y _ hxy
    obtain ⟨U, V, hUV⟩ := T2Space.t2 hxy
    refine ⟨closure U, (closure U)ᶜ, ExtremallyDisconnected.open_closure U hUV.1,
      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_,
      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩
    rw [Set.mem_compl_iff]; rw [mem_closure_iff]
    push Not
    refine ⟨V, ⟨hUV.2.1, hUV.2.2.2.1, ?_⟩⟩
    rw [← Set.disjoint_iff_inter_eq_empty]; rw [disjoint_comm]
    exact hUV.2.2.2.2 }

中文:
实例 [ExtremallyDisconnected
  签名: X] [T2空间 X] : TotallySeparated空间 X
  定义体: { isTotallySeparated_univ := by
    intro x _ y _ hxy
    obtain ⟨U, V, hUV⟩ := T2Space.t2 hxy
    refine ⟨closure U, (closure U)ᶜ, ExtremallyDisconnected.open_closure U hUV.1,
      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_,
      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩
    rw [Set.mem_compl_iff]; rw [mem_closure_iff]
    push Not
    refine ⟨V, ⟨hUV.2.1, hUV.2.2.2.1, ?_⟩⟩
    rw [← Set.disjoint_iff_inter_eq_empty]; rw [disjoint_comm]
    exact hUV.2.2.2.2 }

Depends on / 依赖: ExtremallyDisconnected, ExtremallyDisconnected.open_closure, Set.disjoint_iff_inter_eq_empty, Set.mem_compl_iff, Set.subset_univ, Set.union_compl_self, T2Space, T2Space.t2, closure, disjoint_comm, disjoint_compl_right, disjoint_iff_inter_eq_empty, isClosed_closure, isOpen_compl_iff, isTotallySeparated_univ, mem_closure_iff, mem_compl_iff, open_closure, subset_closure, subset_univ
-/
instance [ExtremallyDisconnected X] [T2Space X] : TotallySeparatedSpace X :=
{ isTotallySeparated_univ := by
    intro x _ y _ hxy
    obtain ⟨U, V, hUV⟩ := T2Space.t2 hxy
    refine ⟨closure U, (closure U)ᶜ, ExtremallyDisconnected.open_closure U hUV.1,
      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_,
      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩
    rw [Set.mem_compl_iff]; rw [mem_closure_iff]
    push Not
    refine ⟨V, ⟨hUV.2.1, hUV.2.2.2.1, ?_⟩⟩
    rw [← Set.disjoint_iff_inter_eq_empty]; rw [disjoint_comm]
    exact hUV.2.2.2.2 }

end TotallySeparated

section

/--
Definition of `CompactT2.Projective` / `CompactT2.Projective` 的定义

English:
definition CompactT2.Projective
  signature: : Prop
  body: forall {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z],
    forall [CompactSpace Y] [T2Space Y] [CompactSpace Z] [T2Space Z],
      forall {f : X -> Z} {g : Y -> Z} (_ : Continuous f) (_ : Continuous g) (_ : Surjective g),
        exists h : X -> Y, Continuous h ∧ g ∘ h = f

中文:
定义 CompactT2.投射
  签名: : 命题
  定义体: forall {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z],
    forall [CompactSpace Y] [T2Space Y] [CompactSpace Z] [T2Space Z],
      forall {f : X -> Z} {g : Y -> Z} (_ : Continuous f) (_ : Continuous g) (_ : Surjective g),
        exists h : X -> Y, Continuous h ∧ g ∘ h = f

Depends on / 依赖: CompactSpace, Continuous, Surjective, T2Space, TopologicalSpace
-/
def CompactT2.Projective : Prop :=
  forall {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z],
    forall [CompactSpace Y] [T2Space Y] [CompactSpace Z] [T2Space Z],
      forall {f : X -> Z} {g : Y -> Z} (_ : Continuous f) (_ : Continuous g) (_ : Surjective g),
        exists h : X -> Y, Continuous h ∧ g ∘ h = f

variable {X}

/--
theorem `StoneCech.projective` / 定理 `StoneCech.projective`

English:
theorem StoneCech.projective
  given: [DiscreteTopology X]
  statement: CompactT2.Projective (StoneCech X)
  proof: by
  intro Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur
let s : Z -> Y := fun z => Classical.choose g_sur z
  have hs : g ∘ s = id := funext fun z => Classical.choose_spec (g_sur z)
  let t := s ∘ f ∘ stoneCechUnit
  have ht : Continuous t := continuous_of_discreteTopology
  let h : StoneCech X -> Y := stoneCechExtend ht
  have hh : Continuous h := continuous_stoneCechExtend ht
  refine ⟨h, hh, denseRange_stoneCechUnit.equalizer (hg.comp hh) hf ?_⟩
  rw [comp_assoc]; rw [stoneCechExtend_extends ht]; rw [← comp_assoc]; rw [hs]; rw [id_comp]

中文:
定理 StoneCech.projective
  条件: [离散拓扑 X]
  结论: CompactT2.投射 (StoneCech X)
  证明: by
  intro Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur
let s : Z -> Y := fun z => Classical.choose g_sur z
  have hs : g ∘ s = id := funext fun z => Classical.choose_spec (g_sur z)
  let t := s ∘ f ∘ stoneCechUnit
  have ht : Continuous t := continuous_of_discreteTopology
  let h : StoneCech X -> Y := stoneCechExtend ht
  have hh : Continuous h := continuous_stoneCechExtend ht
  refine ⟨h, hh, denseRange_stoneCechUnit.equalizer (hg.comp hh) hf ?_⟩
  rw [comp_assoc]; rw [stoneCechExtend_extends ht]; rw [← comp_assoc]; rw [hs]; rw [id_comp]

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Continuous, StoneCech, _csY, _csZ, _t2Y, _tsY, _tsZ, choose_spec, comp_assoc, continuous_of_discreteTopology, continuous_stoneCechExtend, denseRange_stoneCechUnit, denseRange_stoneCechUnit.equalizer, equalizer, g_sur, hg.comp, stoneCechExtend
-/
theorem StoneCech.projective [DiscreteTopology X] : CompactT2.Projective (StoneCech X) := by
  intro Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur
let s : Z -> Y := fun z => Classical.choose g_sur z
  have hs : g ∘ s = id := funext fun z => Classical.choose_spec (g_sur z)
  let t := s ∘ f ∘ stoneCechUnit
  have ht : Continuous t := continuous_of_discreteTopology
  let h : StoneCech X -> Y := stoneCechExtend ht
  have hh : Continuous h := continuous_stoneCechExtend ht
  refine ⟨h, hh, denseRange_stoneCechUnit.equalizer (hg.comp hh) hf ?_⟩
  rw [comp_assoc]; rw [stoneCechExtend_extends ht]; rw [← comp_assoc]; rw [hs]; rw [id_comp]

/--
theorem `CompactT2.Projective.extremallyDisconnected` / 定理 `CompactT2.Projective.extremallyDisconnected`

English:
theorem CompactT2.Projective.extremallyDisconnected
  statement: [CompactSpace X] [T2Space X]
  proof: by
  refine { open_closure := fun U hU => ?_ }
  let Z₁ : Set (X × Bool) := Uᶜ ×ˢ {true}
  let Z₂ : Set (X × Bool) := closure U ×ˢ {false}
  let Z : Set (X × Bool) := Z₁ union Z₂
  have hZ₁₂ : Disjoint Z₁ Z₂ := disjoint_left.2 fun x hx₁ hx₂ => by cases hx₁.2.symm.trans hx₂.2
  have hZ₁ : IsClosed Z₁ := hU.isClosed_compl.prod (T1Space.t1 _)
  have hZ₂ : IsClosed Z₂ := isClosed_closure.prod (T1Space.t1 false)
  have hZ : IsClosed Z := hZ₁.union hZ₂
  let f : Z -> X := Prod.fst ∘ Subtype.val
  have f_cont : Continuous f := continuous_fst.comp continuous_subtype_val
  have f_sur : Surjective f := by
    intro x
    by_cases hx : x in U
    · exact ⟨⟨(x, false), Or.inr ⟨subset_closure hx, mem_singleton _⟩⟩, rfl⟩
    · exact ⟨⟨(x, true), Or.inl ⟨hx, mem_singleton _⟩⟩, rfl⟩
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  obtain ⟨g, hg, g_sec⟩ := h continuous_id f_cont f_sur
  let φ := Subtype.val ∘ g
  have hφ : Continuous φ := continuous_subtype_val.comp hg
  have hφ₁ : forall x, (φ x).1 = x := congr_fun g_sec
  suffices closure U = φ ⁻¹' Z₂ by
    rw [this]; rw [preimage_comp]; rw [← isClosed_compl_iff]; rw [← preimage_compl]; rw [← preimage_subtype_coe_eq_compl Subset.rfl]
    · exact hZ₁.preimage hφ
    · rw [hZ₁₂.inter_eq, inter_empty]
  refine (closure_minimal ?_ <| hZ₂.preimage hφ).antisymm fun x hx => ?_
  · intro x hx
    have : φ x in Z₁ union Z₂ := (g x).2
    rcases this with hφ | hφ
    · exact ((hφ₁ x ▸ hφ.1) hx).elim
    · exact hφ
  · rw [← hφ₁ x]
    exact hx.1

中文:
定理 CompactT2.投射.extremallyDisconnected
  结论: [紧空间 X] [T2空间 X]
  证明: by
  refine { open_closure := fun U hU => ?_ }
  let Z₁ : Set (X × Bool) := Uᶜ ×ˢ {true}
  let Z₂ : Set (X × Bool) := closure U ×ˢ {false}
  let Z : Set (X × Bool) := Z₁ union Z₂
  have hZ₁₂ : Disjoint Z₁ Z₂ := disjoint_left.2 fun x hx₁ hx₂ => by cases hx₁.2.symm.trans hx₂.2
  have hZ₁ : IsClosed Z₁ := hU.isClosed_compl.prod (T1Space.t1 _)
  have hZ₂ : IsClosed Z₂ := isClosed_closure.prod (T1Space.t1 false)
  have hZ : IsClosed Z := hZ₁.union hZ₂
  let f : Z -> X := Prod.fst ∘ Subtype.val
  have f_cont : Continuous f := continuous_fst.comp continuous_subtype_val
  have f_sur : Surjective f := by
    intro x
    by_cases hx : x in U
    · exact ⟨⟨(x, false), Or.inr ⟨subset_closure hx, mem_singleton _⟩⟩, rfl⟩
    · exact ⟨⟨(x, true), Or.inl ⟨hx, mem_singleton _⟩⟩, rfl⟩
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  obtain ⟨g, hg, g_sec⟩ := h continuous_id f_cont f_sur
  let φ := Subtype.val ∘ g
  have hφ : Continuous φ := continuous_subtype_val.comp hg
  have hφ₁ : forall x, (φ x).1 = x := congr_fun g_sec
  suffices closure U = φ ⁻¹' Z₂ by
    rw [this]; rw [preimage_comp]; rw [← isClosed_compl_iff]; rw [← preimage_compl]; rw [← preimage_subtype_coe_eq_compl Subset.rfl]
    · exact hZ₁.preimage hφ
    · rw [hZ₁₂.inter_eq, inter_empty]
  refine (closure_minimal ?_ <| hZ₂.preimage hφ).antisymm fun x hx => ?_
  · intro x hx
    have : φ x in Z₁ union Z₂ := (g x).2
    rcases this with hφ | hφ
    · exact ((hφ₁ x ▸ hφ.1) hx).elim
    · exact hφ
  · rw [← hφ₁ x]
    exact hx.1
-/
protected theorem CompactT2.Projective.extremallyDisconnected [CompactSpace X] [T2Space X]
    (h : CompactT2.Projective X) : ExtremallyDisconnected X := by
  refine { open_closure := fun U hU => ?_ }
  let Z₁ : Set (X × Bool) := Uᶜ ×ˢ {true}
  let Z₂ : Set (X × Bool) := closure U ×ˢ {false}
  let Z : Set (X × Bool) := Z₁ union Z₂
  have hZ₁₂ : Disjoint Z₁ Z₂ := disjoint_left.2 fun x hx₁ hx₂ => by cases hx₁.2.symm.trans hx₂.2
  have hZ₁ : IsClosed Z₁ := hU.isClosed_compl.prod (T1Space.t1 _)
  have hZ₂ : IsClosed Z₂ := isClosed_closure.prod (T1Space.t1 false)
  have hZ : IsClosed Z := hZ₁.union hZ₂
  let f : Z -> X := Prod.fst ∘ Subtype.val
  have f_cont : Continuous f := continuous_fst.comp continuous_subtype_val
  have f_sur : Surjective f := by
    intro x
    by_cases hx : x in U
    · exact ⟨⟨(x, false), Or.inr ⟨subset_closure hx, mem_singleton _⟩⟩, rfl⟩
    · exact ⟨⟨(x, true), Or.inl ⟨hx, mem_singleton _⟩⟩, rfl⟩
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  obtain ⟨g, hg, g_sec⟩ := h continuous_id f_cont f_sur
  let φ := Subtype.val ∘ g
  have hφ : Continuous φ := continuous_subtype_val.comp hg
  have hφ₁ : forall x, (φ x).1 = x := congr_fun g_sec
  suffices closure U = φ ⁻¹' Z₂ by
    rw [this]; rw [preimage_comp]; rw [← isClosed_compl_iff]; rw [← preimage_compl]; rw [← preimage_subtype_coe_eq_compl Subset.rfl]
    · exact hZ₁.preimage hφ
    · rw [hZ₁₂.inter_eq, inter_empty]
  refine (closure_minimal ?_ <| hZ₂.preimage hφ).antisymm fun x hx => ?_
  · intro x hx
    have : φ x in Z₁ union Z₂ := (g x).2
    rcases this with hφ | hφ
    · exact ((hφ₁ x ▸ hφ.1) hx).elim
    · exact hφ
  · rw [← hφ₁ x]
    exact hx.1

end

section

variable {A D E : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace E]

/--
lemma `exists_compact_surjective_zorn_subset` / 引理 `exists_compact_surjective_zorn_subset`

English:
lemma exists_compact_surjective_zorn_subset
  statement: [T1Space A] [CompactSpace D] {X : D -> A}
  proof: by
  -- suffices to apply Zorn's lemma on the subsets of $D$ that are closed and mapped onto $A$
let S : Set Set D := {E : Set D | IsClosed E ∧ X '' E = univ}
  suffices forall (C : Set <| Set D) (_ : C subseteq S) (_ : IsChain (· subseteq ·) C), exists s in S, forall c in C, s subseteq c by
    rcases zorn_superset S this with ⟨E, E_min⟩
    obtain ⟨E_closed, E_surj⟩ := E_min.prop
    refine ⟨E, isCompact_iff_compactSpace.mp E_closed.isCompact, E_surj, ?_⟩
    intro E₀ E₀_min E₀_closed
    contrapose E₀_min
exact eq_univ_of_image_val_eq
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
      exact (directedOn_iff_directed.mp C_chain.directedOn).mono_comp (g := (· inter X ⁻¹' {a})) _
        fun _ _ => inter_subset_inter_left _
    · rw [← image_inter_nonempty_iff, (C_sub c.mem).right, univ_inter]
      exact singleton_nonempty a
all_goals exact (C_sub c.mem).left.inter (T1Space.t1 a).preimage X_cont
  · rw [@iInter_of_empty _ _ <| not_nonempty_iff.mp hC, image_univ_of_surjective X_surj]

中文:
引理 存在_compact_surjective_zorn_subset
  结论: [T1空间 A] [紧空间 D] {X : D -> A}
  证明: by
  -- suffices to apply Zorn's lemma on the subsets of $D$ that are closed and mapped onto $A$
let S : Set Set D := {E : Set D | IsClosed E ∧ X '' E = univ}
  suffices forall (C : Set <| Set D) (_ : C subseteq S) (_ : IsChain (· subseteq ·) C), exists s in S, forall c in C, s subseteq c by
    rcases zorn_superset S this with ⟨E, E_min⟩
    obtain ⟨E_closed, E_surj⟩ := E_min.prop
    refine ⟨E, isCompact_iff_compactSpace.mp E_closed.isCompact, E_surj, ?_⟩
    intro E₀ E₀_min E₀_closed
    contrapose E₀_min
exact eq_univ_of_image_val_eq
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
      exact (directedOn_iff_directed.mp C_chain.directedOn).mono_comp (g := (· inter X ⁻¹' {a})) _
        fun _ _ => inter_subset_inter_left _
    · rw [← image_inter_nonempty_iff, (C_sub c.mem).right, univ_inter]
      exact singleton_nonempty a
all_goals exact (C_sub c.mem).left.inter (T1Space.t1 a).preimage X_cont
  · rw [@iInter_of_empty _ _ <| not_nonempty_iff.mp hC, image_univ_of_surjective X_surj]
-/
lemma exists_compact_surjective_zorn_subset [T1Space A] [CompactSpace D] {X : D -> A}
    (X_cont : Continuous X) (X_surj : X.Surjective) : exists E : Set D, CompactSpace E ∧ X '' E = univ ∧
    forall E₀ : Set E, E₀ != univ -> IsClosed E₀ -> E.domRestrict X '' E₀ != univ := by
  -- suffices to apply Zorn's lemma on the subsets of $D$ that are closed and mapped onto $A$
let S : Set Set D := {E : Set D | IsClosed E ∧ X '' E = univ}
  suffices forall (C : Set <| Set D) (_ : C subseteq S) (_ : IsChain (· subseteq ·) C), exists s in S, forall c in C, s subseteq c by
    rcases zorn_superset S this with ⟨E, E_min⟩
    obtain ⟨E_closed, E_surj⟩ := E_min.prop
    refine ⟨E, isCompact_iff_compactSpace.mp E_closed.isCompact, E_surj, ?_⟩
    intro E₀ E₀_min E₀_closed
    contrapose E₀_min
exact eq_univ_of_image_val_eq
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
      exact (directedOn_iff_directed.mp C_chain.directedOn).mono_comp (g := (· inter X ⁻¹' {a})) _
        fun _ _ => inter_subset_inter_left _
    · rw [← image_inter_nonempty_iff, (C_sub c.mem).right, univ_inter]
      exact singleton_nonempty a
all_goals exact (C_sub c.mem).left.inter (T1Space.t1 a).preimage X_cont
  · rw [@iInter_of_empty _ _ <| not_nonempty_iff.mp hC, image_univ_of_surjective X_surj]

/--
lemma `image_subset_closure_compl_image_compl_of_isOpen` / 引理 `image_subset_closure_compl_image_compl_of_isOpen`

English:
lemma image_subset_closure_compl_image_compl_of_isOpen
  statement: {ρ : E -> A} (ρ_cont : Continuous ρ)
  proof: by
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
have nonempty : (G inter ρ ⁻¹' N).Nonempty := ⟨e, mem_inter he mem_preimage.mpr hN⟩
have is_open : IsOpen G inter ρ ⁻¹' N := hG.inter N_open.preimage ρ_cont
    have ne_univ : ρ '' (G inter ρ ⁻¹' N)ᶜ != univ :=
      zorn_subset _ (compl_ne_univ.mpr nonempty) is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_univ with ⟨x, hx⟩
    -- prove $x \in N \cap (A \setminus \rho(E \setminus G))$
have hx' : x in (ρ '' Gᶜ)ᶜ := fun h => hx image_mono (by simp) h
    rcases ρ_surj x with ⟨y, rfl⟩
have hy : y in G inter ρ ⁻¹' N := by simpa using mt (mem_image_of_mem ρ) mem_compl hx
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩

中文:
引理 image_subset_closure_compl_image_compl_of_isOpen
  结论: {ρ : E -> A} (ρ_cont : 连续 ρ)
  证明: by
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
have nonempty : (G inter ρ ⁻¹' N).Nonempty := ⟨e, mem_inter he mem_preimage.mpr hN⟩
have is_open : IsOpen G inter ρ ⁻¹' N := hG.inter N_open.preimage ρ_cont
    have ne_univ : ρ '' (G inter ρ ⁻¹' N)ᶜ != univ :=
      zorn_subset _ (compl_ne_univ.mpr nonempty) is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_univ with ⟨x, hx⟩
    -- prove $x \in N \cap (A \setminus \rho(E \setminus G))$
have hx' : x in (ρ '' Gᶜ)ᶜ := fun h => hx image_mono (by simp) h
    rcases ρ_surj x with ⟨y, rfl⟩
have hy : y in G inter ρ ⁻¹' N := by simpa using mt (mem_image_of_mem ρ) mem_compl hx
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩
-/
lemma image_subset_closure_compl_image_compl_of_isOpen {ρ : E -> A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : forall E₀ : Set E, E₀ != univ -> IsClosed E₀ -> ρ '' E₀ != univ)
    {G : Set E} (hG : IsOpen G) : ρ '' G subseteq closure ((ρ '' Gᶜ)ᶜ) := by
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
have nonempty : (G inter ρ ⁻¹' N).Nonempty := ⟨e, mem_inter he mem_preimage.mpr hN⟩
have is_open : IsOpen G inter ρ ⁻¹' N := hG.inter N_open.preimage ρ_cont
    have ne_univ : ρ '' (G inter ρ ⁻¹' N)ᶜ != univ :=
      zorn_subset _ (compl_ne_univ.mpr nonempty) is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_univ with ⟨x, hx⟩
    -- prove $x \in N \cap (A \setminus \rho(E \setminus G))$
have hx' : x in (ρ '' Gᶜ)ᶜ := fun h => hx image_mono (by simp) h
    rcases ρ_surj x with ⟨y, rfl⟩
have hy : y in G inter ρ ⁻¹' N := by simpa using mt (mem_image_of_mem ρ) mem_compl hx
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩

/--
lemma `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen` / 引理 `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`

English:
lemma ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen
  statement: [ExtremallyDisconnected A]
  proof: (h.closure_right hU₁).closure_left open_closure U₂ hU₂

中文:
引理 ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen
  结论: [ExtremallyDisconnected A]
  证明: (h.closure_right hU₁).closure_left open_closure U₂ hU₂

Depends on / 依赖: closure_left, closure_right, h.closure_right, open_closure
-/
lemma ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen [ExtremallyDisconnected A]
    {U₁ U₂ : Set A} (h : Disjoint U₁ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) :
    Disjoint (closure U₁) (closure U₂) :=
(h.closure_right hU₁).closure_left open_closure U₂ hU₂

set_option backward.privateInPublic true in
/--
lemma `ExtremallyDisconnected.homeoCompactToT2_injective` / 引理 `ExtremallyDisconnected.homeoCompactToT2_injective`

English:
lemma ExtremallyDisconnected.homeoCompactToT2_injective
  statement: [ExtremallyDisconnected A]
  proof: by
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
    rw [disjoint_iff_inter_eq_empty]; rw [← compl_union]; rw [← image_union]; rw [← compl_inter]; rw [disjoint_iff_inter_eq_empty.mp disj]; rw [compl_empty]; rw [compl_empty_iff]; rw [image_univ_of_surjective ρ_surj]
  -- apply Lemma 2.2 to prove their closures are disjoint
  have disj'' : Disjoint (closure (ρ '' G₁ᶜ)ᶜ) (closure (ρ '' G₂ᶜ)ᶜ) :=
    disjoint_closure_of_disjoint_isOpen disj' G₁_open' G₂_open'
  -- apply Lemma 2.1 to prove $\rho(x_1) = \rho(x_2)$ lies in their intersection
have hx₁' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₁_open
    mem_image_of_mem ρ hx₁
have hx₂' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₂_open
    mem_image_of_mem ρ hx₂
  exact disj''.ne_of_mem hx₁' hx₂' hρx

中文:
引理 ExtremallyDisconnected.homeoCompactToT2_injective
  结论: [ExtremallyDisconnected A]
  证明: by
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
    rw [disjoint_iff_inter_eq_empty]; rw [← compl_union]; rw [← image_union]; rw [← compl_inter]; rw [disjoint_iff_inter_eq_empty.mp disj]; rw [compl_empty]; rw [compl_empty_iff]; rw [image_univ_of_surjective ρ_surj]
  -- apply Lemma 2.2 to prove their closures are disjoint
  have disj'' : Disjoint (closure (ρ '' G₁ᶜ)ᶜ) (closure (ρ '' G₂ᶜ)ᶜ) :=
    disjoint_closure_of_disjoint_isOpen disj' G₁_open' G₂_open'
  -- apply Lemma 2.1 to prove $\rho(x_1) = \rho(x_2)$ lies in their intersection
have hx₁' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₁_open
    mem_image_of_mem ρ hx₁
have hx₂' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₂_open
    mem_image_of_mem ρ hx₂
  exact disj''.ne_of_mem hx₁' hx₂' hρx
-/
private lemma ExtremallyDisconnected.homeoCompactToT2_injective [ExtremallyDisconnected A]
    [T2Space A] [T2Space E] [CompactSpace E] {ρ : E -> A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : forall E₀ : Set E, E₀ != univ -> IsClosed E₀ -> ρ '' E₀ != univ) :
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
    rw [disjoint_iff_inter_eq_empty]; rw [← compl_union]; rw [← image_union]; rw [← compl_inter]; rw [disjoint_iff_inter_eq_empty.mp disj]; rw [compl_empty]; rw [compl_empty_iff]; rw [image_univ_of_surjective ρ_surj]
  -- apply Lemma 2.2 to prove their closures are disjoint
  have disj'' : Disjoint (closure (ρ '' G₁ᶜ)ᶜ) (closure (ρ '' G₂ᶜ)ᶜ) :=
    disjoint_closure_of_disjoint_isOpen disj' G₁_open' G₂_open'
  -- apply Lemma 2.1 to prove $\rho(x_1) = \rho(x_2)$ lies in their intersection
have hx₁' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₁_open
    mem_image_of_mem ρ hx₁
have hx₂' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₂_open
    mem_image_of_mem ρ hx₂
  exact disj''.ne_of_mem hx₁' hx₂' hρx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `ExtremallyDisconnected.homeoCompactToT2` / `ExtremallyDisconnected.homeoCompactToT2` 的定义

English:
definition ExtremallyDisconnected.homeoCompactToT2
  signature: [ExtremallyDisconnected A] [T2Space A]
  body: ρ_cont.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ρ ⟨homeoCompactToT2_injective ρ_cont ρ_surj zorn_subset, ρ_surj⟩)

中文:
定义 ExtremallyDisconnected.homeoCompactToT2
  签名: [ExtremallyDisconnected A] [T2空间 A]
  定义体: ρ_cont.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ρ ⟨homeoCompactToT2_injective ρ_cont ρ_surj zorn_subset, ρ_surj⟩)

Depends on / 依赖: Equiv.ofBijective, _cont.homeoOfEquivCompactToT2, homeoCompactToT2_injective, homeoOfEquivCompactToT2, ofBijective, zorn_subset
-/
noncomputable def ExtremallyDisconnected.homeoCompactToT2 [ExtremallyDisconnected A] [T2Space A]
    [T2Space E] [CompactSpace E] {ρ : E -> A} (ρ_cont : Continuous ρ) (ρ_surj : ρ.Surjective)
    (zorn_subset : forall E₀ : Set E, E₀ != univ -> IsClosed E₀ -> ρ '' E₀ != univ) : E ≃ₜ A :=
  ρ_cont.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ρ ⟨homeoCompactToT2_injective ρ_cont ρ_surj zorn_subset, ρ_surj⟩)

/--
theorem `CompactT2.ExtremallyDisconnected.projective` / 定理 `CompactT2.ExtremallyDisconnected.projective`

English:
theorem CompactT2.ExtremallyDisconnected.projective
  statement: [ExtremallyDisconnected A]
  proof: by
  -- let $B$ and $C$ be compact; let $f : B \twoheadrightarrow C$ and $\phi : A \to C$ be continuous
  intro B C _ _ _ _ _ _ φ f φ_cont f_cont f_surj
  -- let $D := \{(a, b) : \phi(a) = f(b)\}$ with projections $\pi_1 : D \to A$ and $\pi_2 : D \to B$
let D : Set A × B := {x | φ x.fst = f x.snd}
  have D_comp : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_eq (φ_cont.comp continuous_fst) (f_cont.comp continuous_snd)).isCompact
  -- apply Lemma 2.4 to get closed $E$ satisfying "Zorn subset condition"
  let X₁ : D -> A := Prod.fst ∘ Subtype.val
  have X₁_cont : Continuous X₁ := continuous_fst.comp continuous_subtype_val
  have X₁_surj : X₁.Surjective := fun a => ⟨⟨⟨a, _⟩, (f_surj <| φ a).choose_spec.symm⟩, rfl⟩
  rcases exists_compact_surjective_zorn_subset X₁_cont X₁_surj with ⟨E, _, E_onto, E_min⟩
  -- apply Lemma 2.3 to get homeomorphism $\pi_1|_E : E \to A$
  let ρ : E -> A := E.domRestrict X₁
  have ρ_cont : Continuous ρ := X₁_cont.continuousOn.domRestrict
  have ρ_surj : ρ.Surjective := fun a => by
    rcases (E_onto ▸ mem_univ a : a in X₁ '' E) with ⟨d, ⟨hd, rfl⟩⟩; exact ⟨⟨d, hd⟩, rfl⟩
  let ρ' := ExtremallyDisconnected.homeoCompactToT2 ρ_cont ρ_surj E_min
  -- prove $\rho := \pi_2|_E \circ \pi_1|_E^{-1}$ satisfies $\phi = f \circ \rho$
  let X₂ : D -> B := Prod.snd ∘ Subtype.val
  have X₂_cont : Continuous X₂ := continuous_snd.comp continuous_subtype_val
  refine ⟨E.domRestrict X₂ ∘ ρ'.symm,
    ⟨X₂_cont.continuousOn.domRestrict.comp ρ'.symm.continuous, ?_⟩⟩
  suffices f ∘ E.domRestrict X₂ = φ ∘ ρ' by
    rw [← comp_assoc]; rw [this]; rw [comp_assoc]; rw [Homeomorph.self_comp_symm]; rw [comp_id]
  ext x
  exact x.val.mem.symm

中文:
定理 CompactT2.ExtremallyDisconnected.projective
  结论: [ExtremallyDisconnected A]
  证明: by
  -- let $B$ and $C$ be compact; let $f : B \twoheadrightarrow C$ and $\phi : A \to C$ be continuous
  intro B C _ _ _ _ _ _ φ f φ_cont f_cont f_surj
  -- let $D := \{(a, b) : \phi(a) = f(b)\}$ with projections $\pi_1 : D \to A$ and $\pi_2 : D \to B$
let D : Set A × B := {x | φ x.fst = f x.snd}
  have D_comp : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_eq (φ_cont.comp continuous_fst) (f_cont.comp continuous_snd)).isCompact
  -- apply Lemma 2.4 to get closed $E$ satisfying "Zorn subset condition"
  let X₁ : D -> A := Prod.fst ∘ Subtype.val
  have X₁_cont : Continuous X₁ := continuous_fst.comp continuous_subtype_val
  have X₁_surj : X₁.Surjective := fun a => ⟨⟨⟨a, _⟩, (f_surj <| φ a).choose_spec.symm⟩, rfl⟩
  rcases exists_compact_surjective_zorn_subset X₁_cont X₁_surj with ⟨E, _, E_onto, E_min⟩
  -- apply Lemma 2.3 to get homeomorphism $\pi_1|_E : E \to A$
  let ρ : E -> A := E.domRestrict X₁
  have ρ_cont : Continuous ρ := X₁_cont.continuousOn.domRestrict
  have ρ_surj : ρ.Surjective := fun a => by
    rcases (E_onto ▸ mem_univ a : a in X₁ '' E) with ⟨d, ⟨hd, rfl⟩⟩; exact ⟨⟨d, hd⟩, rfl⟩
  let ρ' := ExtremallyDisconnected.homeoCompactToT2 ρ_cont ρ_surj E_min
  -- prove $\rho := \pi_2|_E \circ \pi_1|_E^{-1}$ satisfies $\phi = f \circ \rho$
  let X₂ : D -> B := Prod.snd ∘ Subtype.val
  have X₂_cont : Continuous X₂ := continuous_snd.comp continuous_subtype_val
  refine ⟨E.domRestrict X₂ ∘ ρ'.symm,
    ⟨X₂_cont.continuousOn.domRestrict.comp ρ'.symm.continuous, ?_⟩⟩
  suffices f ∘ E.domRestrict X₂ = φ ∘ ρ' by
    rw [← comp_assoc]; rw [this]; rw [comp_assoc]; rw [Homeomorph.self_comp_symm]; rw [comp_id]
  ext x
  exact x.val.mem.symm
-/
protected theorem CompactT2.ExtremallyDisconnected.projective [ExtremallyDisconnected A]
    [CompactSpace A] [T2Space A] : CompactT2.Projective A := by
  -- let $B$ and $C$ be compact; let $f : B \twoheadrightarrow C$ and $\phi : A \to C$ be continuous
  intro B C _ _ _ _ _ _ φ f φ_cont f_cont f_surj
  -- let $D := \{(a, b) : \phi(a) = f(b)\}$ with projections $\pi_1 : D \to A$ and $\pi_2 : D \to B$
let D : Set A × B := {x | φ x.fst = f x.snd}
  have D_comp : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_eq (φ_cont.comp continuous_fst) (f_cont.comp continuous_snd)).isCompact
  -- apply Lemma 2.4 to get closed $E$ satisfying "Zorn subset condition"
  let X₁ : D -> A := Prod.fst ∘ Subtype.val
  have X₁_cont : Continuous X₁ := continuous_fst.comp continuous_subtype_val
  have X₁_surj : X₁.Surjective := fun a => ⟨⟨⟨a, _⟩, (f_surj <| φ a).choose_spec.symm⟩, rfl⟩
  rcases exists_compact_surjective_zorn_subset X₁_cont X₁_surj with ⟨E, _, E_onto, E_min⟩
  -- apply Lemma 2.3 to get homeomorphism $\pi_1|_E : E \to A$
  let ρ : E -> A := E.domRestrict X₁
  have ρ_cont : Continuous ρ := X₁_cont.continuousOn.domRestrict
  have ρ_surj : ρ.Surjective := fun a => by
    rcases (E_onto ▸ mem_univ a : a in X₁ '' E) with ⟨d, ⟨hd, rfl⟩⟩; exact ⟨⟨d, hd⟩, rfl⟩
  let ρ' := ExtremallyDisconnected.homeoCompactToT2 ρ_cont ρ_surj E_min
  -- prove $\rho := \pi_2|_E \circ \pi_1|_E^{-1}$ satisfies $\phi = f \circ \rho$
  let X₂ : D -> B := Prod.snd ∘ Subtype.val
  have X₂_cont : Continuous X₂ := continuous_snd.comp continuous_subtype_val
  refine ⟨E.domRestrict X₂ ∘ ρ'.symm,
    ⟨X₂_cont.continuousOn.domRestrict.comp ρ'.symm.continuous, ?_⟩⟩
  suffices f ∘ E.domRestrict X₂ = φ ∘ ρ' by
    rw [← comp_assoc]; rw [this]; rw [comp_assoc]; rw [Homeomorph.self_comp_symm]; rw [comp_id]
  ext x
  exact x.val.mem.symm

/--
theorem `CompactT2.projective_iff_extremallyDisconnected` / 定理 `CompactT2.projective_iff_extremallyDisconnected`

English:
theorem CompactT2.projective_iff_extremallyDisconnected
  given: [CompactSpace A] [T2Space A]
  proof: ⟨Projective.extremallyDisconnected, fun _ => ExtremallyDisconnected.projective⟩

中文:
定理 CompactT2.projective_iff_extremallyDisconnected
  条件: [紧空间 A] [T2空间 A]
  证明: ⟨Projective.extremallyDisconnected, fun _ => ExtremallyDisconnected.projective⟩
-/
protected theorem CompactT2.projective_iff_extremallyDisconnected [CompactSpace A] [T2Space A] :
    Projective A ↔ ExtremallyDisconnected A :=
  ⟨Projective.extremallyDisconnected, fun _ => ExtremallyDisconnected.projective⟩

end

-- Note: It might be possible to use Gleason for this instead
/--
Instance `instExtremallyDisconnected` / 实例 `instExtremallyDisconnected`

English:
instance instExtremallyDisconnected
  signature: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  body: by
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

中文:
实例 instExtremallyDisconnected
  签名: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  定义体: by
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

Depends on / 依赖: IsOpenMap, IsOpenMap.preimage_closure_eq_closure_preimage, Sigma.mk, closure, fun_prop, isOpen_empty, isOpen_sigma_iff, preimage_closure_eq_closure_preimage, sigma_mk_preimage_image, sigma_mk_preimage_image_eq_self
-/
instance instExtremallyDisconnected {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [h₀ : forall i, ExtremallyDisconnected (X i)] : ExtremallyDisconnected (Σ i, X i) := by
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
instance (priority := 100) [h : PreirreducibleSpace X] : ExtremallyDisconnected X where
  open_closure U hU := by
    by_cases! Un : U = ∅
    · simp_all
    · exact ((preirreducibleSpace_iff_open_dense X).mp h hU Un).closure_eq ▸ isOpen_univ

/--
theorem `ExtremallyDisconnected.toPreirreducibleSpace` / 定理 `ExtremallyDisconnected.toPreirreducibleSpace`

English:
theorem ExtremallyDisconnected.toPreirreducibleSpace
  statement: [h : ExtremallyDisconnected X]
  proof: by
  apply (preirreducibleSpace_iff_open_dense X).mpr (fun s hs sn => ?_)
  apply dense_iff_closure_eq.mpr
  cases preconnectedSpace_iff_clopen.mp h' (closure s) ⟨isClosed_closure, h.open_closure s hs⟩
  · simp_all
  · assumption

中文:
定理 ExtremallyDisconnected.toPreirreducibleSpace
  结论: [h : ExtremallyDisconnected X]
  证明: by
  apply (preirreducibleSpace_iff_open_dense X).mpr (fun s hs sn => ?_)
  apply dense_iff_closure_eq.mpr
  cases preconnectedSpace_iff_clopen.mp h' (closure s) ⟨isClosed_closure, h.open_closure s hs⟩
  · simp_all
  · assumption

Depends on / 依赖: closure, dense_iff_closure_eq, dense_iff_closure_eq.mpr, h.open_closure, isClosed_closure, open_closure, preconnectedSpace_iff_clopen, preconnectedSpace_iff_clopen.mp, preirreducibleSpace_iff_open_dense
-/
theorem ExtremallyDisconnected.toPreirreducibleSpace [h : ExtremallyDisconnected X]
    [h' : PreconnectedSpace X] :
    PreirreducibleSpace X := by
  apply (preirreducibleSpace_iff_open_dense X).mpr (fun s hs sn => ?_)
  apply dense_iff_closure_eq.mpr
  cases preconnectedSpace_iff_clopen.mp h' (closure s) ⟨isClosed_closure, h.open_closure s hs⟩
  · simp_all
  · assumption

end
