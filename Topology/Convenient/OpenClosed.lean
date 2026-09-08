/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Convenient.GeneratedBy
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds

/-!
# Open or closed subsets that are also `X`-generated spaces

Let `X : ι → Type*` be a family of topological spaces.
If all the opens (resp. closed) subsets of the `X i` are
`X`-generated, then any open (resp. closed) subset of
an `X`-generated space is `X`-generated.

-/

public section

open Topology

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  {Y : Type*} [TopologicalSpace Y]

section

variable [∀ (i : ι) (U : TopologicalSpace.Opens (X i)), IsGeneratedBy X U]

/-
**IsOpen.isGeneratedBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.isGeneratedBy [IsGeneratedBy X Y] {U : Set Y} (hU : IsOpen U) : IsG
eneratedBy X U
参数：hU : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用引理 `Topology.IsGeneratedBy.isOpen_iff`：isOpen_iff {U : Set Y} : IsOpen U ↔ f
orall ⦃i : ι⦄ (f : C(X i, Y)), IsOpen (f ⁻¹' U)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.restrictPreimage_coe`：∀ {α : Type u} {β : Type v} (t : Set β) (f : α
 → β) (a : ↑(f ⁻¹' t)), ↑(t.restrictPreimage f a) = f ↑a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsGeneratedBy.equiv_symm_comp_continuous_iff`：equiv_symm_comp_c
ontinuous_iff (g : Y -> Z) : Continuous ((WithGeneratedByTopology.equiv (X
-/
lemma IsOpen.isGeneratedBy [IsGeneratedBy X Y] {U : Set Y} (hU : IsOpen U) :
    IsGeneratedBy X U := by
  let W (a : Σ (i : ι), C(X i, Y)) : TopologicalSpace.Opens (X a.1) :=
    ⟨a.2 ⁻¹' U, a.2.continuous.isOpen_preimage U hU⟩
  let g (a) : W a → U := U.restrictPreimage a.2
  have hg (a) : Continuous (g a) := a.2.continuous.restrictPreimage
  suffices ∀ (V : Set U), (∀ a, IsOpen ((g a) ⁻¹' V)) → IsOpen V by
    constructor
    rw [continuous_def]
    exact fun _ hV ↦ this _ (fun a ↦
      ((IsGeneratedBy.equiv_symm_comp_continuous_iff X _).2 (hg a)).isOpen_preimage _ hV)
  intro V hV
  obtain ⟨V, hV, rfl⟩ : ∃ (T : Set Y), T ⊆ U ∧ V = Subtype.val ⁻¹' T :=
    ⟨Subtype.val '' V, by simp, by simp⟩
  refine continuous_subtype_val.isOpen_preimage _ ?_
  rw [IsGeneratedBy.isOpen_iff X]
  intro i f
  convert! (W ⟨i, f⟩).isOpen.isOpenMap_subtype_val _ (hV ⟨i, f⟩)
  aesop
/-
**Topology.IsOpenEmbedding.isGeneratedBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.isGeneratedBy [IsGeneratedBy X Y] {F : Type*} [To
pologicalSpace F] {f : F -> Y} (hf : IsOpenEmbedding f) : IsGeneratedBy X F
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOpen.isGeneratedBy`：IsOpen.isGeneratedBy [IsGeneratedBy X Y] {U : Set 
Y} (hU : IsOpen U) : IsGeneratedBy X U
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Topology.IsQuotientMap.isGeneratedBy`：∀ {ι : Type t} {X : ι → Type u} [i
nst : (i : ι) → TopologicalSpace (X i)] {Y : Type v} [tY : TopologicalSpace Y]  
 {Z : Type v'} [inst_1 : T…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
-/
lemma Topology.IsOpenEmbedding.isGeneratedBy [IsGeneratedBy X Y]
    {F : Type*} [TopologicalSpace F] {f : F → Y}
    (hf : IsOpenEmbedding f) :
    IsGeneratedBy X F :=
  have := hf.isOpen_range.isGeneratedBy (X := X)
  hf.toIsEmbedding.toHomeomorph.symm.isQuotientMap.isGeneratedBy

end

section

variable [∀ (i : ι) (F : TopologicalSpace.Closeds (X i)), IsGeneratedBy X F]

/-
**IsClosed.isGeneratedBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.isGeneratedBy [IsGeneratedBy X Y] {F : Set Y} (hF : IsClosed F) :
 IsGeneratedBy X F
参数：hF : IsClosed F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用引理 `Topology.IsGeneratedBy.isClosed_iff`：isClosed_iff {U : Set Y} : IsClosed
 U ↔ forall ⦃i : ι⦄ (f : C(X i, Y)), IsClosed (f ⁻¹' U)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.restrictPreimage_coe`：∀ {α : Type u} {β : Type v} (t : Set β) (f : α
 → β) (a : ↑(f ⁻¹' t)), ↑(t.restrictPreimage f a) = f ↑a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsClosed.isClosedMap_subtype_val`：IsClosed.isClosedMap_subtype_val {s : 
Set X} (hs : IsClosed s) : IsClosedMap ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Closeds.isClosed`：isClosed (s : Closeds α) : IsClosed (
s : Set α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsGeneratedBy.equiv_symm_comp_continuous_iff`：equiv_symm_comp_c
ontinuous_iff (g : Y -> Z) : Continuous ((WithGeneratedByTopology.equiv (X
-/
lemma IsClosed.isGeneratedBy [IsGeneratedBy X Y] {F : Set Y} (hF : IsClosed F) :
    IsGeneratedBy X F := by
  let W (a : Σ (i : ι), C(X i, Y)) : TopologicalSpace.Closeds (X a.1) :=
    ⟨a.2 ⁻¹' F, IsClosed.preimage a.2.continuous hF⟩
  let g (a) : W a → F := F.restrictPreimage a.2
  have hg (a) : Continuous (g a) := a.2.continuous.restrictPreimage
  suffices ∀ (V : Set F), (∀ a, IsClosed ((g a) ⁻¹' V)) → IsClosed V by
    constructor
    rw [continuous_iff_isClosed]
    exact fun _ hV ↦ this _ (fun a ↦ IsClosed.preimage
      ((IsGeneratedBy.equiv_symm_comp_continuous_iff X _).2 (hg a)) hV)
  intro V hV
  obtain ⟨V, hV, rfl⟩ : ∃ (T : Set Y), T ⊆ F ∧ V = Subtype.val ⁻¹' T :=
    ⟨Subtype.val '' V, by simp, by simp⟩
  refine IsClosed.preimage continuous_subtype_val ?_
  rw [IsGeneratedBy.isClosed_iff X]
  intro i f
  convert! (W ⟨i, f⟩).isClosed.isClosedMap_subtype_val _ (hV ⟨i, f⟩)
  aesop
/-
**Topology.IsClosedEmbedding.isGeneratedBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.isGeneratedBy [IsGeneratedBy X Y] {U : Type*} [
TopologicalSpace U] {f : U -> Y} (hf : IsClosedEmbedding f) : IsGeneratedBy X U
参数：hf : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.isGeneratedBy`：IsClosed.isGeneratedBy [IsGeneratedBy X Y] {F : 
Set Y} (hF : IsClosed F) : IsGeneratedBy X F
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Topology.IsQuotientMap.isGeneratedBy`：∀ {ι : Type t} {X : ι → Type u} [i
nst : (i : ι) → TopologicalSpace (X i)] {Y : Type v} [tY : TopologicalSpace Y]  
 {Z : Type v'} [inst_1 : T…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
-/
lemma Topology.IsClosedEmbedding.isGeneratedBy [IsGeneratedBy X Y]
    {U : Type*} [TopologicalSpace U] {f : U → Y}
    (hf : IsClosedEmbedding f) :
    IsGeneratedBy X U :=
  have := hf.isClosed_range.isGeneratedBy (X := X)
  hf.toIsEmbedding.toHomeomorph.symm.isQuotientMap.isGeneratedBy

end

