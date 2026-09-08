/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Open mapping theorem for morphisms of topological groups

We prove that a continuous surjective group morphism from a sigma-compact group to a locally compact
group is automatically open, in `MonoidHom.isOpenMap_of_sigmaCompact`.

We deduce this from a similar statement for the orbits of continuous actions of sigma-compact groups
on Baire spaces, given in `isOpenMap_smul_of_sigmaCompact`.

Note that a sigma-compactness assumption is necessary. Indeed, let `G` be the real line with
the discrete topology, and `H` the real line with the usual topology. Both are locally compact
groups, and the identity from `G` to `H` is continuous but not open.
-/

public section

open scoped Topology Pointwise

open MulAction Set Function

variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
  [Group G] [IsTopologicalGroup G] [MulAction G X]
  [SigmaCompactSpace G] [BaireSpace X] [T2Space X]
  [ContinuousSMul G X] [IsPretransitive G X]

/-- Consider a sigma-compact group acting continuously and transitively on a Baire space. Then
the orbit map is open around the identity. It follows in `isOpenMap_smul_of_sigmaCompact` that it
is open around any point. -/
@[to_additive /-- Consider a sigma-compact additive group acting continuously and transitively on a
Baire space. Then the orbit map is open around zero. It follows in
`isOpenMap_vadd_of_sigmaCompact` that it is open around any point. -/]
/-
**smul_singleton_mem_nhds_of_sigmaCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_singleton_mem_nhds_of_sigmaCompact {U : Set G} (hU : U in 𝓝 1) (x : X
) : U • {x} in 𝓝 x
参数：hU : U in 𝓝 1；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_closed_nhds_one_inv_eq_mul_subset`：exists_closed_nhds_one_inv_eq_
mul_subset {U : Set G} (hU : U in 𝓝 1) : exists V in 𝓝 1, IsClosed V ∧ V⁻¹ = V ∧
 V * V subseteq U
· 使用定理 `countable_cover_nhds_of_sigmaCompact`：countable_cover_nhds_of_sigmaCompa
ct {f : X -> Set X} (hf : forall x, f x in 𝓝 x) : exists s : Set X, s.Countable 
∧ ⋃ x in s, f x = univ
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `nonempty_interior_of_iUnion_of_closed`：nonempty_interior_of_iUnion_of_cl
osed [Countable ι] {f : ι -> Set X} (hc : forall i, IsClosed (f i)) (hU : ⋃ i, f
 i = univ) : exists i, (int…
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `isCompact_compactCovering`：isCompact_compactCovering (n : Nat) : IsCompa
ct (compactCovering X n)
· 使用定理 `IsClosed.smul`：IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsC
losed (c • s)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.smul_singleton`：smul_singleton : s • ({b} : Set β) = (· • b) '' s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `exists_mem_compactCovering`：exists_mem_compactCovering (x : X) : exists 
n, x in compactCovering X n
· 使用定理 `Set.exists_set_mem_of_union_eq_top`：exists_set_mem_of_union_eq_top {ι : 
Type*} (t : Set ι) (s : ι -> Set β) (w : ⋃ i in t, s i = ⊤) (x : β) : exists i i
n t, x in s i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
（共 44 条，此处仅展示前 30 条）
-/
theorem smul_singleton_mem_nhds_of_sigmaCompact
    {U : Set G} (hU : U ∈ 𝓝 1) (x : X) : U • {x} ∈ 𝓝 x := by
  /- Consider a small closed neighborhood `V` of the identity. Then the group is covered by
  countably many translates of `V`, say `gᵢ V`. Let also `Kₙ` be a sequence of compact sets covering
  the space. Then the image of `Kₙ ∩ gᵢ V` in the orbit is compact, and their unions covers the
  space. By Baire, one of them has nonempty interior. Then `gᵢ V • x` has nonempty interior, and
  so does `V • x`. Its interior contains a point `g' x` with `g' ∈ V`. Then `g'⁻¹ • V • x` contains
  a neighborhood of `x`, and it is included in `V⁻¹ • V • x`, which is itself contained in `U • x`
  if `V` is small enough. -/
  obtain ⟨V, V_mem, V_closed, V_symm, VU⟩ : ∃ V ∈ 𝓝 (1 : G), IsClosed V ∧ V⁻¹ = V ∧ V * V ⊆ U :=
    exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨s, s_count, hs⟩ : ∃ (s : Set G), s.Countable ∧ ⋃ g ∈ s, g • V = univ :=
    countable_cover_nhds_of_sigmaCompact fun _ ↦ by simpa
  let K : ℕ → Set G := compactCovering G
  let F : ℕ × s → Set X := fun p ↦ (K p.1 ∩ (p.2 : G) • V) • ({x} : Set X)
  obtain ⟨⟨n, ⟨g, hg⟩⟩, hi⟩ : ∃ i, (interior (F i)).Nonempty := by
    have : Nonempty X := ⟨x⟩
    have : Encodable s := Countable.toEncodable s_count
    apply nonempty_interior_of_iUnion_of_closed
    · rintro ⟨n, ⟨g, hg⟩⟩
      apply IsCompact.isClosed
      suffices H : IsCompact ((fun (g : G) ↦ g • x) '' (K n ∩ g • V)) by
        simpa only [F, smul_singleton] using H
      apply IsCompact.image ?_ (by fun_prop)
      exact (isCompact_compactCovering G n).inter_right (V_closed.smul g)
    · apply eq_univ_iff_forall.2 (fun y ↦ ?_)
      obtain ⟨h, rfl⟩ : ∃ h, h • x = y := exists_smul_eq G x y
      obtain ⟨n, hn⟩ : ∃ n, h ∈ K n := exists_mem_compactCovering h
      obtain ⟨g, gs, hg⟩ : ∃ g ∈ s, h ∈ g • V := exists_set_mem_of_union_eq_top s _ hs _
      simp only [F, smul_singleton, mem_iUnion, mem_image, mem_inter_iff, Prod.exists,
        Subtype.exists, exists_prop]
      exact ⟨n, g, gs, h, ⟨hn, hg⟩, rfl⟩
  have I : (interior ((g • V) • {x})).Nonempty := by
    apply hi.mono
    apply interior_mono
    exact smul_subset_smul_right inter_subset_right
  obtain ⟨y, hy⟩ : (interior (V • ({x} : Set X))).Nonempty := by
    rw [smul_assoc, interior_smul] at I
    exact smul_set_nonempty.1 I
  obtain ⟨g', hg', rfl⟩ : ∃ g' ∈ V, g' • x = y := by simpa using interior_subset hy
  have J : (g'⁻¹ • V) • {x} ∈ 𝓝 x := by
    apply mem_interior_iff_mem_nhds.1
    rwa [smul_assoc, interior_smul, mem_inv_smul_set_iff]
  have : (g'⁻¹ • V) • {x} ⊆ U • ({x} : Set X) := by
    apply smul_subset_smul_right
    apply Subset.trans (smul_set_subset_smul (inv_mem_inv.2 hg')) ?_
    rw [V_symm]
    exact VU
  exact Filter.mem_of_superset J this

/-- Consider a sigma-compact group acting continuously and transitively on a Baire space. Then
the orbit map is open. This is a version of the open mapping theorem, valid notably for the
action of a sigma-compact locally compact group on a locally compact space. -/
@[to_additive /-- Consider a sigma-compact additive group acting continuously and transitively on a
Baire space. Then the orbit map is open. This is a version of the open mapping theorem, valid
notably for the action of a sigma-compact locally compact group on a locally compact space. -/]
/-
**isOpenMap_smul_of_sigmaCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_smul_of_sigmaCompact (x : X) : IsOpenMap (fun (g : G) => g • x)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.smul_singleton`：smul_singleton : s • ({b} : Set β) = (· • b) '' s
· 使用定理 `smul_singleton_mem_nhds_of_sigmaCompact`：smul_singleton_mem_nhds_of_sigm
aCompact {U : Set G} (hU : U in 𝓝 1) (x : X) : U • {x} in 𝓝 x
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `IsOpenMap.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ {x : 
X} {s : Set X}…
· 使用定理 `isOpenMap_mul_right`：isOpenMap_mul_right (a : G) : IsOpenMap (· * a)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
theorem isOpenMap_smul_of_sigmaCompact (x : X) : IsOpenMap (fun (g : G) ↦ g • x) := by
  /- We have already proved the theorem around the basepoint of the orbit, in
  `smul_singleton_mem_nhds_of_sigmaCompact`. The general statement follows around an arbitrary
  point by changing basepoints. -/
  simp_rw [isOpenMap_iff_nhds_le, Filter.le_map_iff]
  intro g U hU
  have : (· • x) = (· • (g • x)) ∘ (· * g⁻¹) := by
    ext g
    simp [smul_smul]
  rw [this, image_comp, ← smul_singleton]
  apply smul_singleton_mem_nhds_of_sigmaCompact
  simpa using isOpenMap_mul_right g⁻¹ |>.image_mem_nhds hU

/-- A surjective morphism of topological groups is open when the source group is sigma-compact and
the target group is a Baire space (for instance a locally compact group). -/
@[to_additive]
/-
**MonoidHom.isOpenMap_of_sigmaCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.isOpenMap_of_sigmaCompact {H : Type*} [Group H] [TopologicalSpac
e H] [BaireSpace H] [T2Space H] [ContinuousMul H] (f : G ->* H) (hf : Function.S
urjective f) (h'f : Continuous f) : IsOpenMap f
参数：f : G ->* H；hf : Function.Surjective f；h'f : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.continuousSMul_compHom`：MulAction.continuousSMul_compHom {N : 
Type*} [TopologicalSpace N] [Monoid N] {f : N ->* M} (hf : Continuous f) : letI 
: MulAction N X
· 使用引理 `MulAction.isPretransitive_compHom`：isPretransitive_compHom {E F G : Type
*} [Monoid E] [Monoid F] [MulAction F G] [IsPretransitive F G] {f : E ->* F} (hf
 : Surjective f) : letI…
· 使用定理 `MulAction.Regular.isPretransitive`：∀ {G : Type u_2} [inst : Group G], Mu
lAction.IsPretransitive G G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isOpenMap_smul_of_sigmaCompact`：isOpenMap_smul_of_sigmaCompact (x : X) :
 IsOpenMap (fun (g : G) => g • x)

--- 原说明 ---
A surjective morphism of topological groups is open when the source group is sig
ma-compact and
the target group is a Baire space (for instance a locally compact group).
-/
theorem MonoidHom.isOpenMap_of_sigmaCompact
    {H : Type*} [Group H] [TopologicalSpace H] [BaireSpace H] [T2Space H] [ContinuousMul H]
    (f : G →* H) (hf : Function.Surjective f) (h'f : Continuous f) :
    IsOpenMap f := by
  let A : MulAction G H := MulAction.compHom _ f
  have : ContinuousSMul G H := continuousSMul_compHom h'f
  have : IsPretransitive G H := isPretransitive_compHom hf
  have : f = (fun (g : G) ↦ g • (1 : H)) := by simp [A, MulAction.compHom_smul_def]
  rw [this]
  exact isOpenMap_smul_of_sigmaCompact _
