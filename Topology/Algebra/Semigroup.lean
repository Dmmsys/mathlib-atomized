/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Idempotents in topological semigroups

This file provides a sufficient condition for a semigroup `M` to contain an idempotent (i.e. an
element `m` such that `m * m = m `), namely that `M` is a nonempty compact Hausdorff space where
right-multiplication by constants is continuous.

We also state a corresponding lemma guaranteeing that a subset of `M` contains an idempotent.
-/

public section


/-- Any nonempty compact Hausdorff semigroup where right-multiplication is continuous contains
an idempotent, i.e. an `m` such that `m * m = m`. -/
@[to_additive
      /-- Any nonempty compact Hausdorff additive semigroup where right-addition is continuous
      contains an idempotent, i.e. an `m` such that `m + m = m` -/]
/-
**exists_idempotent_of_compact_t2_of_continuous_mul_left** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：exists_idempotent_of_compact_t2_of_continuous_mul_left {M} [Nonempty M] [S
emigroup M] [TopologicalSpace M] [CompactSpace M] [T2Space M] (continuous_const_
mul : forall r : M, Continuous (· * r)) : exists m : M, m * m = m
参数：continuous_const_mul : forall r : M, Continuous (· * r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_superset`：zorn_superset (S : Set (Set α)) (h : forall c subseteq S,
 IsChain (· subseteq ·) c -> exists lb in S, forall s in c, lb subseteq s) : exi
sts…
· 使用定理 `isClosed_sInter`：isClosed_sInter {s : Set (Set X)} : (forall t in s, IsC
losed t) -> IsClosed (⋂₀ s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.sInter_eq_iInter`：sInter_eq_iInter {s : Set (Set α)} : ⋂₀ s = ⋂ i : 
s, i
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `Set.Nonempty.coe_sort`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty
 ↑s
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `instReflGe`：∀ {α : Type u} [inst : Preorder α], Std.Refl fun x1 x2 => x2
 ≤ x1
· 使用定理 `IsChain.symm`：IsChain.symm (h : IsChain r s) : IsChain (flip r) s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `Set.mem_sInter`：mem_sInter {x : α} {S : Set (Set α)} : x in ⋂₀ S ↔ foral
l t in S, x in t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `Minimal.eq_of_subset`：Minimal.eq_of_subset (h : Minimal P s) (ht : P t) 
(hts : t subseteq s) : t = s
· 使用定理 `Continuous.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X 
→ Y}, Contin…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
（共 32 条，此处仅展示前 30 条）
-/
theorem exists_idempotent_of_compact_t2_of_continuous_mul_left {M} [Nonempty M] [Semigroup M]
    [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (continuous_const_mul : ∀ r : M, Continuous (· * r)) : ∃ m : M, m * m = m := by
  /- We apply Zorn's lemma to the poset of nonempty closed subsemigroups of `M`.
     It will turn out that any minimal element is `{m}` for an idempotent `m : M`. -/
  let S : Set (Set M) :=
    { N | IsClosed N ∧ N.Nonempty ∧ ∀ (m) (_ : m ∈ N) (m') (_ : m' ∈ N), m * m' ∈ N }
  rsuffices ⟨N, hN⟩ : ∃ N', Minimal (· ∈ S) N'
  · obtain ⟨N_closed, ⟨m, hm⟩, N_mul⟩ := hN.prop
    use m
    /- We now have an element `m : M` of a minimal subsemigroup `N`, and want to show `m + m = m`.
    We first show that every element of `N` is of the form `m' + m`. -/
    have scaling_eq_self : (· * m) '' N = N := by
      apply hN.eq_of_subset
      · refine ⟨(continuous_const_mul m).isClosedMap _ N_closed, ⟨_, ⟨m, hm, rfl⟩⟩, ?_⟩
        rintro _ ⟨m'', hm'', rfl⟩ _ ⟨m', hm', rfl⟩
        exact ⟨m'' * m * m', N_mul _ (N_mul _ hm'' _ hm) _ hm', mul_assoc _ _ _⟩
      · rintro _ ⟨m', hm', rfl⟩
        exact N_mul _ hm' _ hm
    /- In particular, this means that `m' * m = m` for some `m'`. We now use minimality again
       to show that this holds for all `m' ∈ N`. -/
    have absorbing_eq_self : N ∩ { m' | m' * m = m } = N := by
      apply hN.eq_of_subset
      · refine ⟨N_closed.inter ((T1Space.t1 m).preimage (continuous_const_mul m)), ?_, ?_⟩
        · rwa [← scaling_eq_self] at hm
        · rintro m'' ⟨mem'', eq'' : _ = m⟩ m' ⟨mem', eq' : _ = m⟩
          refine ⟨N_mul _ mem'' _ mem', ?_⟩
          rw [Set.mem_ofPred_eq, mul_assoc, eq', eq'']
      apply Set.inter_subset_left
    rw [← absorbing_eq_self] at hm
    exact hm.2
  refine zorn_superset _ fun c hcs hc => ?_
  refine
    ⟨⋂₀ c, ⟨isClosed_sInter fun t ht => (hcs ht).1, ?_, fun m hm m' hm' => ?_⟩, fun s hs =>
      Set.sInter_subset_of_mem hs⟩
  · obtain rfl | hcnemp := c.eq_empty_or_nonempty
    · rw [Set.sInter_empty]
      apply Set.univ_nonempty
    convert!
      @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ _ _ hcnemp.coe_sort
        ((↑) : c → Set M) ?_ ?_ ?_ ?_
    · exact Set.sInter_eq_iInter
    · refine DirectedOn.directed_val (IsChain.directedOn hc.symm)
    exacts [fun i => (hcs i.prop).2.1, fun i => (hcs i.prop).1.isCompact, fun i => (hcs i.prop).1]
  · rw [Set.mem_sInter]
    exact fun t ht => (hcs ht).2.2 m (Set.mem_sInter.mp hm t ht) m' (Set.mem_sInter.mp hm' t ht)

/-- A version of `exists_idempotent_of_compact_t2_of_continuous_mul_left` where the idempotent lies
in some specified nonempty compact subsemigroup. -/
@[to_additive exists_idempotent_in_compact_add_subsemigroup
      /-- A version of
      `exists_idempotent_of_compact_t2_of_continuous_add_left` where the idempotent lies in
      some specified nonempty compact additive subsemigroup. -/]
/-
**exists_idempotent_in_compact_subsemigroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_idempotent_in_compact_subsemigroup {M} [Semigroup M] [TopologicalSp
ace M] [T2Space M] (continuous_const_mul : forall r : M, Continuous (· * r)) (s 
: Set M) (snemp : s.Nonempty) (s_compact : IsCompact s) (s_add : forallᵉ (x in s
) (y in s), x * y in s) : exists m in s, m * m = m
参数：continuous_const_mul : forall r : M, Continuous (· * r)；s : Set M；snemp : s.N
onempty；s_compact : IsCompact s；s_add : forallᵉ (x in s) (y in s), x * y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `exists_idempotent_of_compact_t2_of_continuous_mul_left`：exists_idempoten
t_of_compact_t2_of_continuous_mul_left {M} [Nonempty M] [Semigroup M] [Topologic
alSpace M] [CompactSpace M] [T2Space M] (con…
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem exists_idempotent_in_compact_subsemigroup {M} [Semigroup M] [TopologicalSpace M] [T2Space M]
    (continuous_const_mul : ∀ r : M, Continuous (· * r)) (s : Set M) (snemp : s.Nonempty)
    (s_compact : IsCompact s) (s_add : ∀ᵉ (x ∈ s) (y ∈ s), x * y ∈ s) :
    ∃ m ∈ s, m * m = m := by
  let M' := { m // m ∈ s }
  let : Semigroup M' :=
    { mul := fun p q => ⟨p.1 * q.1, s_add _ p.2 _ q.2⟩
      mul_assoc := fun p q r => Subtype.ext (mul_assoc _ _ _) }
  have : CompactSpace M' := isCompact_iff_compactSpace.mp s_compact
  have : Nonempty M' := nonempty_subtype.mpr snemp
  have : ∀ p : M', Continuous (· * p) := fun p =>
    ((continuous_const_mul p.1).comp continuous_subtype_val).subtype_mk _
  obtain ⟨⟨m, hm⟩, idem⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left this
  exact ⟨m, hm, Subtype.ext_iff.mp idem⟩
