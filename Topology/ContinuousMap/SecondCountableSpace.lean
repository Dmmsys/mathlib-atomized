/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Second countable topology on `C(X, Y)`

In this file we prove that `C(X, Y)` with compact-open topology has second countable topology, if

- both `X` and `Y` have second countable topology;
- `X` is a locally compact space;
-/

public section

open scoped Topology
open Set Function Filter TopologicalSpace

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-
**ContinuousMap.compactOpen_eq_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMap`。
形式化陈述：compactOpen_eq_generateFrom {S : Set (Set X)} {T : Set (Set Y)} (hS₁ : for
all K in S, IsCompact K) (hT : IsTopologicalBasis T) (hS₂ : forall f : C(X, Y), 
forall x, forall V in T, f x in V -> exists K in S, K in 𝓝 x ∧ MapsTo f K V) : c
ompactOpen = .generateFrom (.image2 (fun K t => {f : C(X, Y) | MapsTo f K (⋃₀ t)
}) S {t : Set (Set Y) | t.Finite ∧ t subseteq T})
参数：Set X；Set Y；hS₁ : forall K in S, IsCompact K；hT : IsTopologicalBasis T；hS₂ : 
forall f : C(X, Y), forall x, forall V in T, f x in V -> exists K in S, K in 𝓝 x
 ∧ MapsTo f K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `TopologicalSpace.generateFrom_anti`：generateFrom_anti {α} {g₁ g₂ : Set (
Set α)} (h : g₁ subseteq g₂) : generateFrom g₂ <= generateFrom g₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
· 使用定理 `isOpen_sUnion`：isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpe
n t) : IsOpen (⋃₀ s)
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_of_nhds_le_nhds`：le_of_nhds_le_nhds (h : forall x, @nhds α t₁ x <= @n
hds α t₂ x) : t₁ <= t₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMap.nhds_compactOpen`：nhds_compactOpen (f : C(X, Y)) : 𝓝 f = ⨅
 (K : Set X) (_ : IsCompact K) (U : Set Y) (_ : IsOpen U) (_ : MapsTo f K U), 𝓟 
{g : C(X, Y) | MapsT…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `IsCompact.elim_finite_subcover_image`：IsCompact.elim_finite_subcover_ima
ge {b : Set ι} {c : ι -> Set X} (hs : IsCompact s) (hc₁ : forall i in b, IsOpen 
(c i)) (hc₂ : s subseteq ⋃…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'`：∀ {α : Type u} [t :
 TopologicalSpace α] {B : Set (Set α)},   TopologicalSpace.IsTopologicalBasis B 
→ ∀ {u : Set α}, IsOpen u → u = ⋃₀ {s | s…
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
（共 43 条，此处仅展示前 30 条）
-/
theorem compactOpen_eq_generateFrom {S : Set (Set X)} {T : Set (Set Y)}
    (hS₁ : ∀ K ∈ S, IsCompact K) (hT : IsTopologicalBasis T)
    (hS₂ : ∀ f : C(X, Y), ∀ x, ∀ V ∈ T, f x ∈ V → ∃ K ∈ S, K ∈ 𝓝 x ∧ MapsTo f K V) :
    compactOpen = .generateFrom (.image2 (fun K t ↦
      {f : C(X, Y) | MapsTo f K (⋃₀ t)}) S {t : Set (Set Y) | t.Finite ∧ t ⊆ T}) := by
  apply le_antisymm
  · apply_rules [generateFrom_anti, image2_subset_iff.mpr]
    intro K hK t ht
    exact mem_image2_of_mem (hS₁ K hK) (isOpen_sUnion fun _ h ↦ hT.isOpen <| ht.2 h)
  · refine le_of_nhds_le_nhds fun f ↦ ?_
    simp only [nhds_compactOpen, le_iInf_iff, le_principal_iff]
    intro K (hK : IsCompact K) U (hU : IsOpen U) hfKU
    simp only [TopologicalSpace.nhds_generateFrom]
    obtain ⟨t, htT, htf, hTU, hKT⟩ : ∃ t ⊆ T, t.Finite ∧ (∀ V ∈ t, V ⊆ U) ∧ f '' K ⊆ ⋃₀ t := by
      rw [hT.open_eq_sUnion' hU, mapsTo_iff_image_subset, sUnion_eq_biUnion] at hfKU
      obtain ⟨t, ht, hfin, htK⟩ :=
        (hK.image (map_continuous f)).elim_finite_subcover_image (fun V hV ↦ hT.isOpen hV.1) hfKU
      refine ⟨t, fun _ h ↦ (ht h).1, hfin, fun _ h ↦ (ht h).2, ?_⟩
      rwa [sUnion_eq_biUnion]
    rw [image_subset_iff] at hKT
    obtain ⟨s, hsS, hsf, hKs, hst⟩ : ∃ s ⊆ S, s.Finite ∧ K ⊆ ⋃₀ s ∧ MapsTo f (⋃₀ s) (⋃₀ t) := by
      have : ∀ x ∈ K, ∃ L ∈ S, L ∈ 𝓝 x ∧ MapsTo f L (⋃₀ t) := by
        intro x hx
        rcases hKT hx with ⟨V, hVt, hxV⟩
        rcases hS₂ f x V (htT hVt) hxV with ⟨L, hLS, hLx, hLV⟩
        exact ⟨L, hLS, hLx, hLV.mono_right <| subset_sUnion_of_mem hVt⟩
      choose! L hLS hLmem hLt using this
      rcases hK.elim_nhds_subcover L hLmem with ⟨s, hsK, hs⟩
      refine ⟨L '' s, image_subset_iff.2 fun x hx ↦ hLS x <| hsK x hx, s.finite_toSet.image _,
        by rwa [sUnion_image], ?_⟩
      rw [mapsTo_sUnion, forall_mem_image]
      exact fun x hx ↦ hLt x <| hsK x hx
    have hsub : (⋂ L ∈ s, {g : C(X, Y) | MapsTo g L (⋃₀ t)}) ⊆ {g | MapsTo g K U} := by
      simp only [← ofPred_forall, ← mapsTo_iUnion, ← sUnion_eq_biUnion]
      exact fun g hg ↦ hg.mono hKs (sUnion_subset hTU)
    refine mem_of_superset ((biInter_mem hsf).2 fun L hL ↦ ?_) hsub
    refine mem_iInf_of_mem _ <| mem_iInf_of_mem ?_ <| mem_principal_self _
    exact ⟨hst.mono_left (subset_sUnion_of_mem hL), mem_image2_of_mem (hsS hL) ⟨htf, htT⟩⟩

/-- A version of `instSecondCountableTopology` with a technical assumption
instead of `[SecondCountableTopology X] [LocallyCompactSpace X]`.
It is here as a reminder of what could be an intermediate goal,
if someone tries to weaken the assumptions in the instance
(e.g., from `[LocallyCompactSpace X]` to `[LocallyCompactPair X Y]` - not sure if it's true). -/
/-
**ContinuousMap.secondCountableTopology** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
`。
形式化陈述：secondCountableTopology [SecondCountableTopology Y] (hX : exists S : Set (
Set X), S.Countable ∧ (forall K in S, IsCompact K) ∧ forall f : C(X, Y), forall 
V, IsOpen V -> forall x in f ⁻¹' V, exists K in S, K in 𝓝 x ∧ MapsTo f K V) : Se
condCountableTopology C(X, Y) where is_open_generated_countable
参数：hX : exists S : Set (Set X), S.Countable ∧ (forall K in S, IsCompact K) ∧ for
all f : C(X, Y), forall V, IsOpen V -> forall x in f ⁻¹' V, exists K in S, K in 
𝓝 x ∧ MapsTo f K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.image2`：∀ {α : Type u} {β : Type v} {γ : Type w} {s : Set 
α} {t : Set β},   s.Countable → t.Countable → ∀ (f : α → β → γ), (Set.image2 f s
 t).Counta…
· 使用定理 `Set.countable_ofPred_finite_subset`：countable_ofPred_finite_subset {s : 
Set α} (hs : s.Countable) : { t | Set.Finite t ∧ t subseteq s }.Countable
· 使用定理 `TopologicalSpace.countable_countableBasis`：countable_countableBasis [Sec
ondCountableTopology α] : (countableBasis α).Countable
· 使用定理 `ContinuousMap.compactOpen_eq_generateFrom`：compactOpen_eq_generateFrom {
S : Set (Set X)} {T : Set (Set Y)} (hS₁ : forall K in S, IsCompact K) (hT : IsTo
pologicalBasis T) (hS₂ : forall…
· 使用定理 `TopologicalSpace.isBasis_countableBasis`：isBasis_countableBasis [SecondC
ountableTopology α] : IsTopologicalBasis (countableBasis α)
· 使用定理 `TopologicalSpace.isOpen_of_mem_countableBasis`：isOpen_of_mem_countableBa
sis [SecondCountableTopology α] {s : Set α} (hs : s in countableBasis α) : IsOpe
n s

--- 原说明 ---
A version of `instSecondCountableTopology` with a technical assumption
instead of `[SecondCountableTopology X] [LocallyCompactSpace X]`.
It is here as a reminder of what could be an intermediate goal,
if someone tries to weaken the assumptions in the instance
(e.g., from `[LocallyCompactSpace X]` to `[LocallyCompactPair X Y]` - not sure i
f it's true).
-/
theorem secondCountableTopology [SecondCountableTopology Y]
    (hX : ∃ S : Set (Set X), S.Countable ∧ (∀ K ∈ S, IsCompact K) ∧
      ∀ f : C(X, Y), ∀ V, IsOpen V → ∀ x ∈ f ⁻¹' V, ∃ K ∈ S, K ∈ 𝓝 x ∧ MapsTo f K V) :
    SecondCountableTopology C(X, Y) where
  is_open_generated_countable := by
    rcases hX with ⟨S, hScount, hScomp, hS⟩
    refine ⟨_, ?_, compactOpen_eq_generateFrom (S := S) hScomp (isBasis_countableBasis _) ?_⟩
    · exact .image2 hScount (countable_ofPred_finite_subset (countable_countableBasis Y)) _
    · intro f x V hV hx
      apply hS
      exacts [isOpen_of_mem_countableBasis hV, hx]
/-
**ContinuousMap.instSecondCountableTopology** 是 Mathlib 中的一个实例，位于命名空间 `Continuou
sMap`。
形式化陈述：instSecondCountableTopology [SecondCountableTopology X] [LocallyCompactSpa
ce X] [SecondCountableTopology Y] : SecondCountableTopology C(X, Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.secondCountableTopology`：secondCountableTopology [SecondCo
untableTopology Y] (hX : exists S : Set (Set X), S.Countable ∧ (forall K in S, I
sCompact K) ∧ forall f : C(…
· 使用定理 `IsOpen.locallyCompactSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [LocallyCompactSpace X] {s : Set X}, IsOpen s → LocallyCompactSpace ↑s
· 使用定理 `TopologicalSpace.isOpen_of_mem_countableBasis`：isOpen_of_mem_countableBa
sis [SecondCountableTopology α] {s : Set α} (hs : s in countableBasis α) : IsOpe
n s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `sigmaCompactSpace_of_locallyCompact_secondCountable`：∀ {X : Type u_1} [i
nst : TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X], S
igmaCompactSpace X
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `CompactExhaustion.isCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X
] (K : CompactExhaustion X) (n : ℕ), IsCompact (K n)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `TopologicalSpace.isBasis_countableBasis`：isBasis_countableBasis [SecondC
ountableTopology α] : IsTopologicalBasis (countableBasis α)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `CompactExhaustion.exists_mem_nhds`：exists_mem_nhds (x : X) : exists n, K
 n in 𝓝 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
（共 33 条，此处仅展示前 30 条）
-/
instance instSecondCountableTopology [SecondCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopology Y] : SecondCountableTopology C(X, Y) := by
  apply secondCountableTopology
  have (U : countableBasis X) : LocallyCompactSpace U.1 :=
    (isOpen_of_mem_countableBasis U.2).locallyCompactSpace
  set K := fun U : countableBasis X ↦ CompactExhaustion.choice U.1
  use ⋃ U : countableBasis X, Set.range fun n ↦ K U n
  refine ⟨countable_iUnion fun _ ↦ countable_range _, ?_, ?_⟩
  · simp only [mem_iUnion, mem_range]
    rintro K ⟨U, n, rfl⟩
    exact ((K U).isCompact _).image continuous_subtype_val
  · intro f V hVo x hxV
    obtain ⟨U, hU, hxU, hUV⟩ : ∃ U ∈ countableBasis X, x ∈ U ∧ U ⊆ f ⁻¹' V := by
      rw [← (isBasis_countableBasis _).mem_nhds_iff]
      exact (hVo.preimage (map_continuous f)).mem_nhds hxV
    lift x to U using hxU
    lift U to countableBasis X using hU
    rcases (K U).exists_mem_nhds x with ⟨n, hn⟩
    refine ⟨K U n, mem_iUnion.2 ⟨U, mem_range_self _⟩, ?_, ?_⟩
    · rw [← map_nhds_subtype_coe_eq_nhds x.2]
      exacts [image_mem_map hn, (isOpen_of_mem_countableBasis U.2).mem_nhds x.2]
    · rw [mapsTo_image_iff]
      exact fun y _ ↦ hUV y.2
/-
**ContinuousMap.instSeparableSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instSeparableSpace [SecondCountableTopology X] [LocallyCompactSpace X] [Se
condCountableTopology Y] : SeparableSpace C(X, Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
-/
instance instSeparableSpace [SecondCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopology Y] : SeparableSpace C(X, Y) :=
  inferInstance

end ContinuousMap

