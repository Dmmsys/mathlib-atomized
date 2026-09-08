/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
module

public import Mathlib.Topology.Hom.ContinuousEval
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Separation.Regular

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `ContinuousMap.compactOpen` is the compact-open topology on `C(X, Y)`.
  It is declared as an instance.
* `ContinuousMap.coev` is the coevaluation map `Y → C(X, Y × X)`. It is always continuous.
* `ContinuousMap.curry` is the currying map `C(X × Y, Z) → C(X, C(Y, Z))`. This map always exists
  and it is continuous as long as `X × Y` is locally compact.
* `ContinuousMap.uncurry` is the uncurrying map `C(X, C(Y, Z)) → C(X × Y, Z)`. For this map to
  exist, we need `Y` to be locally compact. If `X` is also locally compact, then this map is
  continuous.
* `Homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(X × Y, Z) ≃ₜ C(X, C(Y, Z))`. This homeomorphism exists if `X` and `Y` are locally compact.


## Tags

compact-open, curry, function space
-/

@[expose] public section


open Set Filter TopologicalSpace Topology

namespace ContinuousMap

section CompactOpen

variable {α X Y Z T : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]
variable {K : Set X} {U : Set Y}

/-- The compact-open topology on the space of continuous maps `C(X, Y)`. -/
/-
**ContinuousMap.compactOpen** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：compactOpen : TopologicalSpace C(X, Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compact-open topology on the space of continuous maps `C(X, Y)`.
-/
instance compactOpen : TopologicalSpace C(X, Y) :=
  .generateFrom <| image2 (fun K U ↦ {f | MapsTo f K U}) {K | IsCompact K} {U | IsOpen U}

/-- Definition of `ContinuousMap.compactOpen`. -/
/-
**ContinuousMap.compactOpen_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：compactOpen_eq : @compactOpen X Y _ _ = .generateFrom (image2 (fun K U => 
{f | MapsTo f K U}) {K | IsCompact K} {t | IsOpen t})
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of `ContinuousMap.compactOpen`.
-/
theorem compactOpen_eq : @compactOpen X Y _ _ =
    .generateFrom (image2 (fun K U ↦ {f | MapsTo f K U}) {K | IsCompact K} {t | IsOpen t}) :=
  rfl
/-
**ContinuousMap.isOpen_setOfPred_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
`。
形式化陈述：isOpen_setOfPred_mapsTo (hK : IsCompact K) (hU : IsOpen U) : IsOpen {f : C
(X, Y) | MapsTo f K U}
参数：hK : IsCompact K；hU : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isOpen_generateFrom_of_mem`：isOpen_generateFrom_of_mem 
{g : Set (Set α)} {s : Set α} (hs : s in g) : IsOpen[generateFrom g] s
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem isOpen_setOfPred_mapsTo (hK : IsCompact K) (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | MapsTo f K U} :=
  isOpen_generateFrom_of_mem <| mem_image2_of_mem hK hU

@[deprecated (since := "2026-07-09")] alias isOpen_setOf_mapsTo := isOpen_setOfPred_mapsTo
/-
**ContinuousMap.eventually_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：eventually_mapsTo {f : C(X, Y)} (hK : IsCompact K) (hU : IsOpen U) (h : Ma
psTo f K U) : forallᶠ g : C(X, Y) in 𝓝 f, MapsTo g K U
参数：X, Y；hK : IsCompact K；hU : IsOpen U；h : MapsTo f K U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ContinuousMap.isOpen_setOfPred_mapsTo`：isOpen_setOfPred_mapsTo (hK : IsC
ompact K) (hU : IsOpen U) : IsOpen {f : C(X, Y) | MapsTo f K U}
-/
lemma eventually_mapsTo {f : C(X, Y)} (hK : IsCompact K) (hU : IsOpen U) (h : MapsTo f K U) :
    ∀ᶠ g : C(X, Y) in 𝓝 f, MapsTo g K U :=
  (isOpen_setOfPred_mapsTo hK hU).mem_nhds h
/-
**ContinuousMap.isOpen_setOfPred_range_subset** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousMap`。
形式化陈述：isOpen_setOfPred_range_subset [CompactSpace X] (hU : IsOpen U) : IsOpen {f
 : C(X, Y) | range f subseteq U}
参数：hU : IsOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMap.isOpen_setOfPred_mapsTo`：isOpen_setOfPred_mapsTo (hK : IsC
ompact K) (hU : IsOpen U) : IsOpen {f : C(X, Y) | MapsTo f K U}
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
-/
lemma isOpen_setOfPred_range_subset [CompactSpace X] (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | range f ⊆ U} := by
  simp_rw [← mapsTo_univ_iff_range_subset]
  exact isOpen_setOfPred_mapsTo isCompact_univ hU

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_range_subset := isOpen_setOfPred_range_subset
/-
**ContinuousMap.eventually_range_subset** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap
`。
形式化陈述：eventually_range_subset [CompactSpace X] {f : C(X, Y)} (hU : IsOpen U) (h 
: range f subseteq U) : forallᶠ g : C(X, Y) in 𝓝 f, range g subseteq U
参数：X, Y；hU : IsOpen U；h : range f subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `ContinuousMap.isOpen_setOfPred_range_subset`：isOpen_setOfPred_range_subs
et [CompactSpace X] (hU : IsOpen U) : IsOpen {f : C(X, Y) | range f subseteq U}
-/
lemma eventually_range_subset [CompactSpace X] {f : C(X, Y)} (hU : IsOpen U) (h : range f ⊆ U) :
    ∀ᶠ g : C(X, Y) in 𝓝 f, range g ⊆ U :=
  (isOpen_setOfPred_range_subset hU).mem_nhds h
/-
**ContinuousMap.nhds_compactOpen** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：nhds_compactOpen (f : C(X, Y)) : 𝓝 f = ⨅ (K : Set X) (_ : IsCompact K) (U 
: Set Y) (_ : IsOpen U) (_ : MapsTo f K U), 𝓟 {g : C(X, Y) | MapsTo g K U}
参数：f : C(X, Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `biInf_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Compl
eteLattice α] {f : β × γ → α} {s : Set β} {t : Set γ},   ⨅ x ∈ s ×ˢ t, f x = ⨅ a
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nhds_compactOpen (f : C(X, Y)) :
    𝓝 f = ⨅ (K : Set X) (_ : IsCompact K) (U : Set Y) (_ : IsOpen U) (_ : MapsTo f K U),
      𝓟 {g : C(X, Y) | MapsTo g K U} := by
  simp_rw +instances [compactOpen_eq, nhds_generateFrom, mem_ofPred_eq, @and_comm (f ∈ _), iInf_and,
    ← image_prod, iInf_image, biInf_prod, mem_ofPred_eq]
/-
**ContinuousMap.tendsto_nhds_compactOpen** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMa
p`。
形式化陈述：tendsto_nhds_compactOpen {l : Filter α} {f : α -> C(Y, Z)} {g : C(Y, Z)} :
 Tendsto f l (𝓝 g) ↔ forall K, IsCompact K -> forall U, IsOpen U -> MapsTo g K U
 -> forallᶠ a in l, MapsTo (f a) K U
参数：Y, Z；Y, Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMap.nhds_compactOpen`：nhds_compactOpen (f : C(X, Y)) : 𝓝 f = ⨅
 (K : Set X) (_ : IsCompact K) (U : Set Y) (_ : IsOpen U) (_ : MapsTo f K U), 𝓟 
{g : C(X, Y) | MapsT…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tendsto_nhds_compactOpen {l : Filter α} {f : α → C(Y, Z)} {g : C(Y, Z)} :
    Tendsto f l (𝓝 g) ↔
      ∀ K, IsCompact K → ∀ U, IsOpen U → MapsTo g K U → ∀ᶠ a in l, MapsTo (f a) K U := by
  simp [nhds_compactOpen]
/-
**ContinuousMap.continuous_compactOpen** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`
。
形式化陈述：continuous_compactOpen {f : X -> C(Y, Z)} : Continuous f ↔ forall K, IsCom
pact K -> forall U, IsOpen U -> IsOpen {x | MapsTo (f x) K U}
参数：Y, Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `continuous_generateFrom_iff`：continuous_generateFrom_iff {t : Topologica
lSpace α} {b : Set (Set β)} : Continuous[t, generateFrom b] f ↔ forall s in b, I
sOpen (f ⁻¹' s)
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
-/
lemma continuous_compactOpen {f : X → C(Y, Z)} :
    Continuous f ↔ ∀ K, IsCompact K → ∀ U, IsOpen U → IsOpen {x | MapsTo (f x) K U} :=
  continuous_generateFrom_iff.trans forall_mem_image2
/-
**ContinuousMap.hasBasis_nhds** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (f : C(X, Y)),   (nhds f).HasBasis     (fun S => S.Finite ∧ ∀ (K
 : Set X) (U : Set Y), (K, U) ∈ S → IsCompact K ∧ IsOpen U ∧ Set.MapsTo (⇑f) K U
) fun x =>     ⋂ KU ∈ x, {g | Set.MapsTo (⇑g) KU.1 KU.2}
参数：f : C(X, Y)；nhds f；fun S => S.Finite ∧ ∀ (K : Set X) (U : Set Y), (K, U) ∈ S 
→ IsCompact K ∧ IsOpen U ∧ Set.MapsTo (⇑f) K U；⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMap.nhds_compactOpen`：nhds_compactOpen (f : C(X, Y)) : 𝓝 f = ⨅
 (K : Set X) (_ : IsCompact K) (U : Set Y) (_ : IsOpen U) (_ : MapsTo f K U), 𝓟 
{g : C(X, Y) | MapsT…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_comm`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Compl
eteLattice α] {f : ι → ι' → α},   ⨅ i, ⨅ j, f i j = ⨅ j, ⨅ i, f i j
· 使用定理 `iInf_prod'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Compl
eteLattice α] (f : β → γ → α),   ⨅ i, ⨅ j, f i j = ⨅ x, f x.1 x.2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_and'`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s :
 p → q → α},   ⨅ (h₁ : p), ⨅ (h₂ : q), s h₁ h₂ = ⨅ (h : p ∧ q), s ⋯ ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma hasBasis_nhds (f : C(X, Y)) :
    (𝓝 f).HasBasis
      (fun S : Set (Set X × Set Y) ↦
        S.Finite ∧ ∀ K U, (K, U) ∈ S → IsCompact K ∧ IsOpen U ∧ MapsTo f K U)
      (⋂ KU ∈ ·, {g : C(X, Y) | MapsTo g KU.1 KU.2}) := by
  refine ⟨fun s ↦ ?_⟩
  simp_rw [nhds_compactOpen, iInf_comm.{_, 0, _ + 1}, iInf_prod', iInf_and']
  simp [mem_biInf_principal, and_assoc]
/-
**ContinuousMap.mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : C(X, Y)}   {s : Set C(X, Y)},   s ∈ nhds f ↔     ∃ S,      
 S.Finite ∧         (∀ (K : Set X) (U : Set Y), (K, U) ∈ S → IsCompact K ∧ IsOpe
n U ∧ Set.MapsTo (⇑f) K U) ∧           {g | ∀ (K : Set X) (U : Set Y), (K, U) ∈ 
S → Set.MapsTo (⇑g) K U} ⊆ s
参数：X, Y；X, Y；∀ (K : Set X) (U : Set Y), (K, U) ∈ S → IsCompact K ∧ IsOpen U ∧ Se
t.MapsTo (⇑f) K U；K : Set X；U : Set Y；K, U；⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `ContinuousMap.hasBasis_nhds`：∀ {X : Type u_2} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)),   (nhds f).HasBasi
s     (fun S => S…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma mem_nhds_iff {f : C(X, Y)} {s : Set C(X, Y)} :
    s ∈ 𝓝 f ↔ ∃ S : Set (Set X × Set Y), S.Finite ∧
      (∀ K U, (K, U) ∈ S → IsCompact K ∧ IsOpen U ∧ MapsTo f K U) ∧
      {g : C(X, Y) | ∀ K U, (K, U) ∈ S → MapsTo g K U} ⊆ s := by
  simp [f.hasBasis_nhds.mem_iff, ← ofPred_forall, and_assoc]
/-
**ContinuousMap._root_.Filter.HasBasis.nhds_continuousMapConst** 是 Mathlib 中的一个引
理，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Filter.HasBasis.nhds_continuousMapConst {ι : Type*} {c : Y} {p : ι → Prop}
    {U : ι → Set Y} (h : (𝓝 c).HasBasis p U) :
    (𝓝 (const X c)).HasBasis (fun Ki : Set X × ι ↦ IsCompact Ki.1 ∧ p Ki.2)
      fun Ki ↦ {f : C(X, Y) | MapsTo f Ki.1 (U Ki.2)} := by
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩⟩
  · rcases ContinuousMap.mem_nhds_iff.mp hs with ⟨S, hSf, hS, hSsub⟩
    choose hScompact hSopen hSmaps using hS
    have : ⋂ KU ∈ S, ⋂ (_ : KU.1.Nonempty), KU.2 ∈ 𝓝 c := by
      simp only [biInter_mem hSf, Prod.forall, iInter_mem]
      rintro K U hKU ⟨x, hx⟩
      exact (hSopen K U hKU).mem_nhds <| hSmaps K U hKU hx
    rcases h.mem_iff.mp this with ⟨i, hpi, hi⟩
    refine ⟨(⋃ KU ∈ S, KU.1, i), ⟨hSf.isCompact_biUnion <| Prod.forall.2 hScompact, hpi⟩,
      Subset.trans ?_ hSsub⟩
    intro f hf K V hKV
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact mapsTo_empty _ _
    · refine hf.out.mono (subset_biUnion_of_mem (u := Prod.fst) hKV) (hi.trans ?_)
      exact (biInter_subset_of_mem hKV).trans <| iInter_subset _ hKne
  · rcases hs with ⟨⟨K, i⟩, ⟨hK, hpi⟩, hi⟩
    filter_upwards [eventually_mapsTo hK isOpen_interior fun x _ ↦
      mem_interior_iff_mem_nhds.mpr <| h.mem_of_mem hpi] with f hf
    exact hi <| hf.mono_right interior_subset

section Functorial

/-- `C(X, ·)` is a functor. -/
@[fun_prop]
/-
**ContinuousMap.continuous_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuous_postcomp (g : C(Y, Z)) : Continuous (ContinuousMap.comp g : C(X
, Y) -> C(X, Z))
参数：g : C(Y, Z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ContinuousMap.continuous_compactOpen`：continuous_compactOpen {f : X -> C
(Y, Z)} : Continuous f ↔ forall K, IsCompact K -> forall U, IsOpen U -> IsOpen {
x | MapsTo (f x) K U}
· 使用定理 `ContinuousMap.isOpen_setOfPred_mapsTo`：isOpen_setOfPred_mapsTo (hK : IsC
ompact K) (hU : IsOpen U) : IsOpen {f : C(X, Y) | MapsTo f K U}
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun

--- 原说明 ---
`C(X, ·)` is a functor.
-/
theorem continuous_postcomp (g : C(Y, Z)) : Continuous (ContinuousMap.comp g : C(X, Y) → C(X, Z)) :=
  continuous_compactOpen.2 fun _K hK _U hU ↦ isOpen_setOfPred_mapsTo hK (hU.preimage g.2)

/-- If `g : C(Y, Z)` is injective,
then the composition `ContinuousMap.comp g : C(X, Y) → C(X, Z)` is injective too. -/
/-
**ContinuousMap.postcomp_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：postcomp_injective (g : C(Y, Z)) (hg : Function.Injective g) : Function.In
jective (ContinuousMap.comp g : C(X, Y) -> C(X, Z))
参数：g : C(Y, Z)；hg : Function.Injective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousMap.cancel_left`：cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (
hf : Injective f) : f.comp g₁ = f.comp g₂ ↔ g₁ = g₂

--- 原说明 ---
If `g : C(Y, Z)` is injective,
then the composition `ContinuousMap.comp g : C(X, Y) → C(X, Z)` is injective too
.
-/
theorem postcomp_injective (g : C(Y, Z)) (hg : Function.Injective g) :
    Function.Injective (ContinuousMap.comp g : C(X, Y) → C(X, Z)) :=
  fun _ _ ↦ (cancel_left hg).1

/-- If `g : C(Y, Z)` is a topology inducing map,
then the composition `ContinuousMap.comp g : C(X, Y) → C(X, Z)` is a topology inducing map too. -/
/-
**ContinuousMap.isInducing_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：isInducing_postcomp (g : C(Y, Z)) (hg : IsInducing g) : IsInducing (g.comp
 : C(X, Y) -> C(X, Z)) where eq_induced
参数：g : C(Y, Z)；hg : IsInducing g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.setOfPred_isOpen`：setOfPred_isOpen (hf : IsInducing 
f) : {s : Set X | IsOpen s} = preimage f '' {t | IsOpen t}
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `induced_generateFrom_eq`：induced_generateFrom_eq {α β} {b : Set (Set β)}
 {f : α -> β} : (generateFrom b).induced f = generateFrom (preimage f '' b)
· 使用定理 `Set.image_image2`：image_image2 (f : α -> β -> γ) (g : γ -> δ) : g '' ima
ge2 f s t = image2 (fun a b => g (f a b)) s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `g : C(Y, Z)` is a topology inducing map,
then the composition `ContinuousMap.comp g : C(X, Y) → C(X, Z)` is a topology in
ducing map too.
-/
theorem isInducing_postcomp (g : C(Y, Z)) (hg : IsInducing g) :
    IsInducing (g.comp : C(X, Y) → C(X, Z)) where
  eq_induced := by
    simp only [compactOpen_eq, induced_generateFrom_eq, image_image2, hg.setOfPred_isOpen,
      image2_image_right, MapsTo, mem_preimage, preimage_ofPred_eq, comp_apply]

/-- If `g : C(Y, Z)` is a topological embedding,
then the composition `ContinuousMap.comp g : C(X, Y) → C(X, Z)` is an embedding too. -/
/-
**ContinuousMap.isEmbedding_postcomp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：isEmbedding_postcomp (g : C(Y, Z)) (hg : IsEmbedding g) : IsEmbedding (g.c
omp : C(X, Y) -> C(X, Z))
参数：g : C(Y, Z)；hg : IsEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.isInducing_postcomp`：isInducing_postcomp (g : C(Y, Z)) (hg
 : IsInducing g) : IsInducing (g.comp : C(X, Y) -> C(X, Z)) where eq_induced
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `ContinuousMap.postcomp_injective`：postcomp_injective (g : C(Y, Z)) (hg :
 Function.Injective g) : Function.Injective (ContinuousMap.comp g : C(X, Y) -> C
(X, Z))
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…

--- 原说明 ---
If `g : C(Y, Z)` is a topological embedding,
then the composition `ContinuousMap.comp g : C(X, Y) → C(X, Z)` is an embedding 
too.
-/
theorem isEmbedding_postcomp (g : C(Y, Z)) (hg : IsEmbedding g) :
    IsEmbedding (g.comp : C(X, Y) → C(X, Z)) :=
  ⟨isInducing_postcomp g hg.1, postcomp_injective g hg.2⟩

/-- `C(·, Z)` is a functor. -/
@[continuity, fun_prop]
/-
**ContinuousMap.continuous_precomp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuous_precomp (f : C(X, Y)) : Continuous (fun g => g.comp f : C(Y, Z)
 -> C(X, Z))
参数：f : C(X, Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ContinuousMap.continuous_compactOpen`：continuous_compactOpen {f : X -> C
(Y, Z)} : Continuous f ↔ forall K, IsCompact K -> forall U, IsOpen U -> IsOpen {
x | MapsTo (f x) K U}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMap.isOpen_setOfPred_mapsTo`：isOpen_setOfPred_mapsTo (hK : IsC
ompact K) (hU : IsOpen U) : IsOpen {f : C(X, Y) | MapsTo f K U}
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun

--- 原说明 ---
`C(·, Z)` is a functor.
-/
theorem continuous_precomp (f : C(X, Y)) : Continuous (fun g => g.comp f : C(Y, Z) → C(X, Z)) :=
  continuous_compactOpen.2 fun K hK U hU ↦ by
    simpa only [mapsTo_image_iff] using! isOpen_setOfPred_mapsTo (hK.image f.2) hU

variable (Z) in
/-- Precomposition by a continuous map is itself a continuous map between spaces of continuous maps.
-/
@[simps apply]
/-
**ContinuousMap.compRightContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`
。
形式化陈述：compRightContinuousMap (f : C(X, Y)) : C(C(Y, Z), C(X, Z)) where toFun g
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposition by a continuous map is itself a continuous map between spaces of 
continuous maps.
-/
def compRightContinuousMap (f : C(X, Y)) :
    C(C(Y, Z), C(X, Z)) where
  toFun g := g.comp f

/-- Any pair of homeomorphisms `X ≃ₜ Z` and `Y ≃ₜ T` gives rise to a homeomorphism
`C(X, Y) ≃ₜ C(Z, T)`. -/
/-
**ContinuousMap._root_.Homeomorph.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `Continuo
usMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any pair of homeomorphisms `X ≃ₜ Z` and `Y ≃ₜ T` gives rise to a homeomorphism
`C(X, Y) ≃ₜ C(Z, T)`.
-/
protected def _root_.Homeomorph.arrowCongr (φ : X ≃ₜ Z) (ψ : Y ≃ₜ T) :
    C(X, Y) ≃ₜ C(Z, T) where
  toFun f := .comp ψ <| f.comp φ.symm
  invFun f := .comp ψ.symm <| f.comp φ
  left_inv f := ext fun _ ↦ ψ.left_inv (f _) |>.trans <| congrArg f <| φ.left_inv _
  right_inv f := ext fun _ ↦ ψ.right_inv (f _) |>.trans <| congrArg f <| φ.right_inv _
  continuous_toFun := continuous_postcomp _ |>.comp <| continuous_precomp _
  continuous_invFun := continuous_postcomp _ |>.comp <| continuous_precomp _

/-- The map from `X × C(Y, Z)` to `C(Y, X × Z)` is continuous. -/
/-
**ContinuousMap.continuous_prodMk_const** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap
`。
形式化陈述：continuous_prodMk_const : Continuous fun p : X × C(Y, Z) => prodMk (const 
Y p.1) p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `generalized_tube_lemma`：generalized_tube_lemma (hs : IsCompact s) {t : S
et Y} (ht : IsCompact t) {n : Set (X × Y)} (hn : IsOpen n) (hp : s ×ˢ t subseteq
 n) : exists…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `prod_mem_nhds`：prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx
 : s in 𝓝 x) (hy : t in 𝓝 y) : s ×ˢ t in 𝓝 (x, y)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `ContinuousMap.eventually_mapsTo`：eventually_mapsTo {f : C(X, Y)} (hK : I
sCompact K) (hU : IsOpen U) (h : MapsTo f K U) : forallᶠ g : C(X, Y) in 𝓝 f, Map
sTo g K U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t

--- 原说明 ---
The map from `X × C(Y, Z)` to `C(Y, X × Z)` is continuous.
-/
lemma continuous_prodMk_const : Continuous fun p : X × C(Y, Z) ↦ prodMk (const Y p.1) p.2 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, ContinuousMap.tendsto_nhds_compactOpen]
  rintro ⟨r, f⟩ K hK U hU H
  obtain ⟨V, W, hV, hW, hrV, hKW, hVW⟩ := generalized_tube_lemma (isCompact_singleton (x := r))
    (hK.image f.continuous) hU (by simpa [Set.subset_def, forall_comm (α := X)])
  refine Filter.eventually_of_mem (prod_mem_nhds (hV.mem_nhds (by simpa using hrV))
    (ContinuousMap.eventually_mapsTo hK hW (Set.mapsTo_iff_image_subset.mpr hKW))) ?_
  rintro ⟨r', f'⟩ ⟨hr'V, hf'⟩ x hxK
  exact hVW (Set.mk_mem_prod hr'V (hf' hxK))

variable [LocallyCompactPair Y Z]

/-- Composition is a continuous map from `C(X, Y) × C(Y, Z)` to `C(X, Z)`,
provided that `Y` is locally compact.
This is Prop. 9 of Chap. X, §3, №. 4 of Bourbaki's *Topologie Générale*. -/
/-
**ContinuousMap.continuous_comp'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuous_comp' : Continuous fun x : C(X, Y) × C(Y, Z) => x.2.comp x.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `exists_mem_nhdsSet_isCompact_mapsTo`：exists_mem_nhdsSet_isCompact_mapsTo
 [LocallyCompactPair X Y] {f : X -> Y} {K : Set X} {U : Set Y} (hf : Continuous 
f) (hK : IsCompact K) (hU…
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_image_iff`：mapsTo_image_iff {f : α -> β} {g : γ -> α} {s : Se
t γ} {t : Set β} : MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_nhds`：Filter.Eventually.prod_nhds {p : X -> Prop}
 {q : Y -> Prop} {x : X} {y : Y} (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in
 𝓝 y, q y) : fora…
· 使用引理 `ContinuousMap.eventually_mapsTo`：eventually_mapsTo {f : C(X, Y)} (hK : I
sCompact K) (hU : IsOpen U) (h : MapsTo f K U) : forallᶠ g : C(X, Y) in 𝓝 f, Map
sTo g K U
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `subset_interior_iff_mem_nhdsSet`：subset_interior_iff_mem_nhdsSet : s sub
seteq interior t ↔ t in 𝓝ˢ s
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
Composition is a continuous map from `C(X, Y) × C(Y, Z)` to `C(X, Z)`,
provided that `Y` is locally compact.
This is Prop. 9 of Chap. X, §3, №. 4 of Bourbaki's *Topologie Générale*.
-/
theorem continuous_comp' : Continuous fun x : C(X, Y) × C(Y, Z) => x.2.comp x.1 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  intro ⟨f, g⟩ K hK U hU (hKU : MapsTo (g ∘ f) K U)
  obtain ⟨L, hKL, hLc, hLU⟩ : ∃ L ∈ 𝓝ˢ (f '' K), IsCompact L ∧ MapsTo g L U :=
    exists_mem_nhdsSet_isCompact_mapsTo g.continuous (hK.image f.continuous) hU
      (mapsTo_image_iff.2 hKU)
  rw [← subset_interior_iff_mem_nhdsSet, ← mapsTo_iff_image_subset] at hKL
  exact ((eventually_mapsTo hK isOpen_interior hKL).prod_nhds
    (eventually_mapsTo hLc hU hLU)).mono fun ⟨f', g'⟩ ⟨hf', hg'⟩ ↦
      hg'.comp <| hf'.mono_right interior_subset
/-
**ContinuousMap._root_.Filter.Tendsto.compCM** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Filter.Tendsto.compCM {α : Type*} {l : Filter α} {g : α → C(Y, Z)} {g₀ : C(Y, Z)}
    {f : α → C(X, Y)} {f₀ : C(X, Y)} (hg : Tendsto g l (𝓝 g₀)) (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto (fun a ↦ (g a).comp (f a)) l (𝓝 (g₀.comp f₀)) :=
  (continuous_comp'.tendsto (f₀, g₀)).comp (hf.prodMk_nhds hg)

variable {X' : Type*} [TopologicalSpace X'] {a : X'} {g : X' → C(Y, Z)} {f : X' → C(X, Y)}
  {s : Set X'}

nonrec lemma _root_.ContinuousAt.compCM (hg : ContinuousAt g a) (hf : ContinuousAt f a) :
    ContinuousAt (fun x ↦ (g x).comp (f x)) a :=
  hg.compCM hf

nonrec lemma _root_.ContinuousWithinAt.compCM (hg : ContinuousWithinAt g s a)
    (hf : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x ↦ (g x).comp (f x)) s a :=
  hg.compCM hf
/-
**ContinuousMap._root_.ContinuousOn.compCM** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousOn.compCM (hg : ContinuousOn g s) (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ (g x).comp (f x)) s := fun a ha ↦
  (hg a ha).compCM (hf a ha)
/-
**ContinuousMap._root_.Continuous.compCM** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Continuous.compCM (hg : Continuous g) (hf : Continuous f) :
    Continuous fun x => (g x).comp (f x) :=
  continuous_comp'.comp (hf.prodMk hg)

end Functorial

section Ev

/-- The evaluation map `C(X, Y) × X → Y` is continuous
if `X, Y` is a locally compact pair of spaces. -/
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation map `C(X, Y) × X → Y` is continuous
if `X, Y` is a locally compact pair of spaces.
-/
instance [LocallyCompactPair X Y] : ContinuousEval C(X, Y) X Y where
  continuous_eval := by
    simp_rw [continuous_iff_continuousAt, ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
    rintro ⟨f, x⟩ U ⟨hx : f x ∈ U, hU : IsOpen U⟩
    rcases exists_mem_nhds_isCompact_mapsTo f.continuous (hU.mem_nhds hx) with ⟨K, hxK, hK, hKU⟩
    filter_upwards [prod_mem_nhds (eventually_mapsTo hK hU hKU) hxK] using fun _ h ↦ h.1 h.2
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousEvalConst C(X, Y) X Y where
  continuous_eval_const x :=
    continuous_def.2 fun U hU ↦ by simpa using! isOpen_setOfPred_mapsTo isCompact_singleton hU
/-
**ContinuousMap.isClosed_setOfPred_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
ap`。
形式化陈述：isClosed_setOfPred_mapsTo {t : Set Y} (ht : IsClosed t) (s : Set X) : IsCl
osed {f : C(X, Y) | MapsTo f s t}
参数：ht : IsClosed t；s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.setOfPred_mapsTo`：IsClosed.setOfPred_mapsTo {α : Type*} {f : X 
-> α -> Z} {s : Set α} {t : Set Z} (ht : IsClosed t) (hf : forall a in s, Contin
uous (f · a)) :…
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
-/
lemma isClosed_setOfPred_mapsTo {t : Set Y} (ht : IsClosed t) (s : Set X) :
    IsClosed {f : C(X, Y) | MapsTo f s t} :=
  ht.setOfPred_mapsTo fun _ _ ↦ continuous_eval_const _

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_mapsTo := isClosed_setOfPred_mapsTo
/-
**ContinuousMap.isClopen_setOfPred_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
ap`。
形式化陈述：isClopen_setOfPred_mapsTo (hK : IsCompact K) (hU : IsClopen U) : IsClopen 
{f : C(X, Y) | MapsTo f K U}
参数：hK : IsCompact K；hU : IsClopen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMap.isClosed_setOfPred_mapsTo`：isClosed_setOfPred_mapsTo {t : 
Set Y} (ht : IsClosed t) (s : Set X) : IsClosed {f : C(X, Y) | MapsTo f s t}
· 使用定理 `IsClopen.isClosed`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X
}, IsClopen s → IsClosed s
· 使用定理 `ContinuousMap.isOpen_setOfPred_mapsTo`：isOpen_setOfPred_mapsTo (hK : IsC
ompact K) (hU : IsOpen U) : IsOpen {f : C(X, Y) | MapsTo f K U}
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
-/
lemma isClopen_setOfPred_mapsTo (hK : IsCompact K) (hU : IsClopen U) :
    IsClopen {f : C(X, Y) | MapsTo f K U} :=
  ⟨isClosed_setOfPred_mapsTo hU.isClosed K, isOpen_setOfPred_mapsTo hK hU.isOpen⟩

@[deprecated (since := "2026-07-09")] alias isClopen_setOf_mapsTo := isClopen_setOfPred_mapsTo

@[norm_cast]
/-
**ContinuousMap.specializes_coe** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：specializes_coe {f g : C(X, Y)} : ⇑f ⤳ ⇑g ↔ f ⤳ g
参数：X, Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
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
· 使用定理 `continuous_coeFun`：continuous_coeFun : Continuous (DFunLike.coe : F -> α
 -> X)
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
-/
lemma specializes_coe {f g : C(X, Y)} : ⇑f ⤳ ⇑g ↔ f ⤳ g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map continuous_coeFun⟩
  suffices ∀ K, IsCompact K → ∀ U, IsOpen U → MapsTo g K U → MapsTo f K U by
    simpa [specializes_iff_pure, nhds_compactOpen]
  exact fun K _ U hU hg x hx ↦ (h.map (continuous_apply x)).mem_open hU (hg hx)

@[norm_cast]
/-
**ContinuousMap.inseparable_coe** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：inseparable_coe {f g : C(X, Y)} : Inseparable (f : X -> Y) g ↔ Inseparable
 f g
参数：X, Y。
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
lemma inseparable_coe {f g : C(X, Y)} : Inseparable (f : X → Y) g ↔ Inseparable f g := by
  simp only [inseparable_iff_specializes_and, specializes_coe]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T0Space Y] : T0Space C(X, Y) :=
  t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R0Space Y] : R0Space C(X, Y) where
  specializes_symm.symm f g h := by
    rw [← specializes_coe] at h ⊢
    exact h.symm
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space Y] : T1Space C(X, Y) :=
  t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R1Space Y] : R1Space C(X, Y) :=
  .of_continuous_specializes_imp continuous_coeFun fun _ _ ↦ specializes_coe.1
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space Y] : T2Space C(X, Y) := inferInstance
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RegularSpace Y] : RegularSpace C(X, Y) :=
  .of_lift'_closure_le fun f ↦ by
    rw [← tendsto_id', tendsto_nhds_compactOpen]
    intro K hK U hU hf
    rcases (hK.image f.continuous).exists_isOpen_closure_subset (hU.mem_nhdsSet.2 hf.image_subset)
      with ⟨V, hVo, hKV, hVU⟩
    filter_upwards [mem_lift' (eventually_mapsTo hK hVo (mapsTo_iff_image_subset.2 hKV))] with g hg
    refine ((isClosed_setOfPred_mapsTo isClosed_closure K).closure_subset ?_).mono_right hVU
    exact closure_mono (fun _ h ↦ h.mono_right subset_closure) hg
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T3Space Y] : T3Space C(X, Y) := inferInstance

end Ev

section DiscreteTopology
variable [DiscreteTopology X]

/-- The continuous functions from `X` to `Y` are the same as the plain functions when `X` is
discrete. -/
@[simps toEquiv]
/-
**ContinuousMap.homeoFnOfDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：homeoFnOfDiscrete : C(X, Y) ≃ₜ (X -> Y) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous functions from `X` to `Y` are the same as the plain functions whe
n `X` is
discrete.
-/
def homeoFnOfDiscrete : C(X, Y) ≃ₜ (X → Y) where
  __ := equivFnOfDiscrete
  continuous_invFun :=
    continuous_compactOpen.2 fun K hK U hU ↦ isOpen_set_pi hK.finite_of_discrete fun _ _ ↦ hU

attribute [simps! -isSimp] homeoFnOfDiscrete
/-
**ContinuousMap.coe_homeoFnOfDiscrete** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : DiscreteTopology X],   ⇑ContinuousMap.homeoFnOfDiscret
e = DFunLike.coe
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_homeoFnOfDiscrete : ⇑homeoFnOfDiscrete = (DFunLike.coe : C(X, Y) → X → Y) := rfl
/-
**ContinuousMap.homeoFnOfDiscrete_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : DiscreteTopology X]   (f : X → Y), ⇑(ContinuousMap.hom
eoFnOfDiscrete.symm f) = f
参数：f : X → Y；ContinuousMap.homeoFnOfDiscrete.symm f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma homeoFnOfDiscrete_symm_apply (f : X → Y) : homeoFnOfDiscrete.symm f = f := rfl
/-
**ContinuousMap.isHomeomorph_coe** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：isHomeomorph_coe : IsHomeomorph ((⇑) : C(X, Y) -> X -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
lemma isHomeomorph_coe : IsHomeomorph ((⇑) : C(X, Y) → X → Y) := homeoFnOfDiscrete.isHomeomorph

end DiscreteTopology

section InfInduced

/-- For any subset `s` of `X`, the restriction of continuous functions to `s` is continuous
as a function from `C(X, Y)` to `C(s, Y)` with their respective compact-open topologies. -/
/-
**ContinuousMap.continuous_restrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuous_restrict (s : Set X) : Continuous fun F : C(X, Y) => F.restrict
 s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))

--- 原说明 ---
For any subset `s` of `X`, the restriction of continuous functions to `s` is con
tinuous
as a function from `C(X, Y)` to `C(s, Y)` with their respective compact-open top
ologies.
-/
theorem continuous_restrict (s : Set X) : Continuous fun F : C(X, Y) => F.restrict s :=
  continuous_precomp <| restrict s <| .id X
/-
**ContinuousMap.compactOpen_le_induced** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`
。
形式化陈述：compactOpen_le_induced (s : Set X) : (ContinuousMap.compactOpen : Topologi
calSpace C(X, Y)) <= .induced (restrict s) ContinuousMap.compactOpen
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.le_induced`：Continuous.le_induced (h : Continuous[t, t'] f) :
 t <= t'.induced f
· 使用定理 `ContinuousMap.continuous_restrict`：continuous_restrict (s : Set X) : Con
tinuous fun F : C(X, Y) => F.restrict s
-/
theorem compactOpen_le_induced (s : Set X) :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) ≤
      .induced (restrict s) ContinuousMap.compactOpen :=
  (continuous_restrict s).le_induced

/-- The compact-open topology on `C(X, Y)`
is equal to the infimum of the compact-open topologies on `C(s, Y)` for `s` a compact subset of `X`.
The key point of the proof is that for every compact set `K`,
the universal set `Set.univ : Set K` is a compact set as well. -/
/-
**ContinuousMap.compactOpen_eq_iInf_induced** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMap`。
形式化陈述：compactOpen_eq_iInf_induced : (ContinuousMap.compactOpen : TopologicalSpac
e C(X, Y)) = ⨅ (K : Set X) (_ : IsCompact K), .induced (.restrict K) ContinuousM
ap.compactOpen
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `ContinuousMap.compactOpen_le_induced`：compactOpen_le_induced (s : Set X)
 : (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) <= .induced (restrict 
s) ContinuousMap.compactOp…
· 使用定理 `le_generateFrom`：le_generateFrom {t : TopologicalSpace α} {g : Set (Set 
α)} (h : forall s in g, IsOpen s) : t <= generateFrom g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.le_def`：∀ {α : Type u_1} {t s : TopologicalSpace α}, t 
≤ s ↔ IsOpen ≤ IsOpen
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
· 使用定理 `ContinuousMap.isOpen_setOfPred_mapsTo`：isOpen_setOfPred_mapsTo (hK : IsC
ompact K) (hU : IsOpen U) : IsOpen {f : C(X, Y) | MapsTo f K U}
· 使用定理 `isCompact_iff_isCompact_univ`：isCompact_iff_isCompact_univ : IsCompact s
 ↔ IsCompact (univ : Set s)

--- 原说明 ---
The compact-open topology on `C(X, Y)`
is equal to the infimum of the compact-open topologies on `C(s, Y)` for `s` a co
mpact subset of `X`.
The key point of the proof is that for every compact set `K`,
the universal set `Set.univ : Set K` is a compact set as well.
-/
theorem compactOpen_eq_iInf_induced :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) =
      ⨅ (K : Set X) (_ : IsCompact K), .induced (.restrict K) ContinuousMap.compactOpen := by
  refine le_antisymm (le_iInf₂ fun s _ ↦ compactOpen_le_induced s) ?_
  refine le_generateFrom <| forall_mem_image2.2 fun K (hK : IsCompact K) U hU ↦ ?_
  refine TopologicalSpace.le_def.1 (iInf₂_le K hK) _ ?_
  convert! isOpen_induced (isOpen_setOfPred_mapsTo (isCompact_iff_isCompact_univ.1 hK) hU)
  simp [Subtype.forall, MapsTo]
/-
**ContinuousMap.nhds_compactOpen_eq_iInf_nhds_induced** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMap`。
形式化陈述：nhds_compactOpen_eq_iInf_nhds_induced (f : C(X, Y)) : 𝓝 f = ⨅ (s) (_ : IsC
ompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s)
参数：f : C(X, Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.compactOpen_eq_iInf_induced`：compactOpen_eq_iInf_induced :
 (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) = ⨅ (K : Set X) (_ : IsC
ompact K), .induced (.restrict …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_compactOpen_eq_iInf_nhds_induced (f : C(X, Y)) :
    𝓝 f = ⨅ (s) (_ : IsCompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s) := by
  rw [compactOpen_eq_iInf_induced]
  simp only [nhds_iInf, nhds_induced]
/-
**ContinuousMap.tendsto_compactOpen_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap`。
形式化陈述：tendsto_compactOpen_restrict {ι : Type*} {l : Filter ι} {F : ι -> C(X, Y)}
 {f : C(X, Y)} (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set X) : Tendsto (fun i => 
(F i).restrict s) l (𝓝 (f.restrict s))
参数：X, Y；X, Y；hFf : Filter.Tendsto F l (𝓝 f)；s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousMap.continuous_restrict`：continuous_restrict (s : Set X) : Con
tinuous fun F : C(X, Y) => F.restrict s
-/
theorem tendsto_compactOpen_restrict {ι : Type*} {l : Filter ι} {F : ι → C(X, Y)} {f : C(X, Y)}
    (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set X) :
    Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  (continuous_restrict s).continuousAt.tendsto.comp hFf
/-
**ContinuousMap.tendsto_compactOpen_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousMap`。
形式化陈述：tendsto_compactOpen_iff_forall {ι : Type*} {l : Filter ι} (F : ι -> C(X, Y
)) (f : C(X, Y)) : Tendsto F l (𝓝 f) ↔ forall K, IsCompact K -> Tendsto (fun i =
> (F i).restrict K) l (𝓝 (f.restrict K))
参数：F : ι -> C(X, Y)；f : C(X, Y)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.compactOpen_eq_iInf_induced`：compactOpen_eq_iInf_induced :
 (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) = ⨅ (K : Set X) (_ : IsC
ompact K), .induced (.restrict …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_compactOpen_iff_forall {ι : Type*} {l : Filter ι} (F : ι → C(X, Y)) (f : C(X, Y)) :
    Tendsto F l (𝓝 f) ↔
      ∀ K, IsCompact K → Tendsto (fun i => (F i).restrict K) l (𝓝 (f.restrict K)) := by
  rw [compactOpen_eq_iInf_induced]
  simp [nhds_iInf, nhds_induced, Filter.tendsto_comap_iff, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
/-- A family `F` of functions in `C(X, Y)` converges in the compact-open topology, if and only if
it converges in the compact-open topology on each compact subset of `X`. -/
/-
**ContinuousMap.exists_tendsto_compactOpen_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMap`。
形式化陈述：exists_tendsto_compactOpen_iff_forall [WeaklyLocallyCompactSpace X] [T2Spa
ce Y] {ι : Type*} {l : Filter ι} [Filter.NeBot l] (F : ι -> C(X, Y)) : (exists f
, Filter.Tendsto F l (𝓝 f)) ↔ forall s : Set X, IsCompact s -> exists f, Filter.
Tendsto (fun i => (F i).restrict s) l (𝓝 f)
参数：F : ι -> C(X, Y)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.tendsto_compactOpen_restrict`：tendsto_compactOpen_restrict
 {ι : Type*} {l : Filter ι} {F : ι -> C(X, Y)} {f : C(X, Y)} (hFf : Filter.Tends
to F l (𝓝 f)) (s : Set X) : Tend…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.tendsto_compactOpen_iff_forall`：tendsto_compactOpen_iff_fo
rall {ι : Type*} {l : Filter ι} (F : ι -> C(X, Y)) (f : C(X, Y)) : Tendsto F l (
𝓝 f) ↔ forall K, IsCompact K -> Te…
· 使用定理 `ContinuousMap.liftCover_restrict'`：liftCover_restrict' {s : Set α} {hs :
 s in A} : (liftCover' A F hF hA).restrict s = F s hs
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A family `F` of functions in `C(X, Y)` converges in the compact-open topology, i
f and only if
it converges in the compact-open topology on each compact subset of `X`.
-/
theorem exists_tendsto_compactOpen_iff_forall [WeaklyLocallyCompactSpace X] [T2Space Y]
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] (F : ι → C(X, Y)) :
    (∃ f, Filter.Tendsto F l (𝓝 f)) ↔
      ∀ s : Set X, IsCompact s → ∃ f, Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 f) := by
  constructor
  · rintro ⟨f, hf⟩ s _
    exact ⟨f.restrict s, tendsto_compactOpen_restrict hf s⟩
  · intro h
    choose f hf using h
    -- By uniqueness of limits in a `T2Space`, since `fun i ↦ F i x` tends to both `f s₁ hs₁ x` and
    -- `f s₂ hs₂ x`, we have `f s₁ hs₁ x = f s₂ hs₂ x`
    have h :
      ∀ (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : X) (hxs₁ : x ∈ s₁) (hxs₂ : x ∈ s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ := by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      have := isCompact_iff_compactSpace.mp hs₁
      have := isCompact_iff_compactSpace.mp hs₂
      have h₁ := (continuous_eval_const (⟨x, hxs₁⟩ : s₁)).continuousAt.tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const (⟨x, hxs₂⟩ : s₂)).continuousAt.tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    refine ⟨liftCover' _ _ h exists_compact_mem_nhds, ?_⟩
    rw [tendsto_compactOpen_iff_forall]
    intro s hs
    rw [liftCover_restrict']
    exact hf s hs

end InfInduced

section Coev

variable (X Y)

/-- The coevaluation map `Y → C(X, Y × X)` sending a point `x : Y` to the continuous function
on `X` sending `y` to `(x, y)`. -/
@[simps -fullyApplied]
/-
**ContinuousMap.coev** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：coev (b : Y) : C(X, Y × X)
参数：b : Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coevaluation map `Y → C(X, Y × X)` sending a point `x : Y` to the continuous
 function
on `X` sending `y` to `(x, y)`.
-/
def coev (b : Y) : C(X, Y × X) :=
  { toFun := Prod.mk b }

variable {X Y}
/-
**ContinuousMap.image_coev** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：image_coev {y : Y} (s : Set X) : coev X Y y '' s = {y} ×ˢ s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.coev_apply`：∀ (X : Type u_2) (Y : Type u_3) [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (b : Y),   ⇑(ContinuousMap.coev X Y 
b) = Prod.mk b
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_coev {y : Y} (s : Set X) : coev X Y y '' s = {y} ×ˢ s := by simp [singleton_prod]

/-- The coevaluation map `Y → C(X, Y × X)` is continuous (always). -/
/-
**ContinuousMap.continuous_coev** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuous_coev : Continuous (coev X Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `ContinuousMap.continuous_prodMk_const`：continuous_prodMk_const : Continu
ous fun p : X × C(Y, Z) => prodMk (const Y p.1) p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
The coevaluation map `Y → C(X, Y × X)` is continuous (always).
-/
theorem continuous_coev : Continuous (coev X Y) :=
  ((continuous_prodMk_const (X := Y) (Y := X) (Z := X)).comp
    (.prodMk continuous_id (continuous_const (y := ContinuousMap.id _))) :)

end Coev

section Curry

/-- The curried form of a continuous map `α × β → γ` as a continuous map `α → C(β, γ)`.
If `a × β` is locally compact, this is continuous. If `α` and `β` are both locally
compact, then this is a homeomorphism, see `Homeomorph.curry`. -/
/-
**ContinuousMap.curry** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：curry (f : C(X × Y, Z)) : C(X, C(Y, Z)) where toFun a
参数：f : C(X × Y, Z)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The curried form of a continuous map `α × β → γ` as a continuous map `α → C(β, γ
)`.
If `a × β` is locally compact, this is continuous. If `α` and `β` are both local
ly
compact, then this is a homeomorphism, see `Homeomorph.curry`.
-/
def curry (f : C(X × Y, Z)) : C(X, C(Y, Z)) where
  toFun a := ⟨Function.curry f a, f.continuous.comp <| by fun_prop⟩
  continuous_toFun := (continuous_postcomp f).comp continuous_coev

@[simp]
/-
**ContinuousMap.curry_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：curry_apply (f : C(X × Y, Z)) (a : X) (b : Y) : f.curry a b = f (a, b)
参数：f : C(X × Y, Z)；a : X；b : Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_apply (f : C(X × Y, Z)) (a : X) (b : Y) : f.curry a b = f (a, b) :=
  rfl

/-- To show continuity of a map `α → C(β, γ)`, it suffices to show that its uncurried form
`α × β → γ` is continuous. -/
/-
**ContinuousMap.continuous_of_continuous_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMap`。
形式化陈述：continuous_of_continuous_uncurry (f : X -> C(Y, Z)) (h : Continuous (Funct
ion.uncurry fun x y => f x y)) : Continuous f
参数：f : X -> C(Y, Z)；h : Continuous (Function.uncurry fun x y => f x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun

--- 原说明 ---
To show continuity of a map `α → C(β, γ)`, it suffices to show that its uncurrie
d form
`α × β → γ` is continuous.
-/
theorem continuous_of_continuous_uncurry (f : X → C(Y, Z))
    (h : Continuous (Function.uncurry fun x y => f x y)) : Continuous f :=
  (curry ⟨_, h⟩).2
/-
**ContinuousMap.continuousOn_of_continuousOn_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousMap`。
形式化陈述：continuousOn_of_continuousOn_uncurry {s : Set X} (f : X -> C(Y, Z)) (h : C
ontinuousOn (Function.uncurry fun x y => f x y) (s ×ˢ univ)) : ContinuousOn f s
参数：f : X -> C(Y, Z)；h : ContinuousOn (Function.uncurry fun x y => f x y) (s ×ˢ u
niv)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `trivial`：True
-/
theorem continuousOn_of_continuousOn_uncurry {s : Set X} (f : X → C(Y, Z))
    (h : ContinuousOn (Function.uncurry fun x y => f x y) (s ×ˢ univ)) : ContinuousOn f s :=
  continuousOn_iff_continuous_domRestrict.mpr <| continuous_of_continuous_uncurry _ <|
    h.comp_continuous (continuous_subtype_val.prodMap continuous_id) (fun x ↦ ⟨x.1.2, trivial⟩)

/-- The currying process is a continuous map between function spaces. -/
/-
**ContinuousMap.continuous_curry** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuous_curry [LocallyCompactSpace (X × Y)] : Continuous (curry : C(X ×
 Y, Z) -> C(X, C(Y, Z)))
参数：X × Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.comp_continuous_iff'`：comp_continuous_iff' (h : X ≃ₜ Y) {f : 
Y -> Z} : Continuous (f ∘ h) ↔ Continuous f
· 使用定理 `ContinuousEval.continuous_eval`：∀ {F : Type u_1} {X : outParam (Type u_2
)} {Y : outParam (Type u_3)} {inst : FunLike F X Y}   {inst_1 : TopologicalSpace
 F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalOfLocallyCompactPair`：∀ {X : Type u_2} {
Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [Locally
CompactPair X Y],   ContinuousEval C(X, Y)…
· 使用定理 `instLocallyCompactPairOfLocallyCompactSpace`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactSp
ace X],   LocallyCompactPair X Y

--- 原说明 ---
The currying process is a continuous map between function spaces.
-/
theorem continuous_curry [LocallyCompactSpace (X × Y)] :
    Continuous (curry : C(X × Y, Z) → C(X, C(Y, Z))) := by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval

/-- The uncurried form of a continuous map `X → C(Y, Z)` is a continuous map `X × Y → Z`. -/
/-
**ContinuousMap.continuous_uncurry_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMap`。
形式化陈述：continuous_uncurry_of_continuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z)
)) : Continuous (Function.uncurry fun x y => f x y)
参数：f : C(X, C(Y, Z))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousEval.continuous_eval`：∀ {F : Type u_1} {X : outParam (Type u_2
)} {Y : outParam (Type u_3)} {inst : FunLike F X Y}   {inst_1 : TopologicalSpace
 F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalOfLocallyCompactPair`：∀ {X : Type u_2} {
Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [Locally
CompactPair X Y],   ContinuousEval C(X, Y)…
· 使用定理 `instLocallyCompactPairOfLocallyCompactSpace`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactSp
ace X],   LocallyCompactPair X Y
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
The uncurried form of a continuous map `X → C(Y, Z)` is a continuous map `X × Y 
→ Z`.
-/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) :
    Continuous (Function.uncurry fun x y => f x y) :=
  continuous_eval.comp <| f.continuous.prodMap continuous_id

/-- The uncurried form of a continuous map `X → C(Y, Z)` as a continuous map `X × Y → Z` (if `Y` is
locally compact). If `X` is also locally compact, then this is a homeomorphism between the two
function spaces, see `Homeomorph.curry`. -/
@[simps]
/-
**ContinuousMap.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：uncurry [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : C(X × Y, Z)
参数：f : C(X, C(Y, Z))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_uncurry_of_continuous`：continuous_uncurry_of_co
ntinuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : Continuous (Function.uncu
rry fun x y => f x y)

--- 原说明 ---
The uncurried form of a continuous map `X → C(Y, Z)` as a continuous map `X × Y 
→ Z` (if `Y` is
locally compact). If `X` is also locally compact, then this is a homeomorphism b
etween the two
function spaces, see `Homeomorph.curry`.
-/
def uncurry [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : C(X × Y, Z) :=
  ⟨_, continuous_uncurry_of_continuous f⟩

set_option backward.defeqAttrib.useBackward true in
/-- The uncurrying process is a continuous map between function spaces. -/
/-
**ContinuousMap.continuous_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuous_uncurry [LocallyCompactSpace X] [LocallyCompactSpace Y] : Conti
nuous (uncurry : C(X, C(Y, Z)) -> C(X × Y, Z))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.comp_continuous_iff'`：comp_continuous_iff' (h : X ≃ₜ Y) {f : 
Y -> Z} : Continuous (f ∘ h) ↔ Continuous f
· 使用定理 `Continuous.eval`：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} {Z : Typ
e u_4} [inst : FunLike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : Topologi
calSp…
· 使用定理 `ContinuousMap.instContinuousEvalOfLocallyCompactPair`：∀ {X : Type u_2} {
Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [Locally
CompactPair X Y],   ContinuousEval C(X, Y)…
· 使用定理 `instLocallyCompactPairOfLocallyCompactSpace`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactSp
ace X],   LocallyCompactPair X Y
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
The uncurrying process is a continuous map between function spaces.
-/
theorem continuous_uncurry [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    Continuous (uncurry : C(X, C(Y, Z)) → C(X × Y, Z)) := by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  dsimp [Function.comp_def]
  exact (continuous_fst.fst.eval continuous_fst.snd).eval continuous_snd

/-- The family of constant maps: `Y → C(X, Y)` as a continuous map. -/
/-
**ContinuousMap.const'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：const' : C(Y, C(X, Y))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of constant maps: `Y → C(X, Y)` as a continuous map.
-/
def const' : C(Y, C(X, Y)) :=
  curry ContinuousMap.fst

@[simp]
/-
**ContinuousMap.coe_const'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_const' : (const' : Y -> C(X, Y)) = const X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_const' : (const' : Y → C(X, Y)) = const X :=
  rfl

@[fun_prop]
/-
**ContinuousMap.continuous_const'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：continuous_const' : Continuous (const X : Y -> C(X, Y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
theorem continuous_const' : Continuous (const X : Y → C(X, Y)) :=
  const'.continuous

section mkD

/-- A variant of `ContinuousMap.continuous_of_continuous_uncurry` in terms of
`ContinuousMap.mkD`.
Of course, in this particular setting, `fun x ↦ mkD (f x) g` is just `f`,
but the `mkD` spelling appears naturally in the context of `C(α, β)`-valued integration. -/
/-
**ContinuousMap.continuous_mkD_of_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousM
ap`。
形式化陈述：continuous_mkD_of_uncurry (f : T -> X -> Y) (g : C(X, Y)) (f_cont : Contin
uous (Function.uncurry f)) : Continuous (fun x => mkD (f x) g)
参数：f : T -> X -> Y；g : C(X, Y)；f_cont : Continuous (Function.uncurry f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ContinuousMap.mkD_of_continuous`：mkD_of_continuous {f : α -> β} {g : C(α
, β)} (hf : Continuous f) : mkD f g = ⟨f, hf⟩

--- 原说明 ---
A variant of `ContinuousMap.continuous_of_continuous_uncurry` in terms of
`ContinuousMap.mkD`.
Of course, in this particular setting, `fun x ↦ mkD (f x) g` is just `f`,
but the `mkD` spelling appears naturally in the context of `C(α, β)`-valued inte
gration.
-/
lemma continuous_mkD_of_uncurry
    (f : T → X → Y) (g : C(X, Y)) (f_cont : Continuous (Function.uncurry f)) :
    Continuous (fun x ↦ mkD (f x) g) := by
  have (x : _) : Continuous (f x) := f_cont.comp (Continuous.prodMk_right x)
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuous (this x)]
  exact f_cont

open Set in
/-
**ContinuousMap.continuousOn_mkD_of_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMap`。
形式化陈述：continuousOn_mkD_of_uncurry {s : Set T} (f : T -> X -> Y) (g : C(X, Y)) (f
_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) : ContinuousOn (fun x => 
mkD (f x) g) s
参数：f : T -> X -> Y；g : C(X, Y)；f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ 
univ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.domRestrict_def`：domRestrict_def (s : Set α) : s.domRestrict (π
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ContinuousMap.mkD_of_continuous`：mkD_of_continuous {f : α -> β} {g : C(α
, β)} (hf : Continuous f) : mkD f g = ⟨f, hf⟩
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
lemma continuousOn_mkD_of_uncurry {s : Set T}
    (f : T → X → Y) (g : C(X, Y)) (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) :
    ContinuousOn (fun x ↦ mkD (f x) g) s := by
  have (x) (hx : x ∈ s) : Continuous (f x) := f_cont.comp_continuous
    (Continuous.prodMk_right x) fun _ ↦ ⟨hx, trivial⟩
  simp_rw [continuousOn_iff_continuous_domRestrict, s.domRestrict_def]
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuous (this x x.2)]
  exact f_cont.comp_continuous (.prodMap continuous_subtype_val continuous_id)
    fun xz ↦ ⟨xz.1.2, trivial⟩

open Set in
/-
**ContinuousMap.continuous_mkD_restrict_of_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntinuousMap`。
形式化陈述：continuous_mkD_restrict_of_uncurry {t : Set X} (f : T -> X -> Y) (g : C(t,
 Y)) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t)) : Continuous (fun 
x => mkD (t.domRestrict (f x)) g)
参数：f : T -> X -> Y；g : C(t, Y)；f_cont : ContinuousOn (Function.uncurry f) (univ 
×ˢ t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `trivial`：True
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ContinuousMap.mkD_of_continuousOn`：mkD_of_continuousOn {s : Set α} {f : 
α -> β} {g : C(s, β)} (hf : ContinuousOn f s) : mkD (s.domRestrict f) g = ⟨s.dom
Restrict f, hf.domRestr…
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma continuous_mkD_restrict_of_uncurry {t : Set X}
    (f : T → X → Y) (g : C(t, Y)) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t)) :
    Continuous (fun x ↦ mkD (t.domRestrict (f x)) g) := by
  have (x : _) : ContinuousOn (f x) t :=
    f_cont.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨trivial, hz⟩
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuousOn (this x)]
  exact f_cont.comp_continuous (.prodMap continuous_id continuous_subtype_val)
    fun xz ↦ ⟨trivial, xz.2.2⟩

open Set in
/-
**ContinuousMap.continuousOn_mkD_restrict_of_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `
ContinuousMap`。
形式化陈述：continuousOn_mkD_restrict_of_uncurry {s : Set T} {t : Set X} (f : T -> X -
> Y) (g : C(t, Y)) (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) : Conti
nuousOn (fun x => mkD (t.domRestrict (f x)) g) s
参数：f : T -> X -> Y；g : C(t, Y)；f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ 
t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.domRestrict_def`：domRestrict_def (s : Set α) : s.domRestrict (π
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ContinuousMap.mkD_of_continuousOn`：mkD_of_continuousOn {s : Set α} {f : 
α -> β} {g : C(s, β)} (hf : ContinuousOn f s) : mkD (s.domRestrict f) g = ⟨s.dom
Restrict f, hf.domRestr…
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
lemma continuousOn_mkD_restrict_of_uncurry {s : Set T} {t : Set X}
    (f : T → X → Y) (g : C(t, Y))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) :
    ContinuousOn (fun x ↦ mkD (t.domRestrict (f x)) g) s := by
  have (x) (hx : x ∈ s) : ContinuousOn (f x) t :=
    f_cont.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  simp_rw [continuousOn_iff_continuous_domRestrict, s.domRestrict_def]
  refine continuous_of_continuous_uncurry _ ?_
  conv in mkD _ _ => rw [mkD_of_continuousOn (this x x.2)]
  exact f_cont.comp_continuous (.prodMap continuous_subtype_val continuous_subtype_val)
    fun xz ↦ ⟨xz.1.2, xz.2.2⟩

end mkD

end Curry

end CompactOpen

end ContinuousMap

open ContinuousMap

namespace Homeomorph

variable {X : Type*} {Y : Type*} {Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Currying as a homeomorphism between the function spaces `C(X × Y, Z)` and `C(X, C(Y, Z))`. -/
/-
**Homeomorph.curry** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：curry [LocallyCompactSpace X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X
, C(Y, Z))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_uncurry`：continuous_uncurry [LocallyCompactSpac
e X] [LocallyCompactSpace Y] : Continuous (uncurry : C(X, C(Y, Z)) -> C(X × Y, Z
))

--- 原说明 ---
Currying as a homeomorphism between the function spaces `C(X × Y, Z)` and `C(X, 
C(Y, Z))`.
-/
def curry [LocallyCompactSpace X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry, continuous_uncurry⟩

/-- If `X` has a single element, then `Y` is homeomorphic to `C(X, Y)`. -/
/-
**Homeomorph.continuousMapOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：continuousMapOfUnique [Unique X] : Y ≃ₜ C(X, Y) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_const'`：continuous_const' : Continuous (const X
 : Y -> C(X, Y))

--- 原说明 ---
If `X` has a single element, then `Y` is homeomorphic to `C(X, Y)`.
-/
def continuousMapOfUnique [Unique X] : Y ≃ₜ C(X, Y) where
  toFun := const X
  invFun f := f default
  right_inv f := by
    ext x
    rw [Unique.eq_default x]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval_const _

@[simp]
/-
**Homeomorph.continuousMapOfUnique_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：continuousMapOfUnique_apply [Unique X] (y : Y) (x : X) : continuousMapOfUn
ique y x = y
参数：y : Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem continuousMapOfUnique_apply [Unique X] (y : Y) (x : X) : continuousMapOfUnique y x = y :=
  rfl

@[simp]
/-
**Homeomorph.continuousMapOfUnique_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomo
rph`。
形式化陈述：continuousMapOfUnique_symm_apply [Unique X] (f : C(X, Y)) : continuousMapO
fUnique.symm f = f default
参数：f : C(X, Y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem continuousMapOfUnique_symm_apply [Unique X] (f : C(X, Y)) :
    continuousMapOfUnique.symm f = f default :=
  rfl

end Homeomorph

section IsQuotientMap

variable {X₀ X Y Z : Type*} [TopologicalSpace X₀] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [LocallyCompactSpace Y] {f : X₀ → X}

/-
**Topology.IsQuotientMap.continuous_lift_prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsQuotientMap.continuous_lift_prod_left (hf : IsQuotientMap f) {g
 : X × Y -> Z} (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g
参数：hf : IsQuotientMap f；hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `ContinuousMap.continuous_uncurry_of_continuous`：continuous_uncurry_of_co
ntinuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : Continuous (Function.uncu
rry fun x y => f x y)
-/
theorem Topology.IsQuotientMap.continuous_lift_prod_left (hf : IsQuotientMap f) {g : X × Y → Z}
    (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g := by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : ∀ x : X, Continuous fun y => g (x, y) := by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).continuous
  let G : X → C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩
/-
**Topology.IsQuotientMap.continuous_lift_prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Topology.IsQuotientMap.continuous_lift_prod_right (hf : IsQuotientMap f) {
g : Y × X -> Z} (hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)) : Continuous 
g
参数：hf : IsQuotientMap f；hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `Topology.IsQuotientMap.continuous_lift_prod_left`：Topology.IsQuotientMap
.continuous_lift_prod_left (hf : IsQuotientMap f) {g : X × Y -> Z} (hg : Continu
ous fun p : X₀ × Y => g (f p.1, p.2)) …
-/
theorem Topology.IsQuotientMap.continuous_lift_prod_right (hf : IsQuotientMap f) {g : Y × X → Z}
    (hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)) : Continuous g := by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) :=
    hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  exact (hf.continuous_lift_prod_left this).comp continuous_swap

end IsQuotientMap

