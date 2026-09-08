/-
Copyright (c) 2024 Anatole Dedeker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedeker, Etienne Marion, Florestan Martin-Baillon, Vincent Guirardel
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocalAtTarget

/-!
# Proper group action

In this file we define proper action of a group on a topological space, and we prove that in this
case the quotient space is T2. We also give equivalent definitions of proper action using
ultrafilters and show the transfer of proper action to a closed subgroup.

## Main definitions

* `ProperSMul` : a group `G` acts properly on a topological space `X`
  if the map `(g, x) ↦ (g • x, x)` is proper, in the sense of `IsProperMap`.

## Main statements

* `t2Space_quotient_mulAction_of_properSMul`: If a group `G` acts properly
  on a topological space `X`, then the quotient space is Hausdorff (T2).
* `t2Space_of_properSMul_of_t1Group`: If a T1 group acts properly on a topological space,
  then this topological space is T2.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

Hausdorff, group action, proper action
-/

public section

open Filter Topology Set Prod

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
/-
**ProperVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) →   (X : Type u_2) → [TopologicalSpace G] → [TopologicalSpa
ce X] → [inst : AddGroup G] → [AddAction G X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`).
-/
class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_vadd_pair : IsProperMap (fun gx ↦ (gx.1 +ᵥ gx.2, gx.2) : G × X → X × X)

/-- Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
@[to_additive existing (attr := mk_iff)]
/-
**ProperSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) →   (X : Type u_2) → [TopologicalSpace G] → [TopologicalSpa
ce X] → [inst : Group G] → [MulAction G X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Proper group action in the sense of Bourbaki:
the map `G × X → X × X` is a proper map (see `IsProperMap`).
-/
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_smul_pair : IsProperMap (fun gx ↦ (gx.1 • gx.2, gx.2) : G × X → X × X)

attribute [to_additive existing] properSMul_iff

variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [TopologicalSpace X]

/-- If a group acts properly then in particular it acts continuously. -/
@[to_additive /-- If a group acts properly then in particular it acts continuously. -/]
-- See note [lower instance property]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ProperSMul.toContinuousSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := isProperMap_smul_pair.continuous.fst

/-- A group `G` acts properly on a topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `g • x₂ = x₁` and `𝒰.fst` converges to `g`. -/
@[to_additive /-- An additive group `G` acts properly on a topological space `X` if and only if
for all ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)`
along the map `(g, x) ↦ (g • x, x)`, then there exists `g : G` such that `g • x₂ = x₁`
and `𝒰.fst` converges to `g`. -/]
/-
**properSMul_iff_continuousSMul_ultrafilter_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：properSMul_iff_continuousSMul_ultrafilter_tendsto : ProperSMul G X ↔ Conti
nuousSMul G X ∧ (forall 𝒰 : Ultrafilter (G × X), forall x₁ x₂ : X, Tendsto (fun 
gx : G × X => (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) -> exists g : G, g • x₂ = x₁ ∧
 Tendsto (Prod.fst : G × X -> G) 𝒰 (𝓝 g))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperSMul.toContinuousSMul`：∀ {G : Type u_1} {X : Type u_2} [inst : Gro
up G] [inst_1 : MulAction G X] [inst_2 : TopologicalSpace G]   [inst_3 : Topolog
icalSpace X] [Pro…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isProperMap_iff_ultrafilter`：isProperMap_iff_ultrafilter : IsProperMap f
 ↔ Continuous f ∧ forall ⦃𝒰 : Ultrafilter X⦄, forall ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) 
-> exists x, f x …
· 使用定理 `properSMul_iff`：∀ (G : Type u_1) (X : Type u_2) [inst : TopologicalSpace
 G] [inst_1 : TopologicalSpace X] [inst_2 : Group G]   [inst_3 : MulAction G X],
 Pro…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.le_prod`：le_prod {f : Filter (α × β)} {g : Filter α} {g' : Filter
 β} : (f <= g ×ˢ g') ↔ Tendsto Prod.fst f g ∧ Tendsto Prod.snd f g'
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
        Tendsto (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) →
        ∃ g : G, g • x₂ = x₁ ∧ Tendsto (Prod.fst : G × X → G) 𝒰 (𝓝 g)) := by
  refine ⟨fun h ↦ ⟨inferInstance, fun 𝒰 x₁ x₂ h' ↦ ?_⟩, fun ⟨cont, h⟩ ↦ ?_⟩
  · rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    rcases h.2 h' with ⟨gx, hgx1, hgx2⟩
    refine ⟨gx.1, ?_, (continuous_fst.tendsto gx).mono_left hgx2⟩
    simp only [Prod.mk.injEq] at hgx1
    rw [← hgx1.2, hgx1.1]
  · rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    refine ⟨(g, x₂), by simp_rw [hg1], ?_⟩
    rw [nhds_prod_eq, 𝒰.le_prod]
    exact ⟨hg2, (continuous_snd.tendsto _).comp hxx⟩

/-- A group `G` acts properly on a T2 topological space `X` if and only if for all ultrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x)`,
then there exists `g : G` such that `𝒰.fst` converges to `g`. -/
/-
**properSMul_iff_continuousSMul_ultrafilter_tendsto_t2** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] : ProperS
Mul G X ↔ ContinuousSMul G X ∧ (forall 𝒰 : Ultrafilter (G × X), forall x₁ x₂ : X
, Tendsto (fun gx : G × X => (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) -> exists g : G
, Tendsto (Prod.fst : G × X -> G) 𝒰 (𝓝 g))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `properSMul_iff_continuousSMul_ultrafilter_tendsto`：properSMul_iff_contin
uousSMul_ultrafilter_tendsto : ProperSMul G X ↔ ContinuousSMul G X ∧ (forall 𝒰 :
 Ultrafilter (G × X), forall x₁ x₂ : X,…
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
A group `G` acts properly on a T2 topological space `X` if and only if for all u
ltrafilters
`𝒰` on `X × G`, if `𝒰` converges to `(x₁, x₂)` along the map `(g, x) ↦ (g • x, x
)`,
then there exists `g : G` such that `𝒰.fst` converges to `g`.
-/
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
        Tendsto (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) →
        ∃ g : G, Tendsto (Prod.fst : G × X → G) 𝒰 (𝓝 g)) := by
  rw [properSMul_iff_continuousSMul_ultrafilter_tendsto]
  refine and_congr_right fun hc ↦ ?_
  congrm ∀ 𝒰 x₁ x₂ hxx, ∃ g, ?_
  exact and_iff_right_of_imp fun hg ↦ tendsto_nhds_unique
    (hg.smul ((continuous_snd.tendsto _).comp hxx)) ((continuous_fst.tendsto _).comp hxx)

/-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/
@[to_additive /-- If `G` acts properly on `X`, then the quotient space is Hausdorff (T2). -/]
/-
**t2Space_quotient_mulAction_of_properSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：t2Space_quotient_mulAction_of_properSMul [ProperSMul G X] : T2Space (Quoti
ent (MulAction.orbitRel G X))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `t2_iff_isClosed_diagonal`：t2_iff_isClosed_diagonal : T2Space X ↔ IsClose
d (diagonal X)
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `IsOpenQuotientMap.prodMap`：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z
 -> W} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap
 (Prod.map f g)
· 使用定理 `MulAction.isOpenQuotientMap_quotientMk`：MulAction.isOpenQuotientMap_quot
ientMk [ContinuousConstSMul Γ T] : IsOpenQuotientMap (Quotient.mk (MulAction.orb
itRel Γ T))
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `ProperSMul.toContinuousSMul`：∀ {G : Type u_1} {X : Type u_2} [inst : Gro
up G] [inst_1 : MulAction G X] [inst_2 : TopologicalSpace G]   [inst_3 : Topolog
icalSpace X] [Pro…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isClosed_preimage`：∀ {X : Type u_1} {Y : Type u_2}
 {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolo
gy.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
· 使用定理 `MulAction.orbitRel_apply`：orbitRel_apply {a b : α} : orbitRel G α a b ↔ 
a in orbit G b
· 使用定理 `MulAction.mem_orbit_iff`：mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ 
exists x : γ, x • a₁ = a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用定理 `ProperSMul.isProperMap_smul_pair`：∀ {G : Type u_1} {X : Type u_2} {inst 
: TopologicalSpace G} {inst_1 : TopologicalSpace X} {inst_2 : Group G}   {inst_3
 : MulAction G X} [sel…

--- 原说明 ---
If `G` acts properly on `X`, then the quotient space is Hausdorff (T2).
-/
instance t2Space_quotient_mulAction_of_properSMul [ProperSMul G X] :
    T2Space (Quotient (MulAction.orbitRel G X)) := by
  rw [t2_iff_isClosed_diagonal]
  set R := MulAction.orbitRel G X
  let π : X → Quotient R := Quotient.mk'
  have : IsOpenQuotientMap (Prod.map π π) :=
    MulAction.isOpenQuotientMap_quotientMk.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [← this.isQuotientMap.isClosed_preimage]
  convert! ProperSMul.isProperMap_smul_pair.isClosedMap.isClosed_range
  · ext ⟨x₁, x₂⟩
    simp only [mem_preimage, map_apply, mem_diagonal_iff, mem_range, Prod.mk.injEq, Prod.exists,
      exists_eq_right]
    rw [Quotient.eq', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  all_goals infer_instance

/-- If a T1 group acts properly on a topological space, then this topological space is T2. -/
@[to_additive /-- If a T1 group acts properly on a topological space,
then this topological space is T2. -/]
/-
**t2Space_of_properSMul_of_t1Group** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2Space_of_properSMul_of_t1Group [h_proper : ProperSMul G X] [T1Space G] :
 T2Space X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsClosedEmbedding.isProperMap`：Topology.IsClosedEmbedding.isPro
perMap (hf : IsClosedEmbedding f) : IsProperMap f
· 使用引理 `isEmbedding_prodMkRight`：isEmbedding_prodMkRight (x : X) : IsEmbedding (
Prod.mk x : Y -> X × Y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsClosed.prod`：IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁
) (h₂ : IsClosed s₂) : IsClosed (s₁ ×ˢ s₂)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `t2_iff_isClosed_diagonal`：t2_iff_isClosed_diagonal : T2Space X ↔ IsClose
d (diagonal X)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `properSMul_iff`：∀ (G : Type u_1) (X : Type u_2) [inst : TopologicalSpace
 G] [inst_1 : TopologicalSpace X] [inst_2 : Group G]   [inst_3 : MulAction G X],
 Pro…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Set.range_diag`：range_diag : range Function.diag = diagonal α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsProperMap.isClosed_range`：IsProperMap.isClosed_range (hf : IsProperMap
 f) : IsClosed (range f)
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
-/
theorem t2Space_of_properSMul_of_t1Group [h_proper : ProperSMul G X] [T1Space G] : T2Space X := by
  let f := fun x : X ↦ ((1 : G), x)
  have proper_f : IsProperMap f := by
    refine IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkRight 1, ?_⟩
    have : range f = ({1} ×ˢ univ) := by simp [f, Set.singleton_prod]
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  rw [t2_iff_isClosed_diagonal]
  let g := fun gx : G × X ↦ (gx.1 • gx.2, gx.2)
  have proper_g : IsProperMap g := (properSMul_iff G X).1 h_proper
  have : g ∘ f = Function.diag := by ext x <;> simp [f, g]
  have range_gf : range (g ∘ f) = diagonal X := by simp [this]
  rw [← range_gf]
  exact (proper_g.comp proper_f).isClosed_range

/-- If two groups `H` and `G` act on a topological space `X` such that `G` acts properly and
there exists a group homomorphism `H → G` which is a closed embedding compatible with the actions,
then `H` also acts properly on `X`. -/
@[to_additive /-- If two groups `H` and `G` act on a topological space `X` such that `G` acts
properly and there exists a group homomorphism `H → G` which is a closed embedding compatible with
the actions, then `H` also acts properly on `X`. -/]
/-
**properSMul_of_isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：properSMul_of_isClosedEmbedding {H : Type*} [Group H] [MulAction H X] [Top
ologicalSpace H] [ProperSMul G X] (f : H ->* G) (f_clemb : IsClosedEmbedding f) 
(f_compat : forall (h : H) (x : X), f h • x = h • x) : ProperSMul H X where isPr
operMap_smul_pair
参数：f : H ->* G；f_clemb : IsClosedEmbedding f；f_compat : forall (h : H) (x : X), 
f h • x = h • x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.prodMap`：IsProperMap.prodMap {g : Z -> W} (hf : IsProperMap 
f) (hg : IsProperMap g) : IsProperMap (Prod.map f g)
· 使用引理 `Topology.IsClosedEmbedding.isProperMap`：Topology.IsClosedEmbedding.isPro
perMap (hf : IsClosedEmbedding f) : IsProperMap f
· 使用定理 `isProperMap_id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsProperMa
p id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
· 使用定理 `ProperSMul.isProperMap_smul_pair`：∀ {G : Type u_1} {X : Type u_2} {inst 
: TopologicalSpace G} {inst_1 : TopologicalSpace X} {inst_2 : Group G}   {inst_3
 : MulAction G X} [sel…
-/
theorem properSMul_of_isClosedEmbedding {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
    [ProperSMul G X] (f : H →* G) (f_clemb : IsClosedEmbedding f)
    (f_compat : ∀ (h : H) (x : X), f h • x = h • x) : ProperSMul H X where
  isProperMap_smul_pair := by
    have h : IsProperMap (Prod.map f (fun x : X ↦ x)) := f_clemb.isProperMap.prodMap isProperMap_id
    have : (fun hx : H × X ↦ (hx.1 • hx.2, hx.2)) = (fun hx ↦ (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    exact ProperSMul.isProperMap_smul_pair.comp h

/-- If `H` is a closed subgroup of `G` and `G` acts properly on `X`, then so does `H`. -/
@[to_additive
/-- If `H` is a closed subgroup of `G` and `G` acts properly on `X`, then so does `H`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X :=
  properSMul_of_isClosedEmbedding H.subtype H_closed.isClosedEmbedding_subtypeVal fun _ _ ↦ rfl

/-- The action `G ↷ G` by left translations is proper. -/
@[to_additive
/-- The action `G ↷ G` by left translations is proper. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalGroup G] : ProperSMul G G where
  isProperMap_smul_pair := by
    let Φ : G × G ≃ₜ G × G :=
    { toFun := fun gh ↦ (gh.1 * gh.2, gh.2)
      invFun := fun gh ↦ (gh.1 * gh.2⁻¹, gh.2)
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
    exact Φ.isProperMap

open MulOpposite in
/-- The action `Gᵐᵒᵖ ↷ G` by right translations is proper. -/
@[to_additive
/-- The action `Gᵃᵒᵖ ↷ G` by right translations is proper. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalGroup G] : ProperSMul Gᵐᵒᵖ G where
  isProperMap_smul_pair := by
    let Φ : Gᵐᵒᵖ × G ≃ₜ G × G :=
    { toFun := fun gh ↦ (gh.2 * (unop gh.1), gh.2)
      invFun := fun gh ↦ (op (gh.2⁻¹ * gh.1), gh.2)
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
    exact Φ.isProperMap

/-- Given a closed subgroup `H` of a topological group `G`, the right action of `H` on `G`
is proper. Note that the corresponding statement for the left action can be proven by
`inferInstance`. -/
@[to_additive /-- Given a closed subgroup `H` of an additive topological group `G`, the right
action of `H` on `G` is proper. Note that the corresponding statement for the left action can be
proven by `inferInstance`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalGroup G] {H : Subgroup G} [H_closed : IsClosed (H : Set G)] :
    ProperSMul H.op G :=
  have : IsClosed (H.op : Set Gᵐᵒᵖ) := H_closed.preimage MulOpposite.continuous_unop
  inferInstance

@[to_additive]
/-
**QuotientGroup.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：QuotientGroup.instT2Space [IsTopologicalGroup G] {H : Subgroup G} [IsClose
d (H : Set G)] : T2Space (G ⧸ H)
参数：H : Set G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instProperSMulSubtypeMulOppositeMemSubgroupOpOfIsTopologicalGroupOfIsClo
sedCoe`：∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopol
ogicalGroup G] {H : Subgroup G}   [H_closed : IsClosed ↑H], ProperSM…
-/
instance QuotientGroup.instT2Space [IsTopologicalGroup G] {H : Subgroup G} [IsClosed (H : Set G)] :
    T2Space (G ⧸ H) :=
  t2Space_quotient_mulAction_of_properSMul

/-- If `G` acts on `X` properly, then the map `G × T → X × T, (g, t) ↦ (g • t, t)` is still
proper for *any* subset `T` of `X`. -/
@[to_additive
/-- If `G` acts on `X` properly, then the map `G × T → X × T, (g, t) ↦ (g +ᵥ t, t)` is still
proper for *any* subset `T` of `X`. -/]
/-
**ProperSMul.isProperMap_smul_pair_set** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ProperSMul.isProperMap_smul_pair_set [ProperSMul G X] {t : Set X} : IsProp
erMap (fun (gx : G × t) => ((gx.1 • gx.2, gx.2) : X × t))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperSMul.isProperMap_smul_pair`：∀ {G : Type u_1} {X : Type u_2} {inst 
: TopologicalSpace G} {inst_1 : TopologicalSpace X} {inst_2 : Group G}   {inst_3
 : MulAction G X} [sel…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
· 使用定理 `Homeomorph.isProperMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y), IsProperMap ⇑e
· 使用引理 `IsProperMap.restrictPreimage`：IsProperMap.restrictPreimage (H : IsProper
Map f) (s : Set β) : IsProperMap (s.restrictPreimage f)
-/
lemma ProperSMul.isProperMap_smul_pair_set [ProperSMul G X] {t : Set X} :
    IsProperMap (fun (gx : G × t) ↦ ((gx.1 • gx.2, gx.2) : X × t)) := by
  let Φ : G × X → X × X := fun gx ↦ (gx.1 • gx.2, gx.2)
  have Φ_proper : IsProperMap Φ := ProperSMul.isProperMap_smul_pair
  let α : G × t ≃ₜ (Φ ⁻¹' snd ⁻¹' t) :=
    have : univ ×ˢ t = Φ ⁻¹' snd ⁻¹' t := by ext; simp [Φ]
    Homeomorph.Set.univ G |>.symm.prodCongr (.refl t) |>.trans
      ((Homeomorph.Set.prod _ t).symm) |>.trans (Homeomorph.setCongr this)
  let β : X × t ≃ₜ (snd ⁻¹' t) :=
    Homeomorph.Set.univ X |>.symm.prodCongr (.refl t) |>.trans
      ((Homeomorph.Set.prod _ t).symm) |>.trans (Homeomorph.setCongr univ_prod)
  exact β.symm.isProperMap.comp (Φ_proper.restrictPreimage (snd ⁻¹' t)) |>.comp α.isProperMap

open scoped Pointwise in
/-- If `G` acts on `X` properly, the set `s • t` is closed when `s : Set G` is *closed* and
`t : Set X` is *compact*.

See also `IsClosed.smul_left_of_isCompact` for a version with the assumptions on `s` and `t`
reversed. -/
@[to_additive
/-- If `G` acts on `X` properly, the set `s +ᵥ t` is closed when `s : Set G` is *closed* and
`t : Set X` is *compact*. In particular, this applies when the action comes from an
`IsTopologicalAddTorsor`.

See also `IsClosed.vadd_left_of_isCompact` for a version with the assumptions on `s` and `t`
reversed. -/]
/-
**IsClosed.smul_right_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.smul_right_of_isCompact [ProperSMul G X] {s : Set G} {t : Set X} 
(hs : IsClosed s) (ht : IsCompact t) : IsClosed (s • t)
参数：hs : IsClosed s；ht : IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProperSMul.isProperMap_smul_pair_set`：ProperSMul.isProperMap_smul_pair_s
et [ProperSMul G X] {t : Set X} : IsProperMap (fun (gx : G × t) => ((gx.1 • gx.2
, gx.2) : X × t))
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.smul_subset_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {
s : Set α} {t u : Set β}, s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.smul_mem_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
: Set α} {t : Set β} {a : α} {b : β}, a ∈ s → b ∈ t → a • b ∈ s • t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
· 使用定理 `isProperMap_fst_of_compactSpace`：isProperMap_fst_of_compactSpace [Compac
tSpace Y] : IsProperMap (Prod.fst : X × Y -> X)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
theorem IsClosed.smul_right_of_isCompact [ProperSMul G X] {s : Set G} {t : Set X} (hs : IsClosed s)
    (ht : IsCompact t) : IsClosed (s • t) := by
  let Ψ : G × t → X × t := fun gx ↦ (gx.1 • gx.2, gx.2)
  have Ψ_proper : IsProperMap Ψ := ProperSMul.isProperMap_smul_pair_set
  have : s • t = (fst ∘ Ψ) '' fst ⁻¹' s :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx ↦ mem_image_of_mem (fst ∘ Ψ) (x := ⟨g, ⟨x, hx⟩⟩) hg)
      (image_subset_iff.mpr fun ⟨g, ⟨x, hx⟩⟩ hg ↦ smul_mem_smul hg hx)
  rw [this]
  have : CompactSpace t := isCompact_iff_compactSpace.mp ht
  exact (isProperMap_fst_of_compactSpace.comp Ψ_proper).isClosedMap _ (hs.preimage continuous_fst)

/-! One may expect `IsClosed.smul_right_of_isCompact` to hold for arbitrary continuous actions,
but such a lemma can't be true in this level of generality. For a counterexample, consider
`ℚ` acting on `ℝ` by translation, and let `s : Set ℚ := univ`, `t : set ℝ := {0}`. Then `s` is
closed and `t` is compact, but `s +ᵥ t` is the set of all rationals, which is definitely not
closed in `ℝ`. -/

open scoped Pointwise in
/-- If `G` acts properly on `X`, then for each pair of compacts `U, V ⊆ X`,
the set of `g` such that `g • U` intersects `V` is compact.

See `MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty` for the two-way implication
under additional conditions on `G` and `X`. -/
@[to_additive /-- If `G` acts properly on `X`, then for each pair of compacts `U, V ⊆ X`,
the set of `g` such that `g +ᵥ U` intersects `V` is compact.

See `AddAction.properVAdd_iff_isCompact_setOfPred_inter_nonempty` for the two-way implication
under additional conditions on `G` and `X`. -/]
/-
**ProperSMul.isCompact_setOfPred_inter_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ProperSMul.isCompact_setOfPred_inter_nonempty {G : Type*} [Group G] [MulAc
tion G X] [TopologicalSpace G] [ProperSMul G X] {U V : Set X} (hU : IsCompact U)
 (hV : IsCompact V) : IsCompact {g : G | (g • U inter V).Nonempty}
参数：hU : IsCompact U；hV : IsCompact V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.exists_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∃ a, q (e a)) ↔ ∃ b, q b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用引理 `IsProperMap.isCompact_preimage`：IsProperMap.isCompact_preimage (h : IsPr
operMap f) {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
· 使用定理 `ProperSMul.isProperMap_smul_pair`：∀ {G : Type u_1} {X : Type u_2} {inst 
: TopologicalSpace G} {inst_1 : TopologicalSpace X} {inst_2 : Group G}   {inst_3
 : MulAction G X} [sel…
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
lemma ProperSMul.isCompact_setOfPred_inter_nonempty
    {G : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [ProperSMul G X]
    {U V : Set X} (hU : IsCompact U) (hV : IsCompact V) :
    IsCompact {g : G | (g • U ∩ V).Nonempty} := by
  convert!
    ((ProperSMul.isProperMap_smul_pair (G := G)).isCompact_preimage (hV.prod hU)).image
      continuous_fst
  ext g
  suffices (∃ v, v ∈ g • U ∧ v ∈ V) ↔ ∃ u, g • u ∈ V ∧ u ∈ U by simpa
  rw [← (MulAction.toPerm g).exists_congr_right]
  simp [and_comm]

@[deprecated (since := "2026-07-09")]
alias ProperSMul.isCompact_setOf_inter_nonempty := ProperSMul.isCompact_setOfPred_inter_nonempty

@[deprecated (since := "2026-07-09")]
alias ProperVAdd.isCompact_setOf_inter_nonempty := ProperVAdd.isCompact_setOfPred_inter_nonempty

/-- If `G` acts transitively on `X`, and the orbit map of a point in `X` is a proper map, then the
action is proper. -/
@[to_additive]
/-
**MulAction.properSMul_of_proper_orbitMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulAction.properSMul_of_proper_orbitMap [ContinuousSMul G X] [IsTopologica
lGroup G] [MulAction.IsPretransitive G X] {x : X} (hx : IsProperMap fun g : G =>
 g • x) : ProperSMul G X
参数：hx : IsProperMap fun g : G => g • x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Surjective f → Function.S
urjective g → Fun…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用引理 `MulAction.surjective_smul`：surjective_smul (x : α) : Surjective fun c : 
M => c • x
· 使用引理 `isProperMap_of_comp_of_surj`：isProperMap_of_comp_of_surj (hf : Continuou
s f) (hg : Continuous g) (hgf : IsProperMap (g ∘ f)) (f_surj : f.Surjective) : I
sProperMap g
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
· 使用引理 `IsProperMap.prodMap`：IsProperMap.prodMap {g : Z -> W} (hf : IsProperMap 
f) (hg : IsProperMap g) : IsProperMap (Prod.map f g)
· 使用定理 `ProperSMul.isProperMap_smul_pair`：∀ {G : Type u_1} {X : Type u_2} {inst 
: TopologicalSpace G} {inst_1 : TopologicalSpace X} {inst_2 : Group G}   {inst_3
 : MulAction G X} [sel…
· 使用定理 `instProperSMulOfIsTopologicalGroup`：∀ {G : Type u_1} [inst : Group G] [i
nst_1 : TopologicalSpace G] [IsTopologicalGroup G], ProperSMul G G

--- 原说明 ---
If `G` acts transitively on `X`, and the orbit map of a point in `X` is a proper
 map, then the
action is proper.
-/
lemma MulAction.properSMul_of_proper_orbitMap
    [ContinuousSMul G X] [IsTopologicalGroup G] [MulAction.IsPretransitive G X]
    {x : X} (hx : IsProperMap fun g : G ↦ g • x) : ProperSMul G X := by
  constructor
  let f : G × G → G × X := Prod.map id (fun g ↦ g • x)
  have hfsurj : f.Surjective := Function.surjective_id.prodMap (surjective_smul G x)
  refine isProperMap_of_comp_of_surj (by fun_prop) (by fun_prop) ?_ hfsurj
  simpa [Function.comp_def, Prod.map_apply, mul_smul]
    using! (hx.prodMap hx).comp (ProperSMul.isProperMap_smul_pair (G := G))

end

