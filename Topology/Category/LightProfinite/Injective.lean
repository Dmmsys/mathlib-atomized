/-
Copyright (c) 2025 Lenny Taelman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lenny Taelman
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Category.LightProfinite.AsLimit
public import Mathlib.Topology.Category.CompHausLike.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.Order.RelClasses

/-!

# Injectivity of light profinite spaces

This file establishes that non-empty light profinite sets are injective in the
category of profinite sets, and thus also in the category of light profinite sets.
This is used in the proof that the null sequence module is internally projective in light
condensed abelian groups.

## Main results

The main result is `Profinite.injective_of_light`, which provides an instance of
`Injective (lightToProfinite.obj S)` for a non-empty light profinite set `S`. We deduce the
instance `LightProfinite.injective` that every light profinite set is an injective object in the
category `LightProfinite`. The proof uses an inductive extension argument along a presentation of
`S` as sequential limit of finite discrete spaces. The key lemma is
`exists_lift_of_finite_of_mono_of_epi`.

## References

* <https://kskedlaya.org/condensed/sec_profinite_set.html#sec_profinite_set-5>
* <https://www.youtube.com/watch?v=_4G582SIo28&t=3187s>

-/

public section

universe u

open Set Topology CategoryTheory Limits

namespace Profinite

/-- This is the key statement for the inductive proof of injectivity of light profinite spaces.
Given a commutative square
```
X >-f->  Y
|g       |g'
v        v
S -f'->> T
```
where `Y` is profinite, `S` is finite, `f` is injective and `f'` is surjective,
there exists a diagonal map `k : Y → S` making the diagram commute.
-/
/-
**Profinite.exists_lift_of_finite_of_injective_of_surjective** 是 Mathlib 中的一个引理，
位于命名空间 `Profinite`。
形式化陈述：exists_lift_of_finite_of_injective_of_surjective {X Y S T : Type*} [Topolo
gicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
 [TotallyDisconnectedSpace Y] [TopologicalSpace S] [T2Space S] [Finite S] [Topol
ogicalSpace T] [T2Space T] (f : X -> Y) (hf : Continuous f) (f_inj : Function.In
jective f) (f' : S -> T) (f'_surj : Function.Surjective f') (g : X -> S) (hg : C
ontinuous g) (g' : Y -> T) (hg' : Continuous g') (h_comm : g' ∘ f = f' ∘ g) : ex
ists k : Y -> S, (Continuo
参数：f : X -> Y；hf : Continuous f；f_inj : Function.Injective f；f' : S -> T；f'_surj
 : Function.Surjective f'；g : X -> S；hg : Continuous g；g' : Y -> T；hg' : Continu
ous g'；h_comm : g' ∘ f = f' ∘ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用定理 `Continuous.isClosedEmbedding`：Continuous.isClosedEmbedding [CompactSpace
 X] [T2Space Y] {f : X -> Y} (h : Continuous f) (hf : Function.Injective f) : Is
ClosedEmbedding f
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.pairwiseDisjoint_iff`：Set.pairwiseDisjoint_iff : s.PairwiseDisjoint 
f ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> (f i inter f j).Nonempty -> i = 
j
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsClopen.preimage`：IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X
 -> Y} (hf : Continuous f) : IsClopen (f ⁻¹' s)
· 使用定理 `isClopen_discrete`：isClopen_discrete [DiscreteTopology X] (s : Set X) : 
IsClopen s
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `exists_clopen_partition_of_clopen_cover`：exists_clopen_partition_of_clop
en_cover {X I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Totall
yDisconnectedSpace X] [Finite…
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `IsLocallyConstant.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocallyConstant
 f → Continuous f
· 使用定理 `IsLocallyConstant.iff_isOpen_fiber`：iff_isOpen_fiber {f : X -> Y} : IsLo
callyConstant f ↔ forall y, IsOpen (f ⁻¹' {y})
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
This is the key statement for the inductive proof of injectivity of light profin
ite spaces.
Given a commutative square
```
X >-f->  Y
|g       |g'
v        v
S -f'->> T
```
where `Y` is profinite, `S` is finite, `f` is injective and `f'` is surjective,
there exists a diagonal map `k : Y → S` making the diagram commute.
-/
lemma exists_lift_of_finite_of_injective_of_surjective {X Y S T : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    [TopologicalSpace S] [T2Space S] [Finite S]
    [TopologicalSpace T] [T2Space T]
    (f : X → Y) (hf : Continuous f) (f_inj : Function.Injective f)
    (f' : S → T) (f'_surj : Function.Surjective f')
    (g : X → S) (hg : Continuous g) (g' : Y → T) (hg' : Continuous g')
    (h_comm : g' ∘ f = f' ∘ g) : ∃ k : Y → S, (Continuous k) ∧ (f' ∘ k = g') ∧ (k ∘ f = g) := by
  -- `T` is finite because it admits a surjection from a finite set
  have : Finite T := Finite.of_surjective f' f'_surj
  -- define the closed partition `Z` so `Z i` is the image under `f` of the fiber of `g` at `i`
  let Z : S → Set Y := fun i ↦ f '' g ⁻¹' {i}
  have Z_closed (i) : IsClosed (Z i) :=
    (IsClosedEmbedding.isClosed_iff_image_isClosed (Continuous.isClosedEmbedding hf f_inj)).mp
    (IsClosed.preimage hg isClosed_singleton)
  have Z_disj : univ.PairwiseDisjoint Z := by
    rw [Set.pairwiseDisjoint_iff]
    simp only [image_inter_nonempty_iff, Z]
    rintro _ _ _ _ ⟨_, rfl, ⟨_, rfl, hy⟩⟩
    rw [f_inj hy]
  -- define `D i` to be the fiber of `g'` at `f' i`
  let D : S → Set Y := fun i ↦ g' ⁻¹' ({f' i})
  -- each `D i` is clopen
  have D_clopen i : IsClopen (D i) := IsClopen.preimage (isClopen_discrete {f' i}) hg'
  -- each `Z i` is contained in `D i`
  have Z_subset_D i : Z i ⊆ D i := by
    intro z hz
    rw [mem_preimage, mem_singleton_iff]
    obtain ⟨x, _, _⟩ := (mem_image _ _ _).mp hz
    have h_comm' : g' (f x) = f' (g x) := congr_fun h_comm x
    simp_all
  -- obtain a clopen partition `C` of `Y` such that `Z i ⊆ C i ⊆ D i`.
  obtain ⟨C, C_clopen, Z_subset_C, C_subset_D, C_cover_D, C_disj⟩ :=
    exists_clopen_partition_of_clopen_cover Z_closed D_clopen Z_subset_D Z_disj
  have D_cover_univ : univ ⊆ (⋃ i, D i) := by
    intro y _
    simp only [mem_iUnion]
    obtain ⟨s, hs⟩ := f'_surj (g' y)
    grind
  have C_cover_univ : ⋃ i, C i = univ := univ_subset_iff.mp (subset_trans D_cover_univ C_cover_D)
  -- define k to be the unique map sending C i to ψ i
  have h_glue (i j : S) (x : Y) (hxi : x ∈ C i) (hxj : x ∈ C j) : i = j := by
    rw [Set.pairwiseDisjoint_iff] at C_disj
    exact C_disj (by simp) (by simp) ⟨x, by grind⟩
  refine ⟨liftCover C (fun i _ ↦ i) h_glue C_cover_univ, IsLocallyConstant.continuous ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_isOpen_fiber]
    intro s
    convert! (C_clopen s).2
    ext y
    simp [preimage_liftCover]
  · ext y
    -- y is contained in C i for some i
    have hy : y ∈ ⋃ i, C i := by simp [C_cover_univ]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    simpa [liftCover_of_mem hi] using symm (C_subset_D i hi)
  · ext x
    simp [liftCover_of_mem <| Z_subset_C (g x) (by simpa [mem_image] using ⟨x, rfl, rfl⟩)]

/-- A categorically stated version of `exists_lift_of_finite_of_injective_of_surjective` in the
category `Profinite`. -/
/-
**Profinite.exists_lift_of_finite_of_mono_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Prof
inite`。
形式化陈述：exists_lift_of_finite_of_mono_of_epi {X Y S T : Profinite.{u}} [Finite S] 
(f : X ⟶ Y) [Mono f] (f' : S ⟶ T) [Epi f'] (g : X ⟶ S) (g' : Y ⟶ T) (h_comm : f 
≫ g' = g ≫ f') : exists k : Y ⟶ S, (k ≫ f' = g') ∧ (f ≫ k = g)
参数：f : X ⟶ Y；f' : S ⟶ T；g : X ⟶ S；g' : Y ⟶ T；h_comm : f ≫ g' = g ≫ f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Profinite.exists_lift_of_finite_of_injective_of_surjective`：exists_lift_
of_finite_of_injective_of_surjective {X Y S T : Type*} [TopologicalSpace X] [Com
pactSpace X] [TopologicalSpace Y] [CompactSpace …
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CompHausLike.mono_iff_injective`：mono_iff_injective {X Y : CompHausLike.
{u} P} (f : X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `Profinite.epi_iff_surjective`：epi_iff_surjective {X Y : Profinite.{u}} (
f : X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Profinite.instHasPropTotallyDisconnectedSpaceCarrier`：∀ (X : Type u_1) [
inst : TopologicalSpace X] [TotallyDisconnectedSpace X],   CompHausLike.HasProp 
(fun Y => TotallyDisconnectedSpace ↑Y) X
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A categorically stated version of `exists_lift_of_finite_of_injective_of_surject
ive` in the
category `Profinite`.
-/
lemma exists_lift_of_finite_of_mono_of_epi {X Y S T : Profinite.{u}} [Finite S]
    (f : X ⟶ Y) [Mono f] (f' : S ⟶ T) [Epi f']
    (g : X ⟶ S) (g' : Y ⟶ T) (h_comm : f ≫ g' = g ≫ f') :
    ∃ k : Y ⟶ S, (k ≫ f' = g') ∧ (f ≫ k = g) := by
  obtain ⟨k_fun, k_cont, h₁, h₂⟩ := exists_lift_of_finite_of_injective_of_surjective
    f (by fun_prop) ((CompHausLike.mono_iff_injective f).mp inferInstance)
    f' ((epi_iff_surjective f').mp inferInstance)
    g (by fun_prop) g' (by fun_prop) (by simp [← CompHausLike.coe_comp, h_comm])
  exact ⟨CompHausLike.ofHom _ ⟨k_fun, k_cont⟩, by ext; simp [← h₁], by ext; simp [← h₂]⟩

/-- Finite sets are injective objects in `Profinite`. -/
/-
**Profinite.injective_of_finite** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
形式化陈述：injective_of_finite (S : Profinite.{u}) [Nonempty S] [Finite S] : Injectiv
e (S) where factors {X Y} g f _
参数：S : Profinite.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `instDiscreteTopologyPUnit`：DiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `Profinite.instHasPropTotallyDisconnectedSpaceCarrier`：∀ (X : Type u_1) [
inst : TopologicalSpace X] [TotallyDisconnectedSpace X],   CompHausLike.HasProp 
(fun Y => TotallyDisconnectedSpace ↑Y) X
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `TotallySeparatedSpace.of_discrete`：∀ (α : Type u_3) [inst : TopologicalS
pace α] [DiscreteTopology α], TotallySeparatedSpace α
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用引理 `Profinite.exists_lift_of_finite_of_mono_of_epi`：exists_lift_of_finite_of
_mono_of_epi {X Y S T : Profinite.{u}} [Finite S] (f : X ⟶ Y) [Mono f] (f' : S ⟶
 T) [Epi f'] (g : X ⟶ S) (g' : Y ⟶ T…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsRegularEpi`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} [h : CategoryTheory.IsR
egularEpi f],   CategoryTheory.Effe…
· 使用定理 `CategoryTheory.instIsRegularEpiOfIsSplitEpi`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplitEp
i f],   CategoryTheory.IsRegularE…
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g

--- 原说明 ---
Finite sets are injective objects in `Profinite`.
-/
instance injective_of_finite (S : Profinite.{u}) [Nonempty S] [Finite S] :
    Injective (S) where
  factors {X Y} g f _ := by
    have (T : Profinite.{u}) [Nonempty T] : IsSplitEpi (CompHausLike.isTerminalPUnit.from T) :=
      IsSplitEpi.mk' { section_ := CompHausLike.const _ (Nonempty.some inferInstance) }
    obtain ⟨k, _, h2⟩ := exists_lift_of_finite_of_mono_of_epi f
        (CompHausLike.isTerminalPUnit.from S) g (CompHausLike.isTerminalPUnit.from Y)
      (CompHausLike.isTerminalPUnit.hom_ext _ _)
    exact ⟨k, h2⟩

set_option backward.isDefEq.respectTransparency false in
/-- A nonempty light profinite space is injective in `Profinite`. -/
/-
**Profinite.injective_of_light** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
形式化陈述：injective_of_light (S : LightProfinite.{u}) [Nonempty S] : Injective (ligh
tToProfinite.obj S) where factors {X Y} g f h
参数：S : LightProfinite.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LightProfinite.epi_iff_surjective`：epi_iff_surjective {X Y : LightProfin
ite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用引理 `LightProfinite.surjective_transitionMap`：surjective_transitionMap (n : N
at) : Function.Surjective (S.transitionMap n)
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `LightProfinite.proj_comp_transitionMap`：proj_comp_transitionMap (n : Nat
) : S.proj (n + 1) ≫ S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩ = S.proj n
· 使用引理 `Profinite.exists_lift_of_finite_of_mono_of_epi`：exists_lift_of_finite_of
_mono_of_epi {X Y S T : Profinite.{u}} [Finite S] (f : X ⟶ Y) [Mono f] (f' : S ⟶
 T) [Epi f'] (g : X ⟶ S) (g' : Y ⟶ T…
· 使用定理 `LightProfinite.instPreservesEpimorphismsProfiniteLightToProfinite`：light
ToProfinite.PreservesEpimorphisms
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.instCountableCategoryNat`：CategoryTheory.CountableCategor
y ℕ
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasCountableLimitsOfCountabl
eCategory`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] (J : T
ype u_2)   [CategoryTheory.Limits.HasCountableLimits C] [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CompHausLike.toCompHausLike_map`：∀ {P P' : TopCat → Prop} (h : ∀ (X : Co
mpHausLike P), P X.toTop → P' X.toTop) {X Y : CompHausLike P} (f : X ⟶ Y),   (Co
mpHausLike.toCompHaus…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
A nonempty light profinite space is injective in `Profinite`.
-/
instance injective_of_light (S : LightProfinite.{u}) [Nonempty S] :
    Injective (lightToProfinite.obj S) where
  factors {X Y} g f h := by
    -- help the instance inference a bit
    have (n : ℕ) : Finite <| lightToProfinite.obj (S.component n) :=
      inferInstanceAs (Finite (FintypeCat.toLightProfinite.obj _))
    have : Nonempty <| lightToProfinite.obj (S.component 0) :=
      Nonempty.map (S.proj 0) inferInstance
    have (n : ℕ) : Epi (S.transitionMap n) := (LightProfinite.epi_iff_surjective _).mpr
      (S.surjective_transitionMap n)
    -- base step of the induction: find k0 : Y ⟶ S.component 0
    obtain ⟨k0, h_down0⟩ := Injective.factors (g ≫ lightToProfinite.map (S.proj 0)) f
    /- Induction step: `next` produces k n+1 out of k n:
    ```
    X        --f-->  Y
    |g' (n+1)        |k n
    v                v
    S (n+1) --p n-> S n
    ```
    find `k (n+1) : Y ⟶ S' (n+1)` making both diagrams commute. That is:
      - `h_up (n+1) : k (n+1) ≫ p n = k n`
      - `h_down n+1 : f ≫ k (n+1) = g' (n+1)`
    Construction of `k (n+1)` through extension lemma requires as input:
      - `h_comm n : g' (n+1) ≫ p n = f ≫ k n`, which can be obtained from h_down n. -/
    have h_comm (n : ℕ) (k : Y ⟶ lightToProfinite.obj (S.component n)) (h_down :
        f ≫ k = g ≫ lightToProfinite.map (S.proj n)) : f ≫ k =
          g ≫ lightToProfinite.map (S.proj (n + 1)) ≫ lightToProfinite.map (S.transitionMap n) := by
      rw [h_down, ← Functor.map_comp, ← S.proj_comp_transitionMap n]
    have h_step (n : ℕ) (k : Y ⟶ lightToProfinite.obj (S.component n))
        (h_down : f ≫ k = g ≫ lightToProfinite.map (S.proj n)) :
        ∃ k' : Y ⟶ lightToProfinite.obj (S.component (n + 1)), k' ≫
          lightToProfinite.map (S.transitionMap n) = k ∧ f ≫ k' = g ≫
            lightToProfinite.map (S.proj (n + 1)) :=
      exists_lift_of_finite_of_mono_of_epi f (lightToProfinite.map (S.transitionMap n))
        (g ≫ lightToProfinite.map (S.proj (n + 1))) k (h_comm _ _ h_down)
    let lifts (n : ℕ) := { k : Y ⟶ lightToProfinite.obj (S.component n) //
      f ≫ k = g ≫ lightToProfinite.map (S.proj n) }
    let next (n : ℕ) : lifts n → lifts (n + 1) :=
      fun k ↦ ⟨(h_step n k.val k.property).choose, (h_step n k.val k.property).choose_spec.2⟩
    -- now define a sequence of lifts using induction
    let k_seq (n : Nat) : lifts n := Nat.rec ⟨k0, h_down0⟩ next n
    -- `h_up` and `h_down` are the required commutativity properties
    have h_down (n : ℕ) : f ≫ (k_seq n).val = g ≫ lightToProfinite.map (S.proj n) :=
      (k_seq n).prop
    have h_up : ∀ n, (k_seq (n + 1)).val ≫ lightToProfinite.map (S.transitionMap n) = (k_seq n).val
    | 0 => (h_step 0 k0 h_down0).choose_spec.1
    | n + 1 => (h_step (n + 1) (k_seq (n + 1)).val (k_seq (n + 1)).prop).choose_spec.1
    let k_cone : Cone (S.diagram ⋙ lightToProfinite) :=
      { pt := Y, π := NatTrans.ofOpSequence (fun n ↦ (k_seq n).val) (fun n ↦ (h_up n).symm) }
    -- now the induced map `Y ⟶ S = limₙ Sₙ` is the desired map
    refine ⟨(isLimitOfPreserves _ S.asLimit).lift k_cone, ?_⟩
    have hg : g = (isLimitOfPreserves _ S.asLimit).lift (k_cone.extend f) := by
      apply (isLimitOfPreserves _ S.asLimit).uniq (k_cone.extend f)
      intro n
      simp [show k_cone.π.app n = (k_seq n.unop).1 from rfl, h_down]
    rw [hg]
    apply (isLimitOfPreserves _ S.asLimit).uniq (k_cone.extend f)
    intro n
    simp [-Functor.mapCone_pt, -Functor.mapCone_π_app]

end Profinite

/-
**LightProfinite.injective** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LightProfinite.injective (S : LightProfinite.{u}) [Nonempty S] : Injective
 S where factors {X Y} g f _
参数：S : LightProfinite.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Injective.factors`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {J : C} [self : CategoryTheory.Injective J] {X Y : C}   (g
 : X ⟶ J) (f : X ⟶ Y) …
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimi
tsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type
 u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.instCountableCategoryOfFinCategory`：∀ (α : Type u_1) [ins
t : CategoryTheory.SmallCategory α] [CategoryTheory.FinCategory α],   CategoryTh
eory.CountableCategory α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasCountableLimits`：∀ (C : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasCo
untableLimits C],   CategoryTheory.Limits.HasFini…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompHausLike.toCompHausLike_map`：∀ {P P' : TopCat → Prop} (h : ∀ (X : Co
mpHausLike P), P X.toTop → P' X.toTop) {X Y : CompHausLike P} (f : X ⟶ Y),   (Co
mpHausLike.toCompHaus…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
instance LightProfinite.injective (S : LightProfinite.{u}) [Nonempty S] : Injective S where
  factors {X Y} g f _ := by
    obtain ⟨h, _⟩ := Injective.factors (lightToProfinite.map g) (lightToProfinite.map f)
    refine ⟨lightToProfiniteFullyFaithful.preimage h, ?_⟩
    apply lightToProfiniteFullyFaithful.map_injective
    cat_disch
