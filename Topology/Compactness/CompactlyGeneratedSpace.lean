/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Etienne Marion
-/
module

public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Compactly generated topological spaces

This file defines compactly generated topological spaces. A compactly generated space is a space `X`
whose topology is coinduced by continuous maps from compact Hausdorff spaces to `X`. In such a
space, a set `s` is closed (resp. open) if and only if for all compact Hausdorff space `K` and
`f : K → X` continuous, `f ⁻¹' s` is closed (resp. open) in `K`.

We provide two definitions. `UCompactlyGeneratedSpace.{u} X` corresponds to the type class where the
compact Hausdorff spaces are taken in an arbitrary universe `u`, and should therefore always be used
with an explicit universe parameter. It is intended for categorical purposes.

`CompactlyGeneratedSpace X` corresponds to the case where compact Hausdorff spaces are taken in
the same universe as `X`, and is intended for topological purposes.

We prove basic properties and instances, and prove that a `SequentialSpace` is compactly generated,
as well as a Hausdorff `WeaklyLocallyCompactSpace`.

## Main definitions

* `UCompactlyGeneratedSpace.{u} X`: the topology of `X` is coinduced by continuous maps coming from
  compact Hausdorff spaces in universe `u`.
* `CompactlyGeneratedSpace X`: the topology of `X` is coinduced by continuous maps coming from
  compact Hausdorff spaces in the same universe as `X`.

## References

* <https://en.wikipedia.org/wiki/Compactly_generated_space>
* <https://ncatlab.org/nlab/files/StricklandCGHWSpaces.pdf>

## Tags

compactly generated space
-/

@[expose] public section

universe u v w x

open TopologicalSpace Filter Topology Set

section UCompactlyGeneratedSpace

variable {X : Type w} {Y : Type x}

/--
The compactly generated topology on a topological space `X`. This is the finest topology
which makes all maps from compact Hausdorff spaces to `X`, which are continuous for the original
topology, continuous.

Note: this definition should be used with an explicit universe parameter `u` for the size of the
compact Hausdorff spaces mapping to `X`.
-/
@[instance_reducible]
/-
**TopologicalSpace.compactlyGenerated** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopologicalSpace.compactlyGenerated (X : Type w) [TopologicalSpace X] : To
pologicalSpace X
参数：X : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compactly generated topology on a topological space `X`. This is the finest 
topology
which makes all maps from compact Hausdorff spaces to `X`, which are continuous 
for the original
topology, continuous.

Note: this definition should be used with an explicit universe parameter `u` for
 the size of the
compact Hausdorff spaces mapping to `X`.
-/
def TopologicalSpace.compactlyGenerated (X : Type w) [TopologicalSpace X] : TopologicalSpace X :=
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  coinduced f inferInstance
/-
**continuous_from_compactlyGenerated** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_from_compactlyGenerated [TopologicalSpace X] [t : TopologicalSp
ace Y] (f : X -> Y) (h : forall (S : CompHaus.{u}) (g : C(S, X)), Continuous (f 
∘ g)) : Continuous[compactlyGenerated.{u} X, t] f
参数：f : X -> Y；h : forall (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma continuous_from_compactlyGenerated [TopologicalSpace X] [t : TopologicalSpace Y] (f : X → Y)
    (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) :
        Continuous[compactlyGenerated.{u} X, t] f := by
  rw [continuous_coinduced_dom]
  continuity

/--
A topological space `X` is compactly generated if its topology is finer than (and thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps from compact
Hausdorff spaces to `X`.

This version includes an explicit universe parameter `u` which should always be specified. It is
intended for categorical purposes. See `CompactlyGeneratedSpace` for the version without this
parameter, intended for topological purposes.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the compact space universe `u` would default
-- to a universe output parameter. See Note [universe output parameters and typeclass caching].
@[univ_out_params]
/-
**UCompactlyGeneratedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type v) → [t : TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class UCompactlyGeneratedSpace (X : Type v) [t : TopologicalSpace X] : Prop where
  /-- The topology of `X` is finer than the compactly generated topology. -/
  le_compactlyGenerated : t ≤ compactlyGenerated.{u} X
/-
**eq_compactlyGenerated** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_compactlyGenerated [t : TopologicalSpace X] [UCompactlyGeneratedSpace.{
u} X] : t = compactlyGenerated.{u} X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `UCompactlyGeneratedSpace.le_compactlyGenerated`：∀ {X : Type v} {t : Topo
logicalSpace X} [self : UCompactlyGeneratedSpace X], t ≤ TopologicalSpace.compac
tlyGenerated X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
lemma eq_compactlyGenerated [t : TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    t = compactlyGenerated.{u} X := by
  apply le_antisymm
  · exact UCompactlyGeneratedSpace.le_compactlyGenerated
  · simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
      Sigma.forall]
    exact fun S f ↦ f.2
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type v) [t : TopologicalSpace X] [DiscreteTopology X] :
    UCompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    rw [DiscreteTopology.eq_bot (t := t)]
    exact bot_le

/- The unused variable linter flags `[tY : TopologicalSpace Y]`,
but we want to use this as a named argument, so we need to disable the linter. -/
set_option linter.unusedVariables false in
/-- Let `f : X → Y`. Suppose that to prove that `f` is continuous, it suffices to show that
for every compact Hausdorff space `K` and every continuous map `g : K → X`, `f ∘ g` is continuous.
Then `X` is compactly generated. -/
/-
**uCompactlyGeneratedSpace_of_continuous_maps** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uCompactlyGeneratedSpace_of_continuous_maps [t : TopologicalSpace X] (h : 
forall {Y : Type w} [tY : TopologicalSpace Y] (f : X -> Y), (forall (S : CompHau
s.{u}) (g : C(S, X)), Continuous (f ∘ g)) -> Continuous f) : UCompactlyGenerated
Space.{u} X where le_compactlyGenerated
参数：h : forall {Y : Type w} [tY : TopologicalSpace Y] (f : X -> Y), (forall (S : 
CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) -> Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_sigma_iff`：continuous_sigma_iff {f : Sigma σ -> X} : Continuo
us f ↔ forall i, Continuous fun a => f ⟨i, a⟩
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
· 使用定理 `continuous_id_iff_le`：continuous_id_iff_le {t t' : TopologicalSpace α} :
 Continuous[t, t'] id ↔ t <= t'

--- 原说明 ---
Let `f : X → Y`. Suppose that to prove that `f` is continuous, it suffices to sh
ow that
for every compact Hausdorff space `K` and every continuous map `g : K → X`, `f ∘
 g` is continuous.
Then `X` is compactly generated.
-/
lemma uCompactlyGeneratedSpace_of_continuous_maps [t : TopologicalSpace X]
    (h : ∀ {Y : Type w} [tY : TopologicalSpace Y] (f : X → Y),
      (∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) → Continuous f) :
        UCompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    suffices Continuous[t, compactlyGenerated.{u} X] (id : X → X) by
      rwa [← continuous_id_iff_le]
    apply h (tY := compactlyGenerated.{u} X)
    intro S g
    let f : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
    suffices ∀ (i : (T : CompHaus.{u}) × C(T, X)),
      Continuous[inferInstance, compactlyGenerated X] (fun (a : i.fst) ↦ f ⟨i, a⟩) from this ⟨S, g⟩
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng

variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/-- If `X` is compactly generated, to prove that `f : X → Y` is continuous it is enough to show
that for every compact Hausdorff space `K` and every continuous map `g : K → X`,
`f ∘ g` is continuous. -/
/-
**continuous_from_uCompactlyGeneratedSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_from_uCompactlyGeneratedSpace [UCompactlyGeneratedSpace.{u} X] 
(f : X -> Y) (h : forall (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) :
 Continuous f
参数：f : X -> Y；h : forall (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_le_dom`：continuous_le_dom {t₁ t₂ : TopologicalSpace α} {t₃ : 
TopologicalSpace β} (h₁ : t₂ <= t₁) (h₂ : Continuous[t₁, t₃] f) : Continuous[t₂,
 t₃] f
· 使用定理 `UCompactlyGeneratedSpace.le_compactlyGenerated`：∀ {X : Type v} {t : Topo
logicalSpace X} [self : UCompactlyGeneratedSpace X], t ≤ TopologicalSpace.compac
tlyGenerated X
· 使用引理 `continuous_from_compactlyGenerated`：continuous_from_compactlyGenerated [
TopologicalSpace X] [t : TopologicalSpace Y] (f : X -> Y) (h : forall (S : CompH
aus.{u}) (g : C(S, X)), …

--- 原说明 ---
If `X` is compactly generated, to prove that `f : X → Y` is continuous it is eno
ugh to show
that for every compact Hausdorff space `K` and every continuous map `g : K → X`,
`f ∘ g` is continuous.
-/
lemma continuous_from_uCompactlyGeneratedSpace [UCompactlyGeneratedSpace.{u} X] (f : X → Y)
    (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) : Continuous f := by
  apply continuous_le_dom UCompactlyGeneratedSpace.le_compactlyGenerated
  exact continuous_from_compactlyGenerated f h

/-- A topological space `X` is compactly generated if a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
/-
**uCompactlyGeneratedSpace_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uCompactlyGeneratedSpace_of_isClosed (h : forall (s : Set X), (forall (S :
 CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)) -> IsClosed s) : UCompactlyGen
eratedSpace.{u} X
参数：h : forall (s : Set X), (forall (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f
 ⁻¹' s)) -> IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `uCompactlyGeneratedSpace_of_continuous_maps`：uCompactlyGeneratedSpace_of
_continuous_maps [t : TopologicalSpace X] (h : forall {Y : Type w} [tY : Topolog
icalSpace Y] (f : X -> Y), (foral…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)

--- 原说明 ---
A topological space `X` is compactly generated if a set `s` is closed when `f ⁻¹
' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff.
-/
theorem uCompactlyGeneratedSpace_of_isClosed
    (h : ∀ (s : Set X), (∀ (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)) → IsClosed s) :
    UCompactlyGeneratedSpace.{u} X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun _ h' ↦
    continuous_iff_isClosed.2 fun _ hs ↦ h _ fun S g ↦ hs.preimage (h' S g)

/-- A topological space `X` is compactly generated if a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
/-
**uCompactlyGeneratedSpace_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uCompactlyGeneratedSpace_of_isOpen (h : forall (s : Set X), (forall (S : C
ompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)) -> IsOpen s) : UCompactlyGenerated
Space.{u} X
参数：h : forall (s : Set X), (forall (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻
¹' s)) -> IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `uCompactlyGeneratedSpace_of_continuous_maps`：uCompactlyGeneratedSpace_of
_continuous_maps [t : TopologicalSpace X] (h : forall {Y : Type w} [tY : Topolog
icalSpace Y] (f : X -> Y), (foral…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)

--- 原说明 ---
A topological space `X` is compactly generated if a set `s` is open when `f ⁻¹' 
s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff.
-/
theorem uCompactlyGeneratedSpace_of_isOpen
    (h : ∀ (s : Set X), (∀ (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)) → IsOpen s) :
    UCompactlyGeneratedSpace.{u} X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun _ h' ↦
    continuous_def.2 fun _ hs ↦ h _ fun S g ↦ hs.preimage (h' S g)

/-- In a compactly generated space `X`, a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
/-
**UCompactlyGeneratedSpace.isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UCompactlyGeneratedSpace.isClosed [UCompactlyGeneratedSpace.{u} X] {s : Se
t X} (hs : forall (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)) : IsClos
ed s
参数：hs : forall (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_compactlyGenerated`：eq_compactlyGenerated [t : TopologicalSpace X] [U
CompactlyGeneratedSpace.{u} X] : t = compactlyGenerated.{u} X
· 使用定理 `TopologicalSpace.compactlyGenerated.eq_1`：∀ (X : Type w) [inst : Topolog
icalSpace X],   TopologicalSpace.compactlyGenerated X =     TopologicalSpace.coi
nduced       (fun x =>        …
· 使用定理 `isClosed_coinduced`：isClosed_coinduced {t : TopologicalSpace α} {s : Set
 β} {f : α -> β} : IsClosed[t.coinduced f] s ↔ IsClosed (f ⁻¹' s)
· 使用定理 `isClosed_sigma_iff`：isClosed_sigma_iff {s : Set (Sigma σ)} : IsClosed s 
↔ forall i, IsClosed (Sigma.mk i ⁻¹' s)

--- 原说明 ---
In a compactly generated space `X`, a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff.
-/
theorem UCompactlyGeneratedSpace.isClosed [UCompactlyGeneratedSpace.{u} X] {s : Set X}
    (hs : ∀ (S : CompHaus.{u}) (f : C(S, X)), IsClosed (f ⁻¹' s)) : IsClosed s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isClosed_coinduced,
    isClosed_sigma_iff]
  exact fun ⟨S, f⟩ ↦ hs S f

/-- In a compactly generated space `X`, a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
/-
**UCompactlyGeneratedSpace.isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UCompactlyGeneratedSpace.isOpen [UCompactlyGeneratedSpace.{u} X] {s : Set 
X} (hs : forall (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)) : IsOpen s
参数：hs : forall (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_compactlyGenerated`：eq_compactlyGenerated [t : TopologicalSpace X] [U
CompactlyGeneratedSpace.{u} X] : t = compactlyGenerated.{u} X
· 使用定理 `TopologicalSpace.compactlyGenerated.eq_1`：∀ (X : Type w) [inst : Topolog
icalSpace X],   TopologicalSpace.compactlyGenerated X =     TopologicalSpace.coi
nduced       (fun x =>        …
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `isOpen_sigma_iff`：isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ fora
ll i, IsOpen (Sigma.mk i ⁻¹' s)

--- 原说明 ---
In a compactly generated space `X`, a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff.
-/
theorem UCompactlyGeneratedSpace.isOpen [UCompactlyGeneratedSpace.{u} X] {s : Set X}
    (hs : ∀ (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' s)) : IsOpen s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isOpen_coinduced,
    isOpen_sigma_iff]
  exact fun ⟨S, f⟩ ↦ hs S f

/-- If the topology of `X` is coinduced by a continuous function whose domain is
compactly generated, then so is `X`. -/
/-
**uCompactlyGeneratedSpace_of_coinduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uCompactlyGeneratedSpace_of_coinduced [UCompactlyGeneratedSpace.{u} X] {f 
: X -> Y} (hf : Continuous f) (ht : tY = coinduced f tX) : UCompactlyGeneratedSp
ace.{u} Y
参数：hf : Continuous f；ht : tY = coinduced f tX。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uCompactlyGeneratedSpace_of_isClosed`：uCompactlyGeneratedSpace_of_isClos
ed (h : forall (s : Set X), (forall (S : CompHaus.{u}) (f : C(S, X)), IsClosed (
f ⁻¹' s)) -> IsClosed s) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosed_coinduced`：isClosed_coinduced {t : TopologicalSpace α} {s : Set
 β} {f : α -> β} : IsClosed[t.coinduced f] s ↔ IsClosed (f ⁻¹' s)
· 使用定理 `UCompactlyGeneratedSpace.isClosed`：UCompactlyGeneratedSpace.isClosed [UC
ompactlyGeneratedSpace.{u} X] {s : Set X} (hs : forall (S : CompHaus.{u}) (f : C
(S, X)), IsClosed (f ⁻¹…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)

--- 原说明 ---
If the topology of `X` is coinduced by a continuous function whose domain is
compactly generated, then so is `X`.
-/
theorem uCompactlyGeneratedSpace_of_coinduced
    [UCompactlyGeneratedSpace.{u} X] {f : X → Y} (hf : Continuous f) (ht : tY = coinduced f tX) :
    UCompactlyGeneratedSpace.{u} Y := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h ↦ ?_
  rw [ht, isClosed_coinduced]
  exact UCompactlyGeneratedSpace.isClosed fun _ ⟨g, hg⟩ ↦ h _ ⟨_, hf.comp hg⟩

/-- The quotient of a compactly generated space is compactly generated. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of a compactly generated space is compactly generated.
-/
instance {S : Setoid X} [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{u} (Quotient S) :=
  uCompactlyGeneratedSpace_of_coinduced continuous_quotient_mk' rfl

/-- The sum of two compactly generated spaces is compactly generated. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two compactly generated spaces is compactly generated.
-/
instance [UCompactlyGeneratedSpace.{u} X] [UCompactlyGeneratedSpace.{v} Y] :
    UCompactlyGeneratedSpace.{max u v} (X ⊕ Y) := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h ↦ isClosed_sum_iff.2 ⟨?_, ?_⟩
  all_goals
    refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦ ?_
  · let g : ULift.{v} S → X ⊕ Y := Sum.inl ∘ f ∘ ULift.down
    have hg : Continuous g := continuous_inl.comp <| hf.comp continuous_uliftDown
    exact (h (CompHaus.of (ULift.{v} S)) ⟨g, hg⟩).preimage continuous_uliftUp
  · let g : ULift.{u} S → X ⊕ Y := Sum.inr ∘ f ∘ ULift.down
    have hg : Continuous g := continuous_inr.comp <| hf.comp continuous_uliftDown
    exact (h (CompHaus.of (ULift.{u} S)) ⟨g, hg⟩).preimage continuous_uliftUp

/-- The sigma type associated to a family of compactly generated spaces is compactly generated. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sigma type associated to a family of compactly generated spaces is compactly
 generated.
-/
instance {ι : Type v} {X : ι → Type w} [∀ i, TopologicalSpace (X i)]
    [∀ i, UCompactlyGeneratedSpace.{u} (X i)] : UCompactlyGeneratedSpace.{u} (Σ i, X i) :=
  uCompactlyGeneratedSpace_of_isClosed fun _ h ↦ isClosed_sigma_iff.2 fun i ↦
    UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦
      h S ⟨Sigma.mk i ∘ f, continuous_sigmaMk.comp hf⟩

open OnePoint in
/-- A sequential space is compactly generated.

The proof is taken from <https://ncatlab.org/nlab/files/StricklandCGHWSpaces.pdf>,
Proposition 1.6. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequential space is compactly generated.

The proof is taken from <https://ncatlab.org/nlab/files/StricklandCGHWSpaces.pdf
>,
Proposition 1.6.
-/
instance (priority := 100) [SequentialSpace X] : UCompactlyGeneratedSpace.{u} X := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h ↦
    SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦ ?_
  let g : ULift.{u} (OnePoint ℕ) → X := (continuousMapMkNat u p hup) ∘ ULift.down
  change ULift.up ∞ ∈ g ⁻¹' s
  have : Filter.Tendsto (@OnePoint.some ℕ) Filter.atTop (𝓝 ∞) := by
    rw [← Nat.cofinite_eq_atTop, ← cocompact_eq_cofinite, ← coclosedCompact_eq_cocompact]
    exact tendsto_coe_infty
  apply IsClosed.mem_of_tendsto _ ((continuous_uliftUp.tendsto ∞).comp this)
  · simp only [Function.comp_apply, mem_preimage, eventually_atTop]
    exact ⟨0, fun b _ ↦ hu b⟩
  · exact h (CompHaus.of (ULift.{u} (OnePoint ℕ))) ⟨g, by fun_prop⟩

end UCompactlyGeneratedSpace

section CompactlyGeneratedSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/--
A topological space `X` is compactly generated if its topology is finer than (and thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps from compact
Hausdorff spaces to `X`.

In this version, intended for topological purposes, the compact spaces are taken
in the same universe as `X`. See `UCompactlyGeneratedSpace` for a version with an explicit
universe parameter, intended for categorical purposes.
-/
/-
**CompactlyGeneratedSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CompactlyGeneratedSpace (X : Type u) [TopologicalSpace X] : Prop
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space `X` is compactly generated if its topology is finer than (an
d thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps fr
om compact
Hausdorff spaces to `X`.

In this version, intended for topological purposes, the compact spaces are taken
in the same universe as `X`. See `UCompactlyGeneratedSpace` for a version with a
n explicit
universe parameter, intended for categorical purposes.
-/
abbrev CompactlyGeneratedSpace (X : Type u) [TopologicalSpace X] : Prop :=
  UCompactlyGeneratedSpace.{u} X

/-- If `X` is compactly generated, to prove that `f : X → Y` is continuous it is enough to show
that for every compact Hausdorff space `K` and every continuous map `g : K → X`,
`f ∘ g` is continuous. -/
/-
**continuous_from_compactlyGeneratedSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_from_compactlyGeneratedSpace [CompactlyGeneratedSpace X] (f : X
 -> Y) (h : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Spa
ce K] -> (forall g : K -> X, Continuous g -> Continuous (f ∘ g))) : Continuous f
参数：f : X -> Y；h : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> 
[T2Space K] -> (forall g : K -> X, Continuous g -> Continuous (f ∘ g))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `continuous_from_uCompactlyGeneratedSpace`：continuous_from_uCompactlyGene
ratedSpace [UCompactlyGeneratedSpace.{u} X] (f : X -> Y) (h : forall (S : CompHa
us.{u}) (g : C(S, X)), Continu…
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop

--- 原说明 ---
If `X` is compactly generated, to prove that `f : X → Y` is continuous it is eno
ugh to show
that for every compact Hausdorff space `K` and every continuous map `g : K → X`,
`f ∘ g` is continuous.
-/
lemma continuous_from_compactlyGeneratedSpace [CompactlyGeneratedSpace X] (f : X → Y)
    (h : ∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      (∀ g : K → X, Continuous g → Continuous (f ∘ g))) : Continuous f :=
  continuous_from_uCompactlyGeneratedSpace f fun K ⟨g, hg⟩ ↦ h K g hg

/-- Let `f : X → Y`. Suppose that to prove that `f` is continuous, it suffices to show that
for every compact Hausdorff space `K` and every continuous map `g : K → X`, `f ∘ g` is continuous.
Then `X` is compactly generated. -/
/-
**compactlyGeneratedSpace_of_continuous_maps** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：compactlyGeneratedSpace_of_continuous_maps (h : forall {Y : Type u} [Topol
ogicalSpace Y] (f : X -> Y), (forall (K : Type u) [TopologicalSpace K], [Compact
Space K] -> [T2Space K] -> (forall g : K -> X, Continuous g -> Continuous (f ∘ g
))) -> Continuous f) : CompactlyGeneratedSpace X
参数：h : forall {Y : Type u} [TopologicalSpace Y] (f : X -> Y), (forall (K : Type 
u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] -> (forall g : K -> X, 
Continuous g -> Continuous (f ∘ g))) -> Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `uCompactlyGeneratedSpace_of_continuous_maps`：uCompactlyGeneratedSpace_of
_continuous_maps [t : TopologicalSpace X] (h : forall {Y : Type w} [tY : Topolog
icalSpace Y] (f : X -> Y), (foral…

--- 原说明 ---
Let `f : X → Y`. Suppose that to prove that `f` is continuous, it suffices to sh
ow that
for every compact Hausdorff space `K` and every continuous map `g : K → X`, `f ∘
 g` is continuous.
Then `X` is compactly generated.
-/
lemma compactlyGeneratedSpace_of_continuous_maps
    (h : ∀ {Y : Type u} [TopologicalSpace Y] (f : X → Y),
      (∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
        (∀ g : K → X, Continuous g → Continuous (f ∘ g))) → Continuous f) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_continuous_maps fun f h' ↦ h f fun K _ _ _ g hg ↦
    h' (CompHaus.of K) ⟨g, hg⟩

/-- A topological space `X` is compactly generated if a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
/-
**compactlyGeneratedSpace_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactlyGeneratedSpace_of_isClosed (h : forall (s : Set X), (forall (K : 
Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] -> forall (f : K -
> X), Continuous f -> IsClosed (f ⁻¹' s)) -> IsClosed s) : CompactlyGeneratedSpa
ce X
参数：h : forall (s : Set X), (forall (K : Type u) [TopologicalSpace K], [CompactSp
ace K] -> [T2Space K] -> forall (f : K -> X), Continuous f -> IsClosed (f ⁻¹' s)
) -> IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uCompactlyGeneratedSpace_of_isClosed`：uCompactlyGeneratedSpace_of_isClos
ed (h : forall (s : Set X), (forall (S : CompHaus.{u}) (f : C(S, X)), IsClosed (
f ⁻¹' s)) -> IsClosed s) :…

--- 原说明 ---
A topological space `X` is compactly generated if a set `s` is closed when `f ⁻¹
' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff.
-/
theorem compactlyGeneratedSpace_of_isClosed
    (h : ∀ (s : Set X), (∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) → IsClosed s) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_isClosed fun s h' ↦ h s fun K _ _ _ f hf ↦ h' (CompHaus.of K) ⟨f, hf⟩

/-- In a compactly generated space `X`, a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
/-
**CompactlyGeneratedSpace.isClosed'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactlyGeneratedSpace.isClosed' [CompactlyGeneratedSpace X] {s : Set X} 
(hs : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] 
-> forall (f : K -> X), Continuous f -> IsClosed (f ⁻¹' s)) : IsClosed s
参数：hs : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K
] -> forall (f : K -> X), Continuous f -> IsClosed (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UCompactlyGeneratedSpace.isClosed`：UCompactlyGeneratedSpace.isClosed [UC
ompactlyGeneratedSpace.{u} X] {s : Set X} (hs : forall (S : CompHaus.{u}) (f : C
(S, X)), IsClosed (f ⁻¹…
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop

--- 原说明 ---
In a compactly generated space `X`, a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff.
-/
theorem CompactlyGeneratedSpace.isClosed' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) : IsClosed s :=
  UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦ hs S f hf

/-- In a compactly generated space `X`, a set `s` is closed when `s ∩ K` is
closed for every compact set `K`. -/
/-
**CompactlyGeneratedSpace.isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactlyGeneratedSpace.isClosed [CompactlyGeneratedSpace X] {s : Set X} (
hs : forall ⦃K⦄, IsCompact K -> IsClosed (s inter K)) : IsClosed s
参数：hs : forall ⦃K⦄, IsCompact K -> IsClosed (s inter K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlyGeneratedSpace.isClosed'`：CompactlyGeneratedSpace.isClosed' [Co
mpactlyGeneratedSpace X] {s : Set X} (hs : forall (K : Type u) [TopologicalSpace
 K], [CompactSpace K] -…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_inter_range`：preimage_inter_range {f : α -> β} {s : Set β} 
: f ⁻¹' (s inter range f) = f ⁻¹' s
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)

--- 原说明 ---
In a compactly generated space `X`, a set `s` is closed when `s ∩ K` is
closed for every compact set `K`.
-/
theorem CompactlyGeneratedSpace.isClosed [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K)) : IsClosed s := by
  refine isClosed' fun K _ _ _ f hf ↦ ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

/-- A topological space `X` is compactly generated if a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
/-
**compactlyGeneratedSpace_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactlyGeneratedSpace_of_isOpen (h : forall (s : Set X), (forall (K : Ty
pe u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] -> forall (f : K -> 
X), Continuous f -> IsOpen (f ⁻¹' s)) -> IsOpen s) : CompactlyGeneratedSpace X
参数：h : forall (s : Set X), (forall (K : Type u) [TopologicalSpace K], [CompactSp
ace K] -> [T2Space K] -> forall (f : K -> X), Continuous f -> IsOpen (f ⁻¹' s)) 
-> IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uCompactlyGeneratedSpace_of_isOpen`：uCompactlyGeneratedSpace_of_isOpen (
h : forall (s : Set X), (forall (S : CompHaus.{u}) (f : C(S, X)), IsOpen (f ⁻¹' 
s)) -> IsOpen s) : UComp…

--- 原说明 ---
A topological space `X` is compactly generated if a set `s` is open when `f ⁻¹' 
s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff.
-/
theorem compactlyGeneratedSpace_of_isOpen
    (h : ∀ (s : Set X), (∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) → IsOpen s) :
    CompactlyGeneratedSpace X :=
  uCompactlyGeneratedSpace_of_isOpen fun s h' ↦ h s fun K _ _ _ f hf ↦ h' (CompHaus.of K) ⟨f, hf⟩

/-- In a compactly generated space `X`, a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
/-
**CompactlyGeneratedSpace.isOpen'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactlyGeneratedSpace.isOpen' [CompactlyGeneratedSpace X] {s : Set X} (h
s : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K] ->
 forall (f : K -> X), Continuous f -> IsOpen (f ⁻¹' s)) : IsOpen s
参数：hs : forall (K : Type u) [TopologicalSpace K], [CompactSpace K] -> [T2Space K
] -> forall (f : K -> X), Continuous f -> IsOpen (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UCompactlyGeneratedSpace.isOpen`：UCompactlyGeneratedSpace.isOpen [UCompa
ctlyGeneratedSpace.{u} X] {s : Set X} (hs : forall (S : CompHaus.{u}) (f : C(S, 
X)), IsOpen (f ⁻¹' s)…
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop

--- 原说明 ---
In a compactly generated space `X`, a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff.
-/
theorem CompactlyGeneratedSpace.isOpen' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ (K : Type u) [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) : IsOpen s :=
  UCompactlyGeneratedSpace.isOpen fun S ⟨f, hf⟩ ↦ hs S f hf

/-- In a compactly generated space `X`, a set `s` is open when `s ∩ K` is
open for every open set `K`. -/
/-
**CompactlyGeneratedSpace.isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactlyGeneratedSpace.isOpen [CompactlyGeneratedSpace X] {s : Set X} (hs
 : forall ⦃K⦄, IsCompact K -> IsOpen (s inter K)) : IsOpen s
参数：hs : forall ⦃K⦄, IsCompact K -> IsOpen (s inter K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlyGeneratedSpace.isOpen'`：CompactlyGeneratedSpace.isOpen' [Compac
tlyGeneratedSpace X] {s : Set X} (hs : forall (K : Type u) [TopologicalSpace K],
 [CompactSpace K] -> …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_inter_range`：preimage_inter_range {f : α -> β} {s : Set β} 
: f ⁻¹' (s inter range f) = f ⁻¹' s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)

--- 原说明 ---
In a compactly generated space `X`, a set `s` is open when `s ∩ K` is
open for every open set `K`.
-/
theorem CompactlyGeneratedSpace.isOpen [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsOpen (s ∩ K)) : IsOpen s := by
  refine isOpen' fun K _ _ _ f hf ↦ ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

/-- If the topology of `X` is coinduced by a continuous function whose domain is
compactly generated, then so is `X`. -/
/-
**compactlyGeneratedSpace_of_coinduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactlyGeneratedSpace_of_coinduced {X : Type u} [tX : TopologicalSpace X
] {Y : Type u} [tY : TopologicalSpace Y] [CompactlyGeneratedSpace X] {f : X -> Y
} (hf : Continuous f) (ht : tY = coinduced f tX) : CompactlyGeneratedSpace Y
参数：hf : Continuous f；ht : tY = coinduced f tX。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uCompactlyGeneratedSpace_of_coinduced`：uCompactlyGeneratedSpace_of_coind
uced [UCompactlyGeneratedSpace.{u} X] {f : X -> Y} (hf : Continuous f) (ht : tY 
= coinduced f tX) : UCompac…

--- 原说明 ---
If the topology of `X` is coinduced by a continuous function whose domain is
compactly generated, then so is `X`.
-/
theorem compactlyGeneratedSpace_of_coinduced
    {X : Type u} [tX : TopologicalSpace X] {Y : Type u} [tY : TopologicalSpace Y]
    [CompactlyGeneratedSpace X] {f : X → Y} (hf : Continuous f) (ht : tY = coinduced f tX) :
    CompactlyGeneratedSpace Y := uCompactlyGeneratedSpace_of_coinduced hf ht

/-- The sigma type associated to a family of compactly generated spaces is compactly generated. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sigma type associated to a family of compactly generated spaces is compactly
 generated.
-/
instance {ι : Type u} {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactlyGeneratedSpace (X i)] :
    CompactlyGeneratedSpace (Σ i, X i) := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦ isClosed_sigma_iff.2 fun i ↦
    CompactlyGeneratedSpace.isClosed' fun K _ _ _ f hf ↦ ?_
  let g : ULift.{u} K → (Σ i, X i) := Sigma.mk i ∘ f ∘ ULift.down
  have hg : Continuous g := continuous_sigmaMk.comp <| hf.comp continuous_uliftDown
  exact (h _ g hg).preimage continuous_uliftUp

variable [T2Space X]
/-
**CompactlyGeneratedSpace.isClosed_iff_of_t2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactlyGeneratedSpace.isClosed_iff_of_t2 [CompactlyGeneratedSpace X] (s 
: Set X) : IsClosed s ↔ forall ⦃K⦄, IsCompact K -> IsClosed (s inter K) where mp
 hs _ hK
参数：s : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `CompactlyGeneratedSpace.isClosed`：CompactlyGeneratedSpace.isClosed [Comp
actlyGeneratedSpace X] {s : Set X} (hs : forall ⦃K⦄, IsCompact K -> IsClosed (s 
inter K)) : IsClosed s
-/
theorem CompactlyGeneratedSpace.isClosed_iff_of_t2 [CompactlyGeneratedSpace X] (s : Set X) :
    IsClosed s ↔ ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K) where
  mp hs _ hK := hs.inter hK.isClosed
  mpr := CompactlyGeneratedSpace.isClosed

/-- Let `s ⊆ X`. Suppose that `X` is Hausdorff, and that to prove that `s` is closed,
it suffices to show that for every compact set `K ⊆ X`, `s ∩ K` is closed.
Then `X` is compactly generated. -/
/-
**compactlyGeneratedSpace_of_isClosed_of_t2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactlyGeneratedSpace_of_isClosed_of_t2 (h : forall s, (forall (K : Set 
X), IsCompact K -> IsClosed (s inter K)) -> IsClosed s) : CompactlyGeneratedSpac
e X
参数：h : forall s, (forall (K : Set X), IsCompact K -> IsClosed (s inter K)) -> Is
Closed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compactlyGeneratedSpace_of_isClosed`：compactlyGeneratedSpace_of_isClosed
 (h : forall (s : Set X), (forall (K : Type u) [TopologicalSpace K], [CompactSpa
ce K] -> [T2Space K] -> f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `IsClosed.isClosedMap_subtype_val`：IsClosed.isClosedMap_subtype_val {s : 
Set X} (hs : IsClosed s) : IsClosedMap ((↑) : s -> X)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
Let `s ⊆ X`. Suppose that `X` is Hausdorff, and that to prove that `s` is closed
,
it suffices to show that for every compact set `K ⊆ X`, `s ∩ K` is closed.
Then `X` is compactly generated.
-/
theorem compactlyGeneratedSpace_of_isClosed_of_t2
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsClosed (s ∩ K)) → IsClosed s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs ↦ h s fun K hK ↦ ?_
  rw [Set.inter_comm, ← Subtype.image_preimage_coe]
  apply hK.isClosed.isClosedMap_subtype_val
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

open scoped Set.Notation in
/-- Let `s ⊆ X`. Suppose that `X` is Hausdorff, and that to prove that `s` is open,
it suffices to show that for every compact set `K ⊆ X`, `s ∩ K` is open in `K`.
Then `X` is compactly generated. -/
/-
**compactlyGeneratedSpace_of_isOpen_of_t2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactlyGeneratedSpace_of_isOpen_of_t2 (h : forall s, (forall (K : Set X)
, IsCompact K -> IsOpen (K ↓inter s)) -> IsOpen s) : CompactlyGeneratedSpace X
参数：h : forall s, (forall (K : Set X), IsCompact K -> IsOpen (K ↓inter s)) -> IsO
pen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compactlyGeneratedSpace_of_isOpen`：compactlyGeneratedSpace_of_isOpen (h 
: forall (s : Set X), (forall (K : Type u) [TopologicalSpace K], [CompactSpace K
] -> [T2Space K] -> for…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
Let `s ⊆ X`. Suppose that `X` is Hausdorff, and that to prove that `s` is open,
it suffices to show that for every compact set `K ⊆ X`, `s ∩ K` is open in `K`.
Then `X` is compactly generated.
-/
theorem compactlyGeneratedSpace_of_isOpen_of_t2
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsOpen (K ↓∩ s)) → IsOpen s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isOpen fun s hs ↦ h s fun K hK ↦ ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs _ Subtype.val continuous_subtype_val

/-- A Hausdorff and weakly locally compact space is compactly generated. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hausdorff and weakly locally compact space is compactly generated.
-/
instance (priority := 100) [WeaklyLocallyCompactSpace X] :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed_of_t2 fun s h ↦ ?_
  rw [isClosed_iff_forall_filter]
  intro x ℱ hℱ₁ hℱ₂ hℱ₃
  rcases exists_compact_mem_nhds x with ⟨K, hK, K_mem⟩
  exact Set.mem_of_mem_inter_left <| isClosed_iff_forall_filter.1 (h _ hK) x ℱ hℱ₁
    (Filter.inf_principal ▸ le_inf hℱ₂ (le_trans hℱ₃ <| Filter.le_principal_iff.2 K_mem)) hℱ₃

/-- Every compactly generated space is a compactly coherent space. -/
/-
**to_compactlyCoherentSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：to_compactlyCoherentSpace [CompactlyGeneratedSpace X] : CompactlyCoherentS
pace X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CompactlyCoherentSpace.of_isOpen_forall_compactSpace`：of_isOpen_forall_c
ompactSpace (h : forall (s : Set X), (forall (K : Type u) [TopologicalSpace K], 
[CompactSpace K] -> forall (f : K -> X), C…
· 使用定理 `CompactlyGeneratedSpace.isOpen'`：CompactlyGeneratedSpace.isOpen' [Compac
tlyGeneratedSpace X] {s : Set X} (hs : forall (K : Type u) [TopologicalSpace K],
 [CompactSpace K] -> …

--- 原说明 ---
Every compactly generated space is a compactly coherent space.
-/
instance to_compactlyCoherentSpace [CompactlyGeneratedSpace X] : CompactlyCoherentSpace X :=
  CompactlyCoherentSpace.of_isOpen_forall_compactSpace fun _ h ↦ CompactlyGeneratedSpace.isOpen'
    fun K _ _ _ f hf ↦ h K f hf

/-- A compactly coherent space that is Hausdorff is compactly generated. -/
/-
**of_compactlyCoherentSpace_of_t2** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：of_compactlyCoherentSpace_of_t2 [CompactlyCoherentSpace X] : CompactlyGene
ratedSpace X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `compactlyGeneratedSpace_of_isClosed_of_t2`：compactlyGeneratedSpace_of_is
Closed_of_t2 (h : forall s, (forall (K : Set X), IsCompact K -> IsClosed (s inte
r K)) -> IsClosed s) : Compactl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CompactlyCoherentSpace.isClosed_iff`：isClosed_iff [CompactlyCoherentSpac
e X] (A : Set X) : IsClosed A ↔ forall K, IsCompact K -> IsClosed (K ↓inter A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.preimage_coe_inter_self`：preimage_coe_inter_self (s t : Set α) :
 ((↑) : s -> α) ⁻¹' (t inter s) = ((↑) : s -> α) ⁻¹' t
· 使用引理 `IsClosed.preimage_val`：IsClosed.preimage_val {s t : Set X} (ht : IsClose
d t) : IsClosed (s ↓inter t)

--- 原说明 ---
A compactly coherent space that is Hausdorff is compactly generated.
-/
instance of_compactlyCoherentSpace_of_t2 [CompactlyCoherentSpace X] :
    CompactlyGeneratedSpace X := by
  apply compactlyGeneratedSpace_of_isClosed_of_t2
  intro s hs
  rw [CompactlyCoherentSpace.isClosed_iff]
  intro K hK
  rw [← Subtype.preimage_coe_inter_self]
  exact (hs K hK).preimage_val

end CompactlyGeneratedSpace

