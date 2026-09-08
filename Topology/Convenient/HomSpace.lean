/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Convenient.ContinuousMapGeneratedBy

/-!
# The topological space of `X`-continuous maps

Let `X i` be a family of topological spaces. Let `Z` and `T` be topological spaces.
In this file, we endow the type `ContinuousMapGeneratedBy X Z T` of
`X`-continuous maps `Z → T` with the coarsest topology which makes
the precomposition maps `ContinuousMapGeneratedBy X Z T → C(X i, T)`
continuous for any continuous map `X i → Z`, where `C(X i, T)`
is endowed with the compact-open topology.

If we assume that the spaces `X i` are locally compact and that the products
`X i × X j` are `X`-generated, we obtain that the curryfication of maps induces
a bijection between the type of `X`-continuous maps `Y × Z → T` and the type of
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T` for all
topological spaces `Y`, `Z` and `T`.

## References
* [Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed
  categories of (core) compactly generated spaces*][escardo-lawson-simpson-2004]

-/
universe v v' v'' t u

@[expose] public section

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]
  {T : Type v''} [TopologicalSpace T]

namespace Topology.ContinuousMapGeneratedBy

/-- Given a continuous map `f : X i → Z`, this is the map
`ContinuousMapGeneratedBy X Z T → C(X i, T)` given by the precomposition with `f`.
This is used in order to define a topology on `ContinuousMapGeneratedBy X Z T`. -/
/-
**Topology.ContinuousMapGeneratedBy.precomp** 是 Mathlib 中的一个定义，位于命名空间 `Topology.
ContinuousMapGeneratedBy`。
形式化陈述：precomp {i : ι} (f : C(X i, Z)) : ContinuousMapGeneratedBy X Z T -> C(X i,
 T)
参数：f : C(X i, Z)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.ContinuousMapGeneratedBy.prop`：∀ {ι : Type t} {X : ι → Type u} 
[inst : (i : ι) → TopologicalSpace (X i)] {Y : Type v} [inst_1 : TopologicalSpac
e Y]   {Z : Type v'} [inst_2…

--- 原说明 ---
Given a continuous map `f : X i → Z`, this is the map
`ContinuousMapGeneratedBy X Z T → C(X i, T)` given by the precomposition with `f
`.
This is used in order to define a topology on `ContinuousMapGeneratedBy X Z T`.
-/
def precomp {i : ι} (f : C(X i, Z)) : ContinuousMapGeneratedBy X Z T → C(X i, T) :=
  fun g ↦ ⟨_, g.prop f⟩

@[simp]
/-
**Topology.ContinuousMapGeneratedBy.precomp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Top
ology.ContinuousMapGeneratedBy`。
形式化陈述：precomp_apply {i : ι} (f : C(X i, Z)) (g : ContinuousMapGeneratedBy X Z T)
 : ⇑(precomp f g) = g ∘ f
参数：f : C(X i, Z)；g : ContinuousMapGeneratedBy X Z T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma precomp_apply {i : ι} (f : C(X i, Z)) (g : ContinuousMapGeneratedBy X Z T) :
    ⇑(precomp f g) = g ∘ f := rfl
/-
**Topology.ContinuousMapGeneratedBy.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.Continu
ousMapGeneratedBy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (ContinuousMapGeneratedBy X Z T) :=
  ⨅ (i : ι) (f : C(X i, Z)), .induced (precomp f) inferInstance
/-
**Topology.ContinuousMapGeneratedBy.continuous_iff** 是 Mathlib 中的一个引理，位于命名空间 `To
pology.ContinuousMapGeneratedBy`。
形式化陈述：continuous_iff {A : Type*} [TopologicalSpace A] {φ : A -> ContinuousMapGen
eratedBy X Z T} : Continuous φ ↔ forall (i : ι) (f : C(X i, Z)), Continuous (pre
comp f ∘ φ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuous_iff {A : Type*} [TopologicalSpace A] {φ : A → ContinuousMapGeneratedBy X Z T} :
    Continuous φ ↔ ∀ (i : ι) (f : C(X i, Z)), Continuous (precomp f ∘ φ) := by
  simp only [continuous_iInf_rng, continuous_induced_rng]

@[continuity, fun_prop]
/-
**Topology.ContinuousMapGeneratedBy.continuous_precomp** 是 Mathlib 中的一个引理，位于命名空间
 `Topology.ContinuousMapGeneratedBy`。
形式化陈述：continuous_precomp {i : ι} (f : C(X i, Z)) : Continuous (precomp (T
参数：f : C(X i, Z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma continuous_precomp {i : ι} (f : C(X i, Z)) : Continuous (precomp (T := T) f) := by
  rw [continuous_iff_le_induced]
  exact (iInf_le _ i).trans (iInf_le _ _)
/-
**Topology.ContinuousMapGeneratedBy.continuousGeneratedBy_iff_uncurry** 是 Mathli
b 中的一个引理，位于命名空间 `Topology.ContinuousMapGeneratedBy`。
形式化陈述：continuousGeneratedBy_iff_uncurry [forall i, LocallyCompactSpace (X i)] (g
 : Z -> ContinuousMapGeneratedBy X Y T) : ContinuousGeneratedBy X g ↔ forall ⦃i₁
 : ι⦄ (f₁ : C(X i₁, Z)) ⦃i₂ : ι⦄ (f₂ : C(X i₂, Y)) , Continuous (fun (x₁, x₂) =>
 g (f₁ x₁) (f₂ x₂))
参数：X i；g : Z -> ContinuousMapGeneratedBy X Y T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `ContinuousMap.continuous_uncurry_of_continuous`：continuous_uncurry_of_co
ntinuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : Continuous (Function.uncu
rry fun x y => f x y)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
lemma continuousGeneratedBy_iff_uncurry [∀ i, LocallyCompactSpace (X i)]
    (g : Z → ContinuousMapGeneratedBy X Y T) :
    ContinuousGeneratedBy X g ↔
      ∀ ⦃i₁ : ι⦄ (f₁ : C(X i₁, Z)) ⦃i₂ : ι⦄ (f₂ : C(X i₂, Y)) ,
        Continuous (fun (x₁, x₂) ↦ g (f₁ x₁) (f₂ x₂)) := by
  simp only [continuousGeneratedBy_def, continuous_iff]
  exact forall_congr' (fun i₁ ↦ forall_congr' (fun f₁ ↦
    forall_congr' (fun i₂ ↦ forall_congr' (fun f₂ ↦
      ⟨fun h ↦ ContinuousMap.continuous_uncurry_of_continuous ⟨_, h⟩,
        fun h ↦ (ContinuousMap.curry ⟨_, h⟩).continuous⟩))))
/-
**Topology.ContinuousMapGeneratedBy.continuousGeneratedBy_dom_prod_iff** 是 Mathl
ib 中的一个引理，位于命名空间 `Topology.ContinuousMapGeneratedBy`。
形式化陈述：continuousGeneratedBy_dom_prod_iff [forall i j, IsGeneratedBy X (X i × X j
)] (g : Y × Z -> T) : ContinuousGeneratedBy X g ↔ forall (i₁ : ι) (f₁ : C(X i₁, 
Z)) (i₂ : ι) (f₂ : C(X i₂, Y)), Continuous (fun (x₁, x₂) => g ⟨f₂ x₂, f₁ x₁⟩)
参数：X i × X j；g : Y × Z -> T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsGeneratedBy.continuous_iff`：continuous_iff (g : Y -> Z) : Con
tinuous g ↔ forall ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)
· 使用定理 `Topology.ContinuousGeneratedBy.comp`：∀ {ι : Type t} {X : ι → Type u} [in
st : (i : ι) → TopologicalSpace (X i)] {Y : Type v} [inst_1 : TopologicalSpace Y
]   {Z : Type v'} [inst_2…
· 使用引理 `Continuous.continuousGeneratedBy`：Continuous.continuousGeneratedBy {g : 
Y -> Z} (hg : Continuous g) : ContinuousGeneratedBy X g
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用引理 `Topology.continuousGeneratedBy_def`：continuousGeneratedBy_def (g : Y -> 
Z) : ContinuousGeneratedBy X g ↔ forall ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘
 f)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
lemma continuousGeneratedBy_dom_prod_iff [∀ i j, IsGeneratedBy X (X i × X j)]
    (g : Y × Z → T) :
    ContinuousGeneratedBy X g ↔
      ∀ (i₁ : ι) (f₁ : C(X i₁, Z)) (i₂ : ι) (f₂ : C(X i₂, Y)),
        Continuous (fun (x₁, x₂) ↦ g ⟨f₂ x₂, f₁ x₁⟩) := by
  refine ⟨fun h i₁ f₁ i₂ f₂ ↦ ?_, fun h ↦ ?_⟩
  · rw [IsGeneratedBy.continuous_iff X]
    intro j p
    let φ : X i₁ × X i₂ → Y × Z := fun (x₁, x₂) ↦ (f₂ x₂, f₁ x₁)
    replace h := h.comp (show Continuous φ by fun_prop).continuousGeneratedBy
    rw [continuousGeneratedBy_def] at h
    exact h p
  · rw [continuousGeneratedBy_def]
    intro i f
    exact (h i (ContinuousMap.snd.comp f) i (ContinuousMap.fst.comp f)).comp
      (Continuous.prodMk continuous_id continuous_id)

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- The bijection between the type of `X`-continuous maps `Y × Z → T` and the type of
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T`. -/
/-
**Topology.ContinuousMapGeneratedBy.curryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Topolo
gy.ContinuousMapGeneratedBy`。
形式化陈述：curryEquiv : ContinuousMapGeneratedBy X (Y × Z) T ≃ ContinuousMapGenerated
By X Z (ContinuousMapGeneratedBy X Y T) where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between the type of `X`-continuous maps `Y × Z → T` and the type o
f
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T`.
-/
def curryEquiv :
  ContinuousMapGeneratedBy X (Y × Z) T ≃
    ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T) where
  toFun g :=
    { toFun z := g.comp ⟨fun y ↦ (y, z), (Continuous.prodMk_left z).continuousGeneratedBy⟩
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using! g.prop }
  invFun g :=
    { toFun x := g x.2 x.1
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using! g.prop }

@[simp]
/-
**Topology.ContinuousMapGeneratedBy.curryEquiv_apply_apply** 是 Mathlib 中的一个引理，位于
命名空间 `Topology.ContinuousMapGeneratedBy`。
形式化陈述：curryEquiv_apply_apply (g : ContinuousMapGeneratedBy X (Y × Z) T) (y : Y) 
(z : Z) : curryEquiv g z y = g (y, z)
参数：g : ContinuousMapGeneratedBy X (Y × Z) T；y : Y；z : Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma curryEquiv_apply_apply (g : ContinuousMapGeneratedBy X (Y × Z) T) (y : Y) (z : Z) :
    curryEquiv g z y = g (y, z) := rfl

@[simp]
/-
**Topology.ContinuousMapGeneratedBy.curryEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命
名空间 `Topology.ContinuousMapGeneratedBy`。
形式化陈述：curryEquiv_symm_apply (g : ContinuousMapGeneratedBy X Z (ContinuousMapGene
ratedBy X Y T)) (y : Y) (z : Z) : curryEquiv.symm g (y, z) = g z y
参数：g : ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T)；y : Y；z : Z
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma curryEquiv_symm_apply (g : ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T))
    (y : Y) (z : Z) :
    curryEquiv.symm g (y, z) = g z y := rfl

/-- The evaluation `Y × ContinuousMapGeneratedBy X Y Z → Z` as a `X`-continuous map. -/
/-
**Topology.ContinuousMapGeneratedBy.ev** 是 Mathlib 中的一个定义，位于命名空间 `Topology.Conti
nuousMapGeneratedBy`。
形式化陈述：ev : ContinuousMapGeneratedBy X (Y × ContinuousMapGeneratedBy X Y Z) Z
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The evaluation `Y × ContinuousMapGeneratedBy X Y Z → Z` as a `X`-continuous map.
-/
def ev : ContinuousMapGeneratedBy X (Y × ContinuousMapGeneratedBy X Y Z) Z :=
  curryEquiv.symm .id

@[simp]
/-
**Topology.ContinuousMapGeneratedBy.ev_apply** 是 Mathlib 中的一个引理，位于命名空间 `Topology
.ContinuousMapGeneratedBy`。
形式化陈述：ev_apply (y : Y) (f : ContinuousMapGeneratedBy X Y Z) : ev (y, f) = f y
参数：y : Y；f : ContinuousMapGeneratedBy X Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ev_apply (y : Y) (f : ContinuousMapGeneratedBy X Y Z) :
    ev (y, f) = f y := rfl

/-- Given a `X`-continuous map `p : Z → T`, this is the postcomposition with `p`
`ContinuousMapGeneratedBy X Y Z → ContinuousMapGeneratedBy X Y T`
as a `X`-continuous map. -/
/-
**Topology.ContinuousMapGeneratedBy.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `Topology
.ContinuousMapGeneratedBy`。
形式化陈述：postcomp (p : ContinuousMapGeneratedBy X Z T) : ContinuousMapGeneratedBy X
 (ContinuousMapGeneratedBy X Y Z) (ContinuousMapGeneratedBy X Y T)
参数：p : ContinuousMapGeneratedBy X Z T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `X`-continuous map `p : Z → T`, this is the postcomposition with `p`
`ContinuousMapGeneratedBy X Y Z → ContinuousMapGeneratedBy X Y T`
as a `X`-continuous map.
-/
def postcomp (p : ContinuousMapGeneratedBy X Z T) :
    ContinuousMapGeneratedBy X (ContinuousMapGeneratedBy X Y Z)
      (ContinuousMapGeneratedBy X Y T) :=
  curryEquiv (p.comp ev)

@[simp]
/-
**Topology.ContinuousMapGeneratedBy.postcomp_apply** 是 Mathlib 中的一个引理，位于命名空间 `To
pology.ContinuousMapGeneratedBy`。
形式化陈述：postcomp_apply (p : ContinuousMapGeneratedBy X Z T) (g : ContinuousMapGene
ratedBy X Y Z) : p.postcomp g = p.comp g
参数：p : ContinuousMapGeneratedBy X Z T；g : ContinuousMapGeneratedBy X Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma postcomp_apply (p : ContinuousMapGeneratedBy X Z T) (g : ContinuousMapGeneratedBy X Y Z) :
    p.postcomp g = p.comp g := rfl

end Topology.ContinuousMapGeneratedBy

