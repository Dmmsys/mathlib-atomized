/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.UniformRing

/-! # Evaluation of multivariate power series

Let `σ`, `R`, `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `IsTopologicalRing R` and `IsUniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `IsLinearTopology S S`, which means there is a basis of neighborhoods of 0
consisting of ideals.

Given `φ : R →+* S`, `a : σ → S`, and `f : MvPowerSeries σ R`,
`MvPowerSeries.eval₂ f φ a` is the evaluation of the multivariate power series `f` at `a`.
If `f` is (the coercion of) a polynomial, it coincides with the evaluation of that polynomial.
Otherwise, it is defined by density from polynomials;
its values are irrelevant unless `φ` is continuous and `a` satisfies two conditions
bundled in `MvPowerSeries.HasEval a` :
  - for all `s : σ`, `a s` is topologically nilpotent,
    meaning that `(a s) ^ n` tends to 0 when `n` tends to infinity
  - when `a s` tends to zero for the filter of cofinite subsets of `σ`.

Under `Continuous φ` and `HasEval a`, the following lemmas furnish the properties of evaluation:

* `MvPowerSeries.eval₂Hom`: the evaluation of multivariate power series, as a ring morphism,
* `MvPowerSeries.aeval`: the evaluation map as an algebra morphism
* `MvPowerSeries.uniformContinuous_eval₂`: uniform continuity of the evaluation
* `MvPowerSeries.continuous_eval₂`: continuity of the evaluation
* `MvPowerSeries.eval₂_eq_tsum`: the evaluation is given by the sum of its monomials, evaluated.

-/

@[expose] public section

namespace MvPowerSeries

open Topology

open Filter MvPolynomial RingHom Set TopologicalSpace UniformSpace

/- ## Necessary conditions -/

section

variable {σ : Type*}
variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable {S : Type*} [CommRing S] [TopologicalSpace S]
variable {φ : R →+* S}

-- We endow MvPowerSeries σ R with the Pi topology
open WithPiTopology

/-- Families at which power series can be consistently evaluated -/
@[mk_iff hasEval_def]
/-
**MvPowerSeries.HasEval** 是 Mathlib 中的一个归纳类型，位于命名空间 `MvPowerSeries`。
形式化陈述：{σ : Type u_1} → {S : Type u_3} → [CommRing S] → [TopologicalSpace S] → (σ
 → S) → Prop
参数：σ → S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Families at which power series can be consistently evaluated
-/
structure HasEval (a : σ → S) : Prop where
  hpow : ∀ s, IsTopologicallyNilpotent (a s)
  tendsto_zero : Tendsto a cofinite (𝓝 0)
/-
**MvPowerSeries.HasEval.mono** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasEval`。
形式化陈述：∀ {σ : Type u_1} {S : Type u_4} [inst : CommRing S] {a : σ → S} {t u : Top
ologicalSpace S},   t ≤ u → MvPowerSeries.HasEval a → MvPowerSeries.HasEval a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `MvPowerSeries.HasEval.hpow`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEval a → ∀
 (s : σ), IsTopo…
· 使用定理 `nhds_mono`：nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂)
 : @nhds α t₁ a <= @nhds α t₂ a
· 使用定理 `MvPowerSeries.HasEval.tendsto_zero`：∀ {σ : Type u_1} {S : Type u_3} [ins
t : CommRing S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEv
al a → Filter.Tendsto a …
-/
theorem HasEval.mono {S : Type*} [CommRing S] {a : σ → S}
    {t u : TopologicalSpace S} (h : t ≤ u) (ha : @HasEval _ _ _ t a) :
    @HasEval _ _ _ u a :=
  ⟨fun s ↦ Filter.Tendsto.mono_right (@HasEval.hpow _ _ _ t a ha s) (nhds_mono h),
   Filter.Tendsto.mono_right (@HasEval.tendsto_zero σ _ _ t a ha) (nhds_mono h)⟩
/-
**MvPowerSeries.HasEval.zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasEval`。
形式化陈述：∀ {σ : Type u_1} {S : Type u_3} [inst : CommRing S] [inst_1 : TopologicalS
pace S], MvPowerSeries.HasEval 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicallyNilpotent.zero`：zero : IsTopologicallyNilpotent (0 : R)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem HasEval.zero : HasEval (0 : σ → S) where
  hpow _ := .zero
  tendsto_zero := tendsto_const_nhds
/-
**MvPowerSeries.HasEval.add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasEval`。
形式化陈述：∀ {σ : Type u_1} {S : Type u_3} [inst : CommRing S] [inst_1 : TopologicalS
pace S] [ContinuousAdd S]   [IsLinearTopology S S] {a b : σ → S},   MvPowerSerie
s.HasEval a → MvPowerSeries.HasEval b → MvPowerSeries.HasEval (a + b)
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicallyNilpotent.add`：add {a b : R} (ha : IsTopologicallyNilpote
nt a) (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a + b)
· 使用定理 `MvPowerSeries.HasEval.hpow`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEval a → ∀
 (s : σ), IsTopo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `MvPowerSeries.HasEval.tendsto_zero`：∀ {σ : Type u_1} {S : Type u_3} [ins
t : CommRing S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEv
al a → Filter.Tendsto a …
-/
theorem HasEval.add [ContinuousAdd S] [IsLinearTopology S S]
    {a b : σ → S} (ha : HasEval a) (hb : HasEval b) : HasEval (a + b) where
  hpow s := (ha.hpow s).add (hb.hpow s)
  tendsto_zero := by rw [← add_zero 0]; exact ha.tendsto_zero.add hb.tendsto_zero
/-
**MvPowerSeries.HasEval.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasEva
l`。
形式化陈述：∀ {σ : Type u_1} {S : Type u_3} [inst : CommRing S] [inst_1 : TopologicalS
pace S] [IsLinearTopology S S] (c : σ → S)   {x : σ → S}, MvPowerSeries.HasEval 
x → MvPowerSeries.HasEval (c * x)
参数：c : σ → S；c * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicallyNilpotent.mul_left`：mul_left (a : R) {b : R} (hb : IsTopo
logicallyNilpotent b) : IsTopologicallyNilpotent (a * b)
· 使用定理 `MvPowerSeries.HasEval.hpow`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEval a → ∀
 (s : σ), IsTopo…
· 使用定理 `IsLinearTopology.tendsto_mul_zero_of_right`：tendsto_mul_zero_of_right [I
sLinearTopology R R] {ι : Type*} {f : Filter ι} (a b : ι -> R) (hb : Tendsto b f
 (𝓝 0)) : Tendsto (a * b) f (𝓝 0…
· 使用定理 `MvPowerSeries.HasEval.tendsto_zero`：∀ {σ : Type u_1} {S : Type u_3} [ins
t : CommRing S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEv
al a → Filter.Tendsto a …
-/
theorem HasEval.mul_left [IsLinearTopology S S]
    (c : σ → S) {x : σ → S} (hx : HasEval x) : HasEval (c * x) where
  hpow s := (hx.hpow s).mul_left (c s)
  tendsto_zero := IsLinearTopology.tendsto_mul_zero_of_right _ _ hx.tendsto_zero
/-
**MvPowerSeries.HasEval.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasEv
al`。
形式化陈述：∀ {σ : Type u_1} {S : Type u_3} [inst : CommRing S] [inst_1 : TopologicalS
pace S] [IsLinearTopology S S] (c : σ → S)   {x : σ → S}, MvPowerSeries.HasEval 
x → MvPowerSeries.HasEval (x * c)
参数：c : σ → S；x * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasEval.mul_left`：∀ {σ : Type u_1} {S : Type u_3} [inst : 
CommRing S] [inst_1 : TopologicalSpace S] [IsLinearTopology S S] (c : σ → S)   {
x : σ → S}, MvPowerS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem HasEval.mul_right [IsLinearTopology S S]
    (c : σ → S) {x : σ → S} (hx : HasEval x) : HasEval (x * c) :=
  mul_comm x c ▸ HasEval.mul_left c hx

/-- [Bourbaki, *Algebra*, chap. 4, §4, n°3, Prop. 4 (i) (a & b)][bourbaki1981]. -/
/-
**MvPowerSeries.HasEval.map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasEval`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] [inst_1 : TopologicalS
pace R] {S : Type u_3} [inst_2 : CommRing S]   [inst_3 : TopologicalSpace S] {φ 
: R →+* S},   Continuous ⇑φ → ∀ {a : σ → R}, MvPowerSeries.HasEval a → MvPowerSe
ries.HasEval fun s => φ (a s)
参数：a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicallyNilpotent.map`：map {F : Type*} [FunLike F R S] [MonoidWit
hZeroHomClass F R S] {φ : F} (hφ : Continuous φ) {a : R} (ha : IsTopologicallyNi
lpotent a) : IsTop…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.HasEval.hpow`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEval a → ∀
 (s : σ), IsTopo…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MvPowerSeries.HasEval.tendsto_zero`：∀ {σ : Type u_1} {S : Type u_3} [ins
t : CommRing S] [inst_1 : TopologicalSpace S] {a : σ → S},   MvPowerSeries.HasEv
al a → Filter.Tendsto a …

--- 原说明 ---
[Bourbaki, *Algebra*, chap. 4, §4, n°3, Prop. 4 (i) (a & b)][bourbaki1981].
-/
theorem HasEval.map (hφ : Continuous φ) {a : σ → R} (ha : HasEval a) :
    HasEval (fun s ↦ φ (a s)) where
  hpow s := (ha.hpow s).map hφ
  tendsto_zero := (map_zero φ ▸ hφ.tendsto 0).comp ha.tendsto_zero
/-
**MvPowerSeries.HasEval.X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasEval`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] [inst_1 : TopologicalS
pace R],   MvPowerSeries.HasEval fun s => MvPowerSeries.X s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_z
ero`：isTopologicallyNilpotent_of_constantCoeff_zero [CommSemiring R] {f : MvPowe
rSeries σ R} (hf : constantCoeff f = 0) : Tendsto (fun n : Nat =>…
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `MvPowerSeries.WithPiTopology.variables_tendsto_zero`：variables_tendsto_z
ero [Semiring R] : Tendsto (X · : σ -> MvPowerSeries σ R) cofinite (nhds 0)
-/
protected theorem HasEval.X :
    HasEval (fun s ↦ (MvPowerSeries.X s : MvPowerSeries σ R)) where
  hpow s := isTopologicallyNilpotent_of_constantCoeff_zero (constantCoeff_X s)
  tendsto_zero := variables_tendsto_zero

variable [IsTopologicalRing S] [IsLinearTopology S S]

/-- The domain of evaluation of `MvPowerSeries`, as an ideal -/
@[simps]
/-
**MvPowerSeries.hasEvalIdeal** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：hasEvalIdeal : Ideal (σ -> S) where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasEval.zero`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S], MvPowerSeries.HasEval 0
· 使用定理 `MvPowerSeries.HasEval.mul_left`：∀ {σ : Type u_1} {S : Type u_3} [inst : 
CommRing S] [inst_1 : TopologicalSpace S] [IsLinearTopology S S] (c : σ → S)   {
x : σ → S}, MvPowerS…

--- 原说明 ---
The domain of evaluation of `MvPowerSeries`, as an ideal
-/
def hasEvalIdeal : Ideal (σ → S) where
  carrier := {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

set_option backward.isDefEq.respectTransparency false in
/-
**MvPowerSeries.mem_hasEvalIdeal_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：mem_hasEvalIdeal_iff {a : σ -> S} : a in hasEvalIdeal ↔ HasEval a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.HasEval.zero`：∀ {σ : Type u_1} {S : Type u_3} [inst : Comm
Ring S] [inst_1 : TopologicalSpace S], MvPowerSeries.HasEval 0
· 使用定理 `MvPowerSeries.HasEval.mul_left`：∀ {σ : Type u_1} {S : Type u_3} [inst : 
CommRing S] [inst_1 : TopologicalSpace S] [IsLinearTopology S S] (c : σ → S)   {
x : σ → S}, MvPowerS…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_hasEvalIdeal_iff {a : σ → S} :
    a ∈ hasEvalIdeal ↔ HasEval a := by
  simp [hasEvalIdeal]
/-
**MvPowerSeries.HasEval.pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasEval`。
形式化陈述：∀ {σ : Type u_1} {S : Type u_3} [inst : CommRing S] [inst_1 : TopologicalS
pace S] [IsTopologicalRing S]   [IsLinearTopology S S] (x : σ → S), MvPowerSerie
s.HasEval x → ∀ {p : ℕ}, 0 < p → MvPowerSeries.HasEval (x ^ p)
参数：x : σ → S；x ^ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPowerSeries.mem_hasEvalIdeal_iff`：mem_hasEvalIdeal_iff {a : σ -> S} : 
a in hasEvalIdeal ↔ HasEval a
· 使用定理 `Ideal.pow_mem_of_mem`：pow_mem_of_mem (ha : a in I) (n : Nat) (hn : 0 < n
) : a ^ n in I
-/
theorem HasEval.pow (x : σ → S) (ha : HasEval x) {p : ℕ} (hp : 0 < p) :
    HasEval (x ^ p) :=
  mem_hasEvalIdeal_iff.mp <| Ideal.pow_mem_of_mem hasEvalIdeal ha p hp

end

/- ## Construction of an evaluation morphism for power series -/

section Evaluation

open WithPiTopology

variable {σ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R]
variable {S : Type*} [CommRing S] [UniformSpace S]
variable {φ : R →+* S}

-- We endow MvPowerSeries σ R with the product uniform structure
set_option backward.privateInPublic true in
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance : UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries inferInstance

/-- The induced uniform structure of MvPolynomial σ R is an additive group uniform structure -/
/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced uniform structure of MvPolynomial σ R is an additive group uniform s
tructure
-/
private instance [IsUniformAddGroup R] : IsUniformAddGroup (MvPolynomial σ R) :=
  IsUniformAddGroup.comap coeToMvPowerSeries.ringHom
/-
**MvPowerSeries._root_.MvPolynomial.toMvPowerSeries_isUniformInducing** 是 Mathli
b 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPolynomial.toMvPowerSeries_isUniformInducing :
    IsUniformInducing (toMvPowerSeries (σ := σ) (R := R)) :=
  (isUniformInducing_iff toMvPowerSeries).mpr rfl
/-
**MvPowerSeries._root_.MvPolynomial.toMvPowerSeries_isDenseInducing** 是 Mathlib 
中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPolynomial.toMvPowerSeries_isDenseInducing :
    IsDenseInducing (toMvPowerSeries (σ := σ) (R := R)) :=
  toMvPowerSeries_isUniformInducing.isDenseInducing denseRange_toMvPowerSeries

variable {a : σ → S}

/-- The evaluation map on multivariate polynomials is uniformly continuous
for the uniform structure induced by that on multivariate power series. -/
/-
**MvPowerSeries._root_.MvPolynomial.toMvPowerSeries_uniformContinuous** 是 Mathli
b 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation map on multivariate polynomials is uniformly continuous
for the uniform structure induced by that on multivariate power series.
-/
theorem _root_.MvPolynomial.toMvPowerSeries_uniformContinuous
    [IsUniformAddGroup R] [IsUniformAddGroup S] [IsLinearTopology S S]
    (hφ : Continuous φ) (ha : HasEval a) :
    UniformContinuous (MvPolynomial.eval₂Hom φ a) := by
  classical
  apply uniformContinuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero, IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro I hI
  let n : σ → ℕ := fun s ↦ sInf {n : ℕ | (a s) ^ n.succ ∈ I}
  have hn_ne : ∀ s, Set.Nonempty {n : ℕ | (a s) ^ n.succ ∈ I} := fun s ↦ by
    rcases ha.hpow s |>.eventually_mem hI |>.exists_forall_of_atTop with ⟨n, hn⟩
    use n
    simpa using hn n.succ n.le_succ
  have hn : Set.Finite (n.support) := by
    change n =ᶠ[cofinite] 0
    filter_upwards [ha.tendsto_zero.eventually_mem hI] with s has
    simpa [n, Pi.zero_apply, Nat.sInf_eq_zero, or_iff_left (hn_ne s).ne_empty] using has
  let n₀ : σ →₀ ℕ := .ofSupportFinite n hn
  let D := Iic n₀
  have hD : Set.Finite D := finite_Iic _
  have : ∀ d ∈ D, ∀ᶠ (p : MvPolynomial σ R) in 𝓝 0, φ (p.coeff d) ∈ I := fun d hd ↦ by
    have : Tendsto (φ ∘ coeff d ∘ toMvPowerSeries) (𝓝 0) (𝓝 0) :=
      hφ.comp (continuous_coeff R d) |>.comp continuous_induced_dom |>.tendsto' 0 0 (map_zero _)
    filter_upwards [this.eventually_mem hI] with f hf
    simpa using hf
  rw [← hD.eventually_all] at this
  filter_upwards [this] with p hp
  rw [coe_eval₂Hom, SetLike.mem_coe, eval₂_eq]
  apply Ideal.sum_mem
  intro d _
  by_cases hd : d ∈ D
  · exact Ideal.mul_mem_right _ _ (hp d hd)
  · apply Ideal.mul_mem_left
    simp only [mem_Iic, D, Finsupp.le_iff] at hd
    push Not at hd
    rcases hd with ⟨s, hs', hs⟩
    exact I.prod_mem hs' (I.pow_mem_of_pow_mem (Nat.sInf_mem (hn_ne s)) hs)

variable (φ a)
open scoped Classical in
/-- Evaluation of a multivariate power series at `f` at a point `a : σ → S`.

It coincides with the evaluation of `f` as a polynomial if `f` is the coercion of a polynomial.
Otherwise, it is only relevant if `φ` is continuous and `HasEval a`. -/
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of a multivariate power series at `f` at a point `a : σ → S`.

It coincides with the evaluation of `f` as a polynomial if `f` is the coercion o
f a polynomial.
Otherwise, it is only relevant if `φ` is continuous and `HasEval a`.
-/
noncomputable def eval₂ (f : MvPowerSeries σ R) : S :=
  if H : ∃ p : MvPolynomial σ R, p = f then (MvPolynomial.eval₂ φ a H.choose)
  else IsDenseInducing.extend toMvPowerSeries_isDenseInducing (MvPolynomial.eval₂ φ a) f

@[simp, norm_cast]
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_coe (f : MvPolynomial σ R) :
    MvPowerSeries.eval₂ φ a f = MvPolynomial.eval₂ φ a f := by
  have : ∃ p : MvPolynomial σ R, (p : MvPowerSeries σ R) = f := ⟨f, rfl⟩
  rw [eval₂, dif_pos this]
  congr
  rw [← MvPolynomial.coe_inj, this.choose_spec]

@[simp]
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C (r : R) : eval₂ φ a (C r) = φ r := by
  rw [← coe_C, eval₂_coe, MvPolynomial.eval₂_C]

@[simp]
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_X (s : σ) : eval₂ φ a (X s) = a s := by
  rw [← coe_X, eval₂_coe, MvPolynomial.eval₂_X]

variable [IsTopologicalSemiring R] [IsUniformAddGroup R]
    [IsUniformAddGroup S] [CompleteSpace S] [T2Space S]
    [IsTopologicalRing S] [IsLinearTopology S S]

variable {φ a}

/-- Evaluation of power series at adequate elements, as a `RingHom` -/
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of power series at adequate elements, as a `RingHom`
-/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    MvPowerSeries σ R →+* S :=
  IsDenseInducing.extendRingHom (i := coeToMvPowerSeries.ringHom)
    toMvPowerSeries_isUniformInducing
    denseRange_toMvPowerSeries
    (toMvPowerSeries_uniformContinuous hφ ha)
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_eq_extend (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    eval₂Hom hφ ha f =
      toMvPowerSeries_isDenseInducing.extend (MvPolynomial.eval₂ φ a) f :=
  rfl
/-
**MvPowerSeries.coe_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    ⇑(eval₂Hom hφ ha) = eval₂ φ a := by
  ext f
  simp only [eval₂Hom_eq_extend, eval₂]
  split_ifs with h
  · obtain ⟨p, rfl⟩ := h
    simpa [MvPolynomial.coe_eval₂Hom] using
      toMvPowerSeries_isDenseInducing.extend_eq
        (toMvPowerSeries_uniformContinuous hφ ha).continuous p
  · rw [← eval₂Hom_eq_extend hφ ha]

-- Note: this is still true without the `T2Space` hypothesis, by arguing that the case
-- disjunction in the definition of `eval₂` only replaces some values by topologically
-- inseparable ones.
/-
**MvPowerSeries.uniformContinuous_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformContinuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    UniformContinuous (eval₂ φ a) := by
  rw [← coe_eval₂Hom hφ ha]
  exact uniformContinuous_uniformly_extend
    toMvPowerSeries_isUniformInducing
    denseRange_toMvPowerSeries
    (toMvPowerSeries_uniformContinuous hφ ha)
/-
**MvPowerSeries.continuous_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem continuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    Continuous (eval₂ φ a : MvPowerSeries σ R → S) :=
  (uniformContinuous_eval₂ hφ ha).continuous
/-
**MvPowerSeries.hasSum_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasSum_eval₂ (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    HasSum
    (fun (d : σ →₀ ℕ) ↦ φ (coeff d f) * (d.prod fun s e => (a s) ^ e))
    (MvPowerSeries.eval₂ φ a f) := by
  rw [← coe_eval₂Hom hφ ha, eval₂Hom_eq_extend hφ ha]
  convert! (hasSum_of_monomials_self f).map (eval₂Hom hφ ha) (?_) with d
  · simp only [Function.comp_apply, coe_eval₂Hom, ← MvPolynomial.coe_monomial,
      eval₂_coe, eval₂_monomial]
  · rw [coe_eval₂Hom]; exact continuous_eval₂ hφ ha
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_eq_tsum (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    MvPowerSeries.eval₂ φ a f =
      ∑' (d : σ →₀ ℕ), φ (coeff d f) * (d.prod fun s e => (a s) ^ e) :=
  (hasSum_eval₂ hφ ha f).tsum_eq.symm
/-
**MvPowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_unique (hφ : Continuous φ) (ha : HasEval a)
    {ε : MvPowerSeries σ R → S} (hε : Continuous ε)
    (h : ∀ p : MvPolynomial σ R, ε p = MvPolynomial.eval₂ φ a p) :
    ε = eval₂ φ a := by
  rw [← coe_eval₂Hom hφ ha]
  exact (toMvPowerSeries_isDenseInducing.extend_unique h hε).symm
/-
**MvPowerSeries.comp_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eval₂ (hφ : Continuous φ) (ha : HasEval a)
    {T : Type*} [UniformSpace T] [CompleteSpace T] [T2Space T]
    [CommRing T] [IsTopologicalRing T] [IsLinearTopology T T] [IsUniformAddGroup T]
    {ε : S →+* T} (hε : Continuous ε) :
    ε ∘ eval₂ φ a = eval₂ (ε.comp φ) (ε ∘ a) := by
  apply eval₂_unique _ (ha.map hε)
  · exact Continuous.comp hε (continuous_eval₂ hφ ha)
  · intro p
    simp only [Function.comp_apply, eval₂_coe]
    rw [← MvPolynomial.coe_eval₂Hom, ← comp_apply, MvPolynomial.comp_eval₂Hom,
      MvPolynomial.coe_eval₂Hom]
  · simp only [coe_comp, Continuous.comp hε hφ]

variable [Algebra R S] [ContinuousSMul R S]

/-- Evaluation of power series at adequate elements, as an `AlgHom` -/
/-
**MvPowerSeries.aeval** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：aeval (ha : HasEval a) : MvPowerSeries σ R ->ₐ[R] S where toRingHom
参数：ha : HasEval a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of power series at adequate elements, as an `AlgHom`
-/
noncomputable def aeval (ha : HasEval a) : MvPowerSeries σ R →ₐ[R] S where
  toRingHom := MvPowerSeries.eval₂Hom (continuous_algebraMap R S) ha
  commutes' r := by
    simp only [toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [← c_eq_algebraMap, coe_eval₂Hom, eval₂_C]
/-
**MvPowerSeries.coe_aeval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval₂ (algebraMap R S) a
参数：ha : HasEval a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coe_eval₂Hom`：coe_eval₂Hom (hφ : Continuous φ) (ha : HasEv
al a) : ⇑(eval₂Hom hφ ha) = eval₂ φ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_aeval (ha : HasEval a) :
    ↑(aeval ha) = eval₂ (algebraMap R S) a := by
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]
/-
**MvPowerSeries.continuous_aeval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：continuous_aeval (ha : HasEval a) : Continuous (aeval ha : MvPowerSeries σ
 R -> S)
参数：ha : HasEval a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval
₂ (algebraMap R S) a
· 使用定理 `MvPowerSeries.continuous_eval₂`：continuous_eval₂ (hφ : Continuous φ) (ha
 : HasEval a) : Continuous (eval₂ φ a : MvPowerSeries σ R -> S)
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
-/
theorem continuous_aeval (ha : HasEval a) :
    Continuous (aeval ha : MvPowerSeries σ R → S) := by
  rw [coe_aeval]
  exact continuous_eval₂ (continuous_algebraMap R S) ha

@[simp]
/-
**MvPowerSeries.aeval_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：aeval_coe (ha : HasEval a) (p : MvPolynomial σ R) : aeval ha (p : MvPowerS
eries σ R) = p.aeval a
参数：ha : HasEval a；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval
₂ (algebraMap R S) a
· 使用定理 `MvPolynomial.aeval_def`：aeval_def (p : MvPolynomial σ R) : aeval f p = e
val₂ (algebraMap R S₁) f p
· 使用定理 `MvPowerSeries.eval₂_coe`：eval₂_coe (f : MvPolynomial σ R) : MvPowerSerie
s.eval₂ φ a f = MvPolynomial.eval₂ φ a f
-/
theorem aeval_coe (ha : HasEval a) (p : MvPolynomial σ R) :
    aeval ha (p : MvPowerSeries σ R) = p.aeval a := by
  rw [coe_aeval, aeval_def, eval₂_coe]
/-
**MvPowerSeries.aeval_unique** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：aeval_unique {ε : MvPowerSeries σ R ->ₐ[R] S} (hε : Continuous ε) : aeval 
(HasEval.X.map hε) = ε
参数：hε : Continuous ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `MvPowerSeries.HasEval.map`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommR
ing R] [inst_1 : TopologicalSpace R] {S : Type u_3} [inst_2 : CommRing S]   [ins
t_3 : Topologic…
· 使用定理 `MvPowerSeries.HasEval.X`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommRin
g R] [inst_1 : TopologicalSpace R],   MvPowerSeries.HasEval fun s => MvPowerSeri
es.X s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval
₂ (algebraMap R S) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.eval₂_unique`：eval₂_unique (hφ : Continuous φ) (ha : HasEv
al a) {ε : MvPowerSeries σ R -> S} (hε : Continuous ε) (h : forall p : MvPolynom
ial σ R, ε p = M…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.aeval_X_left_apply`：aeval_X_left_apply (p : MvPolynomial σ 
R) : aeval X p = p
· 使用引理 `MvPolynomial.comp_aeval_apply`：comp_aeval_apply {B : Type*} [CommSemirin
g B] [Algebra R B] (φ : S₁ ->ₐ[R] B) (p : MvPolynomial σ R) : φ (aeval f p) = ae
val (fun i => φ (f …
· 使用定理 `MvPolynomial.aeval_def`：aeval_def (p : MvPolynomial σ R) : aeval f p = e
val₂ (algebraMap R S₁) f p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.coe_X`：coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerS
eries σ R) = MvPowerSeries.X s
-/
theorem aeval_unique {ε : MvPowerSeries σ R →ₐ[R] S} (hε : Continuous ε) :
    aeval (HasEval.X.map hε) = ε := by
  apply DFunLike.ext'
  rw [coe_aeval]
  refine (eval₂_unique (continuous_algebraMap R S) (HasEval.X.map hε) hε ?_).symm
  intro p
  trans ε.comp (coeToMvPowerSeries.algHom R) p
  · simp
  conv_lhs => rw [← p.aeval_X_left_apply, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def]
  simp
/-
**MvPowerSeries.hasSum_aeval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：hasSum_aeval (ha : HasEval a) (f : MvPowerSeries σ R) : HasSum (fun (d : σ
 ->₀ Nat) => (coeff d f) • (d.prod fun s e => (a s) ^ e)) (MvPowerSeries.aeval h
a f)
参数：ha : HasEval a；f : MvPowerSeries σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MvPowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval
₂ (algebraMap R S) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPowerSeries.hasSum_eval₂`：hasSum_eval₂ (hφ : Continuous φ) (ha : HasEv
al a) (f : MvPowerSeries σ R) : HasSum (fun (d : σ ->₀ Nat) => φ (coeff d f) * (
d.prod fun s e =…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
-/
theorem hasSum_aeval (ha : HasEval a) (f : MvPowerSeries σ R) :
    HasSum (fun (d : σ →₀ ℕ) ↦ (coeff d f) • (d.prod fun s e => (a s) ^ e))
      (MvPowerSeries.aeval ha f) := by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f
/-
**MvPowerSeries.aeval_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：aeval_eq_sum (ha : HasEval a) (f : MvPowerSeries σ R) : MvPowerSeries.aeva
l ha f = tsum (fun (d : σ ->₀ Nat) => (coeff d f) • (d.prod fun s e => (a s) ^ e
))
参数：ha : HasEval a；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `MvPowerSeries.hasSum_aeval`：hasSum_aeval (ha : HasEval a) (f : MvPowerSe
ries σ R) : HasSum (fun (d : σ ->₀ Nat) => (coeff d f) • (d.prod fun s e => (a s
) ^ e)) (MvPower…
-/
theorem aeval_eq_sum (ha : HasEval a) (f : MvPowerSeries σ R) :
    MvPowerSeries.aeval ha f =
      tsum (fun (d : σ →₀ ℕ) ↦ (coeff d f) • (d.prod fun s e => (a s) ^ e)) :=
  (hasSum_aeval ha f).tsum_eq.symm
/-
**MvPowerSeries.comp_aeval** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：comp_aeval (ha : HasEval a) {T : Type*} [CommRing T] [UniformSpace T] [IsU
niformAddGroup T] [IsTopologicalRing T] [IsLinearTopology T T] [T2Space T] [Alge
bra R T] [ContinuousSMul R T] [CompleteSpace T] {ε : S ->ₐ[R] T} (hε : Continuou
s ε) : ε.comp (aeval ha) = aeval (ha.map hε)
参数：ha : HasEval a；hε : Continuous ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `MvPowerSeries.HasEval.map`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommR
ing R] [inst_1 : TopologicalSpace R] {S : Type u_3} [inst_2 : CommRing S]   [ins
t_3 : Topologic…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coe_aeval`：coe_aeval (ha : HasEval a) : ↑(aeval ha) = eval
₂ (algebraMap R S) a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `MvPowerSeries.comp_eval₂`：comp_eval₂ (hφ : Continuous φ) (ha : HasEval a
) {T : Type*} [UniformSpace T] [CompleteSpace T] [T2Space T] [CommRing T] [IsTop
ologicalRing T…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem comp_aeval (ha : HasEval a)
    {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T]
    [T2Space T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]
    {ε : S →ₐ[R] T} (hε : Continuous ε) :
    ε.comp (aeval ha) = aeval (ha.map hε) := by
  apply DFunLike.ext'
  simp only [AlgHom.coe_comp, coe_aeval ha]
  rw [← RingHom.coe_coe,
    comp_eval₂ (continuous_algebraMap R S) ha (show Continuous (ε : S →+* T) from hε), coe_aeval]
  congr!
  simp only [AlgHom.comp_algebraMap_of_tower]

end Evaluation

end MvPowerSeries

