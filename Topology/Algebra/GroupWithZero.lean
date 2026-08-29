/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological group with zero

In this file we define `ContinuousInv₀` to be a mixin typeclass a type with `Inv` and
`Zero` (e.g., a `GroupWithZero`) such that `fun x ↦ x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. Currently the only example of `ContinuousInv₀` in
`mathlib` which is not a normed field is the type `NNReal` (a.k.a. `ℝ≥0`) of nonnegative real
numbers.

Then we prove lemmas about continuity of `x ↦ x⁻¹` and `f / g` providing dot-style `*.inv₀` and
`*.div` operations on `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`,
and `Continuous`. As a special case, we provide `*.div_const` operations that require only
`DivInvMonoid` and `ContinuousMul` instances.

All lemmas about `(⁻¹)` use `inv₀` in their names because lemmas without `₀` are used for
`IsTopologicalGroup`s. We also use `'` in the typeclass name `ContinuousInv₀` for the sake of
consistency of notation.

On a `GroupWithZero` with continuous multiplication, we also define left and right multiplication
as homeomorphisms.
-/

@[expose] public section
open Topology Filter Function

/-!
### A `DivInvMonoid` with continuous multiplication

If `G₀` is a `DivInvMonoid` with continuous `(*)`, then `(/y)` is continuous for any `y`. In this
section we prove lemmas that immediately follow from this fact providing `*.div_const` dot-style
operations on `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`, and
`Continuous`.
-/


variable {α β G₀ : Type*}

section DivConst

variable [DivInvMonoid G₀] [TopologicalSpace G₀] [SeparatelyContinuousMul G₀]
  {f : α -> G₀} {s : Set α} {l : Filter α}

/--
theorem `Filter.Tendsto.div_const` / 定理 `Filter.Tendsto.div_const`

English:
theorem Filter.Tendsto.div_const
  given: {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀)
  proof: by
  simpa only [div_eq_mul_inv] using hf.mul_const _

中文:
定理 滤子.收敛.div_const
  条件: {x : G₀} (hf : 收敛 f l (𝓝 x)) (y : G₀)
  证明: by
  simpa only [div_eq_mul_inv] using hf.mul_const _

Depends on / 依赖: div_eq_mul_inv, hf.mul_const, mul_const
-/
theorem Filter.Tendsto.div_const {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) :
    Tendsto (fun a => f a / y) l (𝓝 (x / y)) := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

variable [TopologicalSpace α]

nonrec theorem ContinuousAt.div_const {a : α} (hf : ContinuousAt f a) (y : G₀) :
    ContinuousAt (fun x => f x / y) a :=
  hf.div_const y

nonrec theorem ContinuousWithinAt.div_const {a} (hf : ContinuousWithinAt f s a) (y : G₀) :
    ContinuousWithinAt (fun x => f x / y) s a :=
  hf.div_const _

/--
theorem `ContinuousOn.div_const` / 定理 `ContinuousOn.div_const`

English:
theorem ContinuousOn.div_const
  given: (hf : ContinuousOn f s) (y : G₀)
  proof: by
  simpa only [div_eq_mul_inv] using hf.mul_const _

@[continuity, fun_prop]

中文:
定理 ContinuousOn.div_const
  条件: (hf : ContinuousOn f s) (y : G₀)
  证明: by
  simpa only [div_eq_mul_inv] using hf.mul_const _

@[continuity, fun_prop]

Depends on / 依赖: div_eq_mul_inv, hf.mul_const, mul_const
-/
theorem ContinuousOn.div_const (hf : ContinuousOn f s) (y : G₀) :
    ContinuousOn (fun x => f x / y) s := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

@[continuity, fun_prop]
/--
theorem `Continuous.div_const` / 定理 `Continuous.div_const`

English:
theorem Continuous.div_const
  given: (hf : Continuous f) (y : G₀)
  statement: Continuous fun x => f x / y
  proof: by
  simpa only [div_eq_mul_inv] using hf.mul_const _

中文:
定理 连续.div_const
  条件: (hf : 连续 f) (y : G₀)
  结论: 连续 fun x => f x / y
  证明: by
  simpa only [div_eq_mul_inv] using hf.mul_const _

Depends on / 依赖: div_eq_mul_inv, hf.mul_const, mul_const
-/
theorem Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x => f x / y := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

end DivConst

/--
Definition of `ContinuousInv₀` / `ContinuousInv₀` 的定义

English:
class ContinuousInv₀
  parameters: (G₀ : Type*) [Zero G₀] [Inv G₀] [TopologicalSpace G₀]
  axioms and operations (1):
    - continuousAt_inv₀ : forall ⦃x : G₀⦄, x != 0 -> ContinuousAt Inv.inv x

中文:
类 余ntinuousInv₀
  参数: (G₀ : 类型) [零 G₀] [取逆 G₀] [拓扑空间 G₀]
  公理与运算 (1 个):
    - continuousAt_inv₀ : 对任意 ⦃x : G₀⦄, x != 0 -> ContinuousAt 取逆.inv x
-/
class ContinuousInv₀ (G₀ : Type*) [Zero G₀] [Inv G₀] [TopologicalSpace G₀] : Prop where
  /-- The map `fun x ↦ x⁻¹` is continuous at all nonzero points. -/
  continuousAt_inv₀ : forall ⦃x : G₀⦄, x != 0 -> ContinuousAt Inv.inv x

export ContinuousInv₀ (continuousAt_inv₀)

section Inv₀

variable [Zero G₀] [Inv G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] {l : Filter α} {f : α -> G₀}
  {s : Set α} {a : α}


/--
theorem `tendsto_inv₀` / 定理 `tendsto_inv₀`

English:
theorem tendsto_inv₀
  given: {x : G₀} (hx : x != 0)
  statement: Tendsto Inv.inv (𝓝 x) (𝓝 x⁻¹)
  proof: continuousAt_inv₀ hx

中文:
定理 tendsto_inv₀
  条件: {x : G₀} (hx : x != 0)
  结论: 收敛 取逆.inv (𝓝 x) (𝓝 x⁻¹)
  证明: continuousAt_inv₀ hx
-/
theorem tendsto_inv₀ {x : G₀} (hx : x != 0) : Tendsto Inv.inv (𝓝 x) (𝓝 x⁻¹) :=
  continuousAt_inv₀ hx

/--
theorem `continuousOn_inv₀` / 定理 `continuousOn_inv₀`

English:
theorem continuousOn_inv₀
  statement: ContinuousOn (Inv.inv : G₀ -> G₀) {0}ᶜ
  proof: fun _x hx =>
  (continuousAt_inv₀ hx).continuousWithinAt

中文:
定理 continuousOn_inv₀
  结论: ContinuousOn (取逆.inv : G₀ -> G₀) {0}ᶜ
  证明: fun _x hx =>
  (continuousAt_inv₀ hx).continuousWithinAt
-/
theorem continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ -> G₀) {0}ᶜ := fun _x hx =>
  (continuousAt_inv₀ hx).continuousWithinAt

/--
theorem `Filter.Tendsto.inv₀` / 定理 `Filter.Tendsto.inv₀`

English:
theorem Filter.Tendsto.inv₀
  given: {a : G₀} (hf : Tendsto f l (𝓝 a)) (ha : a != 0)
  proof: (tendsto_inv₀ ha).comp hf

中文:
定理 滤子.收敛.inv₀
  条件: {a : G₀} (hf : 收敛 f l (𝓝 a)) (ha : a != 0)
  证明: (tendsto_inv₀ ha).comp hf
-/
theorem Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a)) (ha : a != 0) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹) :=
  (tendsto_inv₀ ha).comp hf

variable [TopologicalSpace α]

@[to_fun (attr := fun_prop)]
nonrec theorem ContinuousWithinAt.inv₀ (hf : ContinuousWithinAt f s a) (ha : f a != 0) :
    ContinuousWithinAt f⁻¹ s a :=
  hf.inv₀ ha

@[to_fun (attr := fun_prop)]
nonrec theorem ContinuousAt.inv₀ (hf : ContinuousAt f a) (ha : f a != 0) :
    ContinuousAt f⁻¹ a :=
  hf.inv₀ ha

@[to_fun (attr := continuity, fun_prop)]
/--
theorem `Continuous.inv₀` / 定理 `Continuous.inv₀`

English:
theorem Continuous.inv₀
  given: (hf : Continuous f) (h0 : forall x, f x != 0)
  statement: Continuous f⁻¹
  proof: continuous_iff_continuousAt.2 fun x => (hf.tendsto x).inv₀ (h0 x)

@[to_fun (attr := fun_prop)]

中文:
定理 连续.inv₀
  条件: (hf : 连续 f) (h0 : 对任意 x, f x != 0)
  结论: 连续 f⁻¹
  证明: continuous_iff_continuousAt.2 fun x => (hf.tendsto x).inv₀ (h0 x)

@[to_fun (attr := fun_prop)]

Depends on / 依赖: continuous_iff_continuousAt, hf.tendsto, tendsto
-/
theorem Continuous.inv₀ (hf : Continuous f) (h0 : forall x, f x != 0) : Continuous f⁻¹ :=
  continuous_iff_continuousAt.2 fun x => (hf.tendsto x).inv₀ (h0 x)

@[to_fun (attr := fun_prop)]
/--
theorem `ContinuousOn.inv₀` / 定理 `ContinuousOn.inv₀`

English:
theorem ContinuousOn.inv₀
  given: (hf : ContinuousOn f s) (h0 : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).inv₀ (h0 x hx)

中文:
定理 ContinuousOn.inv₀
  条件: (hf : ContinuousOn f s) (h0 : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).inv₀ (h0 x hx)
-/
theorem ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : forall x in s, f x != 0) :
    ContinuousOn f⁻¹ s := fun x hx => (hf x hx).inv₀ (h0 x hx)

end Inv₀

section GroupWithZero

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]

/--
theorem `Units.isEmbedding_val₀` / 定理 `Units.isEmbedding_val₀`

English:
theorem Units.isEmbedding_val₀
  statement: IsEmbedding (val : G₀ˣ -> G₀)
  proof: embedding_val_mk (continuousOn_inv₀ (G₀ := G₀)).mono fun _ => IsUnit.ne_zero

中文:
定理 单位群.isEmbedding_val₀
  结论: 是嵌入 (val : G₀ˣ -> G₀)
  证明: embedding_val_mk (continuousOn_inv₀ (G₀ := G₀)).mono fun _ => IsUnit.ne_zero

Depends on / 依赖: IsUnit, IsUnit.ne_zero, embedding_val_mk, ne_zero
-/
theorem Units.isEmbedding_val₀ : IsEmbedding (val : G₀ˣ -> G₀) :=
embedding_val_mk (continuousOn_inv₀ (G₀ := G₀)).mono fun _ => IsUnit.ne_zero

/--
Definition of `unitsHomeomorphNeZero` / `unitsHomeomorphNeZero` 的定义

English:
definition unitsHomeomorphNeZero
  signature: : G₀ˣ ≃ₜ {g : G₀ // g != 0}
  body: Units.isEmbedding_val₀.toHomeomorph.trans show _ ≃ₜ {g | _} from .setCongr
Set.ext fun x => (Units.exists_iff_ne_zero (p := (· = x))).trans by simp

中文:
定义 unitsHomeomorphNeZero
  签名: : G₀ˣ ≃ₜ {g : G₀ // g != 0}
  定义体: Units.isEmbedding_val₀.toHomeomorph.trans show _ ≃ₜ {g | _} from .setCongr
Set.ext fun x => (Units.exists_iff_ne_zero (p := (· = x))).trans by simp

Depends on / 依赖: Set.ext, Units.exists_iff_ne_zero, Units.isEmbedding_val, exists_iff_ne_zero, setCongr, toHomeomorph, toHomeomorph.trans
-/
noncomputable def unitsHomeomorphNeZero : G₀ˣ ≃ₜ {g : G₀ // g != 0} :=
Units.isEmbedding_val₀.toHomeomorph.trans show _ ≃ₜ {g | _} from .setCongr
Set.ext fun x => (Units.exists_iff_ne_zero (p := (· = x))).trans by simp

variable (G₀) in
/--
Definition of `Homeomorph.inv₀` / `Homeomorph.inv₀` 的定义

English:
definition Homeomorph.inv₀
  signature: : {g : G₀ // g != 0} ≃ₜ {g : G₀ // g != 0} where
  body: ⟨g⁻¹, inv_ne_zero g.2⟩
  invFun g := ⟨g⁻¹, inv_ne_zero g.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  continuous_toFun := continuous_induced_rng.mpr continuousOn_inv₀.domRestrict
  continuous_invFun := continuous_induced_rng.mpr continuousOn_inv₀.domRestrict

中文:
定义 同胚.inv₀
  签名: : {g : G₀ // g != 0} ≃ₜ {g : G₀ // g != 0} where
  定义体: ⟨g⁻¹, inv_ne_zero g.2⟩
  invFun g := ⟨g⁻¹, inv_ne_zero g.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  continuous_toFun := continuous_induced_rng.mpr continuousOn_inv₀.domRestrict
  continuous_invFun := continuous_induced_rng.mpr continuousOn_inv₀.domRestrict

Depends on / 依赖: inv_ne_zero
-/
def Homeomorph.inv₀ : {g : G₀ // g != 0} ≃ₜ {g : G₀ // g != 0} where
  toFun g := ⟨g⁻¹, inv_ne_zero g.2⟩
  invFun g := ⟨g⁻¹, inv_ne_zero g.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  continuous_toFun := continuous_induced_rng.mpr continuousOn_inv₀.domRestrict
  continuous_invFun := continuous_induced_rng.mpr continuousOn_inv₀.domRestrict

end GroupWithZero

section NhdsInv

open scoped Pointwise

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] {x : G₀}

/--
lemma `nhds_inv₀` / 引理 `nhds_inv₀`

English:
lemma nhds_inv₀
  given: (hx : x != 0)
  statement: 𝓝 x⁻¹ = (𝓝 x)⁻¹
  proof: by
  refine le_antisymm (inv_le_iff_le_inv.1 ?_) (tendsto_inv₀ hx)
  simpa only [inv_inv] using! tendsto_inv₀ (inv_ne_zero hx)

中文:
引理 nhds_inv₀
  条件: (hx : x != 0)
  结论: 𝓝 x⁻¹ = (𝓝 x)⁻¹
  证明: by
  refine le_antisymm (inv_le_iff_le_inv.1 ?_) (tendsto_inv₀ hx)
  simpa only [inv_inv] using! tendsto_inv₀ (inv_ne_zero hx)

Depends on / 依赖: inv_inv, inv_le_iff_le_inv, inv_ne_zero, le_antisymm
-/
lemma nhds_inv₀ (hx : x != 0) : 𝓝 x⁻¹ = (𝓝 x)⁻¹ := by
  refine le_antisymm (inv_le_iff_le_inv.1 ?_) (tendsto_inv₀ hx)
  simpa only [inv_inv] using! tendsto_inv₀ (inv_ne_zero hx)

/--
lemma `tendsto_inv_iff₀` / 引理 `tendsto_inv_iff₀`

English:
lemma tendsto_inv_iff₀
  given: {l : Filter α} {f : α -> G₀} (hx : x != 0)
  proof: by
  simp only [nhds_inv₀ hx, ← Filter.comap_inv, tendsto_comap_iff, Function.comp_def, inv_inv]

中文:
引理 tendsto_inv_iff₀
  条件: {l : 滤子 α} {f : α -> G₀} (hx : x != 0)
  证明: by
  simp only [nhds_inv₀ hx, ← Filter.comap_inv, tendsto_comap_iff, Function.comp_def, inv_inv]

Depends on / 依赖: Filter, Filter.comap_inv, Function, Function.comp_def, comap_inv, comp_def, inv_inv, tendsto_comap_iff
-/
lemma tendsto_inv_iff₀ {l : Filter α} {f : α -> G₀} (hx : x != 0) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 x⁻¹) ↔ Tendsto f l (𝓝 x) := by
  simp only [nhds_inv₀ hx, ← Filter.comap_inv, tendsto_comap_iff, Function.comp_def, inv_inv]

end NhdsInv

/-!
### Continuity of division

If `G₀` is a `GroupWithZero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/

section Div

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [ContinuousMul G₀]
  {f g : α -> G₀}

/--
theorem `Filter.Tendsto.div` / 定理 `Filter.Tendsto.div`

English:
theorem Filter.Tendsto.div
  statement: {l : Filter α} {a b : G₀} (hf : Tendsto f l (𝓝 a))
  proof: by
  simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ hy)

中文:
定理 滤子.收敛.div
  结论: {l : 滤子 α} {a b : G₀} (hf : 收敛 f l (𝓝 a))
  证明: by
  simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ hy)

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 (a / b)) := by
  simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ hy)

/--
theorem `tendsto_div_nhds_one_iff_eq₀` / 定理 `tendsto_div_nhds_one_iff_eq₀`

English:
theorem tendsto_div_nhds_one_iff_eq₀
  proof: ⟨fun hfg => (div_eq_one_iff_eq hb).mp (tendsto_nhds_unique (hf.div hg hb) hfg),
   fun hab => (div_eq_one_iff_eq hb).mpr hab ▸ hf.div hg hb⟩

alias ⟨eq_of_tendsto_div_nhds_one₀, _⟩ := tendsto_div_nhds_one_iff_eq₀

中文:
定理 tendsto_div_nhds_one_iff_eq₀
  证明: ⟨fun hfg => (div_eq_one_iff_eq hb).mp (tendsto_nhds_unique (hf.div hg hb) hfg),
   fun hab => (div_eq_one_iff_eq hb).mpr hab ▸ hf.div hg hb⟩

alias ⟨eq_of_tendsto_div_nhds_one₀, _⟩ := tendsto_div_nhds_one_iff_eq₀

Depends on / 依赖: div_eq_one_iff_eq, hf.div, tendsto_nhds_unique
-/
theorem tendsto_div_nhds_one_iff_eq₀
    {l : Filter α} [l.NeBot] [T2Space G₀] {a b : G₀}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hb : b != 0) :
    Tendsto (fun x => f x / g x) l (𝓝 1) ↔ a = b :=
  ⟨fun hfg => (div_eq_one_iff_eq hb).mp (tendsto_nhds_unique (hf.div hg hb) hfg),
   fun hab => (div_eq_one_iff_eq hb).mpr hab ▸ hf.div hg hb⟩

alias ⟨eq_of_tendsto_div_nhds_one₀, _⟩ := tendsto_div_nhds_one_iff_eq₀

/--
theorem `Filter.tendsto_mul_iff_of_ne_zero` / 定理 `Filter.tendsto_mul_iff_of_ne_zero`

English:
theorem Filter.tendsto_mul_iff_of_ne_zero
  statement: [T1Space G₀] {f g : α -> G₀} {l : Filter α} {x y : G₀}
  proof: by
  refine ⟨fun hfg => ?_, fun hf => hf.mul hg⟩
  rw [← mul_div_cancel_right₀ x hy]
  refine Tendsto.congr' ?_ (hfg.div hg hy)
  exact (hg.eventually_ne hy).mono fun n hn => mul_div_cancel_right₀ _ hn

中文:
定理 滤子.tendsto_mul_iff_of_ne_zero
  结论: [T1空间 G₀] {f g : α -> G₀} {l : 滤子 α} {x y : G₀}
  证明: by
  refine ⟨fun hfg => ?_, fun hf => hf.mul hg⟩
  rw [← mul_div_cancel_right₀ x hy]
  refine Tendsto.congr' ?_ (hfg.div hg hy)
  exact (hg.eventually_ne hy).mono fun n hn => mul_div_cancel_right₀ _ hn

Depends on / 依赖: Tendsto, Tendsto.congr, eventually_ne, hf.mul, hfg.div, hg.eventually_ne
-/
theorem Filter.tendsto_mul_iff_of_ne_zero [T1Space G₀] {f g : α -> G₀} {l : Filter α} {x y : G₀}
    (hg : Tendsto g l (𝓝 y)) (hy : y != 0) :
    Tendsto (fun n => f n * g n) l (𝓝 <| x * y) ↔ Tendsto f l (𝓝 x) := by
  refine ⟨fun hfg => ?_, fun hf => hf.mul hg⟩
  rw [← mul_div_cancel_right₀ x hy]
  refine Tendsto.congr' ?_ (hfg.div hg hy)
  exact (hg.eventually_ne hy).mono fun n hn => mul_div_cancel_right₀ _ hn

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {a : α}

nonrec theorem ContinuousWithinAt.div (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h₀ : g a != 0) : ContinuousWithinAt (f / g) s a :=
  hf.div hg h₀

/--
theorem `ContinuousOn.div` / 定理 `ContinuousOn.div`

English:
theorem ContinuousOn.div
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : forall x in s, g x != 0)
  proof: fun x hx => (hf x hx).div (hg x hx) (h₀ x hx)

中文:
定理 ContinuousOn.div
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : 对任意 x in s, g x != 0)
  证明: fun x hx => (hf x hx).div (hg x hx) (h₀ x hx)
-/
theorem ContinuousOn.div (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : forall x in s, g x != 0) :
    ContinuousOn (f / g) s := fun x hx => (hf x hx).div (hg x hx) (h₀ x hx)

/-- Continuity at a point of the result of dividing two functions continuous at that point, where
the denominator is nonzero. -/
nonrec theorem ContinuousAt.div (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a != 0) :
    ContinuousAt (f / g) a :=
  hf.div hg h₀

@[continuity]
/--
theorem `Continuous.div` / 定理 `Continuous.div`

English:
theorem Continuous.div
  given: (hf : Continuous f) (hg : Continuous g) (h₀ : forall x, g x != 0)
  proof: by simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

中文:
定理 连续.div
  条件: (hf : 连续 f) (hg : 连续 g) (h₀ : 对任意 x, g x != 0)
  证明: by simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem Continuous.div (hf : Continuous f) (hg : Continuous g) (h₀ : forall x, g x != 0) :
    Continuous (f / g) := by simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

/--
theorem `continuousOn_div` / 定理 `continuousOn_div`

English:
theorem continuousOn_div
  statement: ContinuousOn (fun p : G₀ × G₀ => p.1 / p.2) { p | p.2 != 0 }
  proof: continuousOn_fst.div continuousOn_snd fun _ => id

@[fun_prop]

中文:
定理 continuousOn_div
  结论: ContinuousOn (fun p : G₀ × G₀ => p.1 / p.2) { p | p.2 != 0 }
  证明: continuousOn_fst.div continuousOn_snd fun _ => id

@[fun_prop]

Depends on / 依赖: continuousOn_fst, continuousOn_fst.div, continuousOn_snd
-/
theorem continuousOn_div : ContinuousOn (fun p : G₀ × G₀ => p.1 / p.2) { p | p.2 != 0 } :=
  continuousOn_fst.div continuousOn_snd fun _ => id

@[fun_prop]
/--
theorem `Continuous.div₀` / 定理 `Continuous.div₀`

English:
theorem Continuous.div₀
  given: (hf : Continuous f) (hg : Continuous g) (h₀ : forall x, g x != 0)
  proof: by
  simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

@[fun_prop]

中文:
定理 连续.div₀
  条件: (hf : 连续 f) (hg : 连续 g) (h₀ : 对任意 x, g x != 0)
  证明: by
  simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

@[fun_prop]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem Continuous.div₀ (hf : Continuous f) (hg : Continuous g) (h₀ : forall x, g x != 0) :
    Continuous (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

@[fun_prop]
/--
theorem `ContinuousAt.div₀` / 定理 `ContinuousAt.div₀`

English:
theorem ContinuousAt.div₀
  given: (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a != 0)
  proof: ContinuousAt.div hf hg h₀

@[fun_prop]

中文:
定理 ContinuousAt.div₀
  条件: (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a != 0)
  证明: ContinuousAt.div hf hg h₀

@[fun_prop]

Depends on / 依赖: ContinuousAt, ContinuousAt.div
-/
theorem ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a != 0) :
    ContinuousAt (fun x => f x / g x) a := ContinuousAt.div hf hg h₀

@[fun_prop]
/--
theorem `ContinuousOn.div₀` / 定理 `ContinuousOn.div₀`

English:
theorem ContinuousOn.div₀
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : forall x in s, g x != 0)
  proof: ContinuousOn.div hf hg h₀

中文:
定理 ContinuousOn.div₀
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : 对任意 x in s, g x != 0)
  证明: ContinuousOn.div hf hg h₀

Depends on / 依赖: ContinuousOn, ContinuousOn.div
-/
theorem ContinuousOn.div₀ (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : forall x in s, g x != 0) :
    ContinuousOn (fun x => f x / g x) s := ContinuousOn.div hf hg h₀

/--
theorem `ContinuousAt.comp_div_cases` / 定理 `ContinuousAt.comp_div_cases`

English:
theorem ContinuousAt.comp_div_cases
  statement: {f g : α -> G₀} (h : α -> G₀ -> β) (hf : ContinuousAt f a)
  proof: by
  change ContinuousAt (↿h ∘ fun x => (x, f x / g x)) a
  by_cases hga : g a = 0
  · rw [ContinuousAt]
    simp_rw [comp_apply, hga, div_zero]
    exact (h2h hga).comp (continuousAt_id.tendsto.prodMk tendsto_top)
  · fun_prop

中文:
定理 ContinuousAt.comp_div_cases
  结论: {f g : α -> G₀} (h : α -> G₀ -> β) (hf : ContinuousAt f a)
  证明: by
  change ContinuousAt (↿h ∘ fun x => (x, f x / g x)) a
  by_cases hga : g a = 0
  · rw [ContinuousAt]
    simp_rw [comp_apply, hga, div_zero]
    exact (h2h hga).comp (continuousAt_id.tendsto.prodMk tendsto_top)
  · fun_prop

Depends on / 依赖: ContinuousAt, comp_apply, continuousAt_id, continuousAt_id.tendsto.prodMk, div_zero, fun_prop, prodMk, simp_rw, tendsto, tendsto_top
-/
theorem ContinuousAt.comp_div_cases {f g : α -> G₀} (h : α -> G₀ -> β) (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (hh : g a != 0 -> ContinuousAt ↿h (a, f a / g a))
    (h2h : g a = 0 -> Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    ContinuousAt (fun x => h x (f x / g x)) a := by
  change ContinuousAt (↿h ∘ fun x => (x, f x / g x)) a
  by_cases hga : g a = 0
  · rw [ContinuousAt]
    simp_rw [comp_apply, hga, div_zero]
    exact (h2h hga).comp (continuousAt_id.tendsto.prodMk tendsto_top)
  · fun_prop

/--
theorem `Continuous.comp_div_cases` / 定理 `Continuous.comp_div_cases`

English:
theorem Continuous.comp_div_cases
  statement: {f g : α -> G₀} (h : α -> G₀ -> β) (hf : Continuous f)
  proof: continuous_iff_continuousAt.mpr fun a =>
    hf.continuousAt.comp_div_cases _ hg.continuousAt (hh a) (h2h a)

中文:
定理 连续.comp_div_cases
  结论: {f g : α -> G₀} (h : α -> G₀ -> β) (hf : 连续 f)
  证明: continuous_iff_continuousAt.mpr fun a =>
    hf.continuousAt.comp_div_cases _ hg.continuousAt (hh a) (h2h a)

Depends on / 依赖: comp_div_cases, continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, hf.continuousAt.comp_div_cases, hg.continuousAt
-/
theorem Continuous.comp_div_cases {f g : α -> G₀} (h : α -> G₀ -> β) (hf : Continuous f)
    (hg : Continuous g) (hh : forall a, g a != 0 -> ContinuousAt ↿h (a, f a / g a))
    (h2h : forall a, g a = 0 -> Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    Continuous fun x => h x (f x / g x) :=
  continuous_iff_continuousAt.mpr fun a =>
    hf.continuousAt.comp_div_cases _ hg.continuousAt (hh a) (h2h a)

end Div

/-! ### Left and right multiplication as homeomorphisms -/


namespace Homeomorph

variable [TopologicalSpace α] [GroupWithZero α] [SeparatelyContinuousMul α]

/--
Definition of `mulLeft₀` / `mulLeft₀` 的定义

English:
definition mulLeft₀
  signature: (c : α) (hc : c != 0)
  body: { Equiv.mulLeft₀ c hc with
    continuous_toFun := continuous_const_mul _
    continuous_invFun := continuous_const_mul _ }

中文:
定义 mulLeft₀
  签名: (c : α) (hc : c != 0)
  定义体: { Equiv.mulLeft₀ c hc with
    continuous_toFun := continuous_const_mul _
    continuous_invFun := continuous_const_mul _ }
-/
protected def mulLeft₀ (c : α) (hc : c != 0) : α ≃ₜ α :=
  { Equiv.mulLeft₀ c hc with
    continuous_toFun := continuous_const_mul _
    continuous_invFun := continuous_const_mul _ }

/--
Definition of `mulRight₀` / `mulRight₀` 的定义

English:
definition mulRight₀
  signature: (c : α) (hc : c != 0)
  body: { Equiv.mulRight₀ c hc with
    continuous_toFun := continuous_mul_const _
    continuous_invFun := continuous_mul_const _ }

@[simp]

中文:
定义 mulRight₀
  签名: (c : α) (hc : c != 0)
  定义体: { Equiv.mulRight₀ c hc with
    continuous_toFun := continuous_mul_const _
    continuous_invFun := continuous_mul_const _ }

@[simp]
-/
protected def mulRight₀ (c : α) (hc : c != 0) : α ≃ₜ α :=
  { Equiv.mulRight₀ c hc with
    continuous_toFun := continuous_mul_const _
    continuous_invFun := continuous_mul_const _ }

@[simp]
/--
theorem `coe_mulLeft₀` / 定理 `coe_mulLeft₀`

English:
theorem coe_mulLeft₀
  given: (c : α) (hc : c != 0)
  statement: ⇑(Homeomorph.mulLeft₀ c hc) = (c * ·)
  proof: rfl

@[simp]

中文:
定理 coe_mulLeft₀
  条件: (c : α) (hc : c != 0)
  结论: ⇑(同胚.mulLeft₀ c hc) = (c * ·)
  证明: rfl

@[simp]
-/
theorem coe_mulLeft₀ (c : α) (hc : c != 0) : ⇑(Homeomorph.mulLeft₀ c hc) = (c * ·) :=
  rfl

@[simp]
/--
theorem `mulLeft₀_symm_apply` / 定理 `mulLeft₀_symm_apply`

English:
theorem mulLeft₀_symm_apply
  given: (c : α) (hc : c != 0)
  proof: rfl

@[simp]

中文:
定理 mulLeft₀_symm_apply
  条件: (c : α) (hc : c != 0)
  证明: rfl

@[simp]
-/
theorem mulLeft₀_symm_apply (c : α) (hc : c != 0) :
    ((Homeomorph.mulLeft₀ c hc).symm : α -> α) = (c⁻¹ * ·) :=
  rfl

@[simp]
/--
theorem `coe_mulRight₀` / 定理 `coe_mulRight₀`

English:
theorem coe_mulRight₀
  given: (c : α) (hc : c != 0)
  statement: ⇑(Homeomorph.mulRight₀ c hc) = (· * c)
  proof: rfl

@[simp]

中文:
定理 coe_mulRight₀
  条件: (c : α) (hc : c != 0)
  结论: ⇑(同胚.mulRight₀ c hc) = (· * c)
  证明: rfl

@[simp]
-/
theorem coe_mulRight₀ (c : α) (hc : c != 0) : ⇑(Homeomorph.mulRight₀ c hc) = (· * c) :=
  rfl

@[simp]
/--
theorem `mulRight₀_symm_apply` / 定理 `mulRight₀_symm_apply`

English:
theorem mulRight₀_symm_apply
  given: (c : α) (hc : c != 0)
  proof: rfl

中文:
定理 mulRight₀_symm_apply
  条件: (c : α) (hc : c != 0)
  证明: rfl
-/
theorem mulRight₀_symm_apply (c : α) (hc : c != 0) :
    ((Homeomorph.mulRight₀ c hc).symm : α -> α) = (· * c⁻¹) :=
  rfl

end Homeomorph

section map_comap

variable [TopologicalSpace G₀] [GroupWithZero G₀] [SeparatelyContinuousMul G₀] {a : G₀}

/--
theorem `map_mul_left_nhds₀` / 定理 `map_mul_left_nhds₀`

English:
theorem map_mul_left_nhds₀
  given: (ha : a != 0) (b : G₀)
  statement: map (a * ·) (𝓝 b) = 𝓝 (a * b)
  proof: (Homeomorph.mulLeft₀ a ha).map_nhds_eq b

中文:
定理 map_mul_left_nhds₀
  条件: (ha : a != 0) (b : G₀)
  结论: map (a * ·) (𝓝 b) = 𝓝 (a * b)
  证明: (Homeomorph.mulLeft₀ a ha).map_nhds_eq b

Depends on / 依赖: Homeomorph, Homeomorph.mulLeft, map_nhds_eq
-/
theorem map_mul_left_nhds₀ (ha : a != 0) (b : G₀) : map (a * ·) (𝓝 b) = 𝓝 (a * b) :=
  (Homeomorph.mulLeft₀ a ha).map_nhds_eq b

/--
theorem `map_mul_left_nhds_one₀` / 定理 `map_mul_left_nhds_one₀`

English:
theorem map_mul_left_nhds_one₀
  given: (ha : a != 0)
  statement: map (a * ·) (𝓝 1) = 𝓝 (a)
  proof: by
  rw [map_mul_left_nhds₀ ha]; rw [mul_one]

中文:
定理 map_mul_left_nhds_one₀
  条件: (ha : a != 0)
  结论: map (a * ·) (𝓝 1) = 𝓝 (a)
  证明: by
  rw [map_mul_left_nhds₀ ha]; rw [mul_one]

Depends on / 依赖: mul_one
-/
theorem map_mul_left_nhds_one₀ (ha : a != 0) : map (a * ·) (𝓝 1) = 𝓝 (a) := by
  rw [map_mul_left_nhds₀ ha]; rw [mul_one]

/--
theorem `map_mul_right_nhds₀` / 定理 `map_mul_right_nhds₀`

English:
theorem map_mul_right_nhds₀
  given: (ha : a != 0) (b : G₀)
  statement: map (· * a) (𝓝 b) = 𝓝 (b * a)
  proof: (Homeomorph.mulRight₀ a ha).map_nhds_eq b

中文:
定理 map_mul_right_nhds₀
  条件: (ha : a != 0) (b : G₀)
  结论: map (· * a) (𝓝 b) = 𝓝 (b * a)
  证明: (Homeomorph.mulRight₀ a ha).map_nhds_eq b

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, map_nhds_eq
-/
theorem map_mul_right_nhds₀ (ha : a != 0) (b : G₀) : map (· * a) (𝓝 b) = 𝓝 (b * a) :=
  (Homeomorph.mulRight₀ a ha).map_nhds_eq b

/--
theorem `map_mul_right_nhds_one₀` / 定理 `map_mul_right_nhds_one₀`

English:
theorem map_mul_right_nhds_one₀
  given: (ha : a != 0)
  statement: map (· * a) (𝓝 1) = 𝓝 (a)
  proof: by
  rw [map_mul_right_nhds₀ ha]; rw [one_mul]

中文:
定理 map_mul_right_nhds_one₀
  条件: (ha : a != 0)
  结论: map (· * a) (𝓝 1) = 𝓝 (a)
  证明: by
  rw [map_mul_right_nhds₀ ha]; rw [one_mul]

Depends on / 依赖: one_mul
-/
theorem map_mul_right_nhds_one₀ (ha : a != 0) : map (· * a) (𝓝 1) = 𝓝 (a) := by
  rw [map_mul_right_nhds₀ ha]; rw [one_mul]

/--
theorem `nhds_translation_mul_inv₀` / 定理 `nhds_translation_mul_inv₀`

English:
theorem nhds_translation_mul_inv₀
  given: (ha : a != 0)
  statement: comap (· * a⁻¹) (𝓝 1) = 𝓝 a
  proof: ((Homeomorph.mulRight₀ a ha).symm.comap_nhds_eq 1).trans by simp

中文:
定理 nhds_translation_mul_inv₀
  条件: (ha : a != 0)
  结论: comap (· * a⁻¹) (𝓝 1) = 𝓝 a
  证明: ((Homeomorph.mulRight₀ a ha).symm.comap_nhds_eq 1).trans by simp

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, comap_nhds_eq, symm.comap_nhds_eq
-/
theorem nhds_translation_mul_inv₀ (ha : a != 0) : comap (· * a⁻¹) (𝓝 1) = 𝓝 a :=
((Homeomorph.mulRight₀ a ha).symm.comap_nhds_eq 1).trans by simp

/--
theorem `ContinuousInv₀.of_nhds_one` / 定理 `ContinuousInv₀.of_nhds_one`

English:
theorem ContinuousInv₀.of_nhds_one
  given: (h : Tendsto Inv.inv (𝓝 (1 : G₀)) (𝓝 1))
  proof: by
    have hx' := inv_ne_zero hx
    rw [ContinuousAt]; rw [← map_mul_left_nhds_one₀ hx]; rw [← nhds_translation_mul_inv₀ hx']; rw [tendsto_map'_iff]; rw [tendsto_comap_iff]
    simpa only [Function.comp_def, mul_inv_rev, mul_inv_cancel_right₀ hx']

中文:
定理 余ntinuousInv₀.of_nhds_one
  条件: (h : 收敛 取逆.inv (𝓝 (1 : G₀)) (𝓝 1))
  证明: by
    have hx' := inv_ne_zero hx
    rw [ContinuousAt]; rw [← map_mul_left_nhds_one₀ hx]; rw [← nhds_translation_mul_inv₀ hx']; rw [tendsto_map'_iff]; rw [tendsto_comap_iff]
    simpa only [Function.comp_def, mul_inv_rev, mul_inv_cancel_right₀ hx']

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, _iff, comp_def, inv_ne_zero, mul_inv_rev, tendsto_comap_iff, tendsto_map
-/
theorem ContinuousInv₀.of_nhds_one (h : Tendsto Inv.inv (𝓝 (1 : G₀)) (𝓝 1)) :
    ContinuousInv₀ G₀ where
  continuousAt_inv₀ x hx := by
    have hx' := inv_ne_zero hx
    rw [ContinuousAt]; rw [← map_mul_left_nhds_one₀ hx]; rw [← nhds_translation_mul_inv₀ hx']; rw [tendsto_map'_iff]; rw [tendsto_comap_iff]
    simpa only [Function.comp_def, mul_inv_rev, mul_inv_cancel_right₀ hx']

end map_comap

section ZPow

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [ContinuousMul G₀]

/--
theorem `continuousAt_zpow₀` / 定理 `continuousAt_zpow₀`

English:
theorem continuousAt_zpow₀
  given: (x : G₀) (m : Int) (h : x != 0 ∨ 0 <= m)
  proof: by
  rcases m with m | m
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using continuousAt_pow x m
  · simp only [zpow_negSucc]
    have hx : x != 0 := h.resolve_right (Int.negSucc_lt_zero m).not_ge
    exact (continuousAt_pow x (m + 1)).inv₀ (pow_ne_zero _ hx)

中文:
定理 continuousAt_zpow₀
  条件: (x : G₀) (m : 整数) (h : x != 0 ∨ 0 <= m)
  证明: by
  rcases m with m | m
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using continuousAt_pow x m
  · simp only [zpow_negSucc]
    have hx : x != 0 := h.resolve_right (Int.negSucc_lt_zero m).not_ge
    exact (continuousAt_pow x (m + 1)).inv₀ (pow_ne_zero _ hx)

Depends on / 依赖: Int.negSucc_lt_zero, Int.ofNat_eq_natCast, continuousAt_pow, h.resolve_right, negSucc_lt_zero, not_ge, ofNat_eq_natCast, pow_ne_zero, resolve_right, zpow_natCast, zpow_negSucc
-/
theorem continuousAt_zpow₀ (x : G₀) (m : Int) (h : x != 0 ∨ 0 <= m) :
    ContinuousAt (fun x => x ^ m) x := by
  rcases m with m | m
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using continuousAt_pow x m
  · simp only [zpow_negSucc]
    have hx : x != 0 := h.resolve_right (Int.negSucc_lt_zero m).not_ge
    exact (continuousAt_pow x (m + 1)).inv₀ (pow_ne_zero _ hx)

/--
theorem `continuousOn_zpow₀` / 定理 `continuousOn_zpow₀`

English:
theorem continuousOn_zpow₀
  given: (m : Int)
  statement: ContinuousOn (fun x : G₀ => x ^ m) {0}ᶜ
  proof: fun _x hx =>
  (continuousAt_zpow₀ _ _ (Or.inl hx)).continuousWithinAt

中文:
定理 continuousOn_zpow₀
  条件: (m : 整数)
  结论: ContinuousOn (fun x : G₀ => x ^ m) {0}ᶜ
  证明: fun _x hx =>
  (continuousAt_zpow₀ _ _ (Or.inl hx)).continuousWithinAt
-/
theorem continuousOn_zpow₀ (m : Int) : ContinuousOn (fun x : G₀ => x ^ m) {0}ᶜ := fun _x hx =>
  (continuousAt_zpow₀ _ _ (Or.inl hx)).continuousWithinAt

/--
theorem `Filter.Tendsto.zpow₀` / 定理 `Filter.Tendsto.zpow₀`

English:
theorem Filter.Tendsto.zpow₀
  statement: {f : α -> G₀} {l : Filter α} {a : G₀} (hf : Tendsto f l (𝓝 a)) (m : Int)
  proof: (continuousAt_zpow₀ _ m h).tendsto.comp hf

中文:
定理 滤子.收敛.zpow₀
  结论: {f : α -> G₀} {l : 滤子 α} {a : G₀} (hf : 收敛 f l (𝓝 a)) (m : 整数)
  证明: (continuousAt_zpow₀ _ m h).tendsto.comp hf

Depends on / 依赖: tendsto, tendsto.comp
-/
theorem Filter.Tendsto.zpow₀ {f : α -> G₀} {l : Filter α} {a : G₀} (hf : Tendsto f l (𝓝 a)) (m : Int)
    (h : a != 0 ∨ 0 <= m) : Tendsto (fun x => f x ^ m) l (𝓝 (a ^ m)) :=
  (continuousAt_zpow₀ _ m h).tendsto.comp hf

variable {X : Type*} [TopologicalSpace X] {a : X} {s : Set X} {f : X -> G₀}

@[fun_prop]
nonrec theorem ContinuousAt.zpow₀ (hf : ContinuousAt f a) (m : Int) (h : f a != 0 ∨ 0 <= m) :
    ContinuousAt (fun x => f x ^ m) a :=
  hf.zpow₀ m h

nonrec theorem ContinuousWithinAt.zpow₀ (hf : ContinuousWithinAt f s a) (m : Int)
    (h : f a != 0 ∨ 0 <= m) : ContinuousWithinAt (fun x => f x ^ m) s a :=
  hf.zpow₀ m h

@[fun_prop]
/--
theorem `ContinuousOn.zpow₀` / 定理 `ContinuousOn.zpow₀`

English:
theorem ContinuousOn.zpow₀
  given: (hf : ContinuousOn f s) (m : Int) (h : forall a in s, f a != 0 ∨ 0 <= m)
  proof: fun a ha => (hf a ha).zpow₀ m (h a ha)

@[continuity, fun_prop]

中文:
定理 ContinuousOn.zpow₀
  条件: (hf : ContinuousOn f s) (m : 整数) (h : 对任意 a in s, f a != 0 ∨ 0 <= m)
  证明: fun a ha => (hf a ha).zpow₀ m (h a ha)

@[continuity, fun_prop]
-/
theorem ContinuousOn.zpow₀ (hf : ContinuousOn f s) (m : Int) (h : forall a in s, f a != 0 ∨ 0 <= m) :
    ContinuousOn (fun x => f x ^ m) s := fun a ha => (hf a ha).zpow₀ m (h a ha)

@[continuity, fun_prop]
/--
theorem `Continuous.zpow₀` / 定理 `Continuous.zpow₀`

English:
theorem Continuous.zpow₀
  given: (hf : Continuous f) (m : Int) (h0 : forall a, f a != 0 ∨ 0 <= m)
  proof: continuous_iff_continuousAt.2 fun x => (hf.tendsto x).zpow₀ m (h0 x)

中文:
定理 连续.zpow₀
  条件: (hf : 连续 f) (m : 整数) (h0 : 对任意 a, f a != 0 ∨ 0 <= m)
  证明: continuous_iff_continuousAt.2 fun x => (hf.tendsto x).zpow₀ m (h0 x)

Depends on / 依赖: continuous_iff_continuousAt, hf.tendsto, tendsto
-/
theorem Continuous.zpow₀ (hf : Continuous f) (m : Int) (h0 : forall a, f a != 0 ∨ 0 <= m) :
    Continuous fun x => f x ^ m :=
  continuous_iff_continuousAt.2 fun x => (hf.tendsto x).zpow₀ m (h0 x)

end ZPow
