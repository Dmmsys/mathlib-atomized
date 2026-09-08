/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Ring.Action.Pointwise.Set

/-!
# Homeomorphism between a normed space and sphere times `(0, +∞)`

In this file we define a homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) r × Set.Ioi (0 : ℝ)`, `r > 0`.
One may think about it as generalization of polar coordinates to any normed space.

We also specialize this definition to the case `r = 1` and prove
-/

@[expose] public section

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

open Filter Set Metric
open scoped Pointwise Set.Notation Topology

/-- The natural homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) r × Set.Ioi (0 : ℝ)`, `0 < r`.

The forward map sends `⟨x, hx⟩` to `⟨r • ‖x‖⁻¹ • x, ‖x‖ / r⟩`,
the inverse map sends `(x, r)` to `r • x`.

In the case of the unit sphere `r = `,
one may think about it as generalization of polar coordinates to any normed space. -/
@[simps apply_fst_coe apply_snd_coe symm_apply_coe]
/-
**homeomorphSphereProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：homeomorphSphereProd (E : Type*) [NormedAddCommGroup E] [NormedSpace Real 
E] (r : Real) (hr : 0 < r) : ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) r × Ioi (0 : Real
)) where toFun x
参数：E : Type*；r : Real；hr : 0 < r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) r × Set.Ioi (0 : ℝ)`, `0 < r`.

The forward map sends `⟨x, hx⟩` to `⟨r • ‖x‖⁻¹ • x, ‖x‖ / r⟩`,
the inverse map sends `(x, r)` to `r • x`.

In the case of the unit sphere `r = `,
one may think about it as generalization of polar coordinates to any normed spac
e.
-/
noncomputable def homeomorphSphereProd (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) :
    ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) r × Ioi (0 : ℝ)) where
  toFun x :=
    have : 0 < ‖(x : E)‖ := by simpa [-Subtype.coe_prop] using x.2
    (⟨r • ‖x.1‖⁻¹ • x.1, by simp [norm_smul, abs_of_pos hr, this.ne']⟩,
      ⟨‖x.1‖ / r, by rw [mem_Ioi]; positivity⟩)
  invFun x := ⟨x.2.1 • x.1.1, smul_ne_zero x.2.2.out.ne' (ne_of_mem_sphere x.1.2 hr.ne')⟩
  left_inv
  | ⟨x, hx⟩ => by
    have : 0 < ‖x‖ := by simpa using hx
    ext; simp only [smul_smul]; field_simp; simp
  right_inv
  | (⟨x, hx⟩, ⟨d, hd⟩) => by
    rw [mem_Ioi] at hd
    rw [mem_sphere_zero_iff_norm] at hx
    simp (disch := positivity) [norm_smul, smul_smul, abs_of_pos hd, hx]
  continuous_toFun := by
    simp only
    fun_prop (disch := simp)

/-- The natural homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)`.

The forward map sends `⟨x, hx⟩` to `⟨‖x‖⁻¹ • x, ‖x‖⟩`,
the inverse map sends `(x, r)` to `r • x`.

One may think about it as generalization of polar coordinates to any normed space.
See also `homeomorphSphereProd` for a version that works for a sphere of any positive radius. -/
@[simps! apply_fst_coe apply_snd_coe symm_apply_coe]
/-
**homeomorphUnitSphereProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：homeomorphUnitSphereProd : ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) 1 × Ioi (0 : 
Real))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural homeomorphism between nonzero elements of a normed space `E`
and `Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)`.

The forward map sends `⟨x, hx⟩` to `⟨‖x‖⁻¹ • x, ‖x‖⟩`,
the inverse map sends `(x, r)` to `r • x`.

One may think about it as generalization of polar coordinates to any normed spac
e.
See also `homeomorphSphereProd` for a version that works for a sphere of any pos
itive radius.
-/
noncomputable def homeomorphUnitSphereProd :
    ({0}ᶜ : Set E) ≃ₜ (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
  homeomorphSphereProd E 1 one_pos

variable {E}

/-- If `U ∌ 0` is an open set on the real line and `V` is an open set on a sphere of nonzero radius,
then their pointwise scalar product is an open set. -/
/-
**IsOpen.smul_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.smul_sphere {r : Real} (hr : r != 0) {U : Set Real} {V : Set (Metri
c.sphere (0 : E) r)} (hU : IsOpen U) (hU₀ : 0 ∉ U) (hV : IsOpen V) : IsOpen (U •
 (V : Set E))
参数：hr : r != 0；Metric.sphere (0 : E) r；hU : IsOpen U；hU₀ : 0 ∉ U；hV : IsOpen V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `prod_mem_nhds`：prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx
 : s in 𝓝 x) (hy : t in 𝓝 y) : s ×ˢ t in 𝓝 (x, y)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `IsOpen.preimage_val`：IsOpen.preimage_val {s t : Set X} (ht : IsOpen t) :
 IsOpen (s ↓inter t)
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `homeomorphSphereProd_symm_apply_coe`：∀ (E : Type u_2) [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] (r : ℝ) (hr : 0 < r)   (x : ↑(Metric.sphe
re 0 r) × ↑(Set.Ioi 0)), …
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_nhds_subtype_val`：map_nhds_subtype_val {s : Set X} (x : s) : map ((↑
) : s -> X) (𝓝 x) = 𝓝[s] ↑x
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
If `U ∌ 0` is an open set on the real line and `V` is an open set on a sphere of
 nonzero radius,
then their pointwise scalar product is an open set.
-/
theorem IsOpen.smul_sphere {r : ℝ} (hr : r ≠ 0) {U : Set ℝ} {V : Set (Metric.sphere (0 : E) r)}
    (hU : IsOpen U) (hU₀ : 0 ∉ U) (hV : IsOpen V) : IsOpen (U • (V : Set E)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxU, _, ⟨y, hyV, rfl⟩, rfl⟩
  wlog hx₀ : 0 < x generalizing x U
  · replace hx₀ : 0 < -x := by
      rw [not_lt, le_iff_eq_or_lt, ← neg_pos] at hx₀
      exact hx₀.resolve_left <| ne_of_mem_of_not_mem hxU hU₀
    specialize this hU.neg (by simpa) (-x) (by simpa) hx₀
    simp only [neg_smul, nhds_neg, Set.neg_smul, Filter.mem_neg] at this
    simpa using this
  have hr₀ : 0 < r := lt_of_le_of_ne (by simpa using norm_nonneg y.1) hr.symm
  lift x to Ioi (0 : ℝ) using hx₀
  have : V ×ˢ (Ioi (0 : ℝ) ↓∩ U) ∈ 𝓝 (y, x) :=
    prod_mem_nhds (hV.mem_nhds hyV) (hU.preimage_val.mem_nhds hxU)
  replace := image_mem_map (m := Subtype.val ∘ (homeomorphSphereProd E r hr₀).symm) this
  rw [← Filter.map_map, (homeomorphSphereProd _ r hr₀).symm.map_nhds_eq,
    map_nhds_subtype_val, IsOpen.nhdsWithin_eq, homeomorphSphereProd_symm_apply_coe] at this
  · filter_upwards [this]
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    rw [Function.comp_apply, homeomorphSphereProd_symm_apply_coe]
    apply Set.smul_mem_smul
    exacts [hb, mem_image_of_mem _ ha]
  · exact isOpen_compl_singleton
  · simp [x.2.out.ne', ne_zero_of_mem_sphere, hr₀.ne']
